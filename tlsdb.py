#!/usr/bin/env python3
# Author:
#     Christian Heimes <christian@python.org>

import collections
import datetime
import logging
import functools
import json
import os
import re
import tempfile

from pycparser import c_ast, parse_file
import lxml.html
import requests

LOG = logging.getLogger(__name__)

FILES = {
    'openssl-master': {
        'type': 'openssl',
        'base': 'https://raw.githubusercontent.com/openssl/openssl/master/',
        'files': [
            'include/openssl/ssl3.h',
            'include/openssl/tls1.h',
            'include/openssl/dtls1.h',
            'ssl/s3_lib.c',
        ],
    },
    'openssl-1.0.2': {
        'type': 'openssl',
        'base': 'https://raw.githubusercontent.com/openssl/openssl/OpenSSL_1_0_2-stable/',
        'files': [
            # 'ssl/ssl2.h',
            'ssl/ssl3.h',
            'ssl/tls1.h',
            'ssl/dtls1.h',
            'ssl/s3_lib.c',
        ],
    },
    'gnutls-master': {
        'type': 'gnutls',
        'base': 'https://gitlab.com/gnutls/gnutls/raw/master/',
        'files': ['lib/algorithms/ciphersuites.c'],
    },
    'nss-tip': {
        'type': 'nss',
        'base': 'https://hg.mozilla.org/projects/nss/raw-file/tip/',
        'files': ['lib/ssl/sslproto.h'],
    },
    'mod_nss-master': {
        'type': 'mod_nss',
        'base': 'https://git.fedorahosted.org/cgit/mod_nss.git/plain/',
        'files': ['nss_engine_cipher.c'],
    },
    'iana': {
        'type': 'iana',
        'base': 'http://www.iana.org/assignments/tls-parameters/',
        'files': ['tls-parameters.xhtml'],
    },
    'mozilla-server-side': {
        'type': 'serverside',
        'comment': 'https://wiki.mozilla.org/Security/Server_Side_TLS',
        'base': 'https://statics.tls.security.mozilla.org/',
        'files': ['server-side-tls-conf.json'],
    },
}


TRANSLATE_TLS_VERSION = {
    # OpenSSL
    'SSL3_VERSION': 'SSLv3',
    'TLS1_VERSION': 'TLSv1.0',
    'TLS1_1_VERSION': 'TLSv1.1',
    'TLS1_2_VERSION': 'TLSv1.2',
    'TLS1_3_VERSION': 'TLSv1.3',
    'DTLS1_VERSION': 'DTLSv1.0',
    'DTLS1_1_VERSION': 'DTLSv1.1',
    'DTLS1_2_VERSION': 'DTLSv1.2',
    'DTLS1_3_VERSION': 'DTLSv1.3',
    'DTLS1_BAD_VER': 'DTLS1_BAD_VER',
    # NSS
    'SSLV3': 'SSLv3',
    'TLSV1': 'TLSv1.0',
    'TLSV1_1': 'TLSv1.1',
    'TLSV1_2': 'TLSv1.2',
    'TLSV1_3': 'TLSv1.3',
    # invalid
    0: None,
}


CipherSuite = collections.namedtuple('CipherSuite', 'prefix kea auth enc mode hash secure export name')
CipherKEA = collections.namedtuple('CipherKEA', 'name family elliptic ephemeral')
CipherAuth = collections.namedtuple('CipherAuth', 'name family secure')
CipherEnc = collections.namedtuple('CipherEnc', 'name family bits type secure')
CipherMode = collections.namedtuple('CipherMode', 'name aead ae')
CipherHash = collections.namedtuple('CipherHash', 'name family bits secure')

NULL_MODE = CipherMode(None, False, False),

# XXX review names and values
CIPHER_SUITE_PARTS = {
    'kea': {
        'DHE': CipherKEA('DHE', 'DH', False, True),
        'DH': CipherKEA('DH', 'DH', False, False),
        'ECDHE': CipherKEA('ECDHE', 'DH', True, True),
        'ECDH': CipherKEA('ECDH', 'DH', True, False),
        # 'FORTEZZA_KEA',
        # 'GOST',
        # 'GOST94',
        # 'GOST01',
        # 'GOST2001',
        'SRP_SHA': CipherKEA('SRP_SHA', 'PAKE', False, False),  # KEA and auth with PAKE
        'RSA': CipherKEA('RSA', 'kRSA', False, False),
    },
    'auth': {
        'DSS_EXPORT': CipherAuth('DSS_EXPORT', 'DSS', False),
        'DSS': CipherAuth('DSS', 'DSS', False),
        'ECDSA': CipherAuth('ECDSA', 'ECDSA', True),
        'KRB5': CipherAuth('KRB5', 'KRB5', None),
        'KRB5_EXPORT': CipherAuth('KRB_EXPORT', 'KRB', False),
        'NULL': CipherAuth('NULL', 'aNULL', False),
        'PSK': CipherAuth('PSK', 'PAKE', None),
        'PSK_DHE': CipherAuth('PSK_DHE', 'PAKE', None),  # reversed order
        'RSA': CipherAuth('RSA', 'aRSA', True),
        'RSA_EXPORT': CipherAuth('RSA_EXPORT', 'aRSA', False),
        'RSA_FIPS': CipherAuth('RSA_FIPS', 'aRSA', None),
        'SRP_SHA': CipherAuth('SRP_SHA', 'PAKE', None),  # KEA and auth with PAKE
        'anon_EXPORT': CipherAuth('anon_EXPORT', 'aNULL', False),
        'anon': CipherAuth('anon', 'aNULL', False),
    },
    'enc': {
        '3DES_EDE': CipherEnc('3DES_EDE', '3DES', 168, 'block', False),  # Triple-DES encrypt/decrypt/encrypt
        'AES_128': CipherEnc('AES_128', 'AES', 128, 'block', True),
        'AES_256': CipherEnc('AES_256', 'AES', 256, 'block', True),
        'ARIA_128': CipherEnc('ARIA_128', 'ARIA', 'block', 128, False),
        'ARIA_256': CipherEnc('ARIA_128', 'ARIA', 'block', 256, False),
        'CAMELLIA_128': CipherEnc('CAMELLIA_128', 'block', 'CAMELLIA', 128, False),
        'CAMELLIA_256': CipherEnc('CAMELLIA_256', 'block', 'CAMELLIA', 256, False),
        'CHACHA20' : CipherEnc('CHACHA20', 'CHACHA20', 'stream', 256, True),
        'DES' : CipherEnc('DES', 'DES', 56, 'block', False),
        'DES40': CipherEnc('DES40', 'DES', 40, 'block', False),  # also DES_CBC_40
        'FORTEZZA': CipherEnc('FORTEZZA', 'SKIPJACK', 80, 'block', False),
        'GOST89': CipherEnc('GOST89', 'GOST89', None, 'block', False),  # XXX block size?
        # 'GOST2814789CNT',
        # 'GOST2814789CNT12',
        'IDEA': CipherEnc('IDEA', 'IDEA', 128, 'block', False),
        'NULL': CipherEnc('NULL', 'eNULL', 0, None, False),
        'RC2' : CipherEnc('RC2', 'RC2', 64, 'stream', False),
        'RC2_40': CipherEnc('RC2_40', 'RC2_40', 40, 'stream', False),  # RC2_CBC_40
        'RC4_128': CipherEnc('RC4_128', 'RC4', 'stream', 128, False),
        'RC4_40': CipherEnc('RC4_40', 'RC4', 'stream', 40, False),
        'SEED': CipherEnc('SEED', 'SEED', 128, 'block', False),
    },
    'mode': {
        'CBC': CipherMode('CBC', False, False),
        'CBC_40': CipherMode('CBC', False, False),
        'CCM': CipherMode('CCM', False, True),
        'CCM_8': CipherMode('CCM', False, True),
        'GCM': CipherMode('GCM', True, True),
        'POLY1305': CipherMode('POLY1305', True, True),
    },
    'hash': {
        # 'GOST89MAC',
        # 'GOST89MAC12',
        # 'GOST94',
        'NULL': CipherHash('NULL', None, 0, False),
        'MD5': CipherHash('MD5', 'MD5', 128, False),
        'SHA': CipherHash('SHA', 'SHA-1', 160, False),
        'SHA256': CipherHash('SHA256', 'SHA-2', 256, True),
        'SHA384': CipherHash('SHA384', 'SHA-2', 384, True),
    },
}

CIPHER_SUITE_RE_TEMPLATE = (
    r'^(?P<prefix>(TLS|SSL))_'
    r'((?P<kea>({kea}))_)?'
    r'(?P<auth>({auth}))_'
    r'WITH_'
    r'(?P<enc>({enc}))'
    r'(_(?P<mode>({mode})))?'
    r'(_(?P<hash>({hash})))?'
    r'$'
)

CIPHER_SUITE_RE = re.compile(CIPHER_SUITE_RE_TEMPLATE.format(
    **{key: '|'.join(sorted(values)) for key, values in CIPHER_SUITE_PARTS.items()}
))


def parse_suite(name, extended=False):
    """Parse a TLS cipher suite name

    :param name: TLS cipher suite
    :return: dict
    """
    mo = CIPHER_SUITE_RE.match(name)
    if mo is None:
        raise ValueError(name)
    cipher = mo.groupdict()
    cipher['name'] = name
    cipher['export'] = False
    cipher['secure'] = None

    # check for export auth
    if cipher['auth'].endswith('_EXPORT'):
        cipher['auth'] = cipher['auth'][:-7]
        cipher['export'] = True

    # anon is an alias for NULL
    if cipher['auth'] == 'anon':
        cipher['auth'] = 'NULL'

    # without explicit key, suite uses same algorithm for KEA and auth
    if not cipher['kea']:
        cipher['kea'] = cipher['auth']

    # CCM mode has implicit default TLS 1.2 PRF SHA256 (RFC 6655)
    if cipher['hash'] is None and cipher['mode'] in {'CCM', 'CCM_8'}:
        cipher['hash'] = 'SHA256'
    # mode CBC_40 is CBC with 40 bit export encryption
    if cipher['mode'] == 'CBC_40':
        cipher['export'] = True
        cipher['mode'] = 'CBC'
        if cipher['enc'] == 'RC2':
            cipher['enc'] = 'RC2_40'
        elif cipher['enc'] == 'DES':
            cipher['enc'] = 'DES40'
        else:
            raise ValueError(name, cipher['mode'], cipher['enc'])
    # export encryption
    if cipher['enc'] in {'DES40', 'RC2_40', 'RC4_40'}:
        cipher['export'] = True

    if extended:
        for key, info in sorted(CIPHER_SUITE_PARTS.items()):
            cur = cipher[key]
            if key == 'mode' and cur is None:
                value = NULL_MODE
            elif key == 'kea':
                value = info.get(cur, cur)
            elif cur not in info:
                raise ValueError(key, cipher.get(cur), cipher)
            else:
                value = info[cur]
            cipher[key] = value
        cipher['secure'] = not cipher['export'] and all(cipher[key].secure for key in ('auth', 'enc', 'hash'))

    return CipherSuite(**cipher)


def _format_hexid(hexid):
    if hexid[0:2] != '0x' or hexid[4:7] != ',0x':
        raise ValueError(hexid)
    big = int(hexid[2:4], 16)
    little = int(hexid[7:9], 16)
    num = (big << 8) + little
    return '0x{:02X},0x{:02X}'.format(big, little), num


class ParseOpenSSLHeaders(object):
    """Parser OpenSSL headers

    Extract cipher hexid, cipher name and aliases
    """

    openssl_ck_re = re.compile(
        r'^#\s*define\s+'
        r'(?:SSL2|SSL3|TLS1|TLS1_3)_CK_([A-Z0-9_]*)\s+'
        r'0x([0-9A-Fa-f]{8}).*'
    )

    openssl_ck_alias_re = re.compile(
        r'^#\s*define\s+'
        r'(?:SSL2|SSL3|TLS1)_CK_([A-Z0-9_]*)\s+'
        r'(?:SSL2|SSL3|TLS1)_CK_([A-Z0-9_]*).*')

    openssl_txt_re = re.compile(
        r'^#\s*define\s+'
        r'(?:SSL2|SSL3|TLS1|TLS1_3)_TXT_([A-Z0-9_]*)\s+'
        r'"(.*)".*'
    )

    def __init__(self):
        # constant to (integer, short hexid)
        self.const2int = {}
        # CK to CK alias
        self.aliases = {}
        # CK to name
        self.const2name = {}
        # short hexid to long int ids
        self.hexid2num = collections.defaultdict(set)

    def feed(self, text):
        for line in text.split('\n'):
            mo = self.openssl_ck_re.match(line)
            if mo is not None:
                const = mo.group(1)
                if const in {'FALLBACK_SCSV', 'SCSV'}:
                    # OpenSSL has no TXT name for SCSV
                    continue
                if 'FZA_DMS' in const:
                    # Clashes with KRB5 and no longer used
                    continue
                num = int(mo.group(2), 16)
                alt = (num >> 16) & 255
                if alt:
                    # Some alternative name, ignore
                    continue
                hexid = '0x{:02X},0x{:02X}'.format((num >> 8) & 255, num & 255)
                self.const2int[const] = (num, hexid)
                self.hexid2num[hexid].add(num)
                continue
            mo = self.openssl_ck_alias_re.match(line)
            if mo is not None:
                self.aliases[mo.group(1)] = mo.group(2)
                continue
            mo = self.openssl_txt_re.match(line)
            if mo is not None:
                const = mo.group(1)
                if 'FZA_DMS' in const:
                    # Clashes with KRB5 and no longer used
                    continue
                self.const2name[const] = mo.group(2)

    def feed_file(self, filename):
        with open(filename) as f:
            self.feed(f.read())

    def resolve(self):
        hexid2cipher = {}
        aliases = {}
        for const in self.const2int:
            if const in self.aliases:
                continue
            num, hexid = self.const2int[const]
            name = self.const2name[const]
            if hexid not in hexid2cipher:
                hexid2cipher[hexid] = {
                    'openssl': name,
                    'openssl_num': hex(num),
                }
            else:
                raise ValueError(name)

        for alias, dest in self.aliases.items():
            # OpenSSL has aliases like EDH_RSA_DES_192_CBC3_SHA to EDH_RSA_DES_192_CBC3_SHA
            name = self.const2name[alias]
            num, hexid = self.const2int[dest]
            aliases[name] = hexid

        return hexid2cipher, aliases


class ParseOpenSSLCipherSuite(object):
    """Parse SSL_CIPHER table (s3_lib.c)
    """
    extra_headers = [
        "#define OPENSSL_GLOBAL static",
        "typedef struct ssl_cipher_st SSL_CIPHER;",
    ]

    define_re = re.compile(
        (r'^\s*#\s*define\s+(?:SSL2|SSL3|TLS1|TLS1_3)_(?:CK|TXT)')
    )

    def __init__(self):
        self.headers = []
        self.suite = []
        self.ciphers = []

    def feed_file(self, filename):
        if filename.endswith('s3_lib.c'):
            self.read_s3lib(filename)
        elif filename.endswith('.h'):
            self.read_header(filename)
        else:
            raise ValueError(filename)

    def read_s3lib(self, filename):
        # extra ssl3_cipher init table
        extract = False
        with open(filename) as f:
            for line in f:
                if extract:
                    if line.strip().startswith('#'):
                        # skip #ifdef / #endif
                        continue
                    if line.strip().startswith('*'):
                        continue
                    self.suite.append(line.rstrip())
                    if line.strip() == '};':
                        break
                elif 'SSL_CIPHER ssl3_ciphers' in line:
                    self.suite.append(line.strip())
                    extract = True

    def read_header(self, filename):
        with open(filename) as f:
            for line in f:
                if self.define_re.match(line):
                    # remove comments
                    line = line.split('/*')[0].strip()
                    self.headers.append(line)

    def _handle_expr(self, cipher_expr, i, raw=False, multi=False):
        expr = cipher_expr.exprs[i]
        if isinstance(expr, c_ast.Constant):
            value = expr.value
            if raw:
                pass
            elif expr.type == 'int':
                if value.startswith('0x'):
                    value = int(value[2:], 16)
                else:
                    value = int(value)
            elif expr.type == 'string':
                value = value.strip('"')
        elif isinstance(expr, c_ast.ID):
            value = expr.name
        elif isinstance(expr, c_ast.BinaryOp):
            value = []
            while isinstance(expr, c_ast.BinaryOp):
                value.append(expr.right.name)
                expr = expr.left
            value.append(expr.name)
        else:
            raise ValueError(cipher_expr, i, expr)
        if multi:
            if value == 0:
                value = []
            elif not isinstance(value, list):
                value = [value]
        return value

    def handle_cipher(self, cipher_expr):
        handle = functools.partial(self._handle_expr, cipher_expr)
        tv = TRANSLATE_TLS_VERSION
        num = handle(2) & 65535
        hexid = '0x{:02X},0x{:02X}'.format((num >> 8) & 255, num & 255)
        kea = handle(3)
        auth = handle(4)

        cipher = dict(
            hexid=hexid,
            valid=bool(handle(0)),
            name=handle(1),
            kea=kea if kea else None,
            auth=auth if auth else None,
            enc=handle(5),
            mac=handle(6)
        )
        if len(cipher_expr.exprs) == 15:
            cipher.update(
                min_tls=tv[handle(7)],
                max_tls=tv[handle(8)],
                min_dtls=tv[handle(9)],
                max_dtls=tv[handle(10)],
                algo_strength=handle(11, multi=True),
                flags=handle(12, multi=True),  # algorithm2
                strength_bits=int(handle(13)),
                alg_bits=int(handle(14)),
            )
        else:
            cipher.update(
                min_tls=tv[handle(7)],
                max_tls=None,
                min_dtls=None,
                max_dtls=None,
                algo_strength=handle(8, multi=True),
                flags=handle(9, multi=True),  # algorithm2
                strength_bits=int(handle(10)),
                alg_bits=int(handle(11)),
            )
        self.ciphers.append(cipher)

    def parse(self):
        with tempfile.NamedTemporaryFile('w') as f:
            f.write('\n'.join(self.extra_headers))
            f.write('\n\n')
            f.write('\n'.join(self.headers))
            f.write('\n\n')
            f.write('\n'.join(self.suite))
            f.flush()
            ast = parse_file(f.name, use_cpp=True)
        cipher_exprs = ast.ext[-1].init.exprs
        for cipher_expr in cipher_exprs:
            self.handle_cipher(cipher_expr)
        return self.ciphers


class TLSDB(object):
    iana_table_id = 'table-tls-parameters-4'
    source_files = FILES

    tls13_draft = 'draft-ietf-tls-tls13-18'
    tls13_draft_ciphers = {
        '0x13,0x01': 'TLS_AES_128_GCM_SHA256',
        '0x13,0x02': 'TLS_AES_256_GCM_SHA384',
        '0x13,0x03': 'TLS_CHACHA20_POLY1305_SHA256',
        '0x13,0x04': 'TLS_AES_128_CCM_SHA256',
        '0x13,0x05': 'TLS_AES_128_CCM_8_SHA256',
    }

    def __init__(self, downloaddir='downloads'):
        self.downloaddir = downloaddir
        # hex id string to cipher dict
        self.ciphers = {}
        # library -> ciphername -> hex id
        self.indexes = {}
        # Mozilla server side TLS
        self.serverside = {}
        # parsed IANA suites
        self.suites = {}
        # extra fields
        self.fields = {
            'kea': set(),
            'auth': set(),
            'enc': set(),
            'mac': set(),
            'algo_strength': set(),
            'flags': set(),

        }

    def download(self, refresh=False):
        for lib, options in sorted(self.source_files.items()):
            destdir = os.path.join(self.downloaddir, lib)
            if not os.path.isdir(destdir):
                os.makedirs(destdir)
            base = options['base']
            for suffix in options['files']:
                destname = os.path.join(destdir, os.path.basename(suffix))
                if os.path.isfile(destname) and not refresh:
                    LOG.debug("'%s' exists", destname)
                    continue
                url = ''.join((base, suffix))
                LOG.info("Downloading %s to %s", url, destname)
                r = requests.get(url)
                r.raise_for_status()
                with open(destname, 'wb') as f:
                    f.write(r.content)

    def get_files(self, lib):
        destdir = os.path.join(self.downloaddir, lib)
        options = self.source_files[lib]
        for suffix in options['files']:
            yield os.path.join(destdir, os.path.basename(suffix))

    def get_file(self, lib):
        files = list(self.get_files(lib))
        if len(files) != 1:
            raise ValueError(lib, files)
        return files[0]

    def get_libs(self, libtype):
        for lib, options in sorted(self.source_files.items()):
            if options['type'] == libtype:
                yield lib

    def add_cipher(self, hexid, cipherdict):
        lib = 'iana'
        libname = cipherdict[lib]
        cipherdict.update(
            openssl=None, gnutls=None, nss=None, mod_nss=None,
        )
        self.ciphers[hexid] = cipherdict
        self.indexes[lib][libname] = hexid

    def update_cipher(self, lib, hexid, cipherdict):
        libname = cipherdict[lib]
        if hexid not in self.ciphers or hexid is None:
            LOG.info("%s: %s from %s not in IANA list", hexid, libname, lib)
            return False

        self.ciphers[hexid].update(cipherdict)
        self.indexes[lib][libname] = hexid

        for fieldname in self.fields:
            fieldvalue = cipherdict.get(fieldname)
            if fieldvalue is not None:
                if isinstance(fieldvalue, (tuple, list)):
                    self.fields[fieldname].update(fieldvalue)
                else:
                    self.fields[fieldname].add(fieldvalue)

    def parse_iana(self):
        """Parse IANA XHTML document and return cipher suite metadata

        :param text: Text of IANA tls-parameters.xhtml
        """
        lib = 'iana'
        self.indexes.setdefault(lib, {})
        doc = lxml.html.parse(self.get_file('iana'))
        table = doc.xpath('//table[@id=$table_id]', table_id=self.iana_table_id)
        if not table:
            raise ValueError('Table {} not found'.format(self.iana_table_id))

        for tr in table[0].xpath('./tbody/tr'):
            hexid = tr[0].text.strip()
            name = tr[1].text.strip()
            if name.lower().startswith(('reserved', 'unassigned')) or len(hexid) != 9:
                # reserved or unassigned range
                continue
            dtls_ok = tr[2].text.strip().upper()
            rfcs = tr[3].xpath('a/text()')

            hexid, num = _format_hexid(hexid)
            cipherdict = {
                'num': num,
                'iana': name,
                'dtls': True if dtls_ok == 'Y' else False,
                'rfcs': rfcs,
            }
            self.add_cipher(hexid, cipherdict)

    def parse_tls13_draft(self):
        lib = 'iana'
        self.indexes.setdefault(lib, {})
        for hexid, name in self.tls13_draft_ciphers.items():
            hexid, num = _format_hexid(hexid)
            cipherdict = {
                'num': num,
                'iana': name,
                'dtls': True,
                'rfcs': [self.tls13_draft],
            }
            self.add_cipher(hexid, cipherdict)

    gnutls_re = re.compile(
        r'^#\s*define\s+'
        r'GNU(TLS_[A-Z0-9_]*)\s+'
        r'\{\s*'
        r'0x([0-9A-Fa-f]{2})[,\ ]+'
        r'0x([0-9A-Fa-f]{2})\s*'
        r'\}.*')

    def parse_gnutls(self):
        lib = 'gnutls'
        self.indexes.setdefault(lib, {})
        filename = self.get_file('gnutls-master')
        with open(filename) as f:
            for line in f:
                mo = self.gnutls_re.match(line)
                if mo is None:
                    continue
                name, b, l = mo.groups()
                # regexp does not include 0x
                hexid = '0x{},0x{}'.format(b, l)
                hexid, _ = _format_hexid(hexid)
                self.update_cipher(lib, hexid, {lib: name})

    nss_re = re.compile(
        r'^#\s*define\s+'
        r'(TLS_[A-Z0-9_]*)\s+'
        r'0x([0-9A-Fa-f]{2})([0-9A-Fa-f]{2}).*'
    )

    def parse_nss(self):
        lib = 'nss'
        self.indexes.setdefault(lib, {})
        filename = self.get_file('nss-tip')
        with open(filename) as f:
            for line in f:
                mo = self.nss_re.match(line)
                if mo is None:
                    continue
                name, b, l = mo.groups()
                # regexp does not include 0x
                hexid = '0x{},0x{}'.format(b, l)
                hexid, _ = _format_hexid(hexid)
                self.update_cipher(lib, hexid, {lib: name})

    mod_nss_re = re.compile(
        r'\s*\{'
        r'\"(?P<mod_nss>\w+)\",\s*'
        r'(?P<iana>(TLS|SSL)_\w+),\s*'
        r'\"(?P<openssl>[\w-]+)\",\s*'
        r'(?P<attr>[\w|]+),\s*'
        r'(?P<version>\w+),\s*'
        r'(?P<strength>\w+),\s*'
        r'(?P<bits>\d+),\s*'
        r'(?P<alg_bits>\d+)'
    )

    def parse_mod_nss_extended(self):
        """Parse mod_nss cipher names

        Returns a list of NSS cipher suite infos
        """
        lib = 'mod_nss'
        self.indexes.setdefault(lib, {})
        start = False
        filename = self.get_file('mod_nss-master')
        with open(filename) as f:
            for line in f:
                if line.startswith('cipher_properties'):
                    start = True
                elif not start:
                    continue
                elif line.startswith('};'):
                    break

                mo = self.mod_nss_re.match(line)
                if not mo:
                    continue

                match = mo.groupdict()
                match['attr'] = set(match['attr'].split('|'))
                match['bits'] = int(match['bits'])
                match['alg_bits'] = int(match['alg_bits'])
                match['version'] = TRANSLATE_TLS_VERSION[match['version']]

                # some cipher elemets aren't flagged
                for algo in ['SHA256', 'SHA384']:
                    if match['iana'].endswith(algo):
                        match['attr'].add('SSL_{}'.format(algo))

                # cipher block chaining isn't tracked
                if '_CBC' in match['iana']:
                    match['attr'].add('SSL_CBC')

                yield match

    def parse_mod_nss(self):
        lib = 'mod_nss'
        self.indexes.setdefault(lib, {})
        for ciphersuite in self.parse_mod_nss_extended():
            iana = ciphersuite['iana']
            name = ciphersuite['mod_nss']
            hexid = self.indexes['iana'].get(iana)
            self.update_cipher(lib, hexid, {lib: name})

    def parse_openssl_headers(self):
        lib = 'openssl'
        self.indexes.setdefault(lib, {})
        parser = ParseOpenSSLHeaders()
        for libname in self.get_libs(lib):
            for filename in self.get_files(libname):
                if filename.endswith('.h'):
                    parser.feed_file(filename)

        ciphers, aliases = parser.resolve()
        for hexid, cipherdict in ciphers.items():
            self.update_cipher(lib, hexid, cipherdict)
        # extra aliases
        self.indexes[lib].update(aliases)

    def parse_openssl_suites(self):
        lib = 'openssl'
        self.indexes.setdefault(lib, {})
        parser = ParseOpenSSLCipherSuite()
        for filename in self.get_files('openssl-master'):
            parser.feed_file(filename)
        ciphersuites = parser.parse()

        for cipherdict in ciphersuites:
            hexid = cipherdict.pop('hexid')
            cipherdict.pop('valid')
            cipherdict['openssl'] = cipherdict.pop('name')
            self.update_cipher(lib, hexid, cipherdict)

    def parse_serverside(self):
        lib = 'mozilla-server-side'
        filename = self.get_file(lib)
        with open(filename) as f:
            data = json.load(f)
        # OpenSSL names
        hexid2serverside = collections.defaultdict(dict)
        for key, cfg in data['configurations'].items():
            for i, openssl_name in enumerate(cfg['ciphersuites']):
                hexid = self.indexes['openssl'][openssl_name]
                hexid2serverside[hexid][key] = i
        # update cipher directly
        for hexid, serverside in hexid2serverside.items():
            self.ciphers[hexid]['mozilla_server_side'] = serverside

    def parse_suite_strings(self):
        for name, hexid in self.indexes['iana'].items():
            if 'WITH' not in name:
                continue
            self.suites[hexid] = parse_suite(name, True)

    def process(self, refresh=False):
        self.download(refresh)
        self.parse_iana()
        self.parse_tls13_draft()
        self.parse_suite_strings()
        self.parse_gnutls()
        self.parse_nss()
        self.parse_mod_nss()
        self.parse_openssl_headers()
        self.parse_openssl_suites()
        self.parse_serverside()

    def dump(self, file=None):
        # JSON decoder doesn't dump namedtuples as dict
        suites = {}
        for hexid, suite in self.suites.items():
            suite = suite._asdict()
            for key, value in suite.items():
                if hasattr(value, '_asdict'):
                    suite[key] = value._asdict()
            suites[hexid] = suite

        result = {
            'about': {
                'author': 'Christian Heimes',
                'email': 'christian at python.org',
                'created': datetime.datetime.utcnow().strftime('%Y%m%dT%H:%M:%S'),
                'sources': self.source_files,
            },
            'ciphers': self.ciphers,
            'indexes': self.indexes,
            'flags': {name: sorted(v for v in value if v)
                      for name, value in sorted(self.fields.items())},
            'suites': suites,
        }
        if file is None:
            return json.dumps(result, sort_keys=True, indent=2)
        else:
            return json.dump(result, file, sort_keys=True, indent=2)


if __name__ == '__main__':
    logging.basicConfig(level=logging.INFO)
    tlsdb = TLSDB()
    tlsdb.process()
    with open('tlsdb.json', 'w') as f:
        tlsdb.dump(f)
    for name in sorted(tlsdb.indexes['iana']):
        if 'WITH' not in name:
            continue
        suite = parse_suite(name, True)
        if suite.secure and suite.mode.name != 'CCM':
            print(suite.name)
