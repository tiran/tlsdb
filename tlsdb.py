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
    'DTLS1_VERSION': 'DTLSv1.0',
    'DTLS1_1_VERSION': 'DTLSv1.1',
    'DTLS1_2_VERSION': 'DTLSv1.2',
    'DTLS1_BAD_VER': 'DTLS1_BAD_VER',
    # NSS
    'SSLV3': 'SSLv3',
    'TLSV1': 'TLSv1.0',
    'TLSV1_1': 'TLSv1.1',
    'TLSV1_2': 'TLSv1.2',
    # invalid
    0: None,
}


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
        r'(?:SSL2|SSL3|TLS1)_CK_([A-Z0-9_]*)\s+'
        r'0x([0-9A-Fa-f]{8}).*'
    )

    openssl_ck_alias_re = re.compile(
        r'^#\s*define\s+'
        r'(?:SSL2|SSL3|TLS1)_CK_([A-Z0-9_]*)\s+'
        r'(?:SSL2|SSL3|TLS1)_CK_([A-Z0-9_]*).*')

    openssl_txt_re = re.compile(
        r'^#\s*define\s+'
        r'(?:SSL2|SSL3|TLS1)_TXT_([A-Z0-9_]*)\s+'
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
        (r'^\s*#\s*define\s+(?:SSL2|SSL3|TLS1)_(?:CK|TXT)')
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
        cipher = dict(
            hexid=hexid,
            valid=bool(handle(0)),
            name=handle(1),
            kea=handle(3),
            auth=handle(4),
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

    def __init__(self, downloaddir='downloads'):
        self.downloaddir = downloaddir
        # hex id string to cipher dict
        self.ciphers = {}
        # library -> ciphername -> hex id
        self.indexes = {}
        # Mozilla server side TLS
        self.serverside = {}
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

    def process(self, refresh=False):
        self.download(refresh)
        self.parse_iana()
        self.parse_gnutls()
        self.parse_nss()
        self.parse_mod_nss()
        self.parse_openssl_headers()
        self.parse_openssl_suites()
        self.parse_serverside()

    def dump(self, file=None):
        result = {
            'about': {
                'author': 'Christian Heimes',
                'email': 'christian at python.org',
                'created': datetime.datetime.utcnow().strftime('%Y%m%dT%H:%M:%S'),
                'sources': self.source_files,
            },
            'ciphers': self.ciphers,
            'indexes': self.indexes,
            'flags': {name: sorted(value) for name, value in self.fields.items()},
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
