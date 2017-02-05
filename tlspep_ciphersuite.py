#!/usr/bin/python3
# Author:
#     Christian Heimes <christian@python.org>
"""Generate CipherSuite list for TLS ABC PEP

Key Exchange Algorithm / Key Agreement
--------------------------------------

Omitted algorithms:

* KRB5, nowadays Kerberos/GSSAPI is handled on higher levels, e.g.
  WWW-Authenticate Negotiate.
* NULL
* PSK, pre-shared key is irrelevant on the web
* SRP, TLS-SRP (secure remote password) never took off


Authentication algorithms
-------------------------

Omitted algorithms:

* export grade algorithms
* NULL and its alias `anon`
* DSS, DSA certificates are irrelevant
* KRB5
* PSK
* SRP


Bulk encryption algorithms
--------------------------

Omitted algorithms:

* NULL
* export grade (`40` suffix)
* ARIA
* DES
* RC2


Pseudo Random Functions (Hash)
------------------------------

Omitted algorithms:

* NULL
* MD5

"""

import csv
import io
import re
import urllib.request


IANA_CSV = \
    'https://www.iana.org/assignments/tls-parameters/tls-parameters-4.csv'


# IANA list does not contain algorithms from TLS 1.3 draft
TLS13_DRAFT = {
    0x1301: 'TLS_AES_128_GCM_SHA256',
    0x1302: 'TLS_AES_256_GCM_SHA384',
    0x1303: 'TLS_CHACHA20_POLY1305_SHA256',
    0x1304: 'TLS_AES_128_CCM_SHA256',
    0x1305: 'TLS_AES_128_CCM_8_SHA256',
}


IGNORE = {'TLS_EMPTY_RENEGOTIATION_INFO_SCSV', 'TLS_FALLBACK_SCSV'}


CIPHER_SUITE_PARTS = dict(
    kea={
        'DH': True, 'DHE': True,
        'ECDH': True, 'ECDHE': True,
        'KRB5': False,
        'NULL': False,
        'PSK': False, 'PSK_DHE': False,
        'RSA': True,
        'SRP_SHA': False,
        'TLS13': True,
    },
    auth={
        'DSS': False, 'DSS_EXPORT': False,
        'ECDSA': True,
        'KRB5': False, 'KRB5_EXPORT': False,
        'NULL': False,
        'PSK': False, 'PSK_DHE': False,
        'RSA': True, 'RSA_EXPORT': False, 'RSA_FIPS': False,
        'SRP_SHA': False,
        'anon': False, 'anon_EXPORT': False,
        'TLS13': True,
    },
    enc={
        '3DES_EDE': True,
        'AES_128': True, 'AES_256': True,
        'ARIA_128': False, 'ARIA_256': False,
        'CAMELLIA_128': True, 'CAMELLIA_256': True,
        'CHACHA20': True,
        'DES': False, 'DES40': False,
        # 'FORTEZZA': False,
        # 'GOST89': False,
        'IDEA': True,
        'NULL': False,
        'RC2': False, 'RC2_40': False,
        'RC4_128': True, 'RC4_40': False,
        'SEED': True
    },
    mode={
        'CBC': True, 'CBC_40': False,
        'CCM': True, 'CCM_8': True,
        'GCM': True,
        'POLY1305': True
    },
    prf={
        'MD5': False,
        'NULL': False,
        'SHA': True,
        'SHA256': True,
        'SHA384': True
    },
)


CIPHER_SUITE_RE_TEMPLATE = (
    r'^(TLS|SSL)_'
    r'(?:'
    r'((?P<kea>({kea}))_)?'
    r'(?P<auth>({auth}))_'
    r'WITH_'
    r')?'
    r'(?P<enc>({enc}))'
    r'(_(?P<mode>({mode})))?'
    r'(_(?P<prf>({prf})))?'
    r'$'
)


CIPHER_SUITE_RE = re.compile(CIPHER_SUITE_RE_TEMPLATE.format(
    **{key: '|'.join(sorted(values))
       for key, values in CIPHER_SUITE_PARTS.items()}
))


def parse_iana(url=IANA_CSV):
    with urllib.request.urlopen(url) as f:
        encoded = io.StringIO(f.read().decode('utf-8'))

    for row in csv.DictReader(encoded):
        hexid = row['Value']
        name = row['Description']
        if name.lower().startswith(('reserved', 'unassigned')):
            # reserved or unassigned range
            continue
        if hexid[0:2] != '0x' or hexid[4:7] != ',0x':
            raise ValueError(hexid)
        num = (int(hexid[2:4], 16) << 8) + int(hexid[7:9], 16)
        yield num, name


def check_suite(name):
    """Parse a TLS cipher suite name
    """
    if name in IGNORE:
        return False
    mo = CIPHER_SUITE_RE.match(name)
    if mo is None:
        raise ValueError(name)
    cipher = mo.groupdict()

    # TLS 1.3 cipher suites no longer contain key exchange and auth
    if cipher['auth'] is None:
        cipher['auth'] = 'TLS13'
    # missing key exchange means same algo as auth
    if cipher['kea'] is None:
        cipher['kea'] = cipher['auth']
        if cipher['kea'].endswith(('_EXPORT', '_FIPS')):
            cipher['kea'] = cipher['kea'].split('_', 1)[0]
    # CCM implies SHA256 PRF
    if cipher['mode'] in {'CCM', 'CCM_8'}:
        cipher['prf'] = 'SHA256'

    for key, value in cipher.items():
        if value is None and key == 'mode':
            continue
        if not CIPHER_SUITE_PARTS[key][value]:
            return False

    return True


def main():
    iana_ciphers = dict(parse_iana())
    iana_ciphers.update(TLS13_DRAFT)
    for num, cipher in sorted(iana_ciphers.items()):
        prefix = '' if check_suite(cipher) else '# '
        print('    {}{} = 0x{:04x}'.format(prefix, cipher, num))


if __name__ == '__main__':
    main()
