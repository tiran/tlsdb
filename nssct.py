#!/usr/bin/env python3
import ctypes
import enum
from collections import OrderedDict


WEAK = set()
STRONG = set()

PRUint16 = ctypes.c_uint16
PRUintn = ctypes.c_uint
PRBool = ctypes.c_int
PRInt32 = ctypes.c_int32
PRUint32 = ctypes.c_uint32
PRErrorCode = PRInt32
PRLanguageCode = PRUint32
SECStatus = ctypes.c_int  # enum


class c_text_p(ctypes.c_char_p):
    """A c_char_p variant that can handle ASCII text"""
    @classmethod
    def from_param(cls, value):
        if value is None:
            return None
        if isinstance(value, str):
            return value.encode('ascii')
        elif not isinstance(value, bytes):
            raise TypeError(value)
        else:
            return value

    @property
    def value(self):
        value = super().value
        if value is None:
            return None
        elif not isinstance(value, str):
            return value.decode('ascii')
        return value

    def __repr__(self):
        return "<c_text: '{}'>".format(self.value)

    def __str__(self):
        return self.value


class c_enum(ctypes.c_int):
    enum = None

    @classmethod
    def from_param(cls, value):
        if not isinstance(value, self.enum):
            raise TypeError(value)
        else:
            return int(value)

    @property
    def value(self):
        return self.enum(super().value)

    def __repr__(self):
        return '<c_enum: {}>'.format(repr(self.value))


class PRBool(ctypes.c_int):
    @property
    def value(self):
        return bool(super().value)

    def __repr__(self):
        if self.value:
            return 'PRTrue'
        else:
            return 'PRFalse'


class SSLEnum(enum.IntEnum):
    def __eq__(self, other):
        if not isinstance(other, type(self)):
            return NotImplemented
        return other.value == self.value

    def __ne__(self, other):
        if not isinstance(other, type(self)):
            return NotImplemented
        return other.value != self.value

    def __lt__(self, other):
        # sort any SSLEnum
        if not isinstance(other, SSLEnum):
            return NotImplemented
        return (self.__class__.__name__, self.value) < (other.__class__.__name__, other.value)

    def __hash__(self):
        return hash(str(self))


class SSLAuthTypeEnum(SSLEnum):
    null = 0
    rsa_decrypt = 1  # static RSA
    dsa = 2
    kea = 3  # unused
    ecdsa = 4
    ecdh_rsa = 5  # ECDH cert with an RSA signature
    ecdh_ecdsa = 6  # ECDH cert with an ECDSA signature
    rsa_sign = 7  # RSA PKCS#1.5 signing
    rsa_pss = 8
    psk = 9
    # size = 10  # number of  algorithms


WEAK.update((
    SSLAuthTypeEnum.null,
    SSLAuthTypeEnum.dsa,
    # SSLAuthTypeEnum.kea,
    # SSLAuthTypeEnum.psk,
))
STRONG.update((
    SSLAuthTypeEnum.rsa_decrypt,
    SSLAuthTypeEnum.ecdsa,
    SSLAuthTypeEnum.ecdh_rsa,
    SSLAuthTypeEnum.ecdh_ecdsa,
    SSLAuthTypeEnum.rsa_sign,
))

class SSLAuthType(c_enum):
    enum = SSLAuthTypeEnum


class SSLCipherAlgorithmEnum(SSLEnum):
    null = 0
    rc4 = 1
    rc2 = 2
    des = 3
    tripledes = 4  # 3DES
    idea = 5
    fortezza = 6  # deprecated, now unused
    aes = 7
    camellia = 8
    seed = 9
    aes_gcm = 10
    chacha20 = 11

WEAK.update((
    SSLCipherAlgorithmEnum.null,
    SSLCipherAlgorithmEnum.rc4,
    SSLCipherAlgorithmEnum.rc2,
    SSLCipherAlgorithmEnum.des,
    SSLCipherAlgorithmEnum.tripledes,
    SSLCipherAlgorithmEnum.idea,
    SSLCipherAlgorithmEnum.fortezza,
    SSLCipherAlgorithmEnum.camellia,
    SSLCipherAlgorithmEnum.seed,
))
STRONG.update((
    SSLCipherAlgorithmEnum.aes,
    SSLCipherAlgorithmEnum.aes_gcm,
    SSLCipherAlgorithmEnum.chacha20,
))
STREAM_CIPHER = set([
    SSLCipherAlgorithmEnum.rc4,
    SSLCipherAlgorithmEnum.rc2,
    SSLCipherAlgorithmEnum.chacha20,
])


class SSLCipherAlgorithm(c_enum):
    enum = SSLCipherAlgorithmEnum


class SSLMACAlgorithmEnum(SSLEnum):
    null = 0
    mac_md5 = 1
    mac_sha = 2
    hmac_md5 = 3  # TLS HMAC version of mac_md5
    hmac_sha = 4  # TLS HMAC version of mac_sha
    hmac_sha256 = 5
    mac_aead = 6
    hmac_sha384 = 7


WEAK.update((
    SSLMACAlgorithmEnum.null,
    SSLMACAlgorithmEnum.mac_md5,
    SSLMACAlgorithmEnum.hmac_md5,
))
STRONG.update((
    SSLMACAlgorithmEnum.mac_sha,  # ???
    SSLMACAlgorithmEnum.hmac_sha,  # ???
    SSLMACAlgorithmEnum.hmac_sha256,
    SSLMACAlgorithmEnum.mac_aead,
    SSLMACAlgorithmEnum.hmac_sha384,
))


class SSLMACAlgorithm(c_enum):
    enum = SSLMACAlgorithmEnum


class SSLKEATypeEnum(SSLEnum):
    null = 0
    rsa = 1
    dh = 2
    fortezza = 3  # deprecated, now unused
    ecdh = 4
    ecdh_psk = 5
    dh_psk = 6
    # size = 7  # number of  algorithms


WEAK.update((
    SSLKEATypeEnum.null,
    SSLKEATypeEnum.fortezza,
    SSLKEATypeEnum.ecdh_psk,
    SSLKEATypeEnum.dh_psk,
))
STRONG.update((
    SSLKEATypeEnum.rsa,
    SSLKEATypeEnum.dh,
    SSLKEATypeEnum.ecdh,
))


class SSLKEAType(c_enum):
    enum = SSLKEATypeEnum


CIPHER_TO_VERSION = {
    'SSL_RSA_FIPS_WITH_3DES_EDE_CBC_SHA': 'SSLv3',
    'SSL_RSA_FIPS_WITH_DES_CBC_SHA': 'SSLv3',
    'TLS_DHE_RSA_WITH_DES_CBC_SHA': 'SSLv3',
    'TLS_RSA_EXPORT_WITH_RC2_CBC_40_MD5': 'SSLv3',
    'TLS_RSA_EXPORT_WITH_RC4_40_MD5': 'SSLv3',
    'TLS_RSA_WITH_3DES_EDE_CBC_SHA': 'SSLv3',
    'TLS_RSA_WITH_DES_CBC_SHA': 'SSLv3',
    'TLS_RSA_WITH_NULL_MD5': 'SSLv3',
    'TLS_RSA_WITH_NULL_SHA': 'SSLv3',
    'TLS_RSA_WITH_RC4_128_MD5': 'SSLv3',
    'TLS_RSA_WITH_RC4_128_SHA': 'SSLv3',
    # TLSv1.0
    'TLS_DHE_RSA_WITH_CAMELLIA_128_CBC_SHA': 'TLSv1.0',
    'TLS_DHE_RSA_WITH_CAMELLIA_256_CBC_SHA': 'TLSv1.0',
    'TLS_ECDHE_ECDSA_WITH_3DES_EDE_CBC_SHA': 'TLSv1.0',
    'TLS_ECDHE_ECDSA_WITH_AES_128_CBC_SHA': 'TLSv1.0',
    'TLS_ECDHE_ECDSA_WITH_AES_256_CBC_SHA': 'TLSv1.0',
    'TLS_ECDHE_ECDSA_WITH_NULL_SHA': 'TLSv1.0',
    'TLS_ECDHE_ECDSA_WITH_RC4_128_SHA': 'TLSv1.0',
    'TLS_ECDHE_RSA_WITH_3DES_EDE_CBC_SHA': 'TLSv1.0',
    'TLS_ECDHE_RSA_WITH_AES_128_CBC_SHA': 'TLSv1.0',
    'TLS_ECDHE_RSA_WITH_AES_256_CBC_SHA': 'TLSv1.0',
    'TLS_ECDHE_RSA_WITH_NULL_SHA': 'TLSv1.0',
    'TLS_ECDHE_RSA_WITH_RC4_128_SHA': 'TLSv1.0',
    'TLS_ECDH_ECDSA_WITH_3DES_EDE_CBC_SHA': 'TLSv1.0',
    'TLS_ECDH_ECDSA_WITH_AES_128_CBC_SHA': 'TLSv1.0',
    'TLS_ECDH_ECDSA_WITH_AES_256_CBC_SHA': 'TLSv1.0',
    'TLS_ECDH_ECDSA_WITH_NULL_SHA': 'TLSv1.0',
    'TLS_ECDH_ECDSA_WITH_RC4_128_SHA': 'TLSv1.0',
    'TLS_ECDH_RSA_WITH_3DES_EDE_CBC_SHA': 'TLSv1.0',
    'TLS_ECDH_RSA_WITH_AES_128_CBC_SHA': 'TLSv1.0',
    'TLS_ECDH_RSA_WITH_AES_256_CBC_SHA': 'TLSv1.0',
    'TLS_ECDH_RSA_WITH_NULL_SHA': 'TLSv1.0',
    'TLS_ECDH_RSA_WITH_RC4_128_SHA': 'TLSv1.0',
    'TLS_ECDH_anon_WITH_3DES_EDE_CBC_SHA': 'TLSv1.0',
    'TLS_ECDH_anon_WITH_AES_128_CBC_SHA': 'TLSv1.0',
    'TLS_ECDH_anon_WITH_AES_256_CBC_SHA': 'TLSv1.0',
    'TLS_ECDH_anon_WITH_NULL_SHA': 'TLSv1.0',
    'TLS_ECDH_anon_WITH_RC4_128_SHA': 'TLSv1.0',
    'TLS_RSA_EXPORT1024_WITH_DES_CBC_SHA': 'TLSv1.0',
    'TLS_RSA_EXPORT1024_WITH_RC4_56_SHA': 'TLSv1.0',
    'TLS_DHE_RSA_WITH_3DES_EDE_CBC_SHA': 'TLSv1.0',
    'TLS_DHE_RSA_WITH_AES_128_CBC_SHA': 'TLSv1.0',
    'TLS_DHE_RSA_WITH_AES_256_CBC_SHA': 'TLSv1.0',
    'TLS_RSA_WITH_AES_128_CBC_SHA': 'TLSv1.0',
    'TLS_RSA_WITH_AES_256_CBC_SHA': 'TLSv1.0',
    'TLS_RSA_WITH_CAMELLIA_128_CBC_SHA': 'TLSv1.0',
    'TLS_RSA_WITH_CAMELLIA_256_CBC_SHA': 'TLSv1.0',
    # TLSv1.0 not mod_nss
    'TLS_DHE_DSS_WITH_3DES_EDE_CBC_SHA': 'TLSv1.0',
    'TLS_DHE_DSS_WITH_AES_128_CBC_SHA': 'TLSv1.0',
    'TLS_DHE_DSS_WITH_AES_256_CBC_SHA': 'TLSv1.0',
    'TLS_DHE_DSS_WITH_CAMELLIA_128_CBC_SHA': 'TLSv1.0',
    'TLS_DHE_DSS_WITH_CAMELLIA_256_CBC_SHA': 'TLSv1.0',
    'TLS_DHE_DSS_WITH_DES_CBC_SHA': 'TLSv1.0',
    'TLS_DHE_DSS_WITH_RC4_128_SHA': 'TLSv1.0',
    'TLS_RSA_WITH_SEED_CBC_SHA': 'TLSv1.0',
    # TLSv1.2
    'TLS_DHE_RSA_WITH_AES_128_CBC_SHA256': 'TLSv1.2',
    'TLS_DHE_RSA_WITH_AES_128_GCM_SHA256': 'TLSv1.2',
    'TLS_DHE_RSA_WITH_AES_256_CBC_SHA256': 'TLSv1.2',
    'TLS_DHE_RSA_WITH_AES_256_GCM_SHA384': 'TLSv1.2',
    'TLS_ECDHE_ECDSA_WITH_AES_128_CBC_SHA256': 'TLSv1.2',
    'TLS_ECDHE_ECDSA_WITH_AES_128_GCM_SHA256': 'TLSv1.2',
    'TLS_ECDHE_ECDSA_WITH_AES_256_CBC_SHA384': 'TLSv1.2',
    'TLS_ECDHE_ECDSA_WITH_AES_256_GCM_SHA384': 'TLSv1.2',
    'TLS_ECDHE_RSA_WITH_AES_128_CBC_SHA256': 'TLSv1.2',
    'TLS_ECDHE_RSA_WITH_AES_128_GCM_SHA256': 'TLSv1.2',
    'TLS_ECDHE_RSA_WITH_AES_256_CBC_SHA384': 'TLSv1.2',
    'TLS_ECDHE_RSA_WITH_AES_256_GCM_SHA384': 'TLSv1.2',
    'TLS_RSA_WITH_AES_128_CBC_SHA256': 'TLSv1.2',
    'TLS_RSA_WITH_AES_128_GCM_SHA256': 'TLSv1.2',
    'TLS_RSA_WITH_AES_256_CBC_SHA256': 'TLSv1.2',
    'TLS_RSA_WITH_AES_256_GCM_SHA384': 'TLSv1.2',
    'TLS_RSA_WITH_NULL_SHA256': 'TLSv1.2',
     # TLSv1.2 not mod_nss
    'TLS_DHE_DSS_WITH_AES_128_CBC_SHA256': 'TLSv1.2',
    'TLS_DHE_DSS_WITH_AES_128_GCM_SHA256': 'TLSv1.2',
    'TLS_DHE_DSS_WITH_AES_256_CBC_SHA256': 'TLSv1.2',
    'TLS_DHE_DSS_WITH_AES_256_GCM_SHA384': 'TLSv1.2',
    'TLS_DHE_PSK_WITH_AES_128_GCM_SHA256': 'TLSv1.2',
    'TLS_DHE_PSK_WITH_AES_256_GCM_SHA384': 'TLSv1.2',
    'TLS_ECDHE_PSK_WITH_AES_128_GCM_SHA256': 'TLSv1.2',
    'TLS_ECDHE_PSK_WITH_AES_256_GCM_SHA384': 'TLSv1.2',
    # TLSv1.3, not mod_nss
    'TLS_DHE_PSK_WITH_CHACHA20_POLY1305_SHA256': 'TLSv1.3',
    'TLS_DHE_RSA_WITH_CHACHA20_POLY1305_SHA256': 'TLSv1.3',
    'TLS_ECDHE_ECDSA_WITH_CHACHA20_POLY1305_SHA256': 'TLSv1.3',
    'TLS_ECDHE_PSK_WITH_CHACHA20_POLY1305_SHA256': 'TLSv1.3',
    'TLS_ECDHE_RSA_WITH_CHACHA20_POLY1305_SHA256': 'TLSv1.3',
}


class SSLCipherSuiteInfo(ctypes.Structure):
    _fields_ = [
        ('length', PRUint16),
        ('cipherSuite', PRUint16),

        ('cipherSuiteName', c_text_p),

        ('authAlgorithmName', c_text_p),
        ('_authAlgorithm', SSLAuthType),  # deprecated

        ('keaTypeName', c_text_p),
        ('keaType', SSLKEAType),

        ('symCipherName', c_text_p),
        ('symCipher', SSLCipherAlgorithm),
        ('symKeyBits', PRUint16),
        ('symKeySpace', PRUint16),
        ('effectiveKeyBits', PRUint16),

        ('macAlgorithmName', c_text_p),
        ('macAlgorithm', SSLMACAlgorithm),
        ('macBits', PRUint16),

        # bit field
        ('isFIPS', PRBool, 1),  # PRUintn
        ('isExportable', PRBool, 1),  # PRUintn
        ('nonStandard', PRBool, 1),  # PRUintn
        ('reserved', PRUintn, 29),

        ('authType', SSLAuthType)
    ]

    def __init__(self, suite):
        enabled = PRBool()
        SSL_GetCipherSuiteInfo(suite,
                               ctypes.byref(self),
                               ctypes.sizeof(type(self)))
        SSL_CipherPrefGetDefault(suite, ctypes.byref(enabled))
        self.enabled = enabled.value

    #def __getattribute__(self, name):
    #    value = super().__getattribute__(name)
    #    return getattr(value, 'valueXXX', value)  # resolve values

    def __str__(self):
        return "<SSLCipherSuiteInfo {self.cipherSuiteName}>".format(self=self)

    @property
    def ephemeral(self):
        # NSS has no flag for ephemeral Key Exchange Algorithm
        return str(self.keaTypeName) in {'DHE', 'ECDHE'}

    @property
    def tlsversion(self):
        return CIPHER_TO_VERSION[str(self.cipherSuiteName)]

    @property
    def sym_cipher_mode(self):
        value = self.symCipher.value
        if value in STREAM_CIPHER:
            return 'stream'
        elif value == SSLCipherAlgorithmEnum.null:
            return 'null'
        #if self.macAlgorithm.value == SSLMACAlgorithmEnum.mac_aead:
        #    return 'AEAD'
        name = self.cipherSuiteName.value
        if '_CBC_' in name:
            return 'cbc'
        elif '_GCM_' in name:
            return 'gcm'
        else:
            raise KeyError(name)

    @property
    def hash_algorithm(self):
        name = self.cipherSuiteName.value
        if name.endswith('_SHA'):
            return 'sha1'
        elif name.endswith('_SHA256'):
            return 'sha256'
        elif name.endswith('_SHA384'):
            return 'sha384'

    def check_strong(self, bits):
        reasons = []
        if self.isExportable:
            reasons.append('isExportable')
        if self.symKeyBits < bits:
            reasons.append('symKeyBits')
        if self.effectiveKeyBits < 128:
            reasons.append('effectiveKeyBits')
        if self.macBits < 128:
            reasons.append('macBits')
        if self.keaType.value not in STRONG:
            reasons.append('keaType')
        if self.symCipher.value not in STRONG:
            reasons.append('symCipher')
        if self.macAlgorithm.value not in STRONG:
            reasons.append('macAlgorithm')
        if self.authType.value not in STRONG:
            reasons.append('authType')
        return not bool(reasons), reasons

    def get_fields(self, resolve_values=False, bits=128):
        strong, reasons = self.check_strong(bits)
        suite = self.cipherSuite
        fields = [
            ('cipherSuiteName', self.cipherSuiteName.value),
            ('enabled', self.enabled),
            ('ephemeral', self.ephemeral),
            ('tlsversion', self.tlsversion),
            ('sym_cipher_mode', self.sym_cipher_mode),
            ('hash_algorithm', self.hash_algorithm),
            ('cipherSuiteHex', '0x{:02X},0x{:02X}'.format(suite>>8, suite%256)),
            ('strong', strong),
            ('weak_reasons', reasons),
        ]
        for field in self._fields_:
            name = field[0]
            if name == 'cipherSuiteName':
                continue
            value = getattr(self, field[0])
            if resolve_values:
                value = getattr(value, 'value', value)
            fields.append((name, value))
        return OrderedDict(fields)


libssl3 = ctypes.CDLL('libssl3.so')

PR_ErrorToString = libssl3.PR_ErrorToString
PR_ErrorToString.argtypes = [PRErrorCode, PRLanguageCode]
PR_ErrorToString.restype = ctypes.c_char_p

PR_GetError = libssl3.PR_GetError
PR_GetError.argtypes = []
PR_GetError.restype = PRErrorCode

def secstatus_errorcheck(result, func, args):
    if result != 0:
        err = PR_GetError()
        text = PR_ErrorToString(err, 0)
        raise ValueError(err, text)
    return args

SSL_GetCipherSuiteInfo = libssl3.SSL_GetCipherSuiteInfo
SSL_GetCipherSuiteInfo.argtypes = [PRUint16, ctypes.POINTER(SSLCipherSuiteInfo), PRUintn]
SSL_GetCipherSuiteInfo.restype = SECStatus
SSL_GetCipherSuiteInfo.errcheck = secstatus_errorcheck

SSL_CipherPrefGetDefault = libssl3.SSL_CipherPrefGetDefault
SSL_CipherPrefGetDefault.argtypes = [PRUint16, ctypes.POINTER(PRBool)]
SSL_CipherPrefGetDefault.restype = SECStatus
SSL_CipherPrefGetDefault.errcheck = secstatus_errorcheck

SSL_NumImplementedCiphers = PRUint16.in_dll(libssl3, "SSL_NumImplementedCiphers").value


class ImplementedCiphers(ctypes.Array):
    _type_ = PRUint16
    _length_ = SSL_NumImplementedCiphers


SSL_ImplementedCiphers = ImplementedCiphers.in_dll(libssl3, "SSL_ImplementedCiphers")


if __name__ == '__main__':
    for suite in SSL_ImplementedCiphers:
        info = SSLCipherSuiteInfo(suite)
        fields = info.get_fields(True, 128)
        if not fields['strong']:
            continue
        if fields['hash_algorithm'] == 'sha384':
            continue
        if fields['sym_cipher_mode'] == 'cbc' and fields['macBits'] >= 128:
            print('#', fields['cipherSuiteName'], fields['effectiveKeyBits'], fields['macBits'])
        else:
            print(fields['cipherSuiteName'], fields['effectiveKeyBits'], fields['macBits'])
        print(fields)

    #print(sorted(WEAK))
