TLS cipher suite database
=========================

A JSON file with TLS cipher suite information. It contains data from IANA
registry, OpenSSL 1.0.2, OpenSSL master, NSS, mod_nss and Mozilla Server
Side TLS.

Requirements
------------

  * Python 3
  * requests
  * lxml (to parse IANA XHTML document)
  * pyparsing (to parse OpenSSL's s3_lib.c)
  * a C preprocessor (cpp) for pyparsing

Fields
------

ciphers: a mapping of hex id to cipher definitions

flags: cipher suite flags taken from OpenSSL

indexes: library specific name to hex id