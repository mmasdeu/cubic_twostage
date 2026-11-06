# SPDX-License-Identifier: GPL-3.0-or-later
"""Complete list of complex cubic fields (signature (1,1)) with class number 1, |d| <= B.
usage: python3 enum_fields.py [B]   (default 1500) -> data/h1_<B>.txt, sorted by |d|.
PARI nflist("S3",[1,B],1): all non-Galois cubics with 1 complex place (complex cubics are never cyclic)."""
import sys
from sage.all import pari, NumberField, PolynomialRing, QQ
B = int(sys.argv[1]) if len(sys.argv) > 1 else 1500
R = PolynomialRing(QQ, 'x')
L = pari(f'nflist("S3",[1,{B}],1)')
out = []
for f in L:
    K = NumberField(R(str(pari(f).polredabs())), 't')
    if K.class_number(proof=False) == 1:
        out.append((int(K.discriminant()), str(K.polynomial()).replace('t', 'x')))
out.sort(reverse=True)
print(len(L), "fields,", len(out), "with h=1")
open(f'data/h1_{B}.txt', 'w').write('\n'.join(p for d, p in out) + '\n')
