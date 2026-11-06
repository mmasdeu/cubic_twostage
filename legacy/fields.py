# SPDX-License-Identifier: GPL-3.0-or-later
from sage.all import *
R = PolynomialRing(QQ,'x'); x=R.gen()
seen={}
B=4
for a in range(-B,B+1):
  for b in range(-B,B+1):
    for c in range(1,B+1):
      f=x**3+a*x**2+b*x+c
      if not f.is_irreducible(): continue
      if f.discriminant()>=0: continue
      K=NumberField(f,'t'); d=K.discriminant()
      if -d>500: continue
      if d not in seen: seen[d]=K.optimized_representation()[0].polynomial()
for d in sorted(seen,reverse=True):
    K=NumberField(seen[d],'t')
    print(d, K.class_number(proof=False), seen[d])
