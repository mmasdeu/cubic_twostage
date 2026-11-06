# SPDX-License-Identifier: GPL-3.0-or-later
from twostage import *
import pickle, sys
f=sys.argv[1]
S=TwoStage(f)
print("field", f, "disc", S.K.discriminant(), "unit", S.eps)
for N in range(2,40):
    certs,failed=S.cover(N,T=3,maxdepth=12)
    if not failed: break
t=time.time()
cert=S.certify(certs)
print(f"certified {len(cert)} boxes rigorously in {time.time()-t:.1f}s; max denominator norm used:",
      max(c[2][1] for c in cert), "; max depth", max(c[1] for c in cert))
from collections import Counter
print("regions used by Nm(q2):", sorted(Counter(c[2][1] for c in cert).items()))
pickle.dump((f,cert), open(f"cert_{-S.K.discriminant()}.pkl","wb"))
