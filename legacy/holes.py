# SPDX-License-Identifier: GPL-3.0-or-later
from twostage import *
for f in ["x^3 - x^2 - 4*x - 3","x^3 - x^2 + 3*x + 2"]:
    S=TwoStage(f)
    certs,failed=S.cover(1,T=4,maxdepth=11,verbose=False)
    P=np.array([lo+w/2 for lo,w,d in failed])
    print(S.K.discriminant(), "failed",len(P), "basis", S.basis)
    # cluster
    reps=[]
    for p in P:
        if not any(np.max(np.abs(((p-r+0.5)%1)-0.5))<0.02 for r in reps): reps.append(p)
    for r in reps:
        # guess rational with small denominator
        from fractions import Fraction
        print("  hole ~", np.round(r,4), [str(Fraction(float(v)).limit_denominator(12)) for v in r])
