# SPDX-License-Identifier: GPL-3.0-or-later
from twostage import *
import pickle, random
random.seed(1)
for disc,f in [(199,"x^3 - x^2 - 4*x - 3"),(307,"x^3 - x^2 + 3*x + 2")]:
    S=TwoStage(f); K=S.K; t=K.gen()
    _,cert=pickle.load(open(f"cert_{disc}.pkl","rb"))
    vol=sum(QQ(1)/8**c[1] for c in cert)
    # disjointness: dyadic boxes from a tree are disjoint unless nested; check no nesting
    keys=set((c[1],)+c[0] for c in cert)
    nested=sum(1 for d,*m in keys for e in range(d) if (e,)+tuple(mi>>(d-e) for mi in m) in keys)
    print(f"d=-{disc}: total volume of certified boxes = {vol}, nested pairs = {nested}")
    # tamper test: re-certify with every region radius halved -> must fail somewhere
    S.cover(3 if disc==199 else 2,T=3,maxdepth=12,verbose=False)
    certs,_=S.cover(3 if disc==199 else 2,T=3,maxdepth=12,verbose=False)
    bad=[(lo,w,d,k) for lo,w,d,k in certs]
    old=S._cl; S._cl=[(c[0],2*c[1],c[2],c[3]) for c in old]
    try: S.certify(bad); print("  tamper test: NOT rejected (bad)")
    except ValueError: print("  tamper test: rejected as expected")
    S._cl=old
    S.build_lookup(cert)
    # exact continued fractions of random elements, incl. the hole point
    tests=[(1+2*t+4*t**2)/7 if disc==199 else (1+t**2)/2]
    for _ in range(200):
        num=sum(random.randint(-10**6,10**6)*t**i for i in range(3))
        den=sum(random.randint(-10**4,10**4)*t**i for i in range(3))
        tests.append(num/den)
    lens=[]
    for x in tests:
        qs=S.continued_fraction(x)
        assert all(q.is_integral() for q in qs) and evaluate_cf(qs)==x
        lens.append(len(qs))
    print(f"  200+1 random continued fractions exact; length avg {sum(lens)/len(lens):.1f}, max {max(lens)}")
    x=tests[0]; qs=S.continued_fraction(x)
    print("  CF of hole point", x, "=", qs)
