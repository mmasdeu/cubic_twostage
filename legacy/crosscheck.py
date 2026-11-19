# SPDX-License-Identifier: GPL-3.0-or-later
# compare fast and slow exact tests on random candidates
import random, time
from twostage import TwoStage
from witness2 import Witness
from witness_fast import FastWitness
from sage.all import QQ
random.seed(3); agree=0; pos=0
for f in ['x^3 - x^2 + 4*x + 1','x^3 + 3*x - 3','x^3 - x^2 + 3*x + 2','x^3 - x^2 + x + 11']:
    S=TwoStage(f); W=Witness(S); F=FastWitness(S,7)
    for _ in range(40):
        m=random.randint(2,7); a=tuple(random.randrange(m) for _ in range(3))
        if all(ai==0 for ai in a): continue
        x=S.elt(tuple(QQ(ai)/m for ai in a))
        if x.denominator()!=m: continue
        s=W.min_at_least_one(x)[0]; fa=F.is_witness(a,m)
        assert s==fa,(f,a,m); agree+=1; pos+=s
    # also known witnesses
print("agree on",agree,"candidates (",pos,"witnesses)")
