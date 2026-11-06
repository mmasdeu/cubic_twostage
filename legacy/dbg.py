# SPDX-License-Identifier: GPL-3.0-or-later
from twostage import *
from witness2 import Witness
import time
S=TwoStage("x^3 - x^2 - 4*x - 3"); t=S.K.gen()
t0=time.time(); c1,failed=S.cover(1,T=3,maxdepth=9,verbose=False); print("cover",time.time()-t0,len(failed))
W=Witness(S)
for x in [(1+2*t+4*t**2)/7, (1+t)/2, (1+t+t**2)/5]:
    t0=time.time(); print(x, W.min_at_least_one(x), time.time()-t0, flush=True)
