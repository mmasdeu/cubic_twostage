# SPDX-License-Identifier: GPL-3.0-or-later
from twostage import *
import sys
for line in open('h1b.txt'):
    f=line.strip()
    S=TwoStage(f)
    t=time.time()
    certs,failed=S.cover(1,T=3,maxdepth=12,verbose=False)
    print(S.K.discriminant(), f, "boxes",len(certs),"failed",len(failed), f"{time.time()-t:.1f}s", flush=True)
