# SPDX-License-Identifier: GPL-3.0-or-later
from twostage import *
for f in ["x^3-x-1","x^3+2*x-2"]:
    S=TwoStage(f)
    certs,failed=S.cover(1,T=3,maxdepth=10)
    print(f, "N=1 failed boxes:",len(failed))
