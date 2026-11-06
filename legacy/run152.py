# SPDX-License-Identifier: GPL-3.0-or-later
from twostage import *
S=TwoStage("x^3-x^2-2*x-2")
print(S.K.discriminant(), S.eps)
for N in [1,2,3,4,5,6,8]:
    certs,failed=S.cover(N,T=3,maxdepth=11)
    if not failed: break
