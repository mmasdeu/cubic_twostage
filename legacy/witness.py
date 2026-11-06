# SPDX-License-Identifier: GPL-3.0-or-later
from twostage import *
def local_min(S, x, bound_factor=2):
    """exact min over gamma in O_F of |Nm(x-gamma)|, searched up to bound_factor."""
    K=S.K; m=x.denominator(); c=K(m*x); I=K.ideal(m)
    # unit image mod m
    U=[]; u=K(1)
    while True:
        for s in (u,-u):
            if all((s-t) not in I for t in U): U.append(s)
        u=I.reduce(u*S.eps)
        if (u-1) in I: break
    B=int(bound_factor*m**3)
    for k,ideals in sorted(K.ideals_of_bdd_norm(B).items()):
        for J in ideals:
            be=J.gens_reduced()[0]
            for s in U:
                if (s*be - c) in I:
                    return QQ(k)/m**3, be*s  # y = s*be in c + mO, Nm(x - gamma) = Nm(y)/m^3
    return None
if __name__=="__main__":
  for f,xs in [("x^3 - x^2 - 4*x - 3", "(1+2*t+4*t^2)/7"), ("x^3 - x^2 + 3*x + 2","(1+t^2)/2")]:
     S=TwoStage(f); K=S.K; t=K.gen()
     x=K(eval(xs.replace('^','**')))
     mn,y=local_min(S,x)
     m=x.denominator()
     gamma=x-y/m
     print(K.discriminant(), "x =",xs, " min_gamma |Nm(x-gamma)| =", mn, " attained at gamma =", gamma, "check:", (x-gamma).norm().abs(), gamma.is_integral())
