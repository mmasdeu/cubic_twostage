# SPDX-License-Identifier: GPL-3.0-or-later
from sage.all import QQ


class Witness:
    """Exact test whether x in F has |Nm(x-g)| >= 1 for every g in O_F."""

    def __init__(self, S):
        self.S = S
        self.gens = {}
        self.maxB = 0

    def _ensure(self, B):
        if B > self.maxB:
            K = self.S.K
            self.gens = {k: [J.gens_reduced()[0] for J in v]
                         for k, v in K.ideals_of_bdd_norm(B).items()}
            self.maxB = B

    def min_at_least_one(self, x):
        # y = m(x-g) runs over c + mO_F; need |Nm y| >= m^3 for all such y.
        # Every y of norm k is unit * generator, so check unit orbits mod m.
        S = self.S
        K = S.K
        m = x.denominator()
        c = K(m * x)
        I = K.ideal(m)
        U = []
        u = K(1)
        while True:
            for s in (u, -u):
                if all((s - t) not in I for t in U):
                    U.append(s)
            u = I.reduce(u * S.eps)
            if (u - 1) in I:
                break
        self._ensure(max(m ** 3 - 1, 1))
        for k in sorted(self.gens):
            if k >= m ** 3:
                break
            for be in self.gens[k]:
                if any((s * be - c) in I for s in U):
                    return False, QQ(k) / m ** 3
        return True, None
