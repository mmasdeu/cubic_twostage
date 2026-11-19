# SPDX-License-Identifier: GPL-3.0-or-later
"""Fast exact non-norm-euclidean witness test (same mathematics as witness2).

x = c/m with c in O_F.  min_g |Nm(x-g)| < 1  <=>  some y in c + mO_F has |Nm y| < m^3
<=> some ideal generator beta with Nm(beta) < m^3 and some unit u satisfy u*beta = c (mod m)
<=> beta mod m lies in the orbit {u*c mod m : u in <-1, eps>}   (orbit is closed under u -> u^-1).
Everything is done with integer coordinate vectors in the integral basis, mod m.
"""

import itertools

import numpy as np
from sage.all import QQ, ZZ, matrix, vector


class FastWitness:
    def __init__(self, S, mmax=12):
        if S.signature() != (1, 1):
            raise NotImplementedError("implemented for complex cubic fields only")
        self.S = S
        K = S.K
        B = max(mmax**3 - 1, 1)
        self.gens = []  # (norm, integer coord vector)
        for k, ideals in K.ideals_of_bdd_norm(B).items():
            for J in ideals:
                be = J.gens_reduced()[0]
                self.gens.append((k, tuple(int(a) for a in S.coords(be))))
        # multiplication-by-eps matrix in the integral basis (acts on row vectors)
        E = matrix(QQ, [S.coords(S.eps * w) for w in S.basis])
        assert all(e in ZZ for e in E.list())
        self.E = np.array(E, dtype=np.int64)
        self._res = {}

    def residues(self, m):
        if m not in self._res:
            self._res[m] = {tuple(v % m for v in g) for k, g in self.gens if k < m**3}
        return self._res[m]

    def is_witness(self, a, m):
        """a = integer lattice coords of c = m*x. True iff min |Nm(x-g)| >= 1."""
        res = self.residues(m)
        E = self.E % m
        v = np.array(a, dtype=np.int64) % m
        start = tuple(v)
        while True:
            for s in (v, (-v) % m):
                if tuple(s) in res:
                    return False
            v = (v @ E) % m
            if tuple(v) == start:
                return True
