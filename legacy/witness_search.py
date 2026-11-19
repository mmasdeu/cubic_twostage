# SPDX-License-Identifier: GPL-3.0-or-later
"""Systematic search for x in F with min_g |Nm(x-g)| >= 1 (non-norm-euclidean proof).
Candidates: x = a/m, a in (Z/m)^3 lattice coordinates, m = 2..mmax.
Float filter: discard x if some nearby g in O_F gives |Nm(x-g)| < 0.999.
Survivors get the exact test of witness2.Witness (sound)."""
import itertools, time
import numpy as np
from sage.all import QQ
from witness_fast import FastWitness


def witness_search(S, mmax=12, T=3, max_exact=5000):
    G = np.array(list(itertools.product(range(-T, T + 1), repeat=3)), float)
    GM = G @ S.M.T
    W = FastWitness(S, mmax)
    seen = set()
    n_exact = 0
    for m in range(2, mmax + 1):
        A = np.array(list(itertools.product(range(m), repeat=3)), float) / m
        X = A @ S.M.T
        D = X[:, None, :] - GM[None, :, :]
        nm = np.abs(D[..., 0]) * (D[..., 1] ** 2 + D[..., 2] ** 2)
        surv = np.where(nm.min(axis=1) >= 0.999)[0]
        for i in surv:
            a = tuple(int(round(v * m)) for v in A[i])
            g = np.gcd.reduce(list(a) + [m])
            key = tuple(QQ(ai) / m for ai in a)
            if key in seen or g > 1:
                continue
            seen.add(key)
            n_exact += 1
            if W.is_witness(a, m):
                return S.elt(key), m, n_exact
            if n_exact >= max_exact:
                return None, m, n_exact
    return None, mmax, n_exact
