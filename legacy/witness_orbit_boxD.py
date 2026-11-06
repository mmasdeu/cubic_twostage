# SPDX-License-Identifier: GPL-3.0-or-later
"""Exact non-norm-euclidean witnesses with denominator m, via unit invariance.

For x in F and y = x - g with |Nm y| < 1, some eps^k y lies in the box
    B = { |y_1| <= lam^(1/2), |y_2| <= lam^(1/4) },   lam = max(|s1(eps)|, 1/|s1(eps)|)
(normalize log|y_1| - log|y_2| into [-3/4 log lam, 3/4 log lam]; each eps step moves it by
3/2 log lam since |s1(eps)| |s2(eps)|^2 = 1).  And eps^k y = x' - g' with x' = eps^k x mod O_F.
Hence, for x = a/m:
    min_g |Nm(x-g)| >= 1  <=>  for every a' in the <-1,eps>-orbit of a mod m, and every
    integer d with (a'/m - d) in B:  |Nm(a' - m d)| >= m^3.
The candidate set of d is enlarged generously (float bounds + slack), and the norms are
exact integers (cubic norm form with integer coefficients), so the test is exact.
`witnesses(m)` returns ALL a in (Z/m)^3 (lattice coords, primitive or not) that are witnesses.

Same idea one level up (2-stage, smooth level): x is covered by the centre c = r/alpha
(n = |Nm alpha|) iff f(x - c) < 1/n, f(y) = min_g |Nm(y - g)|.  For x = a/m, x - c = b/(mn)
with b integral, and f is unit invariant, so `uncovered_mask(mn, n)` decides it exactly for
all b at once.  `level_witnesses(m, S.classes(L))`: points a/m covered by no centre of norm
<= L, i.e. proofs that the smooth level is > L.
"""
import itertools, math
import numpy as np
from sage.all import PolynomialRing, ZZ, QQ, matrix


class OrbitWitness:
    def __init__(self, S):
        self.S = S
        K = S.K
        # exact cubic norm form N(v) = Nm(sum v_j w_j), integer coefficients
        R = PolynomialRing(ZZ, 'v0,v1,v2')
        v = R.gens()
        mult = [matrix(QQ, [S.coords(w * b) for b in S.basis]) for w in S.basis]
        Mv = sum(vi * mj.change_ring(ZZ) for vi, mj in zip(v, mult))
        Nf = Mv.det()
        self.terms = [(int(c), tuple(int(e) for e in mon.exponents()[0]))
                      for c, mon in zip(Nf.coefficients(), Nf.monomials())]
        E = matrix(QQ, [S.coords(S.eps * w) for w in S.basis])   # coords(eps x) = coords(x) E
        assert all(e in ZZ for e in E.list()) and abs(E.det()) == 1
        self.E = np.array(E, dtype=np.int64)
        e1 = abs(float(S.M[0] @ np.array([float(c) for c in S.coords(S.eps)])))
        lam = max(e1, 1 / e1) * 1.01                      # slack
        b1, b2 = lam ** 0.5, lam ** 0.25
        # lattice-coordinate bounds for y in B: |y_lat_j| <= sum_i |Minv_ji| * bound_i
        Minv = np.linalg.inv(S.M)
        Rj = np.abs(Minv) @ np.array([b1, b2, b2])
        rng = [range(-int(np.ceil(r)) - 1, int(np.ceil(r)) + 2) for r in Rj]
        D = np.array(list(itertools.product(*rng)), dtype=np.int64)
        # keep d only if the cube [0,1]^3 - d can meet B (conservative interval test)
        mid = (0.5 - D) @ S.M.T
        rad = np.abs(S.M).sum(axis=1) * 0.5 * 1.000001 + 1e-9
        lo = np.maximum(np.abs(mid) - rad, 0)
        ok = (lo[:, 0] <= b1) & (np.hypot(lo[:, 1], lo[:, 2]) <= b2)
        # ... and only if |Nm(x - d)| < 1 is possible for some x in the cube (sound lower bound,
        # with slack): the relevant part of B is a thin hyperbolic region, much smaller than B
        ok &= S.lower(np.zeros(3), 1.0, D @ S.M.T) < 1.001
        self.D = D[ok]
        self.lam = lam
        self._mask = {}

    def norm(self, V):
        """exact integer norms of rows of V (object dtype to avoid overflow)."""
        V = V.astype(object)
        out = np.zeros(len(V), dtype=object)
        for c, (e0, e1, e2) in self.terms:
            out = out + c * V[:, 0] ** e0 * V[:, 1] ** e1 * V[:, 2] ** e2
        return out

    def uncovered_mask(self, M, n=1):
        """Boolean mask over A = all b in (Z/M)^3 (lexicographic order, index (b0*M+b1)*M+b2):
        True iff f(b/M) := min_g |Nm(b/M - g)| >= 1/n  (exact; unit-orbit argument above,
        the translate set D for threshold 1 is a superset of the one needed for 1/n)."""
        key = (M, n)
        if key in self._mask:
            return self._mask[key]
        A = np.array(list(itertools.product(range(M), repeat=3)), dtype=np.int64)
        idx = lambda X: (X[:, 0] * M + X[:, 1]) * M + X[:, 2]
        # 1. directly covered: some d in D with n |N(b - M d)| < M^3.
        #    float prefilter (generous), exact check of the few borderline hits.
        cov = np.zeros(len(A), bool)
        Mf = self.S.M
        thr = M ** 3 / n
        for d in self.D:
            V = A - M * d
            Y = V @ Mf.T
            nf = np.abs(Y[:, 0]) * (Y[:, 1] ** 2 + Y[:, 2] ** 2)
            sure = nf < thr * (1 - 1e-6)
            maybe = (~sure) & (nf < thr * (1 + 1e-6)) & (~cov)
            cov |= sure
            if maybe.any():
                ii = np.where(maybe)[0]
                ex = n * np.abs(self.norm(V[ii])) < M ** 3
                cov[ii[ex.astype(bool)]] = True
        # 2. orbit closure: uncovered iff whole <-1,eps>-orbit is not directly covered
        pE = idx((A @ self.E) % M)
        pN = idx((-A) % M)
        # label every point by the minimal index in its eps-cycle (pointer doubling) ...
        lab = np.arange(len(A)); P = pE.copy()
        while True:
            lab2 = np.minimum(lab, lab[P])
            P = P[P]
            if (lab2 == lab).all() and (lab[P] >= lab).all():
                # one more check: stable under a single step means cycle-min reached
                if (np.minimum(lab, lab[pE]) == lab).all():
                    break
            lab = lab2
        # ... then merge each cycle with the cycle of -a: orbit of <-1, eps>
        lab = np.minimum(lab, lab[pN])
        bad = np.zeros(len(A), bool)
        np.logical_or.at(bad, lab, cov)            # orbit contains a covered point
        U = ~bad[lab]
        if M ** 3 <= 2 * 10 ** 6:
            self._mask[key] = U
        return U

    def witnesses(self, m):
        """All a in (Z/m)^3 with min_g |Nm(a/m - g)| >= 1 (not norm-euclidean witnesses)."""
        A = np.array(list(itertools.product(range(m), repeat=3)), dtype=np.int64)
        return A[self.uncovered_mask(m, 1)]

    def level_witnesses(self, m, classes):
        """All a in (Z/m)^3 such that x = a/m is covered by NO centre of `classes`
        (output of TwoStage.classes(L): (coords of r/alpha mod 1, n=|Nm alpha|, alpha, r)),
        i.e. f(x - c) >= 1/n for every class c.  Such x proves: smooth level > L.
        x - c = b/(mn) with b = n a - m (n c) integral, so it is a lookup in uncovered_mask(mn, n)."""
        A = np.array(list(itertools.product(range(m), repeat=3)), dtype=np.int64)
        ok = np.ones(len(A), bool)
        for c, n, al, r in sorted(classes, key=lambda t: t[1]):
            M = m * n
            nc = [int(ci * n) for ci in c]
            assert all(ci * n == v for ci, v in zip(c, nc))
            B = (n * A - m * np.array(nc, dtype=np.int64)) % M
            if M ** 3 <= 4 * 10 ** 6:
                U = self.uncovered_mask(M, n)
                ok &= U[(B[:, 0] * M + B[:, 1]) * M + B[:, 2]]
            else:
                # (Z/M)^3 too large: exact orbit check of the few surviving candidates only
                for i in np.where(ok)[0]:
                    ok[i] = self.verify(B[i], M, n)
            if not ok.any():
                break
        return A[ok]

    def verify(self, a, m, n=1):
        """Fully exact re-check (no floats in the decision): True iff f(a/m) >= 1/n."""
        a = np.array([int(x) % m for x in a], dtype=np.int64)
        orbit, v = set(), a
        while tuple(v) not in orbit:
            orbit.add(tuple(v)); orbit.add(tuple((-v) % m))
            v = (v @ self.E) % m
        V = np.array([np.array(o) - m * d for o in orbit for d in self.D])
        return bool((n * np.abs(self.norm(V)) >= m ** 3).all())

    def verify_level(self, a, m, classes):
        """Exact re-check that a/m is covered by no centre in `classes`."""
        for c, n, al, r in classes:
            nc = [int(ci * n) for ci in c]
            b = [(n * int(ai) - m * v) % (m * n) for ai, v in zip(a, nc)]
            if not self.verify(b, m * n, n):
                return False
        return True


def orbit_witness_search(S, mmax=60, mmin=2):
    """First m in [mmin, mmax] with a primitive witness a/m. Returns (x, m, #primitive)."""
    from sage.all import QQ
    O = OrbitWitness(S)
    for m in range(mmin, mmax + 1):
        prim = [a for a in O.witnesses(m) if math.gcd(*[int(x) for x in a], m) == 1]
        if prim:
            a = prim[0]
            assert O.verify(a, m), "float prefilter disagreed with exact check"
            return S.elt([QQ(int(x)) / m for x in a]), m, len(prim)
    return None, mmax, 0


def level_witness_search(S, L, mmax=20, mmin=2):
    """Smallest m in [mmin, mmax] with a point x = a/m covered by no centre of norm <= L.
    Returns (x, m, #points) or (None, mmax, 0).  A witness proves: smooth level N_min > L."""
    from sage.all import QQ
    O = OrbitWitness(S)
    cl = S.classes(L)
    for m in range(mmin, mmax + 1):
        W = O.level_witnesses(m, cl)
        if len(W):
            a = W[0]
            assert O.verify_level(a, m, cl), "float prefilter disagreed with exact check"
            return S.elt([QQ(int(x)) / m for x in a]), m, len(W)
    return None, mmax, 0
