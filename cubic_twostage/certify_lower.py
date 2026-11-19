# SPDX-License-Identifier: GPL-3.0-or-later
"""Rigorous re-verification of the exact lower bounds (witnesses and level witnesses).

witness_orbit.py finds witnesses with a translate set D built in floating point (LLL +
Fincke-Pohst with slack).  Its final check uses exact integer norms, but only over that D,
so the completeness of D was not proved.  This script re-checks every claimed point with
  * lambda: an upper bound from 1024-bit interval arithmetic for the fundamental unit,
    which is certified by PARI bnfcertify;
  * D: a provable superset of {d in Z^3 : sigma([0,1]^3 - d) meets B and |Nm| < 1 there},
    with B = {|y1| <= lam^(1/2), |y2| <= lam^(1/4)} (Lemma "normalize").  The hyperbolic part
    of B is covered by the dyadic pieces
        P_i0 = {|y1| <= 2^i0, |y2| <= b2},
        P_i  = {|y1| <= 2^i, |y2| <= min(b2, 2^{-(i-1)/2})}   (i0 < i <= i1, 2^i1 >= b1).
    For each piece, the d with d in [0,1]^3 - M^{-1} P are enumerated as integer points of a
    box in coordinates z = U^{-1} d (U from LLL, but any unimodular U is correct).  The box
    is computed with 256-bit interval arithmetic (M^{-1} from the trace-dual basis).  It is
    then pruned only by lower bounds that hold with explicit floating-point error margins;
  * norms: integral norm form, float evaluation with an a priori error bound
    (1e-13 * sum of |terms|, about 60x the standard bound (k+4)u); undecided cases are
    evaluated exactly with Python integers.
The classes of centres (ideals of norm <= L via PARI, unit residues) are exact.

Only for complex cubic fields (signature (1,1)).  The batch re-check of the paper's data
is scripts/certify_lower.py.
"""

import itertools
import math
import os

import numpy as np

MAX_D = int(
    float(os.environ.get("CUBIC_MAX_D", 2e7))
)  # refuse larger translate boxes (time)
ERR = 1e-13  # relative error margin of float evaluations (see docstring)


class RigorousLower:
    def __init__(self, S, build_D=True):
        if S.signature() != (1, 1):
            raise NotImplementedError(
                "RigorousLower is implemented for complex cubic fields only"
            )
        from sage.all import (
            QQ,
            ZZ,
            ComplexIntervalField,
            PolynomialRing,
            RealIntervalField,
            matrix,
            pari,
        )

        self.S = S
        K = S.K
        # --- exact norm form N(v) = Nm(sum v_j w_j)
        R = PolynomialRing(ZZ, "v0,v1,v2")
        v = R.gens()
        mult = [matrix(QQ, [S.coords(w * b) for b in S.basis]) for w in S.basis]
        Nf = sum(vi * mj.change_ring(ZZ) for vi, mj in zip(v, mult)).det()
        self.terms = [
            (int(c), tuple(int(e) for e in mon.exponents()[0]))
            for c, mon in zip(Nf.coefficients(), Nf.monomials())
        ]
        assert all(sum(e) == 3 and abs(c) < 2**50 for c, e in self.terms)
        # --- fundamental unit: certified by bnfcertify, compared through the regulator
        bnf = pari(K.defining_polynomial()).bnfinit(1)
        assert int(pari.bnfcertify(bnf)) == 1
        Rcert = float(bnf.bnf_get_reg())
        eps = S.eps
        E = matrix(QQ, [S.coords(eps * w) for w in S.basis])
        assert all(e in ZZ for e in E.list()) and abs(E.det()) == 1
        self.E = E.change_ring(ZZ)
        RIFb = RealIntervalField(1024)
        emb = [e for e in K.embeddings(RIFb)]
        assert len(emb) == 1
        s1 = emb[0](eps)
        lam = max(s1.abs(), (1 / s1).abs())
        assert lam.lower() > 1
        self.loglam = float(lam.log().center())
        # eps generates the units mod torsion iff log lam equals the certified regulator
        assert abs(self.loglam - Rcert) < 1e-6 * max(1.0, Rcert), (self.loglam, Rcert)
        RIF = RealIntervalField(256)
        lamI = RIF(lam.upper())
        self.b1 = float(lamI.sqrt().upper()) * (1 + 1e-12)
        self.b2 = float(lamI.sqrt().sqrt().upper()) * (1 + 1e-12)
        # --- interval M (rows sigma1, Re sigma2, Im sigma2) and M^{-1} via the trace dual
        CIF = ComplexIntervalField(256)
        cembs = K.embeddings(CIF)
        ire = min(cembs, key=lambda e: abs(e(K.gen()).imag().center()))
        icx = [e for e in cembs if e(K.gen()).imag().center() > 0][0]
        self.MI = [
            [RIF(ire(w).real()) for w in S.basis],
            [RIF(icx(w).real()) for w in S.basis],
            [RIF(icx(w).imag()) for w in S.basis],
        ]
        T = matrix(QQ, 3, 3, [(wi * wj).trace() for wi in S.basis for wj in S.basis])
        Tinv = T.inverse()
        dual = [sum(Tinv[i, j] * S.basis[j] for j in range(3)) for i in range(3)]
        # a_j = Tr(x w_j*) = u s1(w_j*) + 2 Re(w s2(w_j*))
        self.MinvI = [
            [RIF(ire(dj).real()), 2 * RIF(icx(dj).real()), -2 * RIF(icx(dj).imag())]
            for dj in dual
        ]
        # sanity: Minv * M = I
        for i in range(3):
            for j in range(3):
                s = sum(self.MinvI[i][k] * self.MI[k][j] for k in range(3))
                assert s.contains_zero() if i != j else (s - 1).contains_zero()
        self.Mf = np.array([[float(x.center()) for x in row] for row in self.MI])
        self.D = self._build_D() if build_D else None

    # ------------------------------------------------------------------ ideal method
    def uncovered_ideals(self, a, m):
        """Exact alternative to uncovered(a, m, 1) for small m (no translate set):
        a/m is covered iff some beta = a - m g has 0 < |Nm beta| < m^3 (or a = 0 mod m), and
        such beta is u*gamma with gamma a generator of an ideal of norm < m^3, u a unit.  So
        a/m is a witness iff a mod m lies in no <-1,eps>-orbit of such generators mod m.
        """
        a = tuple(int(x) % m for x in a)
        if a == (0, 0, 0):
            return False, 0
        K, S = self.S.K, self.S
        nchk = 0
        for k, ideals in K.ideals_of_bdd_norm(m**3 - 1).items():
            for I in ideals:
                if k == 0:
                    continue
                g = I.gens_reduced()[0]
                assert abs(g.norm()) == k
                c = [int(x) for x in S.coords(g)]
                if any(tuple(o) == a for o in self.orbit(c, m)):
                    return False, nchk
                nchk += 1
        return True, nchk

    # ------------------------------------------------------------------ translate set
    def _build_D(self):
        from sage.all import QQ, ZZ, RealIntervalField, matrix, pari

        RIF = RealIntervalField(256)
        b1, b2 = self.b1, self.b2
        Mf = self.Mf
        radc = np.abs(Mf).sum(axis=1) * 0.5
        r1, r2 = radc[0], math.hypot(radc[1], radc[2])
        i1 = int(math.ceil(math.log2(b1)))
        while 2.0**i1 < b1:
            i1 += 1
        i0 = min(i1, int(math.floor(math.log2(1 / b2**2))) - 1)
        pieces = [(2.0**i0 if i0 < i1 else b1, b2)]
        for i in range(i0 + 1, i1 + 1):
            pieces.append((2.0**i, min(b2, 2.0 ** (-(i - 1) / 2) * (1 + 1e-12))))
        rcI = [sum(x.abs() for x in row) / 2 for row in self.MI]  # cube radii, rigorous
        Ds, total = [], 0
        for A, Bw in pieces:
            # reduction matrix U: any unimodular U is correct; LLL makes the box tight
            Bas = np.diag([1 / (A + r1), 1 / (Bw + r2), 1 / (Bw + r2)]) @ Mf
            e = int(np.ceil(np.log2(1 / np.abs(Bas[Bas != 0]).min()))) + 40
            Bi = matrix(ZZ, 3, 3, [int(round(x * 2.0**e)) for x in Bas.flatten()])
            U = matrix(ZZ, pari(Bi).qflll().sage())
            assert abs(U.det()) == 1
            Ui = U.inverse().change_ring(ZZ)
            # sigma(x) for x in [0,1]^3 lies in the box sigma(c0) + [-rc_k, rc_k] (c0 = cube
            # centre), so sigma(d) = sigma(x) - y lies in sigma(c0) + prod [-(h_k+rc_k), h_k+rc_k]
            # and z = Ui d = Ui c0 + G (sigma(d) - sigma(c0)) with G = Ui M^{-1}.
            h = [RIF(A) + rcI[0], RIF(Bw) + rcI[1], RIF(Bw) + rcI[2]]
            lo, hi = [], []
            for i in range(3):
                G = [
                    sum(Ui[i, j] * self.MinvI[j][k] for j in range(3)) for k in range(3)
                ]
                s = sum(G[k].abs() * h[k] for k in range(3))
                zc = RIF(sum(Ui[i, j] for j in range(3))) / 2
                lo.append(int((zc - s).lower().floor()))
                hi.append(int((zc + s).upper().ceil()))
            size = 1
            for a, b in zip(lo, hi):
                size *= b - a + 1
            total += size
            if total > MAX_D:
                raise MemoryError(f"translate box too large ({total:.2e})")
            Un = np.array(U, dtype=np.int64)
            # stream over slices z0 = const to keep memory proportional to the kept points
            Z12 = np.array(
                list(
                    itertools.product(range(lo[1], hi[1] + 1), range(lo[2], hi[2] + 1))
                ),
                dtype=np.int64,
            )
            for z0 in range(lo[0], hi[0] + 1):
                Z = np.empty((len(Z12), 3), dtype=np.int64)
                Z[:, 0] = z0
                Z[:, 1:] = Z12
                Dp = Z @ Un.T
                Ds.append(Dp[self._keep(Dp)])
        D = np.unique(np.concatenate(Ds), axis=0)
        return D

    def _keep(self, D):
        """False only where provably sigma([0,1]^3 - d) misses B or has |Nm| >= 1 throughout.
        Float evaluation with error margin e_i >= 1e-12 * (sum |M_ij| |0.5 - d_j| + sum |M_ij|),
        far above the rounding errors (a few units of 2^-53 of the same quantities)."""
        Mf = self.Mf
        X = 0.5 - D.astype(float)
        mid = X @ Mf.T
        mag = np.abs(X) @ np.abs(Mf).T + np.abs(Mf).sum(axis=1)
        rad = np.abs(Mf).sum(axis=1) * 0.5
        lo = np.maximum(np.abs(mid) - rad - 1e-12 * mag, 0)
        miss_box = (lo[:, 0] > self.b1 * (1 + 1e-9)) | (
            lo[:, 1] ** 2 + lo[:, 2] ** 2 > self.b2**2 * (1 + 1e-9)
        )
        miss_hyp = lo[:, 0] * (lo[:, 1] ** 2 + lo[:, 2] ** 2) > 1 + 1e-9
        return ~(miss_box | miss_hyp)

    # ------------------------------------------------------------------ norms
    def exact_norm(self, V):
        out = []
        for row in V:
            a, b, c = (int(x) for x in row)
            out.append(
                sum(co * a**e0 * b**e1 * c**e2 for co, (e0, e1, e2) in self.terms)
            )
        return out

    def covered_any(self, V, M, n):
        """True iff some row v of V (int64) has n |N(v)| < M^3 (rigorous)."""
        assert np.abs(V).max() < 2**52
        F = V.astype(float)
        val = np.zeros(len(V))
        mag = np.zeros(len(V))
        for c, (e0, e1, e2) in self.terms:
            t = float(c) * F[:, 0] ** e0 * F[:, 1] ** e1 * F[:, 2] ** e2
            val += t
            mag += np.abs(t)
        err = ERR * mag + 1e-300
        thr = float(M) ** 3 / n
        if (np.abs(val) + err < thr * (1 - 1e-15)).any():
            return True
        und = np.where(np.abs(val) - err < thr * (1 + 1e-15))[0]
        if len(und):
            M3 = int(M) ** 3
            for N in self.exact_norm(V[und]):
                if n * abs(N) < M3:
                    return True
        return False

    def orbit(self, b, M):
        Em = np.array(self.E, dtype=object) % M
        Em = np.array(Em, dtype=np.int64)
        b = np.array([int(x) % M for x in b], dtype=np.int64)
        seen, out, v = set(), [], b
        while tuple(v) not in seen:
            for w in (v, (-v) % M):
                if tuple(w) not in seen:
                    seen.add(tuple(w))
                    out.append(w.copy())
            v = (v @ Em) % M
        return np.array(out, dtype=np.int64)

    def uncovered(self, b, M, n=1, chunk=4 * 10**6):
        """True iff f(b/M) >= 1/n, i.e. b/M lies in no V(g), g in O, of radius 1/n."""
        O = self.orbit(b, M)
        D = self.D
        per = max(1, chunk // max(1, len(D)))
        MD = M * D
        for s in range(0, len(O), per):
            V = (O[s : s + per, None, :] - MD[None, :, :]).reshape(-1, 3)
            if self.covered_any(V, M, n):
                return False, len(O)
        return True, len(O)
