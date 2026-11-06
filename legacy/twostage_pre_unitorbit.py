# SPDX-License-Identifier: GPL-3.0-or-later
"""
2-stage euclideanity and continued fractions in complex cubic fields.
Generalizes Guitart-Masdeu (arXiv:1106.0856) from real quadratic to
signature (1,1) fields of class number 1.

Minkowski space: F_R = R x C = R^3 with coordinates (x, Re z, Im z),
Nm(x, z) = x * |z|^2.  Boxes are taken in *lattice coordinates*
a in [0,1]^3 (x = sum a_j w_j, w_j an integral basis), so we subdivide the
fundamental domain D itself rather than a box containing it.

Centres: [q1,q2] mod O_F = r/alpha with r ranging over the image of the
unit group in (O_F/alpha)^*, alpha over generators of ideals of norm <= N.
The region V(q) = {x : |Nm(x-q)| < 1/Nm(alpha)}.

Search is done in floating point; every (box, centre) pair used is then
certified with 128-bit interval arithmetic, so the final covering is a proof.
"""
from sage.all import (NumberField, PolynomialRing, QQ, ZZ, matrix, vector,
                      ComplexIntervalField, RealIntervalField, ComplexField,
                      floor, cartesian_product, prod, Integer)
import numpy as np
import itertools, time, sys


class TwoStage:
    def __init__(self, f, prec=128):
        R = PolynomialRing(QQ, 'x')
        self.K = K = NumberField(R(f), 't')
        assert K.signature() == (1, 1), "signature (1,1) only"
        assert K.class_number(proof=False) == 1
        self.basis = K.integral_basis()
        # coordinates of K-elements w.r.t. integral basis
        self.Bmat = matrix(QQ, [b.vector() for b in self.basis])
        self.Binv = self.Bmat.inverse()
        # embeddings: real one and one complex one (Im > 0)
        CC = ComplexField(200)
        embs = K.embeddings(CC)
        re = [e for e in embs if e(K.gen()).imag().abs() < 1e-30][0]
        cx = [e for e in embs if e(K.gen()).imag() > 0][0]
        self.M = np.array([[float(re(w).real()) for w in self.basis],
                           [float(cx(w).real()) for w in self.basis],
                           [float(cx(w).imag()) for w in self.basis]])
        self.absM = np.abs(self.M)
        # interval embeddings for certification
        CIF = ComplexIntervalField(prec)
        self.RIF = RealIntervalField(prec)
        iembs = K.embeddings(CIF)
        ire = min(iembs, key=lambda e: abs(e(K.gen()).imag().center()))
        icx = [e for e in iembs
               if e(K.gen()).imag().center() > 0][0]
        self.Mi = [[self.RIF(ire(w).real()) for w in self.basis],
                   [self.RIF(icx(w).real()) for w in self.basis],
                   [self.RIF(icx(w).imag()) for w in self.basis]]
        u = K.unit_group()
        self.eps = K(u.fundamental_units()[0])

    # ---------- lattice coordinates ----------
    def coords(self, x):
        return vector(QQ, x.vector()) * self.Binv

    def elt(self, a):
        return sum(QQ(ai) * w for ai, w in zip(a, self.basis))

    # ---------- centres ----------
    def classes(self, N):
        """(lattice coords in [0,1)^3 of r/alpha, Nm(alpha), alpha, r)"""
        K = self.K
        out = []
        for n, ideals in sorted(K.ideals_of_bdd_norm(N).items()):
            for I in ideals:
                al = I.gens_reduced()[0]
                if n == 1:
                    out.append(((QQ(0),) * 3, 1, K(1), K(1)))
                    continue
                res = []
                u = K(1)
                while True:
                    for s in (u, -u):
                        rr = I.reduce(s)
                        if all(((rr - t) not in I) for t in res):
                            res.append(rr)
                    u = I.reduce(u * self.eps)
                    if (u - 1) in I:
                        break
                for r in res:
                    c = self.coords(r / al)
                    c = tuple(ci - floor(ci) for ci in c)
                    out.append((c, n, al, r))
        return out

    def centres(self, N, T):
        cl = self.classes(N)
        B = np.array([[float(ci) for ci in c[0]] for c in cl])
        rho = np.array([1.0 / c[1] for c in cl])
        G = np.array(list(itertools.product(range(-T, T + 1), repeat=3)),
                     dtype=float)
        P = (B[:, None, :] + G[None, :, :]).reshape(-1, 3)       # lattice
        idx = np.repeat(np.arange(len(cl)), len(G))
        gi = np.tile(np.arange(len(G)), len(cl))
        C = P @ self.M.T                                          # Minkowski
        r = rho[idx]
        # keep centres whose region can meet [0,1]^3
        lo = self.lower(np.zeros(3), 1.0, C)
        keep = lo < r
        self._cl, self._G = cl, G
        return C[keep], r[keep], idx[keep], gi[keep]

    # ---------- box bounds (float) ----------
    def _intervals(self, lo, w, C):
        mid = self.M @ (lo + w / 2)
        rad = self.absM.sum(axis=1) * (w / 2)
        return mid[None, :] - C, rad

    def upper(self, lo, w, C):
        c, rad = self._intervals(lo, w, C)
        m = np.abs(c) + rad
        return m[:, 0] * (m[:, 1] ** 2 + m[:, 2] ** 2)

    def lower(self, lo, w, C):
        c, rad = self._intervals(lo, w, C)
        m = np.maximum(np.abs(c) - rad, 0)
        return m[:, 0] * (m[:, 1] ** 2 + m[:, 2] ** 2)

    # ---------- covering search ----------
    def cover(self, N, T=3, maxdepth=14, verbose=True, max_failed=None):
        t0 = time.time()
        C, rho, idx, gi = self.centres(N, T)
        if verbose:
            print(f"N={N}: {len(self._cl)} classes, {len(C)} centres",
                  flush=True)
        certs, failed = [], []
        stack = [(np.zeros(3), 1.0, 0, np.arange(len(C)))]
        corners = np.array(list(itertools.product((0, 1), repeat=3)),
                           dtype=float)
        while stack:
            lo, w, d, cand = stack.pop()
            if len(cand) == 0:
                failed.append((lo, w, d))
                if max_failed and len(failed) >= max_failed:
                    break
                continue
            Cc, rc = C[cand], rho[cand]
            ub = self.upper(lo, w, Cc)
            ratio = ub / rc
            j = np.argmin(ratio)
            if ratio[j] < 1 - 1e-9:
                certs.append((lo.copy(), w, d, cand[j]))
                continue
            if d >= maxdepth:
                failed.append((lo, w, d))
                if max_failed and len(failed) >= max_failed:
                    break
                continue
            lb = self.lower(lo, w, Cc)
            cand = cand[lb < rc]
            for cn in corners:
                stack.append((lo + cn * w / 2, w / 2, d + 1, cand))
        self._C, self._rho, self._idx, self._gi = C, rho, idx, gi
        if verbose:
            print(f"   boxes certified: {len(certs)}, failed: {len(failed)},"
                  f" {time.time()-t0:.1f}s", flush=True)
        return certs, failed

    # ---------- rigorous certification ----------
    def certify(self, certs):
        RIF = self.RIF
        out = []
        for lo, w, d, k in certs:
            ci = self._cl[self._idx[k]]
            g = self._G[self._gi[k]]
            b = [ci[0][j] + Integer(int(g[j])) for j in range(3)]
            # exact dyadic box: lo = m * 2^-d
            m = [Integer(round(lo[j] * 2 ** d)) for j in range(3)]
            I = [RIF(QQ(m[j]) / 2 ** d - b[j], QQ(m[j] + 1) / 2 ** d - b[j])
                 for j in range(3)]
            L = [sum(self.Mi[i][j] * I[j] for j in range(3)) for i in range(3)]
            A = [l.abs().upper() for l in L]
            sup = RIF(A[0]) * (RIF(A[1]) ** 2 + RIF(A[2]) ** 2)
            if not sup < RIF(1) / ci[1]:
                raise ValueError("certification failed", lo, w, k)
            out.append((tuple(m), d, ci, tuple(int(x) for x in g)))
        return out

    # ---------- continued fractions (part (ii) of the Main Theorem) -------
    def build_lookup(self, cert):
        self.cert = cert
        self.maxd = max(c[1] for c in cert)
        self.lookup = {}
        for m, d, ci, g in cert:
            self.lookup[(d,) + m] = (ci, g)

    def find_q(self, x):
        """q1, q2 in O_F with |Nm(x - [q1,q2])| < 1/|Nm(q2)|."""
        a = self.coords(x)
        fl = vector(ZZ, [floor(ai) for ai in a])
        fr = a - fl
        for d in range(self.maxd + 1):
            key = (d,) + tuple(int(floor(fr[j] * 2 ** d)) for j in range(3))
            if key in self.lookup:
                (c, n, al, r), g = self.lookup[key]
                q = self.elt(vector(QQ, c) + vector(QQ, g) + fl)
                # r = u mod alpha for a unit u; recover u from r
                u = self._unit_lift(r, al)
                q2 = al / u
                q1 = q - 1 / q2
                assert q1.is_integral() and q2.is_integral()
                return q1, q2
        raise ValueError("point not covered")

    def _unit_lift(self, r, al):
        if al.norm().abs() == 1:
            return self.K(1)
        I = self.K.ideal(al)
        u = self.K(1)
        while True:
            for s in (u, -u):
                if (s - r) in I:
                    return s
            u = u * self.eps

    def chain_step(self, a, b):
        """one 1- or 2-stage decreasing division chain for a, b (b != 0)."""
        x = a / b
        q1, q2 = self.find_q(x)
        r1 = a - q1 * b
        r2 = b - q2 * r1
        assert r2.norm().abs() < b.norm().abs()
        return [q1, q2], r1, r2

    def continued_fraction(self, x):
        K = self.K
        x = K(x)
        d = x.denominator()
        a, b = x * d, K(d)
        qs = []
        while b != 0:
            q, r1, r2 = self.chain_step(a, b)
            if r1 == 0:
                qs.append(q[0]); break
            qs += q
            a, b = r1, r2
        return qs


def evaluate_cf(qs):
    v = qs[-1]
    for q in reversed(qs[:-1]):
        v = q + 1 / v
    return v
