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


def ellipsoid_points(Q, c, r2=1.0, basis=None):
    """All integer a with (a-c)^T Q (a-c) <= r2 (Q 3x3 positive definite, float).
    LLL-reduce, then Fincke-Pohst with the innermost loop vectorised.
    basis: optional B with Q = B^T B.  Preferred for ill-conditioned Q (e.g. very elongated
    boxes): LLL runs on the integer-scaled basis (qflll), which stays nonsingular, whereas the
    rounded Gram matrix can degenerate and make qflllgram overflow the PARI stack."""
    from sage.all import pari
    if basis is not None:
        B = np.asarray(basis, dtype=float)
        mn = np.abs(B[B != 0]).min()
        e = int(np.ceil(np.log2(1 / mn))) + 40            # >= 40 bits for the smallest entry
        Bi = matrix(ZZ, 3, 3, [int(round(x * 2.0 ** e)) if abs(x * 2.0 ** e) < 2 ** 52
                               else int(x * 2.0 ** min(e, 900)) * 2 ** max(0, e - 900)
                               for x in B.flatten()])
        U = np.array(pari(Bi).qflll().sage(), dtype=np.int64)    # columns: B U reduced
        BU = B @ U
        Qb = BU.T @ BU
    else:
        s = 1.0 / np.abs(Q).max()
        Gm = matrix(ZZ, 3, 3, [int(round(x * s * 2**40)) for x in Q.flatten()])
        U = np.array(pari(Gm).qflllgram().sage(), dtype=np.int64)   # a = U b
        Qb = U.T @ Q @ U
    cb = np.linalg.solve(U.astype(float), c)
    L = np.linalg.cholesky(Qb)                             # Qb = L L^T
    R = L.T                                                # (b-cb)^T R^T R (b-cb)
    out = []
    r = np.sqrt(r2)
    # coordinate order: b2 outermost, then b1, then b0 vectorised
    def rng(lo, hi):
        return range(int(np.ceil(lo)), int(np.floor(hi)) + 1)
    h2 = r / R[2, 2]
    for b2 in rng(cb[2] - h2, cb[2] + h2):
        t2 = (R[2, 2] * (b2 - cb[2])) ** 2
        rem2 = r2 - t2
        if rem2 < 0: continue
        # row 1: R11 (b1-cb1) + R12 (b2-cb2)
        m1 = cb[1] - R[1, 2] * (b2 - cb[2]) / R[1, 1]
        h1 = np.sqrt(rem2) / R[1, 1]
        for b1 in rng(m1 - h1, m1 + h1):
            t1 = (R[1, 1] * (b1 - cb[1]) + R[1, 2] * (b2 - cb[2])) ** 2
            rem1 = rem2 - t1
            if rem1 < 0: continue
            m0 = cb[0] - (R[0, 1] * (b1 - cb[1]) + R[0, 2] * (b2 - cb[2])) / R[0, 0]
            h0 = np.sqrt(rem1) / R[0, 0]
            b0 = np.arange(int(np.ceil(m0 - h0)), int(np.floor(m0 + h0)) + 1)
            if len(b0):
                B = np.empty((len(b0), 3), dtype=np.int64)
                B[:, 0] = b0; B[:, 1] = b1; B[:, 2] = b2
                out.append(B)
    if not out:
        return np.zeros((0, 3), dtype=np.int64)
    return np.concatenate(out) @ U.T


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

    def unit_matrix(self):
        """Integer matrix E with coords(eps*x) = coords(x) * E (row vectors)."""
        if not hasattr(self, "_E"):
            E = matrix(QQ, [self.coords(self.eps * w) for w in self.basis])
            assert all(e in ZZ for e in E.list()) and abs(E.det()) == 1
            self._E = E.change_ring(ZZ)
        return self._E

    def local_centres(self, cl, points, Kp, Tp=2, reach=2.0 ** -9):
        """Centres needed near given points p (lattice coords): eps^k (b' + h) for |k| <= Kp,
        h in floor(eps^-k p - b') + [-Tp, Tp]^3, b' = class of eps^-k b.  These are the centres
        of the thin far tubes through p (the unit maps the needle around p onto a fat box around
        eps^-k p).  Exact: class b plus integer translate (h - s) E^k where eps^-k b = b' + s.
        Minkowski coordinates are computed multiplicatively, sigma(eps)^k sigma(b' + h), to avoid
        cancellation in huge lattice vectors.  Only centres whose tube can meet the box
        p +- reach are kept (sound lower bound), so a point costs few centres.
        Returns lists (C, rho, idx, translates)."""
        E = self.unit_matrix()
        pos = {c[0]: i for i, c in enumerate(cl)}
        Bf = np.array([[float(ci) for ci in c[0]] for c in cl])
        rho_cl = np.array([1.0 / c[1] for c in cl])
        se = self.M @ np.array([float(c) for c in self.coords(self.eps)])
        s1, s2 = se[0], complex(se[1], se[2])
        G = np.array(list(itertools.product(range(-Tp, Tp + 1), repeat=3)), dtype=np.int64)
        P = np.atleast_2d(np.array(points, dtype=float))
        out = [], [], [], []
        for k in range(-Kp, Kp + 1):
            Ek, Eki = E ** k, E ** (-k)
            if max(abs(x) for x in Ek.list() + Eki.list()) > 10 ** 12:
                continue                                    # keep everything well inside int64
            Ekn = np.array(Ek, dtype=np.int64)
            Ekif = np.array(Eki, dtype=float)
            for j, c in enumerate(cl):
                q = vector(QQ, c[0]) * Eki                  # eps^-k b_j = b_jk + s
                fl = [floor(qi) for qi in q]
                jk = pos[tuple(qi - f for qi, f in zip(q, fl))]
                s = np.array([int(f) for f in fl], dtype=np.int64)
                Q = P @ Ekif                                # approx eps^-k p
                ok = np.isfinite(Q).all(axis=1) & (np.abs(Q).max(axis=1) < 1e12)
                for p, q in zip(P[ok], Q[ok]):
                    H = np.floor(q - Bf[jk]).astype(np.int64) + G
                    tr = (H - s) @ Ekn                      # exact integer translate for class j
                    z = (Bf[jk] + H) @ self.M.T             # sigma(b_jk + h)
                    wz = (z[:, 1] + 1j * z[:, 2]) * s2 ** k
                    C = np.stack([z[:, 0] * s1 ** k, wz.real, wz.imag], axis=1)
                    keep = self.lower(p - reach, 2 * reach, C) < rho_cl[j]
                    out[0].append(C[keep]); out[1].append(np.full(keep.sum(), rho_cl[j]))
                    out[2].append(np.full(keep.sum(), j)); out[3].append(tr[keep])
        return out

    def centres(self, N, T, K=0, L=0, W=0, points=None, Kp=12):
        """Centres b + g (b a class of norm <= N, g in [-T,T]^3) together with
        their unit images eps^k (b + g), |k| <= K.  Since |Nm(eps^k y)| = |Nm y|,
        eps^k(b+g) is again a centre with the same radius: it equals
        b' + g' with b' = class of eps^k b and g' in O_F (exact integer vector).
        The tubes {|Nm(x-c)| < rho} are unbounded along the unit directions,
        so far-away centres matter; K > 0 brings in the relevant ones.
        L, W > 0 add every centre b + g (g in O_F) whose Minkowski image lies in one of
        the two slabs around the image of [0,1]^3 (centre (u0, w0), radii r1, r2):
            |u - u0| <= L, |w - w0| <= 2 r2 + 1      (long in the real direction)
            |u - u0| <= 2 r1 + 1, |w - w0| <= W      (long in the complex direction)
        A tube meeting the cube has (|u-u0|-r1)(|w-w0|-r2)^2 < 1, so for L, W -> oo these
        slabs contain all relevant centres (the 2r enlargement absorbs the class offset b).
        points: add local_centres(points, Kp) (see there) -- used by cover_adaptive.
        Returns float Minkowski centres, radii, class indices, integer translates."""
        cl = self.classes(N)
        pos = {c[0]: i for i, c in enumerate(cl)}
        G = np.array(list(itertools.product(range(-T, T + 1), repeat=3)),
                     dtype=np.int64)
        E = self.unit_matrix()
        Bf = np.array([[float(ci) for ci in c[0]] for c in cl])
        rho_cl = np.array([1.0 / c[1] for c in cl])
        allC, allR, allI, allT = [], [], [], []
        for k in range(-K, K + 1):
            Ek = E ** k
            if max(abs(x) for x in Ek.list()) > 10 ** 15:
                continue          # huge unit: eps^k centres would overflow int64 (and are useless)
            Ekn = np.array(Ek, dtype=np.int64)
            jmap, shift = [], []
            for c in cl:
                q = vector(QQ, c[0]) * Ek
                fl = [floor(qi) for qi in q]
                key = tuple(qi - f for qi, f in zip(q, fl))
                jmap.append(pos[key])          # KeyError = classes not unit-stable
                shift.append([int(f) for f in fl])
            jmap = np.array(jmap)
            shift = np.array(shift, dtype=np.int64)
            GE = G @ Ekn                                     # integer
            tr = (shift[:, None, :] + GE[None, :, :]).reshape(-1, 3)
            idx = np.repeat(jmap, len(G))
            P = Bf[idx] + tr                                 # lattice coords
            C = P @ self.M.T
            r = rho_cl[idx]
            keep = self.lower(np.zeros(3), 1.0, C) < r
            allC.append(C[keep]); allR.append(r[keep])
            allI.append(idx[keep]); allT.append(tr[keep])
        if L > 0 or W > 0:
            u0 = self.M @ np.full(3, 0.5)
            rad = self.absM.sum(axis=1) * 0.5
            r1, r2 = rad[0], np.hypot(rad[1], rad[2])
            Minv_c = np.linalg.solve(self.M, u0)
            gs = []
            for A, Bc in ((L, 2 * r2 + 1), (2 * r1 + 1, W)):
                if A <= 0 or Bc <= 0:
                    continue
                D = np.diag([1 / A ** 2, 1 / Bc ** 2, 1 / Bc ** 2])
                Q = self.M.T @ D @ self.M
                Bas = np.diag([1 / A, 1 / Bc, 1 / Bc]) @ self.M
                gs.append(ellipsoid_points(Q, Minv_c, 3.0, basis=Bas))   # box inside r^2 = 3
            g = np.unique(np.concatenate(gs), axis=0)
            for j in range(len(cl)):
                P = Bf[j] + g
                C = P @ self.M.T
                keep = self.lower(np.zeros(3), 1.0, C) < rho_cl[j]
                allC.append(C[keep]); allR.append(np.full(keep.sum(), rho_cl[j]))
                allI.append(np.full(keep.sum(), j)); allT.append(g[keep])
        if points is not None and len(points):
            lc = self.local_centres(cl, points, Kp)
            allC += lc[0]; allR += lc[1]; allI += lc[2]; allT += lc[3]
        idx = np.concatenate(allI); tr = np.concatenate(allT)
        key = np.concatenate([idx[:, None], tr], axis=1)
        _, u = np.unique(key, axis=0, return_index=True)    # drop duplicates
        self._cl = cl
        return (np.concatenate(allC)[u], np.concatenate(allR)[u], idx[u], tr[u])

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
    def cover(self, N, T=3, maxdepth=14, verbose=True, max_failed=None, K=0, L=0, W=0,
              points=None, Kp=12, cell_cap=None, cell_depth=14):
        t0 = time.time()
        C, rho, idx, tr = self.centres(N, T, K, L, W, points, Kp)
        if verbose:
            print(f"N={N}: {len(self._cl)} classes, {len(C)} centres",
                  flush=True)
        certs, failed = [], []
        stack = [(np.zeros(3), 1.0, 0, np.arange(len(C)))]
        corners = np.array(list(itertools.product((0, 1), repeat=3)),
                           dtype=float)
        cells = {}          # cell_cap: failures per 2^-cell_depth cell; full cells are skipped
        csc = 2.0 ** cell_depth
        while stack:
            lo, w, d, cand = stack.pop()
            if cell_cap and d >= cell_depth:
                ck = tuple((lo * csc).astype(np.int64))
                if cells.get(ck, 0) >= cell_cap:
                    continue
            if len(cand) == 0:
                failed.append((lo, w, d))
                if cell_cap and d >= cell_depth:
                    cells[ck] = cells.get(ck, 0) + 1
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
                if cell_cap and d >= cell_depth:
                    cells[ck] = cells.get(ck, 0) + 1
                if max_failed and len(failed) >= max_failed:
                    break
                continue
            lb = self.lower(lo, w, Cc)
            cand = cand[lb < rc]
            for cn in corners:
                stack.append((lo + cn * w / 2, w / 2, d + 1, cand))
        self._C, self._rho, self._idx, self._tr = C, rho, idx, tr
        if verbose:
            print(f"   boxes certified: {len(certs)}, failed: {len(failed)},"
                  f" {time.time()-t0:.1f}s", flush=True)
        return certs, failed

    def cover_adaptive(self, N, T=3, maxdepth=16, K=2, L=300, W=20, rounds=8, Kp=12,
                       max_failed=200000, max_points=8000, per_round=2000, verbose=False):
        """cover() + local centres at the failures, repeated: after each failed round the
        failures get new points by hierarchical refinement (see below), up to `per_round`.
        Returns (certs, failed, points_used)."""
        pts = np.zeros((0, 3))
        for rd in range(rounds):
            certs, failed = self.cover(N, T, maxdepth, verbose=False, max_failed=max_failed,
                                       K=K, L=L, W=W, points=pts, Kp=Kp, cell_cap=50)
            if verbose:
                print(f"  round {rd}: {len(self._C)} centres, {len(pts)} points, "
                      f"{len(certs)} boxes, {len(failed)} failed", flush=True)
            if not failed:
                break
            F = np.array([lo + w / 2 for lo, w, d in failed])
            # hierarchical refinement: each failure gets a local point at the coarsest grid level
            # (2^-10, 2^-12, ...) whose cell holds no point yet.  One point's local centres cover
            # a box of depth ~8-10 in easy regions but only ~13-17 near thin-tube sheets.
            new, todo = [], np.ones(len(F), bool)
            for g in (10, 13, 16, 19):
                have = {tuple(c) for c in np.floor(pts * 2 ** g).astype(np.int64)}
                cg = np.floor(F * 2 ** g).astype(np.int64)
                free = todo & np.array([tuple(c) not in have for c in cg])
                if free.any():
                    _, first = np.unique(cg[free], axis=0, return_index=True)
                    new.append(F[np.where(free)[0][first]])
                todo &= ~free
            new = np.concatenate(new) if new else np.zeros((0, 3))
            if len(pts) + len(new) > max_points:
                new = new[: max(0, max_points - len(pts))]
                if len(new) == 0:
                    break
            pts = np.concatenate([pts, new])
        return certs, failed, pts

    # ---------- rigorous certification ----------
    def certify(self, certs):
        RIF = self.RIF
        out = []
        for lo, w, d, k in certs:
            ci = self._cl[self._idx[k]]
            g = self._tr[k]
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
        K = self.K
        for m, d, ci, g in cert:
            # unpickled field elements may live in a different parent: coerce via coefficients
            ci = (ci[0], ci[1], K(list(ci[2].list())), K(list(ci[3].list())))
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
