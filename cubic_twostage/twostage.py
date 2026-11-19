# SPDX-License-Identifier: GPL-3.0-or-later
r"""
Two-stage Euclidean algorithm and continued fractions in number fields.

This generalizes the algorithm of Guitart--Masdeu (*Continued fractions in 2-stage Euclidean
quadratic fields*, arXiv:1106.0856) from real quadratic fields to number fields of any
signature with class number one.  It is used and tested for

- real quadratic fields, signature `(2, 0)`;
- complex cubic fields, signature `(1, 1)` (the case of the accompanying paper);
- totally real cubic fields, signature `(3, 0)`.

The five norm-Euclidean imaginary quadratic fields also work (with `N = 1`).

Setting.  Let `K` have degree `n`, signature `(r_1, r_2)`, ring of integers `O_K` with integral
basis `w_1, ..., w_n`.  Minkowski space `K \otimes \RR = \RR^{r_1} \times \CC^{r_2}` is identified
with `\RR^n` (real places first, then real and imaginary parts of the complex places), and the
norm is `\prod |x_i| \prod |z_j|^2`.  Elements are written in *lattice coordinates*
`a \in \QQ^n`, `x = \sum a_j w_j`; the fundamental domain is `[0,1]^n`.

A pair `\alpha, \beta` has a decreasing chain of length at most two iff
`|\mathrm{Nm}(\alpha/\beta - [q_1, q_2])| < 1/|\mathrm{Nm}(q_2)|` for some `q_1, q_2 \in O_K`
(Cooke).  The centres `[q_1, q_2] = q_1 + 1/q_2` are, modulo `O_K`, the points `r/\alpha` with
`\alpha` a generator of an ideal of norm `n` and `r` in the image of the unit group in
`(O_K/\alpha)^*`; the region of such a centre is `\{x : |\mathrm{Nm}(x - c)| < 1/n\}`.
A *covering* of level `N` is a finite list of dyadic boxes of `[0,1]^n`, each contained in the
region of one centre of norm `\le N`.  It is found in floating point (:meth:`TwoStage.cover`)
and then every (box, centre) pair is re-checked with interval arithmetic
(:meth:`TwoStage.certify`), so a certified covering proves that `K` is 2-stage Euclidean, and
it computes continued fractions of every element of `K` (:meth:`TwoStage.continued_fraction`).

EXAMPLES:

The real quadratic field `\QQ(\sqrt{14})` is 2-stage but not norm-Euclidean::

    sage: from cubic_twostage import TwoStage, evaluate_cf
    sage: S = TwoStage("x^2 - 14")
    sage: S.find_covering()
    2
    sage: a = S.K.gen()
    sage: x = (3 + 5*a) / (2 - 7*a)
    sage: qs = S.continued_fraction(x)
    sage: evaluate_cf(qs) == x
    True

A complex cubic field (discriminant `-327`, not norm-Euclidean)::

    sage: S = TwoStage("x^3 - x^2 - 2*x - 3")
    sage: S.signature()
    (1, 1)
    sage: S.find_covering()
    3
    sage: t = S.K.gen()
    sage: x = (2 + 3*t + 5*t^2) / (7 - t)
    sage: qs = S.continued_fraction(x); qs   # random (depends on the covering)
    [t^2 + t, 1, t^2 - 3*t, 1, -t^2 + t, t]
    sage: evaluate_cf(qs) == x
    True
    sage: all(q.is_integral() for q in qs)
    True

A totally real cubic field (discriminant `49`, norm-Euclidean)::

    sage: S = TwoStage("x^3 - x^2 - 2*x + 1")
    sage: S.find_covering()
    1
    sage: t = S.K.gen()
    sage: x = (1 + 2*t - t^2) / (5 + t^2)
    sage: evaluate_cf(S.continued_fraction(x)) == x
    True
"""

import itertools
import pickle
import time

import numpy as np
from sage.all import (
    QQ,
    ZZ,
    ComplexIntervalField,
    Integer,
    NumberField,
    PolynomialRing,
    RealIntervalField,
    floor,
    identity_matrix,
    matrix,
    prod,
    vector,
)


def ellipsoid_points(Q, c, r2=1.0, basis=None):
    r"""
    Return all integer vectors `a` with `(a - c)^T Q (a - c) \le r_2`.

    ``Q`` is a positive definite ``n x n`` float matrix.  The quadratic form is LLL-reduced and
    the points are enumerated by Fincke--Pohst, with the innermost coordinate vectorised.

    INPUT:

    - ``Q`` -- positive definite matrix (numpy array)
    - ``c`` -- centre (numpy array of length ``n``)
    - ``r2`` -- squared radius
    - ``basis`` -- optional ``B`` with ``Q = B^T B``.  Preferred for ill-conditioned ``Q``
      (very elongated ellipsoids): LLL then runs on the integer-scaled basis (``qflll``),
      which stays nonsingular, whereas a rounded Gram matrix can degenerate.

    OUTPUT: an integer numpy array with one point per row.

    EXAMPLES::

        sage: import numpy as np
        sage: from cubic_twostage.twostage import ellipsoid_points
        sage: P = ellipsoid_points(np.eye(2), np.zeros(2), 1.0)
        sage: sorted(map(tuple, P.tolist()))
        [(-1, 0), (0, -1), (0, 0), (0, 1), (1, 0)]
        sage: len(ellipsoid_points(np.eye(3), np.full(3, 0.5), 3.0))
        32
    """
    from sage.all import pari

    c = np.asarray(c, dtype=float)
    n = len(c)
    if basis is not None:
        B = np.asarray(basis, dtype=float)
        mn = np.abs(B[B != 0]).min()
        e = int(np.ceil(np.log2(1 / mn))) + 40  # >= 40 bits for the smallest entry
        Bi = matrix(
            ZZ,
            n,
            n,
            [
                (
                    int(round(x * 2.0**e))
                    if abs(x * 2.0**e) < 2**52
                    else int(x * 2.0 ** min(e, 900)) * 2 ** max(0, e - 900)
                )
                for x in B.flatten()
            ],
        )
        U = np.array(pari(Bi).qflll().sage(), dtype=np.int64)  # columns: B U reduced
        BU = B @ U
        Qb = BU.T @ BU
    else:
        s = 1.0 / np.abs(Q).max()
        Gm = matrix(
            ZZ, n, n, [int(round(x * s * 2**40)) for x in np.asarray(Q).flatten()]
        )
        U = np.array(pari(Gm).qflllgram().sage(), dtype=np.int64)  # a = U b
        Qb = U.T @ Q @ U
    cb = np.linalg.solve(U.astype(float), c)
    R = np.linalg.cholesky(Qb).T  # Qb = R^T R, R upper triangular
    out = []
    b = np.zeros(n, dtype=np.int64)

    def rec(i, rem):
        # fixed: b[i+1:], remaining squared radius rem
        s = sum(R[i, j] * (b[j] - cb[j]) for j in range(i + 1, n))
        m = cb[i] - s / R[i, i]
        h = np.sqrt(rem) / R[i, i]
        lo, hi = int(np.ceil(m - h)), int(np.floor(m + h))
        if i == 0:
            if hi >= lo:
                P = np.empty((hi - lo + 1, n), dtype=np.int64)
                P[:, 0] = np.arange(lo, hi + 1)
                P[:, 1:] = b[1:]
                out.append(P)
            return
        for bi in range(lo, hi + 1):
            t = (R[i, i] * (bi - cb[i]) + s) ** 2
            if rem - t < 0:
                continue
            b[i] = bi
            rec(i - 1, rem - t)

    rec(n - 1, r2)
    if not out:
        return np.zeros((0, n), dtype=np.int64)
    return np.concatenate(out) @ U.T


def _key(x):
    return tuple(x.list())


class TwoStage:
    r"""
    Coverings by 2-stage regions and continued fractions in a number field.

    INPUT:

    - ``f`` -- a defining polynomial (string, coefficient list or polynomial) or an absolute
      number field
    - ``prec`` -- bits of precision of the interval embeddings used to certify (default 128)
    - ``names`` -- name of the generator when ``f`` is a polynomial (default ``'t'``)
    - ``check_class_number`` -- if ``True`` (default), raise ``ValueError`` unless `h_K = 1`
      (a 2-stage Euclidean field is a principal ideal domain)

    Attributes: ``K`` (the field), ``basis`` (integral basis), ``M`` (float Minkowski matrix,
    columns = basis), ``Mi`` (the same with real intervals), ``units`` (fundamental units),
    ``torsion`` (generator of the roots of unity), ``eps`` (first fundamental unit).

    EXAMPLES::

        sage: from cubic_twostage import TwoStage
        sage: S = TwoStage("x^2 - x - 1"); S
        2-stage covering machinery for Number Field in t with defining polynomial x^2 - x - 1
        sage: S.signature(), S.unit_rank()
        ((2, 0), 1)
        sage: TwoStage("x^2 + 5")
        Traceback (most recent call last):
        ...
        ValueError: class number 2 > 1: the field is not 2-stage Euclidean

    A number field can be passed directly::

        sage: K.<a> = NumberField(x^3 - 3*x - 1)
        sage: S = TwoStage(K); S.K is K
        True
        sage: S.signature(), S.unit_rank()
        ((3, 0), 2)
    """

    def __init__(self, f, prec=128, names="t", check_class_number=True):
        if hasattr(f, "integral_basis"):
            K = f
            if not K.is_absolute():
                raise ValueError("an absolute number field is needed")
        else:
            K = NumberField(PolynomialRing(QQ, "x")(f), names)
        self.K = K
        self.n = n = K.degree()
        if n < 2:
            raise ValueError("the degree must be at least 2")
        self.r1, self.r2 = K.signature()
        if check_class_number:
            h = K.class_number(proof=False)
            if h != 1:
                raise ValueError(
                    f"class number {h} > 1: the field is not 2-stage Euclidean"
                )
        self.basis = K.integral_basis()
        # coordinates of K-elements w.r.t. the integral basis
        self.Bmat = matrix(QQ, [b.vector() for b in self.basis])
        self.Binv = self.Bmat.inverse()
        # places: the r1 real embeddings, then one embedding (Im > 0) per complex place
        CIF = ComplexIntervalField(prec)
        self.RIF = RealIntervalField(prec)
        gen = K.gen()
        embs = sorted(K.embeddings(CIF), key=lambda e: abs(e(gen).imag().center()))
        re = sorted(embs[: self.r1], key=lambda e: e(gen).real().center())
        cx = sorted(
            [e for e in embs[self.r1 :] if e(gen).imag().center() > 0],
            key=lambda e: e(gen).real().center(),
        )
        assert len(cx) == self.r2
        self._places = re + cx
        rows = [[self.RIF(e(w).real()) for w in self.basis] for e in re]
        for e in cx:
            rows.append([self.RIF(e(w).real()) for w in self.basis])
            rows.append([self.RIF(e(w).imag()) for w in self.basis])
        self.Mi = rows
        self.M = np.array([[float(x.center()) for x in row] for row in rows])
        self.absM = np.abs(self.M)
        self._cx = [(self.r1 + 2 * j, self.r1 + 2 * j + 1) for j in range(self.r2)]
        # units: any generators of a finite-index subgroup of the units would give a valid
        # covering (the centres would be a subset); PARI's fundamental units are used.
        U = K.unit_group(proof=False)
        self.torsion = K(U.torsion_generator())
        self.units = [K(u) for u in U.fundamental_units()]
        assert all(u.is_unit() for u in self.units)
        self.eps = self.units[0] if self.units else None
        self.unit_gens = [self.torsion] + self.units
        self._lift_cache = {}

    def __repr__(self):
        return f"2-stage covering machinery for {self.K}"

    def signature(self):
        """The signature `(r_1, r_2)` of the field."""
        return (self.r1, self.r2)

    def unit_rank(self):
        """The rank `r_1 + r_2 - 1` of the unit group."""
        return len(self.units)

    # ---------- lattice coordinates ----------
    def coords(self, x):
        """Lattice coordinates of ``x`` (w.r.t. the integral basis).

        EXAMPLES::

            sage: from cubic_twostage import TwoStage
            sage: S = TwoStage("x^2 - 5"); S.basis
            [1/2*t + 1/2, t]
            sage: S.coords(S.K.gen() / 3)
            (0, 1/3)
        """
        return vector(QQ, self.K(x).vector()) * self.Binv

    def elt(self, a):
        """The element with lattice coordinates ``a``."""
        return sum(QQ(ai) * w for ai, w in zip(a, self.basis))

    # ---------- Minkowski space helpers ----------
    def _nm(self, m):
        """Norm of rows of nonnegative coordinate bounds m (k x n): prod real * prod |z|^2."""
        out = np.ones(len(m))
        for i in range(self.r1):
            out = out * m[:, i]
        for a, b in self._cx:
            out = out * (m[:, a] ** 2 + m[:, b] ** 2)
        return out

    def _to_places(self, Z):
        """Minkowski rows (k x n, real) -> place values (k x (r1+r2), complex)."""
        W = np.empty((len(Z), self.r1 + self.r2), dtype=complex)
        W[:, : self.r1] = Z[:, : self.r1]
        for j, (a, b) in enumerate(self._cx):
            W[:, self.r1 + j] = Z[:, a] + 1j * Z[:, b]
        return W

    def _from_places(self, W):
        Z = np.empty((len(W), self.n))
        Z[:, : self.r1] = W[:, : self.r1].real
        for j, (a, b) in enumerate(self._cx):
            Z[:, a] = W[:, self.r1 + j].real
            Z[:, b] = W[:, self.r1 + j].imag
        return Z

    def _place_values(self, x):
        """sigma_p(x) for the places p, as complex floats (accurate even for huge units)."""
        return np.array([complex(e(x).center()) for e in self._places])

    # ---------- centres ----------
    def unit_residues(self, I):
        r"""
        The image of the unit group in `(O_K/I)^*`.

        OUTPUT: a list of pairs ``(r, u)`` with ``r`` reduced modulo ``I`` and ``u`` a unit with
        `u \equiv r \pmod I`, one for each element of the image.

        EXAMPLES::

            sage: from cubic_twostage import TwoStage
            sage: S = TwoStage("x^2 - 14")
            sage: len(S.unit_residues(S.K.ideal(5)))
            4
        """
        K = self.K
        one = I.reduce(K(1))
        res = {_key(one): (one, K(1))}
        frontier = [(one, K(1))]
        while frontier:
            new = []
            for r, u in frontier:
                for g in self.unit_gens:
                    r2 = I.reduce(r * g)
                    k = _key(r2)
                    if k not in res:
                        res[k] = (r2, u * g)
                        new.append(res[k])
            frontier = new
        return list(res.values())

    def classes(self, N):
        r"""
        Classes modulo `O_K` of the centres of norm at most ``N``.

        OUTPUT: a list of tuples ``(c, n, alpha, r)``: ``c`` the lattice coordinates in
        `[0,1)^n` of ``r/alpha``, ``n`` `= |\mathrm{Nm}(\alpha)|`, ``alpha`` a generator of an
        ideal of norm ``n``, ``r`` a unit residue modulo ``alpha``.

        EXAMPLES::

            sage: from cubic_twostage import TwoStage
            sage: S = TwoStage("x^2 - 14")
            sage: [(c, n) for c, n, al, r in S.classes(2)]
            [((0, 0), 1), ((0, 1/2), 2)]
        """
        K = self.K
        out = []
        for n, ideals in sorted(K.ideals_of_bdd_norm(N).items()):
            for I in ideals:
                g = I.gens_reduced()
                if len(g) != 1:
                    raise ValueError(f"an ideal of norm {n} is not principal")
                al = g[0]
                if n == 1:
                    out.append(((QQ(0),) * self.n, 1, K(1), K(1)))
                    continue
                for r, u in self.unit_residues(I):
                    c = self.coords(r / al)
                    c = tuple(ci - floor(ci) for ci in c)
                    out.append((c, n, al, r))
        return out

    def ideal_norms(self, N):
        """The norms ``<= N`` of integral ideals of the field (the possible levels)."""
        return sorted(n for n, I in self.K.ideals_of_bdd_norm(N).items() if I)

    def unit_matrices(self):
        """Integer matrices `E_i` with ``coords(u_i x) = coords(x) E_i`` for the fundamental
        units `u_i`."""
        if not hasattr(self, "_Es"):
            Es = []
            for u in self.units:
                E = matrix(QQ, [self.coords(u * w) for w in self.basis])
                assert all(e in ZZ for e in E.list()) and abs(E.det()) == 1
                Es.append(E.change_ring(ZZ))
            self._Es = Es
        return self._Es

    def unit_matrix(self):
        """The matrix of :meth:`unit_matrices` for the first fundamental unit ``eps``."""
        return self.unit_matrices()[0]

    def _unit_powers(self, K, l1=False):
        """(k, E^k) for multi-indices k in [-K, K]^rank (|k|_1 <= K if l1)."""
        Es = self.unit_matrices()
        for kv in itertools.product(range(-K, K + 1), repeat=len(Es)):
            if l1 and sum(map(abs, kv)) > K:
                continue
            yield kv, prod((E**k for E, k in zip(Es, kv)), identity_matrix(ZZ, self.n))

    def local_centres(self, cl, points, Kp, Tp=2, reach=2.0**-9):
        r"""
        Centres needed near given points ``p`` (lattice coordinates).

        These are `u^k (b' + h)` for units `u^k` (`|k|_1 \le` ``Kp``), `h` in
        ``floor(u^-k p - b') + [-Tp, Tp]^n``, `b'` the class of `u^{-k} b`: the unit maps the
        thin far tube through `p` onto a fat box around `u^{-k} p`.  Translates are exact;
        Minkowski coordinates are computed multiplicatively, `\sigma(u)^k \sigma(b' + h)`, to
        avoid cancellation.  Only centres whose region can meet the box ``p +- reach`` are kept.

        OUTPUT: lists (C, rho, idx, translates) as in :meth:`centres`.
        """
        out = [], [], [], []
        if not self.units:
            return out
        n = self.n
        pos = {c[0]: i for i, c in enumerate(cl)}
        Bf = np.array([[float(ci) for ci in c[0]] for c in cl])
        rho_cl = np.array([1.0 / c[1] for c in cl])
        sig = [self._place_values(u) for u in self.units]
        G = np.array(
            list(itertools.product(range(-Tp, Tp + 1), repeat=n)), dtype=np.int64
        )
        P = np.atleast_2d(np.array(points, dtype=float))
        for kv, Ek in self._unit_powers(Kp, l1=True):
            Eki = Ek.inverse().change_ring(ZZ)
            if max(abs(x) for x in Ek.list() + Eki.list()) > 10**12:
                continue  # keep everything well inside int64
            fac = np.prod([s**k for s, k in zip(sig, kv)], axis=0)
            Ekn = np.array(Ek, dtype=np.int64)
            Ekif = np.array(Eki, dtype=float)
            Q = P @ Ekif  # approx u^-k p
            ok = np.isfinite(Q).all(axis=1) & (np.abs(Q).max(axis=1) < 1e12)
            for j, c in enumerate(cl):
                q = vector(QQ, c[0]) * Eki  # u^-k b_j = b_jk + s
                fl = [floor(qi) for qi in q]
                jk = pos[tuple(qi - f for qi, f in zip(q, fl))]
                s = np.array([int(f) for f in fl], dtype=np.int64)
                for p, qp in zip(P[ok], Q[ok]):
                    H = np.floor(qp - Bf[jk]).astype(np.int64) + G
                    tr = (H - s) @ Ekn  # exact integer translate for class j
                    z = (Bf[jk] + H) @ self.M.T  # sigma(b_jk + h)
                    C = self._from_places(self._to_places(z) * fac)
                    keep = self.lower(p - reach, 2 * reach, C) < rho_cl[j]
                    out[0].append(C[keep])
                    out[1].append(np.full(keep.sum(), rho_cl[j]))
                    out[2].append(np.full(keep.sum(), j))
                    out[3].append(tr[keep])
        return out

    def centres(self, N, T, K=0, L=0, W=0, points=None, Kp=12):
        r"""
        Centres of norm at most ``N`` that may meet `[0,1]^n`.

        - `b + g`, ``b`` a class of :meth:`classes`, `g \in [-T, T]^n`, and their unit images
          `u^k (b + g)` for `|k_i| \le` ``K`` (exact: class of `u^k b` plus an integer
          translate).  The regions are unbounded along the unit directions, so far-away centres
          matter.
        - if ``L`` or ``W`` is positive: all `b + g` whose Minkowski image lies in a slab long
          in one place (half-length ``L`` for a real place, radius ``W`` for a complex place)
          and narrow (twice the radius of the cube, plus 1) in the others, enumerated with
          :func:`ellipsoid_points`.
        - ``points``: :meth:`local_centres` at these points.

        Everything is pre-filtered with a sound lower bound.

        OUTPUT: float Minkowski centres, radii, class indices, integer translates.
        """
        n = self.n
        cl = self.classes(N)
        pos = {c[0]: i for i, c in enumerate(cl)}
        G = np.array(
            list(itertools.product(range(-T, T + 1), repeat=n)), dtype=np.int64
        )
        Bf = np.array([[float(ci) for ci in c[0]] for c in cl])
        rho_cl = np.array([1.0 / c[1] for c in cl])
        zero = np.zeros(n)
        allC, allR, allI, allT = [], [], [], []
        for kv, Ek in self._unit_powers(K):
            if max(abs(x) for x in Ek.list()) > 10**15:
                continue  # huge unit: these centres would overflow int64 (and are useless)
            Ekn = np.array(Ek, dtype=np.int64)
            jmap, shift = [], []
            for c in cl:
                q = vector(QQ, c[0]) * Ek
                fl = [floor(qi) for qi in q]
                jmap.append(pos[tuple(qi - f for qi, f in zip(q, fl))])
                shift.append([int(f) for f in fl])
            jmap = np.array(jmap)
            shift = np.array(shift, dtype=np.int64)
            GE = G @ Ekn
            tr = (shift[:, None, :] + GE[None, :, :]).reshape(-1, n)
            idx = np.repeat(jmap, len(G))
            C = (Bf[idx] + tr) @ self.M.T
            r = rho_cl[idx]
            keep = self.lower(zero, 1.0, C) < r
            allC.append(C[keep])
            allR.append(r[keep])
            allI.append(idx[keep])
            allT.append(tr[keep])
        if L > 0 or W > 0:
            u0 = self.M @ np.full(n, 0.5)
            rad = self.absM.sum(axis=1) * 0.5
            prad = [rad[i] for i in range(self.r1)] + [
                np.hypot(rad[a], rad[b]) for a, b in self._cx
            ]
            pcols = [[i] for i in range(self.r1)] + [[a, b] for a, b in self._cx]
            Minv_c = np.linalg.solve(self.M, u0)
            gs = []
            for p in range(self.r1 + self.r2):
                A = L if p < self.r1 else W
                if A <= 0:
                    continue
                scale = np.empty(n)
                for q, cols in enumerate(pcols):
                    scale[cols] = A if q == p else 2 * prad[q] + 1
                Bas = np.diag(1 / scale) @ self.M
                gs.append(ellipsoid_points(Bas.T @ Bas, Minv_c, float(n), basis=Bas))
            if gs:
                g = np.unique(np.concatenate(gs), axis=0)
                for j in range(len(cl)):
                    C = (Bf[j] + g) @ self.M.T
                    keep = self.lower(zero, 1.0, C) < rho_cl[j]
                    allC.append(C[keep])
                    allR.append(np.full(keep.sum(), rho_cl[j]))
                    allI.append(np.full(keep.sum(), j))
                    allT.append(g[keep])
        if points is not None and len(points):
            lc = self.local_centres(cl, points, Kp)
            allC += lc[0]
            allR += lc[1]
            allI += lc[2]
            allT += lc[3]
        idx = np.concatenate(allI)
        tr = np.concatenate(allT)
        key = np.concatenate([idx[:, None], tr], axis=1)
        _, u = np.unique(key, axis=0, return_index=True)  # drop duplicates
        self._cl = cl
        return (np.concatenate(allC)[u], np.concatenate(allR)[u], idx[u], tr[u])

    # ---------- box bounds (float) ----------
    def _intervals(self, lo, w, C):
        mid = self.M @ (lo + w / 2)
        rad = self.absM.sum(axis=1) * (w / 2)
        return mid[None, :] - C, rad

    def upper(self, lo, w, C):
        """Upper bounds of `|\\mathrm{Nm}(x - c)|` over the box ``lo + [0, w]^n``, for the centres ``C``."""
        c, rad = self._intervals(lo, w, C)
        return self._nm(np.abs(c) + rad)

    def lower(self, lo, w, C):
        """Lower bounds of `|\\mathrm{Nm}(x - c)|` over the box ``lo + [0, w]^n``, for the centres ``C``."""
        c, rad = self._intervals(lo, w, C)
        return self._nm(np.maximum(np.abs(c) - rad, 0))

    # ---------- covering search ----------
    def cover(
        self,
        N,
        T=3,
        maxdepth=14,
        verbose=True,
        max_failed=None,
        K=0,
        L=0,
        W=0,
        points=None,
        Kp=12,
        cell_cap=None,
        cell_depth=14,
    ):
        r"""
        Floating-point search for a covering of `[0,1]^n` by regions of centres of norm
        `\le N`.

        Depth-first subdivision into dyadic boxes; each box inherits the candidate centres of
        its parent, pruned by a lower bound.  The centre set is given by ``T, K, L, W, points,
        Kp`` (see :meth:`centres`).

        OUTPUT: ``(certs, failed)``: the boxes found (``(lo, w, depth, centre index)``) and the
        boxes that could not be covered down to ``maxdepth`` (stops after ``max_failed``).
        The covering is complete iff ``failed`` is empty; then pass ``certs`` to
        :meth:`certify`.

        EXAMPLES::

            sage: from cubic_twostage import TwoStage
            sage: S = TwoStage("x^2 - 14")
            sage: certs, failed = S.cover(1, maxdepth=8, max_failed=10, verbose=False)
            sage: len(failed) > 0      # Q(sqrt 14) is not norm-Euclidean
            True
            sage: certs, failed = S.cover(2, verbose=False); failed
            []
        """
        n = self.n
        t0 = time.time()
        C, rho, idx, tr = self.centres(N, T, K, L, W, points, Kp)
        if verbose:
            print(f"N={N}: {len(self._cl)} classes, {len(C)} centres", flush=True)
        certs, failed = [], []
        stack = [(np.zeros(n), 1.0, 0, np.arange(len(C)))]
        corners = np.array(list(itertools.product((0, 1), repeat=n)), dtype=float)
        cells = {}  # cell_cap: failures per 2^-cell_depth cell; full cells are skipped
        csc = 2.0**cell_depth
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
            ratio = self.upper(lo, w, Cc) / rc
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
            cand = cand[self.lower(lo, w, Cc) < rc]
            for cn in corners:
                stack.append((lo + cn * w / 2, w / 2, d + 1, cand))
        self._C, self._rho, self._idx, self._tr = C, rho, idx, tr
        if verbose:
            print(
                f"   boxes certified: {len(certs)}, failed: {len(failed)},"
                f" {time.time() - t0:.1f}s",
                flush=True,
            )
        return certs, failed

    def cover_adaptive(
        self,
        N,
        T=3,
        maxdepth=16,
        K=2,
        L=300,
        W=20,
        rounds=8,
        Kp=12,
        max_failed=200000,
        max_points=8000,
        per_round=2000,
        verbose=False,
    ):
        """:meth:`cover` plus :meth:`local_centres` at the failures, repeated.

        After each failed round every failure gets a local point by hierarchical refinement
        (grids `2^{-10}, 2^{-13}, \\dots`: the coarsest cell holding no point yet).

        OUTPUT: ``(certs, failed, points_used)``.
        """
        n = self.n
        pts = np.zeros((0, n))
        for rd in range(rounds):
            certs, failed = self.cover(
                N,
                T,
                maxdepth,
                verbose=False,
                max_failed=max_failed,
                K=K,
                L=L,
                W=W,
                points=pts,
                Kp=Kp,
                cell_cap=50,
            )
            if verbose:
                print(
                    f"  round {rd}: {len(self._C)} centres, {len(pts)} points, "
                    f"{len(certs)} boxes, {len(failed)} failed",
                    flush=True,
                )
            if not failed:
                break
            F = np.array([lo + w / 2 for lo, w, d in failed])
            new, todo = [], np.ones(len(F), bool)
            for g in (10, 13, 16, 19):
                have = {tuple(c) for c in np.floor(pts * 2**g).astype(np.int64)}
                cg = np.floor(F * 2**g).astype(np.int64)
                free = todo & np.array([tuple(c) not in have for c in cg])
                if free.any():
                    _, first = np.unique(cg[free], axis=0, return_index=True)
                    new.append(F[np.where(free)[0][first]])
                todo &= ~free
            new = np.concatenate(new) if new else np.zeros((0, n))
            if len(pts) + len(new) > max_points:
                new = new[: max(0, max_points - len(pts))]
                if len(new) == 0:
                    break
            pts = np.concatenate([pts, new])
        return certs, failed, pts

    # ---------- rigorous certification ----------
    def sup_norm(self, m, d, b):
        r"""
        Interval upper bound of `|\mathrm{Nm}(x - b)|` over the dyadic box
        `2^{-d}(m + [0,1]^n)` (``b``: lattice coordinates of the centre, rational).
        """
        RIF = self.RIF
        n = self.n
        I = [RIF(QQ(m[j]) / 2**d - b[j], QQ(m[j] + 1) / 2**d - b[j]) for j in range(n)]
        A = [
            RIF(sum(self.Mi[i][j] * I[j] for j in range(n)).abs().upper())
            for i in range(n)
        ]
        sup = prod((A[i] for i in range(self.r1)), RIF(1))
        for a, b2 in self._cx:
            sup = sup * (A[a] ** 2 + A[b2] ** 2)
        return sup

    def certify(self, certs):
        """Re-check every (box, centre) pair of a :meth:`cover` result with interval
        arithmetic and return the certificate: a list of ``(m, depth, class, translate)``,
        box `2^{-depth}(m + [0,1]^n)`, centre ``class[0] + translate`` of radius
        ``1/class[1]``.  Raises ``ValueError`` if a pair fails."""
        out = []
        for lo, w, d, k in certs:
            ci = self._cl[self._idx[k]]
            g = self._tr[k]
            b = [ci[0][j] + Integer(int(g[j])) for j in range(self.n)]
            m = [
                Integer(round(lo[j] * 2**d)) for j in range(self.n)
            ]  # lo = m 2^-d exactly
            if not self.sup_norm(m, d, b) < self.RIF(1) / ci[1]:
                raise ValueError("certification failed", lo, w, k)
            out.append((tuple(m), d, ci, tuple(int(x) for x in g)))
        return out

    # ---------- high level ----------
    def find_covering(
        self,
        Nmax=100,
        T=3,
        maxdepth=14,
        max_failed=4000,
        K=2,
        L=300,
        W=20,
        verbose=False,
    ):
        r"""
        Find and certify a covering of the smallest level `N \le` ``Nmax`` that the search
        finds (the levels tried are the ideal norms), store it and return `N`.

        The search parameters are those of :meth:`cover` (defaults of the paper's pipeline).
        The certificate is kept in ``self.cert``; :meth:`continued_fraction` uses it.  A
        covering of level ``N`` proves that the smooth level is at most ``N``; failing at
        smaller levels proves nothing (the search may need more centres or depth).

        EXAMPLES::

            sage: from cubic_twostage import TwoStage
            sage: S = TwoStage("x^3 - x^2 + 1")     # d = -23, norm-Euclidean
            sage: S.find_covering(), S.N, len(S.cert) > 0
            (1, 1, True)
        """
        for N in self.ideal_norms(Nmax):
            certs, failed = self.cover(
                N, T, maxdepth, verbose, max_failed=max_failed, K=K, L=L, W=W
            )
            if not failed:
                self.N = N
                self.build_lookup(self.certify(certs))
                return N
        raise ValueError(f"no covering of level <= {Nmax} found with these parameters")

    def save_certificate(self, filename):
        """Pickle ``(defining polynomial, certificate)`` to ``filename``."""
        with open(filename, "wb") as fo:
            pickle.dump((str(self.K.defining_polynomial()), self.cert), fo)

    @classmethod
    def from_certificate(cls, filename, **kwds):
        """Load a pickled certificate (as written by :meth:`save_certificate` or by the
        pipeline scripts) and return a :class:`TwoStage` ready for continued fractions.

        EXAMPLES::

            sage: import os, tempfile
            sage: from cubic_twostage import TwoStage, evaluate_cf
            sage: S = TwoStage("x^2 - 14"); _ = S.find_covering()
            sage: fn = os.path.join(tempfile.mkdtemp(), "cert.pkl")
            sage: S.save_certificate(fn)
            sage: S2 = TwoStage.from_certificate(fn)
            sage: x = S2.K.gen() / 3
            sage: qs = S2.continued_fraction(x); qs   # random (depends on the covering)
            [-2, 1, -1, t + 4, 12*t - 46, 1]
            sage: evaluate_cf(qs) == x
            True
        """
        with open(filename, "rb") as fi:
            poly, cert = pickle.load(fi)
        S = cls(poly, **kwds)
        S.build_lookup(cert)
        S.N = max(c[2][1] for c in cert)
        return S

    # ---------- continued fractions ----------
    def build_lookup(self, cert):
        """Index a certificate by dyadic box for :meth:`find_q`."""
        self.cert = cert
        self.maxd = max(c[1] for c in cert)
        self.lookup = {}
        K = self.K
        for m, d, ci, g in cert:
            # unpickled field elements may live in a different parent: coerce via coefficients
            ci = (ci[0], ci[1], K(list(ci[2].list())), K(list(ci[3].list())))
            self.lookup[(d,) + tuple(m)] = (ci, g)

    def find_q(self, x):
        r"""`q_1, q_2 \in O_K` with `|\mathrm{Nm}(x - [q_1, q_2])| < 1/|\mathrm{Nm}(q_2)|`."""
        if not hasattr(self, "lookup"):
            self.find_covering()
        a = self.coords(x)
        fl = vector(ZZ, [floor(ai) for ai in a])
        fr = a - fl
        for d in range(self.maxd + 1):
            key = (d,) + tuple(int(floor(fr[j] * 2**d)) for j in range(self.n))
            if key in self.lookup:
                (c, n, al, r), g = self.lookup[key]
                q = self.elt(vector(QQ, c) + vector(QQ, g) + fl)
                u = self._unit_lift(r, al)  # unit with u = r mod alpha
                q2 = al / u
                q1 = q - 1 / q2
                assert q1.is_integral() and q2.is_integral()
                return q1, q2
        raise ValueError("point not covered")

    def _unit_lift(self, r, al):
        if abs(al.norm()) == 1:
            return self.K(1)
        k = _key(al)
        if k not in self._lift_cache:
            I = self.K.ideal(al)
            self._lift_cache[k] = (I, {_key(rr): u for rr, u in self.unit_residues(I)})
        I, table = self._lift_cache[k]
        return table[_key(I.reduce(r))]

    def chain_step(self, a, b):
        """One decreasing division chain of length 1 or 2 for ``a, b`` (``b != 0``):
        returns ``[q1, q2], r1, r2`` with ``a = q1 b + r1``, ``b = q2 r1 + r2``."""
        q1, q2 = self.find_q(a / b)
        r1 = a - q1 * b
        r2 = b - q2 * r1
        assert r2.norm().abs() < b.norm().abs()
        return [q1, q2], r1, r2

    def continued_fraction(self, x):
        r"""
        Continued fraction expansion of ``x`` with partial quotients in `O_K`.

        Uses the stored certificate (computing one with :meth:`find_covering` if needed).

        OUTPUT: a list ``[q_1, ..., q_k]`` of integral elements with
        ``evaluate_cf([q_1, ..., q_k]) == x``.

        EXAMPLES::

            sage: from cubic_twostage import TwoStage, evaluate_cf
            sage: S = TwoStage("x^3 - x^2 + 1")
            sage: t = S.K.gen()
            sage: qs = S.continued_fraction(t / 2); qs   # random (depends on the covering)
            [t - 1, 1, -2*t^2 + 2*t - 2, 1]
            sage: evaluate_cf(qs) == t / 2
            True
        """
        K = self.K
        x = K(x)
        d = x.denominator()
        a, b = x * d, K(d)
        qs = []
        while b != 0:
            q, r1, r2 = self.chain_step(a, b)
            if r1 == 0:
                qs.append(q[0])
                break
            qs += q
            a, b = r1, r2
        return qs


def evaluate_cf(qs):
    """The value `q_1 + 1/(q_2 + 1/(\\cdots))` of a finite continued fraction.

    EXAMPLES::

        sage: from cubic_twostage import evaluate_cf
        sage: evaluate_cf([1, 2, 3])
        10/7
    """
    v = qs[-1]
    for q in reversed(qs[:-1]):
        v = q + 1 / v
    return v


_CACHE = {}


def continued_fraction(x, **kwds):
    r"""
    Continued fraction of an element ``x`` of a number field (see
    :meth:`TwoStage.continued_fraction`).  The covering of the field is computed on first use
    (keyword arguments go to :meth:`TwoStage.find_covering`) and cached.

    EXAMPLES::

        sage: from cubic_twostage import continued_fraction, evaluate_cf
        sage: K.<a> = QuadraticField(14)
        sage: qs = continued_fraction((1 + a) / 7); qs   # random (depends on the covering)
        [0, 1, 1, 1, -a - 8, a + 4, -11*a + 40, 1]
        sage: evaluate_cf(qs)
        1/7*a + 1/7
    """
    K = x.parent()
    if K not in _CACHE:
        S = TwoStage(K)
        S.find_covering(**kwds)
        _CACHE[K] = S
    return _CACHE[K].continued_fraction(x)
