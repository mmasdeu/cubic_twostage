# SPDX-License-Identifier: GPL-3.0-or-later
"""Covering of R_0 for a real quadratic field, exactly as in Algorithm SOLVE of the paper
(corner test of Lemma 3.2, subdivision into 4), used to generate the TikZ figures.
All containment tests are certified with 200-bit interval arithmetic."""
import itertools
from sage.all import QuadraticField, RealIntervalField, ZZ, QQ, floor, ceil, sqrt

RIF = RealIntervalField(200)


class Cover2D:
    def __init__(self, m):
        self.m = m
        self.K = K = QuadraticField(m, 'a')
        a = K.gen()
        self.w = a if m % 4 != 1 else (1 + a) / 2
        self.eps = K.units()[0]
        self.sq = RIF(m).sqrt()

        def v(z):
            st = list(z) + [0, 0]
            a0, a1 = QQ(st[0]), QQ(st[1])      # z = a0 + a1 sqrt(m)
            return (RIF(a0) + RIF(a1) * self.sq, RIF(a0) - RIF(a1) * self.sq)
        self.v = v
        corners = [v(s + t * self.w) for s in (0, 1) for t in (0, 1)]
        self.D = [(float(c[0].center()), float(c[1].center())) for c in
                  (v(K(0)), v(K(1)), v(1 + self.w), v(self.w))]
        self.R0 = (QQ(floor(min(c[0] for c in corners).lower() * 1024)) / 1024,
                   QQ(ceil(max(c[0] for c in corners).upper() * 1024)) / 1024,
                   QQ(floor(min(c[1] for c in corners).lower() * 1024)) / 1024,
                   QQ(ceil(max(c[1] for c in corners).upper() * 1024)) / 1024)

    def classes(self, N):
        """(r/alpha mod O_F as element, |Nm alpha|): centres with denominator of norm <= N."""
        K = self.K; out = []
        for n, ideals in sorted(K.ideals_of_bdd_norm(N).items()):
            for I in ideals:
                al = I.gens_reduced()[0]
                if n == 1:
                    out.append((K(0), 1)); continue
                res, u = [], K(1)
                while True:
                    for s in (u, -u):
                        rr = I.reduce(s)
                        if all((rr - t) not in I for t in res): res.append(rr)
                    u = I.reduce(u * self.eps)
                    if (u - 1) in I: break
                out += [(r / al, n) for r in res]
        return out

    def centres(self, N, T):
        """Q_{T,N}: translates c + d + b w (|b| < T) whose region meets R_0 (float prefilter:
        it only decides which centres are tried; containment is certified in `inside`)."""
        x0, x1, y0, y1 = [float(t) for t in self.R0]
        out = []
        for c, n in self.classes(N):
            cb = QQ((list(c) + [0, 0])[1]) if self.m % 4 != 1 else None
            for b in range(-T - 1, T + 1):
                for d in range(-60, 61):
                    q = c + d + b * self.w
                    # paper's Q_{T,N}: q = a + b' w with |b'| < T
                    bq = (q - (list(q) + [0, 0])[0]) / self.w if self.m % 4 != 1 else None
                    if bq is not None and not abs(QQ(bq)) < T:
                        continue
                    X, Y = self.v(q)
                    xf, yf = float(X.center()), float(Y.center())
                    ux = max(0.0, x0 - xf, xf - x1); uy = max(0.0, y0 - yf, yf - y1)
                    if ux * uy < 1.0 / n:
                        out.append((q, n, X, Y))
        return out

    def inside(self, box, cen):
        """Lemma 3.2: box inside V(q) iff max|x - X| * max|y - Y| < 1/n (certified)."""
        x0, x1, y0, y1 = box; q, n, X, Y = cen
        mx = max(abs(RIF(x0) - X), abs(RIF(x1) - X)); my = max(abs(RIF(y0) - Y), abs(RIF(y1) - Y))
        return (mx * my).upper() < (1 / RIF(n)).lower()

    def solve(self, N, T, maxdepth=12):
        C = self.centres(N, T)
        leaves, failed = [], []
        stack = [(self.R0, 0)]
        while stack:
            box, d = stack.pop()
            hit = next((i for i, c in enumerate(C) if self.inside(box, c)), None)
            if hit is not None:
                leaves.append((box, d, hit)); continue
            if d >= maxdepth:
                failed.append(box); continue
            x0, x1, y0, y1 = box; xm, ym = (x0 + x1) / 2, (y0 + y1) / 2
            stack += [((x0, xm, y0, ym), d + 1), ((xm, x1, y0, ym), d + 1),
                      ((x0, xm, ym, y1), d + 1), ((xm, x1, ym, y1), d + 1)]
        return C, leaves, failed
