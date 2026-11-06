# SPDX-License-Identifier: GPL-3.0-or-later
"""Diagnose why an N-covering fails: run cover() with given far-centre settings and report
where the failed boxes are and a float estimate of f(x) = min_g |Nm(x - g)| there.
usage: python3 diag_cover.py "poly" [--N 1] K:L:W:depth [K:L:W:depth ...]
f~ uses unit invariance: min over |k| <= 6 of min over |g| <= 4 of |Nm(eps^k x mod O - g)|
(heuristic, an over-estimate of f). Failures at points with small f~ mean missing centres;
failures where f~ is close to the radius mean the covering is genuinely tight there."""
import os
for _v in ('OMP_NUM_THREADS', 'OPENBLAS_NUM_THREADS', 'MKL_NUM_THREADS'):
    os.environ.setdefault(_v, '1')
import sys, time, itertools
import numpy as np
from twostage import TwoStage


class FEstimate:
    def __init__(self, S, T=4, K=6):
        self.S = S
        G = np.array(list(itertools.product(range(-T, T + 1), repeat=3)), float)
        self.GM = G @ S.M.T
        E = np.array(S.unit_matrix(), float)
        Ei = np.linalg.inv(E)
        self.Es = [np.linalg.matrix_power(E if k >= 0 else Ei, abs(k)) for k in range(-K, K + 1)]

    def f0(self, A):
        X = A @ self.S.M.T
        out = np.empty(len(A))
        for i in range(0, len(A), 256):
            D = X[i:i + 256, None, :] - self.GM[None]
            out[i:i + 256] = (np.abs(D[..., 0]) * (D[..., 1] ** 2 + D[..., 2] ** 2)).min(axis=1)
        return out

    def __call__(self, A):
        return np.min([self.f0((A @ Ek) % 1) for Ek in self.Es], axis=0)


if __name__ == "__main__":
    args = sys.argv[1:]
    f = args[0]
    N = int(args[args.index("--N") + 1]) if "--N" in args else 1
    levels = [a for a in args[1:] if ":" in a]
    S = TwoStage(f)
    Fx = FEstimate(S)
    print(f, int(S.K.discriminant()), "eps =", S.eps, flush=True)
    for a in levels:
        K, L, W, md = map(int, a.split(":"))
        t = time.time()
        certs, failed = S.cover(N, T=3, maxdepth=md, verbose=False, max_failed=20000, K=K, L=L, W=W)
        print(f"N={N} K={K} L={L} W={W} depth={md}: centres={len(S._C)} certs={len(certs)} "
              f"failed={len(failed)} {time.time()-t:.1f}s", flush=True)
        if not failed:
            print("  covered")
            break
        P = np.array([lo + w / 2 for lo, w, d in failed])
        v = Fx(P)
        u = np.unique(np.round(P * 16).astype(int), axis=0)
        print(f"   failed vol {sum(w**3 for lo, w, d in failed):.2e}; f~ max {v.max():.4f} "
              f"median {np.median(v):.4f}; clusters(1/16)={len(u)}")
        for j in np.argsort(-v)[:3]:
            print(f"   f~{v[j]:.5f} at {np.round(P[j], 5)}")
