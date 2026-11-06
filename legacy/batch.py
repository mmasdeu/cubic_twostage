# SPDX-License-Identifier: GPL-3.0-or-later
from twostage import *
from witness2 import Witness
from fractions import Fraction
import pickle, sys

for line in open(sys.argv[1]):
    f = line.strip()
    S = TwoStage(f)
    K = S.K
    d = K.discriminant()
    t0 = time.time()
    c1, failed = S.cover(1, T=3, maxdepth=9, verbose=False)
    wit = "-"
    if failed:
        P = [lo + w / 2 for lo, w, _ in failed]
        reps = []
        for p in P:
            if not any(np.max(np.abs(((p - r + 0.5) % 1) - 0.5)) < 0.03
                       for r in reps):
                reps.append(p)
        W = Witness(S)
        best = None
        for r in reps[:30]:
            tried = set()
            for D in range(2, 13):
                a = tuple(QQ(int(round(float(v) * D))) / D for v in r)
                if a in tried:
                    continue
                tried.add(a)
                x = S.elt(a)
                if x.is_integral():
                    continue
                ok, _ = W.min_at_least_one(x)
                if ok:
                    best = x
                    break
            if best is not None:
                break
        wit = f"non-euclid witness x={best}" if best is not None \
            else "no witness found"
    N = 1
    certs = c1
    while failed:
        N += 1
        certs, failed = S.cover(N, T=3, maxdepth=12, verbose=False)
    cert = S.certify(certs)
    pickle.dump((f, cert), open(f"cert_{-d}.pkl", "wb"))
    print(f"{d:5d}  {f:24s} covered with N={N:2d}  boxes {len(cert):6d}  "
          f"{wit}  ({time.time()-t0:.0f}s)", flush=True)
