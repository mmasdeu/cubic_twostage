# SPDX-License-Identifier: GPL-3.0-or-later
"""Independent verification of covering certificates (Proposition "verify" of the write-up).
usage: python3 verify_all.py [certificate_dir=data/certificates] [--shard i/n]
For every certificate (poly, [(m, depth, class, g), ...]) it checks
 (i)   every box 2^-depth (m + [0,1]^3) lies in [0,1]^3 (0 <= m_j < 2^depth), the boxes are
       pairwise distinct and non-nested, and their volumes add up to exactly 1;
 (ii)  every centre class (r/alpha, n) has |Nm(alpha)| = n, coords(r/alpha) = stored class
       mod Z^3, and r = +-eps^k mod alpha (so r lies in the image U_alpha of the units);
 (iii) every (box, centre) inequality A1 (A2^2 + A3^2) < 1/n in 128-bit interval arithmetic;
and finally computes continued fractions of random elements with the certificate and checks
them exactly.  (check_unit_residues.py is the older stand-alone version of (ii).)"""
from twostage import *
import pickle, glob, random, sys
args = [a for a in sys.argv[1:]]
SHARD = (0, 1)
if "--shard" in args:
    k = args.index("--shard"); i, n = args[k + 1].split("/"); SHARD = (int(i), int(n)); del args[k:k + 2]
CDIR = args[0] if args else "data/certificates"
random.seed(7)


def unit_residue(S, al, r):
    """True iff r = +-eps^k mod alpha for some k."""
    I = S.K.ideal(al)
    u, seen = S.K(1), set()
    while True:
        if (r - u) in I or (r + u) in I:
            return True
        key = tuple(I.reduce(u).list())
        if key in seen:
            return False
        seen.add(key); u = I.reduce(u * S.eps)


ok = 0
files = sorted(glob.glob(CDIR + "/cert_*.pkl"))
for p in files[SHARD[0]::SHARD[1]]:
    f, cert = pickle.load(open(p, "rb"))
    S = TwoStage(f); t = S.K.gen()
    # (i) boxes
    keys = [(c[1],) + tuple(c[0]) for c in cert]
    assert all(0 <= mi < 2 ** d for d, *m in keys for mi in m), (p, "box outside [0,1]^3")
    kset = set(keys)
    assert len(kset) == len(keys), (p, "duplicate box")
    assert sum(QQ(1) / 8 ** d for d, *m in keys) == 1, (p, "volume")
    assert not any((e,) + tuple(mi >> (d - e) for mi in m) in kset
                   for d, *m in kset for e in range(d)), (p, "nested boxes")
    # (ii) centre classes
    seen = {}
    for m, d, ci, g in cert:
        key = (tuple(ci[0]), ci[1], tuple(ci[2].list()), tuple(ci[3].list()))
        if key in seen:
            continue
        al, r = S.K(list(ci[2].list())), S.K(list(ci[3].list()))
        assert abs(al.norm()) == ci[1], (p, "norm of alpha")
        assert S.coords(r / al) - vector(QQ, ci[0]) in ZZ ** 3, (p, "class")
        assert ci[1] == 1 or unit_residue(S, al, r), (p, "r not a unit residue")
        seen[key] = True
    # (iii) every (box, centre) inequality with 128-bit intervals
    RIF = S.RIF
    for m, d, ci, g in cert:
        b = [ci[0][j] + Integer(g[j]) for j in range(3)]
        I = [RIF(QQ(m[j]) / 2**d - b[j], QQ(m[j] + 1) / 2**d - b[j]) for j in range(3)]
        A = [sum(S.Mi[i][j] * I[j] for j in range(3)).abs().upper() for i in range(3)]
        assert RIF(A[0]) * (RIF(A[1])**2 + RIF(A[2])**2) < RIF(1) / ci[1], (p, m, d)
    S.build_lookup(cert)
    for _ in range(20):
        x=sum(random.randint(-999,999)*t**i for i in range(3))/sum(random.randint(-99,99)*t**i for i in range(3))
        qs=S.continued_fraction(x); assert evaluate_cf(qs)==x and all(q.is_integral() for q in qs)
    ok += 1
    print("ok", p, len(cert), "boxes", len(seen), "classes", flush=True)
print("verified", ok, "fields")
