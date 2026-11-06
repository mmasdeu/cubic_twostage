# SPDX-License-Identifier: GPL-3.0-or-later
"""Independent check of condition (ii) of the certificate verification: for every centre class
(r/alpha, n) used in a certificate, |Nm(alpha)| = n and r is congruent mod alpha to a unit
(+-eps^k).  Then r/alpha + g = [q1, q2] with q2 = alpha/u of norm n (Lemma lem:classes of the
write-up).  Superseded: verify_all.py now checks this too.
usage: python3 check_unit_residues.py certdir [--shard i/n]"""
import os, sys, glob, pickle
import sage.all
from twostage import TwoStage

args = sys.argv[1:]
shard = (0, 1)
if "--shard" in args:
    k = args.index("--shard"); i, n = args[k + 1].split("/"); shard = (int(i), int(n)); del args[k:k + 2]
files = sorted(glob.glob(args[0] + "/cert_*.pkl"))[shard[0]::shard[1]]
for p in files:
    f, cert = pickle.load(open(p, "rb"))
    S = TwoStage(f); K = S.K
    classes = {}
    for m, d, ci, g in cert:
        classes[(tuple(ci[0]), ci[1])] = ci
    for key, ci in classes.items():
        n = ci[1]
        al, r = K(list(ci[2].list())), K(list(ci[3].list()))
        assert abs(al.norm()) == n, (p, "norm", n)
        if n == 1:
            continue
        I = K.ideal(al)
        u, seen, ok = K(1), set(), False
        while True:
            if (r - u) in I or (r + u) in I:
                ok = True; break
            key_u = tuple(I.reduce(u).list())
            if key_u in seen:
                break
            seen.add(key_u); u = I.reduce(u * S.eps)
        assert ok, (p, "residue not a unit", n, str(r), str(al))
        assert tuple(S.coords(r / al) - __import__("sage.all").all.vector(__import__("sage.all").all.QQ, ci[0])) and \
            all(x in __import__("sage.all").all.ZZ for x in (S.coords(r / al) - __import__("sage.all").all.vector(__import__("sage.all").all.QQ, ci[0])))
    print("ok", p, len(classes), "classes", flush=True)
print("checked", len(files), "certificates")
