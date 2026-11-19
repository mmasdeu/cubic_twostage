# SPDX-License-Identifier: GPL-3.0-or-later
"""Smooth level N_min: exactness per field and its relation to small ideal norms / splitting.
usage: python3 scripts/analyze_smooth.py results_final.jsonl smooth.jsonl [out.csv]
N is the certified covering level (upper bound for N_min).  It is exact if
  - N = 1, or
  - smooth.jsonl has a level-(N-1) witness (a point covered by no centre of norm <= N-1), or
  - the field has an ordinary witness (not norm-euclidean) and no ideal has norm in (1, N)
    (then the centres of norm <= N-1 are just those of norm 1).
Writes per-field rows (disc, poly, N, exact, reason, splitting of 2,3,5,7, ideal norms) to out.csv."""
import sys, json, csv, collections
from sage.all import NumberField, PolynomialRing, QQ

res, smooth = sys.argv[1:3]
outcsv = sys.argv[3] if len(sys.argv) > 3 else None
R = {json.loads(l)["poly"]: json.loads(l) for l in open(res)}
S = {}
for l in open(smooth):
    s = json.loads(l)
    if "error" not in s:
        S[s["poly"]] = s
P = PolynomialRing(QQ, "x")


def ftype(K, p):
    F = K.ideal(p).factor()
    return "".join(sorted(str(Q.residue_class_degree()) + ("^%d" % e if e > 1 else "") for Q, e in F))


rows = []
for p, r in R.items():
    K = NumberField(P(p), "t")
    N = r["N"]
    norms = sorted(n for n, I in K.ideals_of_bdd_norm(max(64, N)).items() if I and n > 1)
    s = S.get(p)
    reason = ""
    if N == 1:
        reason = "N=1"
    elif s is not None and s.get("N") == N and s.get("lw"):
        reason = f"level-{N-1} witness m={s['lw_m']}"
    elif r.get("witness") and not any(1 < n < N for n in norms):
        reason = "ordinary witness, no ideal norm in (1,N)"
    consistent = None if s is None or s.get("N") != N else s["consistent"]
    rows.append(dict(disc=r["disc"], poly=p, N=N, exact=bool(reason), reason=reason,
                     consistent=consistent, k=(norms.index(N) + 1 if N in norms else 0),
                     s2=ftype(K, 2), s3=ftype(K, 3), s5=ftype(K, 5), s7=ftype(K, 7),
                     norms=" ".join(map(str, norms[:8]))))
rows.sort(key=lambda t: -t["disc"])
ex = [t for t in rows if t["exact"]]
print(f"{len(rows)} fields; N exact for {len(ex)}; consistency checked for "
      f"{sum(t['consistent'] is not None for t in rows)}, failures: "
      f"{[t['disc'] for t in rows if t['consistent'] is False]}")
print("exactness reasons:", collections.Counter(t["reason"].split(" m=")[0] for t in ex))
ex2 = [t for t in ex if t["N"] >= 2]
print("exact N_min >= 2: N_min is the k-th smallest ideal norm > 1:",
      sorted(collections.Counter(t["k"] for t in ex2).items()))
print("splitting of 2 -> N_min (exact, N_min >= 2):")
by2 = collections.defaultdict(list)
for t in ex2:
    by2[t["s2"]].append(t["N"])
for k, v in sorted(by2.items()):
    print(f"  2 = {k:6s} n={len(v):3d}  {sorted(collections.Counter(v).items())}")
by23 = collections.defaultdict(list)
for t in ex2:
    by23[(t["s2"], t["s3"])].append(t["N"])
print("(2, 3) splitting -> N_min:")
for k, v in sorted(by23.items(), key=lambda kv: -len(kv[1])):
    print(f"  {str(k):16s} n={len(v):3d}  {sorted(collections.Counter(v).items())}")
print("N distribution (all, upper bounds):", sorted(collections.Counter(t["N"] for t in rows).items()))
if outcsv:
    with open(outcsv, "w", newline="") as f:
        w = csv.DictWriter(f, fieldnames=list(rows[0].keys()))
        w.writeheader(); w.writerows(rows)
    print("wrote", outcsv)
