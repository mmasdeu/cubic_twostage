# SPDX-License-Identifier: GPL-3.0-or-later
"""Merge batch4 outputs from several runs/machines into one final record per field.
usage: python3 merge_results.py out.jsonl --results r1.jsonl r2.jsonl ... --updates u1.jsonl ...
Rules: a record without "error" beats an error record; among good batch records the last one
wins; update records (resolve_hard / manual notes) override batch records, last one wins.
Then each record is checked against its certificate file: max class norm in the certificate
== N, and (N == 1) == norm_euclid_cover.  Prints missing fields and inconsistencies."""
import sys, json, pickle, os

args = sys.argv[1:]
out = args[0]
mode, res, upd = None, [], []
for a in args[1:]:
    if a in ("--results", "--updates"):
        mode = a
    elif mode == "--results":
        res.append(a)
    else:
        upd.append(a)

R = {}
for fn in res:
    for l in open(fn):
        r = json.loads(l)
        if "error" in r and r["poly"] in R and "error" not in R[r["poly"]]:
            continue
        R[r["poly"]] = r
for fn in upd:
    for l in open(fn):
        r = json.loads(l)
        R[r["poly"]] = r

F = [l.strip() for l in open("data/h1_5000.txt") if l.strip()]
missing = [f for f in F if f not in R or "error" in R[f]]
bad = []
for f in F:
    r = R.get(f)
    if r is None or "error" in r:
        continue
    if not os.path.exists(r["cert"]):
        bad.append((r["disc"], "certificate file missing", r["cert"])); continue
    pf, cert = pickle.load(open(r["cert"], "rb"))
    Nc = max(c[2][1] for c in cert)
    if pf != f or Nc != r["N"] or (Nc == 1) != r["norm_euclid_cover"] or len(cert) != r["boxes"]:
        bad.append((r["disc"], f"record N={r['N']} boxes={r['boxes']} ne={r['norm_euclid_cover']} "
                               f"vs cert N={Nc} boxes={len(cert)}", r["cert"]))
with open(out, "w") as fo:
    for f in F:
        if f in R:
            fo.write(json.dumps(R[f]) + "\n")
print(f"{len(F)} fields: {len(F) - len(missing)} with results, missing/error: {missing}")
print(f"record/certificate inconsistencies: {len(bad)}")
for b in bad:
    print("  ", b)
