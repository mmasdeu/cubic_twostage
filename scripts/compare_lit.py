# SPDX-License-Identifier: GPL-3.0-or-later
"""Compare our norm-euclidean results with Cavallar-Lemmermeyer's table (|d| <= 1219)
and the completeness theorem of Bagger-Booker-Trudgian (arXiv:2610.38073: the 58 'E' fields
are the only norm-euclidean complex cubic fields).
usage: python3 scripts/compare_lit.py results.jsonl"""
import sys, json, csv
R = [json.loads(l) for l in open(sys.argv[1])]
R = [r for r in R if "error" not in r]
lit = {}
for row in csv.reader(l for l in open("data/literature_cavallar_lemmermeyer.csv") if not l.startswith("#")):
    if row[0] == "disc": continue
    lit.setdefault(int(row[0]), []).append((row[1], row[2]))
E58 = {d for d, v in lit.items() if any(s == "E" for s, _ in v)}
assert len(E58) == 58
agree, conflict, undecided = 0, [], []
for r in R:
    d = r["disc"]
    ours = "E" if r["norm_euclid_cover"] else ("N" if r["witness"] else "?")
    truth = "E" if d in E58 else "N"          # completeness theorem (h=1 fields only)
    if ours == "?":
        undecided.append((d, truth, lit.get(d, [("", "")])[0][1]))
    elif ours == truth:
        agree += 1
    else:
        conflict.append((d, ours, truth))
print(f"{len(R)} fields: {agree} agree with literature, {len(conflict)} CONFLICTS, {len(undecided)} undecided by us")
print("conflicts:", conflict)
print("undecided (disc, literature status, literature M):", undecided)
missing = sorted(E58 - {r["disc"] for r in R}, reverse=True)
print("E58 fields not in results:", missing)
