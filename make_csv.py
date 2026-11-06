# SPDX-License-Identifier: GPL-3.0-or-later
"""results.jsonl [+ updates.jsonl] -> CSV (one row per field, sorted by |d|).
usage: python3 make_csv.py out.csv results.jsonl [updates.jsonl ...]
status: norm-euclidean (certified N=1 cover) | NOT norm-euclidean (exact witness, denominator m)
        | could not check (N=1) (gave up, see n1_note) | open (neither).  lit_status/lit_M: Cavallar-Lemmermeyer table (|d| <= 1219), where
        E/N/H as in their paper; '' = beyond their table."""
import sys, json, csv
recs = {}
for fn in sys.argv[2:]:
    for l in open(fn):
        r = json.loads(l)
        if "error" not in r:
            recs[r["poly"]] = r                     # later files override
lit = {}
for row in csv.reader(l for l in open("data/literature_cavallar_lemmermeyer.csv") if not l.startswith("#")):
    if row[0] != "disc":
        lit.setdefault(int(row[0]), []).append(row)
cols = ["disc", "poly", "status", "N", "witness", "wit_m", "n1_level", "lit_status", "lit_M",
        "t_n1", "t_wit", "t_cover", "t_cert", "t_total", "boxes", "maxdepth", "cert"]
with open(sys.argv[1], "w", newline="") as f:
    w = csv.writer(f); w.writerow(cols)
    for r in sorted(recs.values(), key=lambda r: (-r["disc"], r["poly"])):
        st = ("norm-euclidean" if r["norm_euclid_cover"] else
              "NOT norm-euclidean" if r["witness"] else
              "could not check (N=1)" if r.get("n1_note") else "open")
        L = lit.get(r["disc"], [])
        ls = "/".join(sorted({x[1] for x in L})); lm = "/".join(x[2] for x in L)
        w.writerow([r["disc"], r["poly"], st, r["N"], r["witness"] or "",
                    r.get("wit_m", "") if r["witness"] else "", r.get("n1_level", ""), ls, lm] +
                   [round(r[k], 2) for k in ("t_n1", "t_wit", "t_cover", "t_cert", "t_total")] +
                   [r["boxes"], r["maxdepth"], r["cert"]])
print("wrote", len(recs), "rows to", sys.argv[1])
