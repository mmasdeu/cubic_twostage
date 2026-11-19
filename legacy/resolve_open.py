# SPDX-License-Identifier: GPL-3.0-or-later
"""Exact witness search with large denominators for the fields left 'open'
(N=1 covering failed, no witness with m <= 16), using witness_orbit.py.
usage: python3 resolve_open.py results.jsonl [results2.jsonl ...] -- out.jsonl [mmax=80] [workers=2]
Reads every field with norm_euclid_cover false and no witness; appends/resumes out.jsonl
with {"poly", "disc", "witness", "m", "n_prim", "t"}  (witness null = none with m <= mmax)."""
import os
# one BLAS/OpenMP thread per worker process (otherwise 7 workers x 8 threads oversubscribe)
for _v in ('OMP_NUM_THREADS', 'OPENBLAS_NUM_THREADS', 'MKL_NUM_THREADS'):
    os.environ.setdefault(_v, '1')
import sys, json, time, multiprocessing as mp


def run(args):
    f, mmax = args
    from twostage import TwoStage
    from witness_orbit import orbit_witness_search
    t = time.time()
    S = TwoStage(f)
    x, m, n = orbit_witness_search(S, mmax=mmax, mmin=2)
    return {"poly": f, "disc": int(S.K.discriminant()), "witness": str(x) if x is not None else None,
            "m": int(m), "n_prim": int(n), "mmax": mmax, "t": time.time() - t}


if __name__ == "__main__":
    k = sys.argv.index("--")
    ins, out = sys.argv[1:k], sys.argv[k + 1]
    mmax = int(sys.argv[k + 2]) if len(sys.argv) > k + 2 else 80
    nw = int(sys.argv[k + 3]) if len(sys.argv) > k + 3 else 2
    wit = {}
    try:
        for l in open("data/wit_final.jsonl"):
            r = json.loads(l); wit[r["poly"]] = r["witness"]
    except FileNotFoundError:
        pass
    todo = []
    for fn in ins:
        for l in open(fn):
            r = json.loads(l)
            if r.get("error") or r["norm_euclid_cover"]:
                continue
            w = r["witness"] if "wit_m" in r else wit.get(r["poly"], r.get("witness"))
            if w is None:
                todo.append(r["poly"])
    done = set()
    try:
        done = {json.loads(l)["poly"] for l in open(out)}
    except FileNotFoundError:
        pass
    todo = [f for f in todo if f not in done]
    print(len(todo), "fields to do", flush=True)
    with open(out, "a") as fo, mp.get_context("fork").Pool(nw) as P:
        for r in P.imap_unordered(run, [(f, mmax) for f in todo]):
            fo.write(json.dumps(r) + "\n"); fo.flush()
            print(r["disc"], r["m"] if r["witness"] else f"none<= {mmax}", f'{r["t"]:.0f}s', flush=True)
