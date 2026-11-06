# SPDX-License-Identifier: GPL-3.0-or-later
"""Lower bounds for the smooth level (2-stage): for each field with certified covering level N,
search an exact point x = a/m covered by no centre of norm <= N-1 (witness_orbit.level_witness_search).
Found => N_min = N exactly.  Also re-checks consistency: no point may escape all centres of norm <= N.
usage: python3 smooth_level.py out.jsonl results.jsonl [updates.jsonl ...] [--mmax 24] [--workers 4]"""
import os
for _v in ('OMP_NUM_THREADS', 'OPENBLAS_NUM_THREADS', 'MKL_NUM_THREADS'):
    os.environ.setdefault(_v, '1')
import sys, json, time, multiprocessing as mp

MCHECK = 10        # consistency check range for level N


def init_worker():
    mem = float(os.environ.get("CUBIC_MEM_GB", "0"))
    if mem > 0:
        import resource
        lim = int(mem * 2 ** 30)
        resource.setrlimit(resource.RLIMIT_AS, (lim, lim))


def run(args):
    r, mmax = args
    from twostage import TwoStage
    from witness_orbit import level_witness_search
    t = time.time()
    S = TwoStage(r["poly"])
    N = r["N"]
    xc, _, _ = level_witness_search(S, N, mmax=MCHECK)
    out = {"poly": r["poly"], "disc": r["disc"], "N": N, "consistent": xc is None,
           "lw": None, "lw_m": None, "lw_npts": 0, "lw_mmax": mmax}
    if N >= 2:
        x, m, k = level_witness_search(S, N - 1, mmax=mmax)
        if x is not None:
            out.update({"lw": str(x), "lw_m": int(m), "lw_npts": int(k)})
    # N = 2 is also exact when batch4 found an ordinary (level-1) witness
    out["N_exact"] = (N == 1) or out["lw"] is not None or (N == 2 and r.get("witness") is not None)
    out["t"] = time.time() - t
    return out


def safe_run(args):
    try:
        return run(args)
    except Exception as e:
        return {"poly": args[0]["poly"], "disc": args[0]["disc"], "error": repr(e)}


if __name__ == "__main__":
    args = sys.argv[1:]
    mmax = int(args[args.index("--mmax") + 1]) if "--mmax" in args else 24
    nw = int(args[args.index("--workers") + 1]) if "--workers" in args else 4
    files = [a for a in args if not a.startswith("--") and not a.isdigit()]
    out, ins = files[0], files[1:]
    R = {}
    for fn in ins:
        for l in open(fn):
            r = json.loads(l)
            if "error" not in r:
                R[r["poly"]] = r
    done = set()
    if os.path.exists(out):
        done = {json.loads(l)["poly"] for l in open(out)}
    todo = sorted((r for p, r in R.items() if p not in done), key=lambda r: -r["disc"])
    print(len(todo), "fields", flush=True)
    with open(out, "a") as fo, mp.get_context("fork").Pool(nw, initializer=init_worker) as P:
        for o in P.imap_unordered(safe_run, [(r, mmax) for r in todo]):
            fo.write(json.dumps(o) + "\n"); fo.flush()
            if "error" in o:
                print(o["disc"], "ERROR", o["error"], flush=True); continue
            print(o["disc"], "N=%d" % o["N"], "exact" if o["N_exact"] else "upper bound",
                  "" if o["consistent"] else "INCONSISTENT!", "%.0fs" % o["t"], flush=True)
