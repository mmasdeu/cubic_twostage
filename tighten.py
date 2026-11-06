# SPDX-License-Identifier: GPL-3.0-or-later
"""Try to lower the certified covering level N for fields where N is not known to be minimal.
For each such field, try the ideal norms N' < N (largest first) with a stronger search
(far centres K, L, W, deeper boxes); on success certify, write the certificate (replacing the
old one) and an updated record; stop at the first N' that fails.
usage: python3 tighten.py results_final.jsonl smooth.jsonl updates_out.jsonl [workers]
env: CUBIC_MEM_GB (per-worker address-space cap), TIGHT_LEVEL="K:L:W:depth" (default 3:3000:60:16)"""
import os
for _v in ('OMP_NUM_THREADS', 'OPENBLAS_NUM_THREADS', 'MKL_NUM_THREADS'):
    os.environ.setdefault(_v, '1')
import sys, json, time, pickle, multiprocessing as mp

LEVEL = tuple(int(x) for x in os.environ.get("TIGHT_LEVEL", "3:3000:60:16").split(":"))


def init_worker():
    mem = float(os.environ.get("CUBIC_MEM_GB", "0"))
    if mem > 0:
        import resource
        lim = int(mem * 2 ** 30)
        resource.setrlimit(resource.RLIMIT_AS, (lim, lim))


def run(r):
    from twostage import TwoStage
    t0 = time.time()
    S = TwoStage(r["poly"])
    norms = sorted(n for n, I in S.K.ideals_of_bdd_norm(r["N"] - 1).items() if I)
    Ku, L, W, md = LEVEL
    out = dict(r)
    tried = []
    best = None
    for Np in reversed(norms):
        if Np < 2:
            break
        certs, failed = S.cover(Np, 3, md, verbose=False, max_failed=4000, K=Ku, L=L, W=W)
        tried.append(Np)
        if failed:
            break
        best = (Np, S.certify(certs))
    if best is not None:
        Np, cert = best
        pickle.dump((r["poly"], cert), open(r["cert"], "wb"))
        out.update({"N": Np, "boxes": len(cert), "maxdepth": max(c[1] for c in cert),
                    "n_classes": len(S.classes(Np)), "K": Ku, "L": L, "W": W,
                    "tightened_from": r["N"]})
    out["tighten_tried"] = tried
    out["t_tighten"] = time.time() - t0
    return out


def safe_run(r):
    try:
        return run(r)
    except Exception as e:
        return {"poly": r["poly"], "disc": r["disc"], "tighten_error": repr(e)}


if __name__ == "__main__":
    res, smooth, outfn = sys.argv[1:4]
    nw = int(sys.argv[4]) if len(sys.argv) > 4 else 4
    R = {json.loads(l)["poly"]: json.loads(l) for l in open(res)}
    S = {}
    for l in open(smooth):
        s = json.loads(l)
        if "error" not in s:
            S[s["poly"]] = s
    todo = []
    for p, r in R.items():
        s = S.get(p)
        exact = r["N"] == 1 or (s is not None and s["N_exact"] and s["N"] == r["N"]) or \
            (r["N"] == 2 and r.get("witness") is not None)
        if not exact:
            todo.append(r)
    done = set()
    if os.path.exists(outfn):
        done = {json.loads(l)["poly"] for l in open(outfn)}
    todo = sorted((r for r in todo if r["poly"] not in done), key=lambda r: -r["disc"])
    print(len(todo), "fields to tighten, level", LEVEL, flush=True)
    with open(outfn, "a") as fo, mp.get_context("fork").Pool(nw, initializer=init_worker) as P:
        for o in P.imap_unordered(safe_run, todo):
            fo.write(json.dumps(o) + "\n"); fo.flush()
            if "tighten_error" in o:
                print(o["disc"], "ERROR", o["tighten_error"], flush=True)
            else:
                print(o["disc"], "N", o.get("tightened_from", o["N"]), "->", o["N"], "tried", o["tighten_tried"], flush=True)
