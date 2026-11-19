# SPDX-License-Identifier: GPL-3.0-or-later
"""Extra N=1 covering attempts (larger far-centre sets, deeper boxes) for fields that batch4
left undecided (no N=1 cover, no witness).  On success, certifies and writes an N=1
certificate (replacing the batch4 one) and an updated record.
usage: python3 scripts/resolve_hard.py results.jsonl updates.jsonl [workers=2] [K:L:W:depth ...]
Merge: records in updates.jsonl override those in results.jsonl (same poly)."""
import os
# one BLAS/OpenMP thread per worker process (otherwise 7 workers x 8 threads oversubscribe)
for _v in ('OMP_NUM_THREADS', 'OPENBLAS_NUM_THREADS', 'MKL_NUM_THREADS'):
    os.environ.setdefault(_v, '1')
import sys, json, time, pickle, multiprocessing as mp

LEVELS = [(4, 20000, 150, 20)]


def run(args):
    r, levels = args
    from cubic_twostage import TwoStage
    S = TwoStage(r["poly"])
    r = dict(r)
    t0 = time.time()
    for Ku, L, W, md in levels:
        t = time.time()
        certs, failed = S.cover(1, T=3, maxdepth=md, verbose=False, max_failed=4000, K=Ku, L=L, W=W)
        r["t_n1"] += time.time() - t
        if not failed:
            t = time.time()
            cert = S.certify(certs)
            r.update({"norm_euclid_cover": True, "n1_level": f"{Ku}:{L}:{W}:{md}", "N": 1,
                      "n_classes": 1, "K": Ku, "L": L, "W": W,
                      "t_cert": time.time() - t, "boxes": len(cert),
                      "maxdepth": max(c[1] for c in cert)})
            pickle.dump((r["poly"], cert), open(r["cert"], "wb"))
            break
    # t_total = batch4 time (incl. the superseded N>1 cover) + time spent here
    r["t_extra"] = time.time() - t0
    r["t_total"] += r["t_extra"]
    return r


if __name__ == "__main__":
    R = [json.loads(l) for l in open(sys.argv[1])]
    nw = int(sys.argv[3]) if len(sys.argv) > 3 else 2
    levels = [tuple(map(int, a.split(":"))) for a in sys.argv[4:]] or LEVELS
    todo = [r for r in R if "error" not in r and not r["norm_euclid_cover"] and r["witness"] is None]
    print(len(todo), "undecided fields", flush=True)
    with open(sys.argv[2], "a") as fo, mp.get_context("fork").Pool(nw) as P:
        for r in P.imap_unordered(run, [(r, levels) for r in todo]):
            fo.write(json.dumps(r) + "\n"); fo.flush()
            print(r["disc"], "N=1 covered" if r["norm_euclid_cover"] else "still undecided", flush=True)
