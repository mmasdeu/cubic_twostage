# SPDX-License-Identifier: GPL-3.0-or-later
"""Timed pipeline over a list of complex cubic fields, parallel worker processes.
usage: python3 batch4.py fieldlist.txt results.jsonl [workers=2]
Same as batch3.py but with far centres (unit orbits K, slabs L, W) and the exact orbit witness test.
Certificates: data/certificates_k/cert_<|d|>_<a2>_<a1>_<a0>.pkl for x^3+a2x^2+a1x+a0
(unique even when several fields share a discriminant).
Per field phases (wall-clock seconds):
  t_n1      covering attempts with N=1 (norm-euclidean test), see N1_LEVELS
  t_wit     exact non-euclidean witness search (orbit test), see WIT_RANGES
  t_cover   covering search for N=2,3,... until success
  t_cert    128-bit interval certification of the final covering
"""
import os
# one BLAS/OpenMP thread per worker process (otherwise 7 workers x 8 threads oversubscribe)
for _v in ('OMP_NUM_THREADS', 'OPENBLAS_NUM_THREADS', 'MKL_NUM_THREADS'):
    os.environ.setdefault(_v, '1')
import sys, json, time, pickle, multiprocessing as mp

MAXDEPTH = 14
MAX_FAILED = 4000
FIELD_TIMEOUT = int(os.environ.get("CUBIC_TIMEOUT", "2400"))
KUNIT = 2          # centres eps^k (b + g), |k| <= K   (used for N >= 2)
SLAB_L, SLAB_W = 300, 20   # plus all centres in the two slabs (see TwoStage.centres)
# N=1 attempts (K, L, W, maxdepth); after attempt i fails, witness search over m in WIT_RANGES[i]
N1_LEVELS = [(2, 300, 20, 14), (3, 3000, 60, 16)]
WIT_RANGES = [(2, 16), (17, 40)]   # fields with |d| < ~1000 were run with (17, 80)


def run_field(f):
    from twostage import TwoStage, np
    from witness_orbit import orbit_witness_search
    r = {"poly": f}
    t0 = time.time()
    S = TwoStage(f)
    K = S.K
    d = int(K.discriminant())
    r["disc"] = d
    r["t_setup"] = time.time() - t0

    # N=1 (norm-euclidean) attempts with growing far-centre sets, interleaved with the
    # exact witness search (cheap small m first): a witness proves N=1 impossible.
    r["witness"] = None
    r["t_wit"] = r["t_n1"] = 0.0
    r["n1_level"] = None
    for lev, (Ku, L, W, md) in enumerate(N1_LEVELS):
        t = time.time()
        certs, failed = S.cover(1, T=3, maxdepth=md, verbose=False,
                                max_failed=MAX_FAILED, K=Ku, L=L, W=W)
        r["t_n1"] += time.time() - t
        if not failed:
            r["n1_level"] = lev
            break
        m0, m1 = WIT_RANGES[lev]
        t = time.time()
        x, m, n = orbit_witness_search(S, mmax=m1, mmin=m0)
        r["t_wit"] += time.time() - t
        r["wit_m"] = int(m)
        if x is not None:
            r["witness"] = str(x)
            break
    r["norm_euclid_cover"] = not failed

    t = time.time()
    N = 1
    while failed:
        N += 1
        certs, failed = S.cover(N, T=3, maxdepth=MAXDEPTH, verbose=False,
                                max_failed=MAX_FAILED, K=KUNIT, L=SLAB_L, W=SLAB_W)
    r["t_cover"] = time.time() - t
    r["N"] = N
    r["n_classes"] = len(S._cl)
    r["K"], r["L"], r["W"] = KUNIT, SLAB_L, SLAB_W

    t = time.time()
    cert = S.certify(certs)
    r["t_cert"] = time.time() - t
    r["boxes"] = len(cert)
    r["maxdepth"] = max(c[1] for c in cert)
    a = [int(c) for c in reversed(K.polynomial().list()[:3])]
    r["cert"] = f"data/certificates_k/cert_{-d}_{a[0]}_{a[1]}_{a[2]}.pkl"
    pickle.dump((f, cert), open(r["cert"], "wb"))
    r["t_total"] = time.time() - t0
    return r


MEM_GB = float(os.environ.get("CUBIC_MEM_GB", "0"))   # per-worker address-space cap (0 = none)


def worker(f, q):
    if MEM_GB > 0:
        import resource
        lim = int(MEM_GB * 2 ** 30)
        resource.setrlimit(resource.RLIMIT_AS, (lim, lim))
    try:
        q.put(run_field(f))
    except Exception as e:
        q.put({"poly": f, "error": repr(e)})


if __name__ == "__main__":
    fields = [l.strip() for l in open(sys.argv[1]) if l.strip()]
    out = open(sys.argv[2], "a")
    done = set()
    try:
        for l in open(sys.argv[2]):
            done.add(json.loads(l)["poly"])
    except Exception:
        pass
    todo = [f for f in fields if f not in done]
    nworkers = int(sys.argv[3]) if len(sys.argv) > 3 else 2
    ctx = mp.get_context("fork")
    running = []
    while todo or running:
        while todo and len(running) < nworkers:
            f = todo.pop(0)
            q = ctx.Queue()
            p = ctx.Process(target=worker, args=(f, q))
            p.start()
            running.append((f, p, q, time.time()))
        time.sleep(0.5)
        for item in list(running):
            f, p, q, ts = item
            res = None
            if not q.empty():
                res = q.get()
                p.join()
            elif time.time() - ts > FIELD_TIMEOUT:
                p.kill()
                res = {"poly": f, "error": f"timeout {FIELD_TIMEOUT}s"}
            elif not p.is_alive() and q.empty():
                res = {"poly": f, "error": "crashed"}
            if res is not None:
                out.write(json.dumps(res) + "\n")
                out.flush()
                running.remove(item)
