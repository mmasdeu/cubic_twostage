# SPDX-License-Identifier: GPL-3.0-or-later
"""Timed pipeline over a list of complex cubic fields, 2 worker processes.
usage: python3 batch3.py fieldlist.txt results.jsonl [workers=2]
Certificates: data/certificates/cert_<|d|>_<a2>_<a1>_<a0>.pkl for x^3+a2x^2+a1x+a0
(unique even when several fields share a discriminant).
Per field phases (wall-clock seconds):
  t_n1      covering attempt with N=1 (norm-euclidean test)
  t_wit     exact non-euclidean witness search (only if N=1 fails)
  t_cover   covering search for N=2,3,... until success
  t_cert    128-bit interval certification of the final covering
"""
import sys, json, time, pickle, multiprocessing as mp

MAXDEPTH = 12
MAX_FAILED = 4000
FIELD_TIMEOUT = 2400
WIT_MMAX = 16


def run_field(f):
    from twostage import TwoStage, np
    from witness_search import witness_search
    r = {"poly": f}
    t0 = time.time()
    S = TwoStage(f)
    K = S.K
    d = int(K.discriminant())
    r["disc"] = d
    r["t_setup"] = time.time() - t0

    t = time.time()
    certs, failed = S.cover(1, T=3, maxdepth=MAXDEPTH, verbose=False,
                            max_failed=MAX_FAILED)
    r["t_n1"] = time.time() - t
    r["norm_euclid_cover"] = not failed

    r["witness"] = None
    r["t_wit"] = 0.0
    if failed:
        # exact search over x = a/m, m <= WIT_MMAX (witness_search.py)
        t = time.time()
        x, m, n = witness_search(S, mmax=WIT_MMAX)
        r["witness"] = str(x) if x is not None else None
        r["wit_m"], r["wit_n_exact"] = int(m), int(n)
        r["t_wit"] = time.time() - t

    t = time.time()
    N = 1
    while failed:
        N += 1
        certs, failed = S.cover(N, T=3, maxdepth=MAXDEPTH, verbose=False,
                                max_failed=MAX_FAILED)
    r["t_cover"] = time.time() - t
    r["N"] = N
    r["n_classes"] = len(S._cl)

    t = time.time()
    cert = S.certify(certs)
    r["t_cert"] = time.time() - t
    r["boxes"] = len(cert)
    r["maxdepth"] = max(c[1] for c in cert)
    a = [int(c) for c in reversed(K.polynomial().list()[:3])]
    r["cert"] = f"data/certificates/cert_{-d}_{a[0]}_{a[1]}_{a[2]}.pkl"
    pickle.dump((f, cert), open(r["cert"], "wb"))
    r["t_total"] = time.time() - t0
    return r


def worker(f, q):
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
