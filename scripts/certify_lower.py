# SPDX-License-Identifier: GPL-3.0-or-later
"""Rigorous re-check of the paper's witnesses and level witnesses with
cubic_twostage.certify_lower.RigorousLower (see there for the method).

usage: python3 scripts/certify_lower.py out.jsonl [workers]      (from the repository root)
Re-checks:
  (a) every ordinary witness of data/results_final_v2.jsonl (f(x) >= 1); two of them
      (d = -4872, -4952) are false and were removed in data/results_final_v3.jsonl;
  (b) every level witness of data/antz9/smooth_level_v2.jsonl that makes N_min exact
      (x covered by no centre of norm <= N-1).
"""
import os
for _v in ('OMP_NUM_THREADS', 'OPENBLAS_NUM_THREADS', 'MKL_NUM_THREADS'):
    os.environ.setdefault(_v, '1')
import sys, json, time
from cubic_twostage.certify_lower import RigorousLower

def check_field(job):
    from cubic_twostage import TwoStage
    from sage.all import QQ, sage_eval
    t0 = time.time()
    S = TwoStage(job["poly"])
    out = dict(poly=job["poly"], disc=job["disc"], kind=job["kind"], m=job["m"], L=job["L"])
    x = sage_eval(job["x"], locals={"t": S.K.gen()})
    m = job["m"]
    a = [QQ(c) * m for c in S.coords(S.K(x))]
    assert all(c in QQ and c.denominator() == 1 for c in a)
    a = [int(c) % m for c in a]
    out["a"] = a
    try:
        RL = RigorousLower(S)
    except MemoryError as e:
        if job["kind"] == "witness" and m ** 3 <= 4096:
            RL = RigorousLower(S, build_D=False)
            ok, nid = RL.uncovered_ideals(a, m)
            out.update(ok=ok, method="ideals", n_ideal_gens=nid, nD=None, loglam=RL.loglam,
                       note=str(e), t=time.time() - t0)
            return out
        out.update(ok=None, error=str(e), t=time.time() - t0)
        return out
    out.update(nD=int(len(RL.D)), loglam=RL.loglam, method="translates")
    if job["kind"] == "witness":
        ok, osz = RL.uncovered(a, m, 1)
        out.update(ok=ok, orbit=osz, nclasses=1)
        if m ** 3 <= 512:                      # independent second method
            out["ok_ideals"] = RL.uncovered_ideals(a, m)[0]
    else:
        L = job["L"]
        cl = S.classes(L)
        ok, osz_max = True, 0
        for c, n, al, r in sorted(cl, key=lambda t: t[1]):
            assert abs(al.norm()) == n
            nc = [int(ci * n) for ci in c]
            assert all(ci * n == v for ci, v in zip(c, nc))
            b = [(n * ai - m * v) % (m * n) for ai, v in zip(a, nc)]
            u, osz = RL.uncovered(b, m * n, n)
            osz_max = max(osz_max, osz)
            if not u:
                ok = False
                break
        out.update(ok=ok, orbit=osz_max, nclasses=len(cl))
    out["t"] = time.time() - t0
    return out


def jobs():
    R = [json.loads(l) for l in open("data/results_final_v2.jsonl")]
    Sm = {}
    for l in open("data/antz9/smooth_level_v2.jsonl"):
        s = json.loads(l)
        if "error" not in s:
            Sm[s["poly"]] = s
    J = []
    for r in R:
        if r.get("witness"):
            J.append(dict(poly=r["poly"], disc=r["disc"], kind="witness", x=r["witness"],
                          m=r["wit_m"], L=0))
        s = Sm.get(r["poly"])
        if s and s.get("N") == r["N"] and s.get("lw"):
            J.append(dict(poly=r["poly"], disc=r["disc"], kind="level", x=s["lw"],
                          m=s["lw_m"], L=r["N"] - 1))
    return J


if __name__ == "__main__":
    import multiprocessing as mp
    out = sys.argv[1]
    nw = int(sys.argv[2]) if len(sys.argv) > 2 else 4
    J = jobs()
    done = set()
    if os.path.exists(out):
        done = {(json.loads(l)["poly"], json.loads(l)["kind"]) for l in open(out)}
    J = [j for j in J if (j["poly"], j["kind"]) not in done]
    print(len(J), "checks", flush=True)
    with open(out, "a") as fo, mp.get_context("fork").Pool(nw) as P:
        for o in P.imap_unordered(check_field, J):
            fo.write(json.dumps(o) + "\n"); fo.flush()
            print(o["disc"], o["kind"], o.get("ok"), o.get("nD"), o.get("orbit"),
                  "%.0fs" % o["t"], o.get("error", ""), flush=True)
