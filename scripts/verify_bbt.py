# SPDX-License-Identifier: GPL-3.0-or-later
"""Re-verify, with our own rigorous test (certify_lower.py), the non-norm-Euclidean certificates
of Bagger-Booker-Trudgian (arXiv:2610.38073, data: github.com/arbooker/complex-cubic,
results/certificates.txt, SHA-256 67e9f2cc...328d, copied to data/bbt/certificates.txt)
for the fields of our list.

A certificate (alpha, beta) asserts m(alpha + beta O) >= |N beta|, i.e. f(alpha/beta) >= 1.
We map alpha, beta into our model of the field (any field isomorphism), write
x = alpha/beta = a/m with m the least positive integer with m x in O, and decide f(x) >= 1
with the translate test (or the ideal test when the translate set is too large and m^3 is small).

usage: python3 scripts/verify_bbt.py out.jsonl [workers]"""
import os
for _v in ('OMP_NUM_THREADS', 'OPENBLAS_NUM_THREADS', 'MKL_NUM_THREADS'):
    os.environ.setdefault(_v, '1')
import sys, json, time


def parse(line):
    disc, poly, den, B, E, cert = [s.strip() for s in line.split("|")]
    return dict(disc=int(disc), poly=[int(c) for c in poly.split(",")], den=int(den),
                B=[int(c) for c in B.split(",")], E=[int(c) for c in E.split(",")],
                cert=cert.split())


def run(job):
    from sage.all import QQ, ZZ, PolynomialRing, NumberField, lcm
    from cubic_twostage import TwoStage
    from cubic_twostage.certify_lower import RigorousLower
    t0 = time.time()
    rec, c = job["poly"], job["bbt"]
    out = dict(poly=rec, disc=c["disc"], kind=c["cert"][0])
    S = TwoStage(rec)
    P = PolynomialRing(QQ, "s")
    Kp = NumberField(P(c["poly"]), "s")
    s = Kp.gen()
    om = [sum(QQ(c["B"][3 * j + k]) * s ** k for k in range(3)) / c["den"] for j in range(3)]
    assert all(w.is_integral() for w in om)
    assert abs(Kp.discriminant()) == abs(S.K.discriminant()) == -c["disc"]
    eps = sum(e * w for e, w in zip(c["E"], om))
    assert eps.is_unit()
    if c["cert"][0] == "b":
        Bc, tc = c["cert"][1:4], c["cert"][4:7]
        beta = sum(int(b) * w for b, w in zip(Bc, om))
    else:
        n, tc = int(c["cert"][1]), c["cert"][2:5]
        beta = eps ** n - 1
    alpha = sum(int(t) * w for t, w in zip(tc, om))
    phi = Kp.embeddings(S.K)[0]
    x = phi(alpha) / phi(beta)
    co = S.coords(x)
    m = int(lcm([q.denominator() for q in co]))
    a = [int(q * m) % m for q in co]
    out.update(m=m, a=a if m < 10 ** 15 else None)
    if m == 1:
        out.update(ok=False, note="x integral")
        return out
    try:
        if m >= 2 ** 20:
            raise MemoryError("modulus too large for the translate test")
        RL = RigorousLower(S)
        ok, osz = RL.uncovered(a, m, 1)
        out.update(ok=ok, method="translates", nD=int(len(RL.D)), orbit=osz)
    except MemoryError as e:
        if m ** 3 <= 4096:
            RL = RigorousLower(S, build_D=False)
            ok, nid = RL.uncovered_ideals(a, m)
            out.update(ok=ok, method="ideals", n_ideal_gens=nid)
        else:
            out.update(ok=None, error=str(e))
    out["t"] = time.time() - t0
    return out


if __name__ == "__main__":
    import multiprocessing as mp
    from sage.all import PolynomialRing, QQ, NumberField
    outf = sys.argv[1]
    nw = int(sys.argv[2]) if len(sys.argv) > 2 else 4
    C = {}
    for l in open("data/bbt/certificates.txt"):
        if l.strip() and not l.startswith("#"):
            c = parse(l)
            if c["disc"] >= -5000:
                C.setdefault(c["disc"], []).append(c)
    R = [json.loads(l) for l in open("data/results_final_v3.jsonl")]
    P = PolynomialRing(QQ, "x")
    jobs = []
    for r in R:
        if r["norm_euclid_cover"]:
            continue
        cands = C.get(r["disc"], [])
        K = NumberField(P(r["poly"]), "t")
        match = [c for c in cands if K.is_isomorphic(NumberField(P(c["poly"]), "s"))]
        if len(match) != 1:
            print("no unique certificate for", r["disc"], r["poly"], len(match), flush=True)
            continue
        jobs.append(dict(poly=r["poly"], bbt=match[0]))
    print(len(jobs), "fields", flush=True)
    with open(outf, "w") as fo, mp.get_context("fork").Pool(nw) as Pool:
        for o in Pool.imap_unordered(run, jobs):
            fo.write(json.dumps(o) + "\n"); fo.flush()
            print(o["disc"], o["kind"], o.get("m"), o.get("ok"), o.get("method"),
                  o.get("error", ""), flush=True)
