# SPDX-License-Identifier: GPL-3.0-or-later
"""Unconditional class numbers (PARI bnfcertify) for all complex cubic fields |d| <= B.
usage: python3 scripts/certify_h.py B workers -> data/h_certified_<B>.jsonl  {poly, disc, h, certified}"""
import os
for _v in ('OMP_NUM_THREADS', 'OPENBLAS_NUM_THREADS'):
    os.environ.setdefault(_v, '1')
import sys, json, time, multiprocessing as mp


def run(f):
    from sage.all import pari
    t = time.time()
    bnf = pari(f).bnfinit(1)               # flag 1: keep units, needed by bnfcertify
    h = int(bnf.bnf_get_no())
    ok = int(pari.bnfcertify(bnf))        # 1 iff (class group, units) proven
    return {"poly": f, "disc": int(pari(f).nfdisc()), "h": h, "certified": ok == 1, "t": time.time() - t}


if __name__ == "__main__":
    from sage.all import pari
    B, nw = int(sys.argv[1]), int(sys.argv[2])
    L = [str(pari(g).polredabs()) for g in pari(f'nflist("S3",[1,{B}],1)')]
    print(len(L), "fields", flush=True)
    with open(f"data/h_certified_{B}.jsonl", "w") as fo, mp.get_context("fork").Pool(nw) as P:
        for r in P.imap_unordered(run, L):
            fo.write(json.dumps(r) + "\n"); fo.flush()
