# SPDX-License-Identifier: GPL-3.0-or-later
import json, sys, time, glob
from twostage import TwoStage
from witness_search import witness_search
R = [json.loads(l) for l in open('results_1500.jsonl')]
lo, hi = int(sys.argv[1]), int(sys.argv[2])
done = {json.loads(l)['poly'] for f in glob.glob('wit_*.jsonl') for l in open(f)}
out = open(f'wit_{lo}_{hi}.jsonl', 'w')
for r in R[lo:hi]:
    if r['norm_euclid_cover'] or r['poly'] in done:
        continue
    S = TwoStage(r['poly'])
    t = time.time()
    x, m, n = witness_search(S)
    out.write(json.dumps({"poly": r['poly'],
                          "witness2": str(x) if x is not None else None,
                          "m": m, "n_exact": n,
                          "t_wit2": time.time() - t}) + "\n")
    out.flush()
