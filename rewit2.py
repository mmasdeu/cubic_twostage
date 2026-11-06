# SPDX-License-Identifier: GPL-3.0-or-later
import json, time
from twostage import TwoStage
from witness_search import witness_search
R=[json.loads(l) for l in open('data/results_1500.jsonl')]
out=open('data/wit_final.jsonl','w')
for r in R:
    if r['norm_euclid_cover']: continue
    S=TwoStage(r['poly']); t=time.time()
    x,m,n=witness_search(S, mmax=16)
    out.write(json.dumps({"poly":r['poly'],"witness":str(x) if x is not None else None,"m":m,"n_exact":n,"t_wit":time.time()-t})+"\n"); out.flush()
