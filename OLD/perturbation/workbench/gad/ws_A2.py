"""A (all patterns): joint strict feasibility (t>0), else deletion filter for a minimal infeasible pattern set; also per-pattern t."""
import sys; sys.path.insert(0,"."); sys.path.insert(0,"/Users/olegoleg/Code/neo-tiling/poly-hardness")
import numpy as np
from ws_gap import solve
f=sys.argv[1]; d=np.load(f); Qs=list(d['Qs']); Y=d['Y']; pats=d['pats']; cost=d['cost']
def tval(S):
    r=solve([Qs[i] for i in S],Y); return 0.0 if r is None else r[2]/1e-3
print("excess cost",dict(zip(map(tuple,pats.tolist()),np.round(cost-cost.min(),4))))
print("per pattern t",[round(tval([i]),4) for i in range(len(Qs))],flush=True)
allt=tval(list(range(len(Qs)))); print("ALL patterns joint t =",allt,flush=True)
if allt<1e-6:
    keep=list(range(len(Qs)))
    for i in range(len(Qs)):
        tr=[j for j in keep if j!=i]
        if tr and tval(tr)<1e-6: keep=tr
    print("minimal strictly-infeasible pattern set",[tuple(pats[j].tolist()) for j in keep],"costs",[round(cost[j]-cost.min(),4) for j in keep])
