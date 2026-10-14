"""Deletion filter: minimal point subset on which y=1+eps*eta (eta from sys.argv mode) is already not weakly solvable at Q (necessary => obstruction for the full layout)."""
import sys; sys.path.insert(0,"."); sys.path.insert(0,"/Users/olegoleg/Code/neo-tiling/poly-hardness")
import numpy as np
from core import weakly_solvable
def sub_ok(Q,y,keep): return weakly_solvable(Q[keep],y[keep])
def minimal(Q,y):
    keep=list(range(len(y)))
    assert not sub_ok(Q,y,keep)
    for i in range(len(y)):
        tr=[j for j in keep if j!=i]
        if not sub_ok(Q,y,tr): keep=tr
    return keep
def name(q): return ("s%d"%(q//2))+("t" if q%2==0 else "b")
if __name__=="__main__":
    d=np.load(sys.argv[1]); Y=d['Y']; lv=sorted(set(np.round(Y,9))); rank=np.array([lv.index(round(v,9)) for v in Y],float)
    y=1+1e-3*rank/rank.max()
    for k,Q in enumerate(d['Qs'][:int(sys.argv[2])]):
        m=minimal(Q,y); print("pattern",k,"minimal obstruction",[(name(q),int(rank[q])) for q in m],flush=True)
