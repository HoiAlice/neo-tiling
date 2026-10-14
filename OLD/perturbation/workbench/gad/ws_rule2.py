import sys; sys.path.insert(0,"."); sys.path.insert(0,"/Users/olegoleg/Code/neo-tiling/poly-hardness")
import numpy as np, cx2
from ws_rule import *
from core import weakly_solvable
def nm(q): return "s%d%s"%(q//2,"t" if q%2==0 else "b")
if __name__=="__main__":
    kind=sys.argv[1]; sw=build(kind); A,Y,conf,ks=cx2.setup(sw); S=set(conf)
    d=np.load("ws_snap_%s.npz"%kind); Qs=list(d['Qs']); pats=d['pats'].tolist()
    Yr=y_rule(sw,0.02); A2,c2=setup_with(sw,Yr); extra=set(c2)-S; print("extra conflicts",[(nm(a),nm(b),Yr[a],Yr[b]) for a,b in extra])
    for a,b in extra:
        print(" satisfied at all patterns:",all(min(Q[a,0]-Q[b,0],Q[a,1]-Q[b,1])<=1e-9 for Q in Qs))
    print("sw s_c / levels:",[(i,int(s)) for i,s in enumerate(sc(sw))][:30])
    for c in (0.011,0.02,0.05):
        for F in ("lin","conc"):
            Yr=y_rule(sw,c,F); ok=[bool(weakly_solvable(Q,Yr)) for Q in Qs]
            print(kind,"c",c,F,"ratio %.3f"%(Yr.max()/Yr.min()),"weak at all" if all(ok) else "FAIL at %s"%[tuple(p) for p,o in zip(pats,ok) if not o],flush=True)
