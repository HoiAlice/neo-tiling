import sys; sys.path.insert(0,"."); sys.path.insert(0,"/Users/olegoleg/Code/neo-tiling/poly-hardness")
import numpy as np
from ws_rule import *
from core import weakly_solvable
def y_pw(sw,c1,c2,sstar,gap=g,base=1.0):
    s=sc(sw); smax=s.max()
    # F(s)=base+ integral of slope from s to smax; slope c1 for s<=sstar, c2 for s>sstar
    def F(v): 
        hi=max(0,smax-max(v,sstar)); lo=max(0,min(smax,sstar)-v) if v<sstar else 0
        return base+c2*hi+c1*(max(0,sstar-v) if v<sstar else 0)
    y=[]
    for v in s: b=F(v); y+=[b+gap,b]
    return np.array(y)
if __name__=="__main__":
    kind=sys.argv[1]; sw=build(kind); d=np.load("ws_snap_%s.npz"%kind); Qs=list(d['Qs']); pats=d['pats'].tolist()
    for sstar in (4,6,2):
        for c1 in (0.02,0.03):
            for c2 in (0.03,0.05,0.08,0.12):
                y=y_pw(sw,c1,c2,sstar); ok=[bool(weakly_solvable(Q,y)) for Q in Qs]
                print(kind,"s*",sstar,"c1",c1,"c2",c2,"ratio %.2f"%(y.max()/y.min()),"PASS all" if all(ok) else "fail %d/%d"%(len(ok)-sum(ok),len(ok)),flush=True)
