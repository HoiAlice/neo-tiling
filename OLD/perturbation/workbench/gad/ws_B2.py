"""Rule variants with snapping. key per class: mean/min/max of s=x+y of members (point or switch-centre). z_0=-c*key_0, z_k=min(-c*key_k, z_{k-1}-m)."""
import sys; sys.path.insert(0,"."); sys.path.insert(0,"/Users/olegoleg/Code/neo-tiling/poly-hardness")
import numpy as np
from core import weakly_solvable
from ws_p9g import snap
def snapped(Qs): return [np.exp(snap(np.log(Q),1e-5)) for Q in Qs]
def rule(Y,A,c,m,how):
    s=A.sum(1); sc=(s[0::2]+s[1::2])/2
    levels=sorted(set(np.round(Y,9)),reverse=True); cls=[[i for i in range(len(Y)) if round(Y[i],9)==l] for l in levels]
    def key(cl):
        v=sc[[i//2 for i in cl]] if how.endswith("c") else s[cl]
        return {"mean":v.mean(),"min":v.min(),"max":v.max()}[how[:-1] if how[:-1]=="mean" else how[:3]]
    z=[]
    for k,cl in enumerate(cls):
        r=-c*key(cl); z.append(r if k==0 else min(r,z[-1]-m))
    z=np.array(z); z=(z-z.min())/(z.max()-z.min()); e=np.zeros(len(Y))
    for k,cl in enumerate(cls): e[cl]=z[k]
    return e
if __name__=="__main__":
    inst=sys.argv[1]
    if inst=="cp":
        d=np.load("cprime_yfound.npz"); Qs=snapped(d['Qs']); A=np.load("cprime_Q_1010.npz")['A']; Y=d['Y']
    else:
        d=np.load("ws_k3.npz"); Qs=snapped(d['Qs']); A=d['A']; Y=d['Y']
    for how in ["meanp","minp","maxp","meanc","minc","maxc"]:
        good=[]
        for c in [0.1,0.3,1,3]:
            for m in [0.003,0.01,0.03,0.1]:
                e=rule(Y,A,c,m,how)
                if all(weakly_solvable(Q,1+0.1*e) for Q in Qs): good.append((c,m))
        print(inst,how,"passing (c,m):",good,flush=True)
