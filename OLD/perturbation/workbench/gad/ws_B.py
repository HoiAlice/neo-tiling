"""B: explicit level schedule. classes = distinct levels of Y (order from the gadget design). raw r_k=-c*mean_s(class); z_0=r_0, z_k=min(r_k, z_{k-1}-m).
eta = normalised z; y=1+eps*eta. Grid over (c,m); test at all patterns."""
import sys; sys.path.insert(0,"."); sys.path.insert(0,"/Users/olegoleg/Code/neo-tiling/poly-hardness")
import numpy as np
from core import weakly_solvable
f=sys.argv[1]; d=np.load(f); Qs=list(d['Qs']); Y=d['Y']; A=d['A']; s=A.sum(1)
levels=sorted(set(np.round(Y,9)),reverse=True); cls=[[i for i in range(len(Y)) if round(Y[i],9)==l] for l in levels]
ms=[s[c].mean() for c in cls]
print("classes",len(cls),"s spread inside classes (max)",round(max(s[c].max()-s[c].min() for c in cls),2))
def eta_rule(c,m):
    z=[]
    for k in range(len(cls)):
        r=-c*ms[k]; z.append(r if k==0 else min(r,z[-1]-m))
    z=np.array(z); z=(z-z.min())/(z.max()-z.min()); e=np.zeros(len(Y))
    for k,cl in enumerate(cls): e[cl]=z[k]
    return e
res=[]
for c in [0,0.03,0.1,0.3,1,3]:
    for m in [0.01,0.03,0.1,0.3,1]:
        e=eta_rule(c,m); ok=[all(weakly_solvable(Q,1+eps*e) for Q in Qs) for eps in (1e-3,0.1)]
        res.append((c,m,ok)); print("c",c,"m",m,"eps 1e-3/0.1 all patterns:",ok,flush=True)
