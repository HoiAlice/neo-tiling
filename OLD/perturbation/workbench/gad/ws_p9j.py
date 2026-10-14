import sys; sys.path.insert(0,".")
from ws_p9b import *
from ws_gap import solve
from ws_p9g import snap
from core import polish_margin
d=np.load("ws_ser.npz"); conf_l=[tuple(c) for c in d['conf'].tolist()]
Qs=[]; names=[]
for i,p in enumerate(d['pats'].tolist()):
    cm,u=polish_margin(A,conf_l,[int(s) for s in d['sigma'][i]],1e-8); Qs.append(np.exp(snap(u,1e-5))); names.append(tuple(p))
sat=np.load("cprime_yfound.npz")['Qs']
for k,Q in enumerate(sat):
    Ls=snap(np.log(Q),1e-5); print("sat",k,"snapped feasible",feas(Ls)); Qs.append(np.exp(Ls)); names.append(("sat",k))
for sub,lab in [(range(4),"unsat four"),(range(8),"all 8")]:
    r=solve([Qs[i] for i in sub],Y)
    print(lab,"joint t =",None if r is None else round(r[2]/1e-3,4),flush=True)
    if r:
        levels,z,t=r; lev=[levels.index(round(v,9)) for v in Y]; eta=np.array([(z[l]-z.min())/(z.max()-z.min()) for l in lev])
        for eps in (1e-2,0.1,0.3): print("  eps",eps,[bool(weakly_solvable(Q,1+eps*eta)) for Q in Qs],flush=True)
