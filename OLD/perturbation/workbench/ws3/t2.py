from common import *
sw=build("cp"); d=np.load("/Users/olegoleg/Code/neo-tiling/perturbation/workbench/gad/ws_snap_cp.npz"); Qs=list(d['Qs']); pats=d['pats'].tolist()
y,gaps=kinked_y(sw,[4])
res=[]
for p,Q in zip(pats,Qs):
    qs=quad_sets(Q); layer=np.zeros(len(y))
    for i,(t,S) in enumerate(qs): layer+=gaps[i]*S
    out=[]
    for lam in (1.0,1.5,2.0,4.0):
        out.append(bool(feasible(Q,y-lam*layer).feasible) if (y-lam*layer).min()>=0 else None)
    print(p,"lam 1,1.5,2,4:",out,flush=True)
