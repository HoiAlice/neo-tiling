import sys
sys.path.insert(0,"/Users/olegoleg/Code/neo-tiling/perturbation/workbench/ws2")
from common import *
from axcone import quad_lp
sw=build("cp"); d=np.load("/Users/olegoleg/Code/neo-tiling/perturbation/workbench/gad/ws_snap_cp.npz"); Qs=list(d['Qs']); pats=d['pats'].tolist()
y,gaps=kinked_y(sw,[4])
Q=Qs[0]; L=np.round(np.log(Q),9)
qs=quad_sets(Q); layer=np.zeros(len(y))
for i,(t,S) in enumerate(qs): layer+=gaps[i]*S
r=y-layer
for name,yy in (("y",y),("remainder",r)):
    ok,info=quad_lp(L,yy,margin=False)
    mu=info['mu']; V=info['vertices']; idx=np.where(mu>1e-12)[0]
    print(name,ok,"b=%.4f"%info['b'],"support",len(idx),"total mass %.4f"%mu.sum())
    gs=sorted(set(np.round(gaps,6)))
    for j in idx[np.argsort(V[idx,0]+V[idx,1])]:
        # classify: coincides with a point?
        dd=np.abs(L-V[j]).max(axis=1); pt=np.where(dd<1e-8)[0]
        print("  v=(%.3f,%.3f) s=%.3f mass %.5f"%(V[j,0],V[j,1],V[j].sum(),mu[j]), "at point %s"%(("top" if pt[0]%2==0 else "bot")+str(pt[0]//2)) if len(pt) else "")
print("gaps",sorted(set(np.round(gaps,6))))
