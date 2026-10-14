from common import *
import time
sw=build("cp"); d=np.load("/Users/olegoleg/Code/neo-tiling/perturbation/workbench/gad/ws_snap_cp.npz"); Qs=list(d['Qs']); pats=d['pats'].tolist()
y,gaps=kinked_y(sw,[4])
print("npts",len(y),"ratio",y.max()/y.min())
for p,Q in list(zip(pats,Qs))[:int(sys.argv[1]) if len(sys.argv)>1 else 4]:
    t0=time.time()
    full=feasible(Q,y)
    qs=quad_sets(Q)
    types=''.join(t for t,_ in qs)
    layer=np.zeros(len(y))
    for i,(t,S) in enumerate(qs):
        assert S[2*i] and not S[2*i+1], (i,t)
        layer+=gaps[i]*S
    r=y-layer
    rem=feasible(Q,r)
    print(p,types,"full",full.feasible,"| r>=0",r.min()>=-1e-12,"min r %.4f"%r.min(),"remainder feasible",rem.feasible, "%.1fs"%(time.time()-t0),flush=True)
