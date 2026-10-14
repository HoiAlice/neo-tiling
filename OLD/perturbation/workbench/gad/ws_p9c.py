import sys; sys.path.insert(0,".")
from ws_p9b import *
def scale_test(Q0,obs,mv,dls=(1e-3,1e-4,1e-5,1e-6,1e-7,1e-8)):
    L0=np.log(Q0); c0=cost(L0); coords=[(p,k) for p in obs for k in (0,1)]
    for dl in dls:
        L=L0.copy()
        for (p,k),m in zip(coords,mv): L[p,k]+=m*dl
        print("  delta",dl,"feasible",feas(L),"dcost %.2e"%(cost(L)-c0),"weak(full)",weakly_solvable(np.exp(L),y),flush=True)
def cheapest(Q0,obs,dl=1e-4):
    L0=np.log(Q0); c0=cost(L0); coords=[(p,k) for p in obs for k in (0,1)]; best=None
    for mv in itertools.product((-1,0,1),repeat=len(coords)):
        if not any(mv): continue
        L=L0.copy()
        for (p,k),m in zip(coords,mv): L[p,k]+=m*dl
        if not feas(L): continue
        dc=cost(L)-c0
        if best is not None and dc>=best[0]: continue
        if weakly_solvable(np.exp(L)[obs],y[obs]) and weakly_solvable(np.exp(L),y): best=(dc,mv)
    return best
if __name__=="__main__":
    d=np.load("ws_all_cp.npz"); pats=[tuple(p) for p in d['pats'].tolist()]
    pat=tuple(int(c) for c in sys.argv[1]); obs=[int(v) for v in sys.argv[2].split(",")]
    Q0=d['Qs'][pats.index(pat)]
    b=cheapest(Q0,obs); print(pat,"cheapest working move at 1e-4:",b,flush=True)
    if b: scale_test(Q0,obs,b[1])
