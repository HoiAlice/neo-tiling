import sys; sys.path.insert(0,".")
from ws_p9b import *
from core import polish_margin
d=np.load("ws_ser.npz"); conf_l=[tuple(c) for c in d['conf'].tolist()]
def snap(L,tol):
    L=L.copy()
    for k in (0,1):
        v=L[:,k]; o=np.argsort(v); i=0
        while i<len(o):
            j=i
            while j+1<len(o) and v[o[j+1]]-v[o[j]]<=tol: j+=1
            if j>i: L[o[i:j+1],k]=v[o[i:j+1]].mean()
            i=j+1
    return L
if __name__=="__main__":
 for p,sg,Q in zip(d['pats'].tolist(),d['sigma'],d['Qs']):
     L0=np.log(Q); c0=cost(L0)
     for m in (1e-6,1e-8):
         cm,u=polish_margin(A,conf_l,[int(s) for s in sg],m)
         for tol in (1e-5,1e-4):
             Ls=snap(u,tol); print(tuple(p),"polish m",m,"snap tol",tol,"feasible",feas(Ls),"dcost %.2e"%(cost(Ls)-c0),"weak",weakly_solvable(np.exp(Ls),y),flush=True)
