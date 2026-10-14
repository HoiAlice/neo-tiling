import sys; sys.path.insert(0,".")
from ws_p9b import *
d=np.load("ws_ser.npz")
for p,Q in zip(d['pats'].tolist(),d['Qs']):
    L=np.log(Q)
    out=[]
    for dec in (3,4,5,6,7):
        Qs=np.round(Q,dec); Ls=np.log(Qs)
        out.append((dec,feas(Ls),round(cost(Ls)-cost(L),6),bool(weakly_solvable(Qs,y))))
    print(tuple(p),out,flush=True)
