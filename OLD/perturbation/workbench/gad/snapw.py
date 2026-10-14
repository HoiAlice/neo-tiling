import numpy as np, cx2
from core import solve_dom, polish_margin, weakly_solvable
from ysolve import find_y
def snap(L,tol=1e-5):
    L=L.copy()
    for k in (0,1):
        v=L[:,k]; o=np.argsort(v); i=0
        while i<len(o):
            j=i
            while j+1<len(o) and v[o[j+1]]-v[o[j]]<=tol: j+=1
            if j>i: L[o[i:j+1],k]=v[o[i:j+1]].mean()
            i=j+1
    return L
def snapped_solv(sw,idx,combos,tl=900,margin=1e-8,tol=1e-5,ratio=100):
    A,Y,conf,ks=cx2.setup(sw); Qs=[]; costs=[]
    for fx in combos:
        r=solve_dom(A,Y,fixed=dict(zip([ks[i] for i in idx],fx)),conflicts=conf,time_limit=tl)
        cm,u=polish_margin(A,conf,r[1],margin); Q=np.exp(snap(u,tol)); Qs.append(Q); costs.append(round(cm,6))
    per=[find_y([Q],Y,1e-6,ratio) is not None for Q in Qs]
    y=find_y(Qs,Y,1e-6,ratio)
    out=dict(costs=costs,per_combo_y_feasible=per,joint=y is not None)
    if y is not None:
        out["maxmin"]=round(float(y.max()/y.min()),4); out["weak_at_found_y"]=[weakly_solvable(Q,y) for Q in Qs]
    return out,y
