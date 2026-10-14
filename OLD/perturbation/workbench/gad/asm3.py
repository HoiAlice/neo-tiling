from asm import *
from ysolve import find_y
import cx2
if __name__=="__main__":
    sw,idx=build_asm()
    A,Y,conf,ks=cx2.setup(sw)
    Qs=[]
    for fx in [(0,1,0,1),(0,1,1,0),(1,0,0,1),(1,0,1,0)]:
        r=solve_dom(A,Y,fixed=dict(zip([ks[i] for i in idx],fx)),conflicts=conf,time_limit=120)
        cm,u=polish_margin(A,conf,r[1],1e-6); Qs.append(np.exp(u))
    for i,Q in enumerate(Qs):
        for d,rt in [(1e-3,1.9),(1e-6,1.9),(1e-6,100)]:
            y=find_y([Q],Y,d,rt); print("Q",i,"delta",d,"ratio",rt,"feasible",y is not None,flush=True)
    for d,rt in [(1e-6,100)]:
        y=find_y(Qs,Y,d,rt); print("joint",d,rt,y is not None)
