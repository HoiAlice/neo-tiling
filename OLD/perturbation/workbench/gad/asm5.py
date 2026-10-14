from asm import *
from ysolve import find_y
import cx2
if __name__=="__main__":
    for x in (0.0,0.02,0.05,0.06,0.1,0.2):
        sw,idx=build_asm()
        sw[-1]=sw[-1][:3]+(1+0.01+x,1+x)
        A,Y,conf,ks=cx2.setup(sw)
        Qs=[]; costs=[]
        for fx in [(0,1,0,1),(0,1,1,0)]:
            r=solve_dom(A,Y,fixed=dict(zip([ks[i] for i in idx],fx)),conflicts=conf,time_limit=120)
            cm,u=polish_margin(A,conf,r[1],1e-6); Qs.append(np.exp(u)); costs.append(round(cm,5))
        print("x",x,"costs",costs,"joint feasible",find_y(Qs,Y,1e-6,100) is not None,flush=True)
