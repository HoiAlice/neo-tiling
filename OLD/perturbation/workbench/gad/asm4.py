from asm import *
from ysolve import find_y
import cx2, itertools
if __name__=="__main__":
    sw,idx=build_asm()
    A,Y,conf,ks=cx2.setup(sw); n=len(sw)
    fx=(0,1,1,0)
    r=solve_dom(A,Y,fixed=dict(zip([ks[i] for i in idx],fx)),conflicts=conf,time_limit=120)
    cm,u=polish_margin(A,conf,r[1],1e-6); Q=np.exp(u)
    # greedy removal of switches while still infeasible
    keep=list(range(n))
    for i in list(range(n)):
        trial=[j for j in keep if j!=i]
        ii=[2*j+c for j in trial for c in (0,1)]
        if find_y([Q[ii]],Y[ii],1e-6,100) is None: keep=trial
    print("minimal infeasible switch set (indices):",keep)
    for j in keep: print(j,tuple(round(float(v),3) for v in sw[j]))
