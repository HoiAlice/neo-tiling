import numpy as np, cx2, itertools
from core import solve_dom
def chain(n,a=3):
    return [(a*i,-a*i,4,2,1) for i in range(n)]
def eps(sw,sg):
    A,Y,conf,ks=cx2.setup(sw)
    r=solve_dom(A,Y,fixed=dict(zip(ks,sg)),conflicts=conf,time_limit=60)
    U=r[3]; D=np.abs(U-A)
    B=2*(np.exp(0.4)-1)
    return r[2], [round(float(np.sum(np.exp(D[2*k:2*k+2])-1)-B),5) for k in range(len(sw))], np.round(D,3).tolist()
for n,sg in [(2,(0,0)),(2,(0,1)),(3,(0,0,0)),(3,(0,1,0)),(4,(0,0,0,0)),(4,(0,0,1,1)),(5,(0,0,0,0,0)),(5,(0,0,1,0,0))]:
    c,e,D=eps(chain(n),sg); print(sg,round(c,5),e)
