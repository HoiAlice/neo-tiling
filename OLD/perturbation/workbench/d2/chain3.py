import sys, itertools, numpy as np
sys.path.insert(0,"/Users/olegoleg/Code/neo-tiling/perturbation/experiments")
from iso_scipy import iso_cost
def F(P,y,sigma,conf):
    a=[np.log(P[:,0]),np.log(P[:,1])]
    e=[[],[]]
    for (t,s),i in zip(conf,sigma): e[i].append((t,s))
    return iso_cost(a[0],e[0])[0]+iso_cost(a[1],e[1])[0]
P=np.array([[3,3],[2,2],[1,1]],float); y=np.array([1,2,3.])  # index0 lowest y? need conflicts t,s with y_t>y_s and p_t>p_s
# t=2 (y=3, p=1,1) is dominated... choose y so top-right has largest y
y=np.array([3,2,1.])
conf=[(t,s) for t in range(3) for s in range(3) if y[t]>y[s]]
print(conf)
for sig in itertools.product((0,1),repeat=3):
    print(sig, round(F(P,y,sig,conf),4))
