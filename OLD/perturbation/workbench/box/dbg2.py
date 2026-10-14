import numpy as np
from gcons import g_construct, dom_ok
a=np.array([[3,2],[3,2],[2,3],[0,3],[1,3],[3,0],[1,1]],float);y=np.array([2,2,1,0,2,2,1],float)
u=g_construct(a,y,0.6)
print(np.abs(u-a).max())
T=len(a)
for p in range(T):
    for q in range(T):
        if y[p]>y[q]: print(p,q,u[p]-u[q])
