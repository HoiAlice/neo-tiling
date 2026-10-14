import numpy as np
from exact import *
a=np.array([[3,2],[3,2],[2,3],[0,3],[1,3],[3,0],[1,1]],float);y=[2,2,1,0,2,2,1]
r,u,z=rho_exact(a,y,True)
print(r)
C=conflicts(y)
for (p,q),zz in zip(C,z): print(p,q,zz,u[p]-u[q])
