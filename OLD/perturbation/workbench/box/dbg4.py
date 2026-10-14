import numpy as np
from exact import *
a=np.array([[3,2],[3,2],[2,3],[0,3],[1,3],[3,0],[1,1]],float);y=[2,2,1,0,2,2,1]
for r in [0.5,0.6,0.9,1.0]: print(r, rho_exact(a,y,True,rfix=r)[0])
