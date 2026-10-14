import numpy as np, sys
sys.path.insert(0,'.'); sys.path.insert(0,'pc')
from rho_exact import rho_exact
P=np.array([[6,1],[3,3.2],[1,6],[4.8,2.9],[2.1,4.9]]); y=np.array([3,3,3,7,7.])
v,Q,F=rho_exact(P,y,max_fam=2,time_limit=60)
print("rho_exact shared =",v,"F=",[sorted(S) for S in F]); print(np.round(Q,3).tolist())
