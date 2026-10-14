import numpy as np
from ysolve import find_y
d=np.load("cprime_Q_1010.npz"); Q,Y=d["Q"],d["Y"]; n=len(Y)//2
print("full y-feasible:",find_y([Q],Y,1e-6,100) is not None)
keep=list(range(n))
for i in range(n):
    tr=[j for j in keep if j!=i]; ii=[2*j+c for j in tr for c in (0,1)]
    if find_y([Q[ii]],Y[ii],1e-6,100) is None: keep=tr
print("minimal infeasible switches",keep)
ii=[2*j+c for j in keep for c in (0,1)]
print(np.round(np.log(Q[ii])/0.2,3)); print(Y[ii])
