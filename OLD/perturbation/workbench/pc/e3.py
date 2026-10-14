import numpy as np, sys
sys.path.insert(0,'pc')
from land import lp_cost
P=np.array([[4,1],[3,3],[1,4]],float)
for lam in np.linspace(0,1,11):
    print(round(lam,2), round(lp_cost(P,[1],[0,2],{1:lam}),4))
