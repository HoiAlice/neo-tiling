import numpy as np
from lp_box import *
from pair import rho_pair
P=np.array([[4,1],[3,3],[1,4]],float); y=[1,5,3]
print(kappa_lp(P,y))
P=np.array([[1,4],[2.5,2.5],[4,1]],float); y=[1,5,1]
print(kappa_lp(P,y))
