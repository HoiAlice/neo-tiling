import numpy as np
from exact import rho_exact
from twosat import rho_2sat
from pair import rho_pair
a=np.array([[3,2],[3,2],[2,3],[0,3],[1,3],[3,0],[1,1]],float);y=[2,2,1,0,2,2,1]
print(rho_exact(a,y,True),rho_2sat(a,y),rho_pair(a,y))
