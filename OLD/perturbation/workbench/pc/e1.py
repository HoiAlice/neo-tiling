import numpy as np, sys
sys.path.insert(0,'pc')
from a2 import solve
def show(name,P,y):
    v,Q,c=solve(P,y); print(name,"rho=%.5f"%v,"triples",c); 
    if Q is not None: print(np.round(Q,3).tolist())
    return v
# single triangle two-class
v1=show("tri",[[4,1],[3,3],[1,4]],[3,7,3])
# two far-apart triangles (second scaled anti-diagonally) 
P=[[4,1],[3,3],[1,4],[400,.01],[300,.03],[100,.04]]; 
show("two tri apart",P,[3,7,3,3,7,3])
# shared light: L1,L2,L3 heavies h1 above L1L2, h2 above L2L3
P=[[6,1],[3,3.2],[1,6],[4.8,2.9],[2.1,4.9]]
show("shared",P,[3,3,3,7,7])
P=[[6,1],[3,3.2],[1,6],[4.8,2.9]]
show("shared half",P,[3,3,3,7])
