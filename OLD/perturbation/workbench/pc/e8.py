import numpy as np, sys
sys.path.insert(0,'pc')
from a2 import solve
# chain: 4 lights on a convex chain, 3 heavies over the 3 faces
L=[[8,1],[4,2.2],[2.2,4],[1,8]]
H=[[6.3,1.9],[3.2,3.3],[1.8,6.2]]
P=np.array(L+H,float); y=[3]*4+[7]*3
for sub,name in [([4],"h1 only"),([5],"h2 only"),([6],"h3 only"),([4,5],"h1,h2"),([4,5,6],"all")]:
    idx=list(range(4))+sub; v,Q,c=solve(P[idx],[y[i] for i in idx],tl=100); print(name,round(v,5),"lights moved:",np.round(Q[:4]-P[:4],2).tolist()); sys.stdout.flush()
