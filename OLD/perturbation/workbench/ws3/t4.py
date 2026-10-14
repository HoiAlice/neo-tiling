import sys
sys.path.insert(0,"/Users/olegoleg/Code/neo-tiling/perturbation/workbench/ws2")
from common import *
from axcone import quad_lp
sw=build("cp"); d=np.load("/Users/olegoleg/Code/neo-tiling/perturbation/workbench/gad/ws_snap_cp.npz"); Qs=list(d['Qs']); pats=d['pats'].tolist()
y,gaps=kinked_y(sw,[4])
for p,Q in list(zip(pats,Qs))[:int(sys.argv[1])]:
    L=np.round(np.log(Q),9)
    ok,info=quad_lp(L,y,margin=True)
    print(p,"y in quad cone:",ok,"t=%.3e"%info.get('t',float('nan')),flush=True)
