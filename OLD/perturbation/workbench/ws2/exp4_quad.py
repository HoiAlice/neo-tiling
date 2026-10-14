import sys; sys.path.insert(0,"."); sys.path.insert(0,"../gad"); sys.path.insert(0,"/Users/olegoleg/Code/neo-tiling/poly-hardness")
import numpy as np, time
from axcone import quad_lp
from ws_rule import build
from ws_rule4 import y_pw
kind=sys.argv[1] if len(sys.argv)>1 else "cp"
sw=build(kind); d=np.load("../gad/ws_snap_%s.npz"%kind); Qs=list(d['Qs']); pats=d['pats'].tolist()
for (c1,c2,ss,gap) in [(0.02,0.07,4,0.01),(0.02,0.12,4,0.002),(0.02,0.62,4,0.002)]:
    y=y_pw(sw,c1,c2,ss,gap=gap)
    for p,Q in zip(pats,Qs):
        L=np.log(Q); t0=time.time()
        ok,info=quad_lp(L,y,margin=True)
        # vertices at bottoms only
        bots=[tuple(L[2*i+1]) for i in range(len(sw))]
        okb,infob=quad_lp(L,y,vertices=bots,margin=True)
        print((c1,c2,ss,gap),p,"quad(all grid vertices)",ok,"t=%.2e"%info['t'],"support",int((info['mu']>1e-9).sum()),"| bottoms only",okb,"t=%.2e"%infob['t'],"%.1fs"%(time.time()-t0),flush=True)
