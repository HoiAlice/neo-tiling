"""Experiment 2: log-space ridge families on cprime / K_3 snapped optima."""
import sys; sys.path.insert(0,"."); sys.path.insert(0,"../gad"); sys.path.insert(0,"/Users/olegoleg/Code/neo-tiling/poly-hardness")
import numpy as np, time
from axcone import cone_lp, AX
from ws_rule import build
from ws_rule4 import y_pw
kind=sys.argv[1] if len(sys.argv)>1 else "cp"
sw=build(kind); d=np.load("../gad/ws_snap_%s.npz"%kind); Qs=list(d['Qs']); pats=d['pats'].tolist()
fams={"ax+diag":AX+[(1.,1.)], "ax+diag+2":AX+[(1.,1.),(1.,2.),(2.,1.)], "ax+diag+4":AX+[(1.,1.),(1.,2.),(2.,1.),(1.,3.),(3.,1.),(2.,3.),(3.,2.)]}
for (c1,c2,ss,gap) in [(0.02,0.07,4,0.01),(0.02,0.12,4,0.002),(0.02,0.62,4,0.002)]:
    y=y_pw(sw,c1,c2,ss,gap=gap)
    for p,Q in zip(pats,Qs):
        L=np.log(Q); out=[]
        for nm,dirs in fams.items():
            ok,info=cone_lp(L,y,dirs,margin=True); out.append("%s %s t=%.1e"%(nm,ok,info['t']))
        print((c1,c2,ss,gap),p," | ".join(out),flush=True)
