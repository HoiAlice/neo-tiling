import sys,os; sys.path.insert(0,".")
import numpy as np
import ws_two as W
from ws_gmax import gmax
mult=float(os.environ.get("WS_M","1")); slopes=[0.02,0.02+0.05*mult,0.02+0.10*mult]
fb=np.array([W.F_pw(v,W.K,slopes) for v in W.s]); F=np.repeat(fb,2); tau=np.tile([1.0,0.0],len(fb))
scale=(fb.max()+0.01); F=1+0.3*F/scale  # normalise like y_multi (eps 0.3); t in same units
rng=np.random.default_rng(2); allp=[(i,j) for i in range(16) for j in range(16)]; sel=[allp[k] for k in rng.choice(256,int(os.environ.get("WS_N","8")),replace=False)]
vals=[(lambda v: -1.0 if v is None else v)(gmax(W.Qcat(*ij),F,tau)) for ij in sel]
print("g_raw(min)=%.2e (raw units: c1=0.02, Delta=%.2f)"%(min(vals)*scale/0.3,0.05*mult),"D",W.D,"mult",mult,"gmax (units of y) min/median/max over",len(sel),"patterns: %.2e %.2e %.2e"%(min(vals),np.median(vals),max(vals)),"| in units of 0.3/scale*0.01:",min(vals)/(0.3*0.01/scale),flush=True)
