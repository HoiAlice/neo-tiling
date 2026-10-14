import sys,os; sys.path.insert(0,".")
import numpy as np, time
from fractions import Fraction as Fr
from ws_h import *
import ws_glue as GL
from ws_exact import y_rational
DX=DY=float(os.environ.get("D","30")); h=float(os.environ.get("H","0.2")); kap=Fr(os.environ.get("KAPPA","0.01"))
# hierarchical y (rational): copy 2 local profile eta_loc; copy 1 = eta_loc + off
c1,c2,gap=Fr(2,100),Fr(12,100),Fr(2,1000)
def eta_loc_exact():
    s=sc3(list(sw3)); smax=max(s); out=[]
    for v in s:
        v=Fr(int(v)); fb=Fr(0)
        for lo,hi,sl in ((-10**9,4,c1),(4,10**9,c2)):
            a=max(Fr(lo),v); b=min(Fr(hi),Fr(int(smax)))
            if b>a: fb+=sl*(b-a)
        out+=[fb+gap,fb]
    return out
e=eta_loc_exact(); off=max(e)*Fr(os.environ.get('OF','3/2')); eta=[v+off for v in e]+e; mx=max(eta); y=[1+Fr(3,10)*v/mx for v in eta]
# GL expects the layout of ws_two with n1 switches per copy: here sw3 copy size
GL.W=type("W",(),{})(); GL.W.n1=len(sw3)
rng=np.random.default_rng(11); sel=[(PATS[a],PATS[b]) for a,b in zip(rng.integers(0,16,int(os.environ.get('N','3'))),rng.integers(0,16,int(os.environ.get('N','3'))))]
sel=sel[:1] if os.environ.get('ONLY1') else sel
for pa,pb in sel:
    t=time.time(); Q=Qcat(h,DX,DY,pa,pb); ok,msg=GL.glue(Q,y,kap); print("h",h,"D",DX,pa,pb,"GLUING",ok,msg,"%.0fs"%(time.time()-t),flush=True)
