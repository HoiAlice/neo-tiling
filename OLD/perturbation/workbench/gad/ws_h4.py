import sys,os; sys.path.insert(0,".")
from ws_h import *
h=float(os.environ.get("H","0.02")); DX=DY=float(os.environ.get("D","12")); N=int(os.environ.get("N","6"))
rng=np.random.default_rng(3); sel=[(PATS[a],PATS[b]) for a,b in zip(rng.integers(0,16,N),rng.integers(0,16,N))]
sw=two(DX,DY); K=[4,4+DX+DY]
for R in (2,3,4,6):
    c3=R*0.62+0.02; Y=y_rule(sw,K,[0.02,0.62,c3],0.002,0.3)
    ok=sum(bool(weakly_solvable(Qcat(h,DX,DY,pa,pb),Y)) for pa,pb in sel)
    print("h",h,"D",DX,"slopes 0.02, 0.62, %.2f (R=%d): pass %d of %d"%(c3,R,ok,N),flush=True)
