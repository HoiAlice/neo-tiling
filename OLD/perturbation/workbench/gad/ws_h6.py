import sys,os; sys.path.insert(0,".")
from ws_h import *
DX=DY=float(os.environ.get("D","12")); N=6
rng=np.random.default_rng(3); sel=[(PATS[a],PATS[b]) for a,b in zip(rng.integers(0,16,N),rng.integers(0,16,N))]
sw=two(DX,DY); K=[4,4+DX+DY]; Y=y_rule(sw,K,[0.02,0.62,3.74],0.002,0.3)
for h in (0.2,0.05,0.02):
    out=[]
    for pa,pb in sel:
        r=solve([Qcat(h,DX,DY,pa,pb)],Y); out.append(round(0.0 if r is None else r[2]/1e-3,5))
    print("h",h,"D",DX,"free-y t per pattern pair:",out,flush=True)
