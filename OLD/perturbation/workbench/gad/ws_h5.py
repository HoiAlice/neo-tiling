import sys,os; sys.path.insert(0,".")
from ws_h import *
h=float(os.environ.get("H","0.02")); DX=DY=float(os.environ.get("D","12")); N=int(os.environ.get("N","6"))
rng=np.random.default_rng(3); sel=[(PATS[a],PATS[b]) for a,b in zip(rng.integers(0,16,N),rng.integers(0,16,N))]
sw=two(DX,DY); K=[4,4+DX+DY]
for R,c2,gap in [(6,0.62,0.0005),(12,0.62,0.002),(12,0.62,0.0005),(6,2.0,0.002),(6,2.0,0.0005),(12,3.0,0.0005)]:
    c3=R*c2+0.02; Y=y_rule(sw,K,[0.02,c2,c3],gap,0.3)
    ok=sum(bool(weakly_solvable(Qcat(h,DX,DY,pa,pb),Y)) for pa,pb in sel)
    print("h",h,"slopes 0.02, %.2f, %.2f gap %g: pass %d of %d"%(c2,c3,gap,ok,N),flush=True)
