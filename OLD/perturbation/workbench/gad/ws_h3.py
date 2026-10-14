import sys,os; sys.path.insert(0,".")
from ws_h import *
from ws_far import farkas
from ws_p9 import minimal_switches
h=float(os.environ.get("H","0.02")); DX=DY=float(os.environ.get("D","12"))
sw=two(DX,DY); K=[4,4+DX+DY]; Y=y_rule(sw,K,[0.02,0.62,float(os.environ.get('C3','1.22'))],0.002,0.3); n1=len(sw3)
import itertools
rng=np.random.default_rng(3); N=6; sel=[(PATS[a],PATS[b]) for a,b in zip(rng.integers(0,16,N),rng.integers(0,16,N))]
for pa,pb in sel:
    Q=Qcat(h,DX,DY,pa,pb)
    if not weakly_solvable(Q,Y): break
else: raise SystemExit('all pass')
PA,PB=pa,pb
print(pa,pb); print("h",h,"weak",weakly_solvable(Q,Y),flush=True)
kk,P=minimal_switches(Q,Y); print("min switches",kk,"points",len(P),flush=True)
lam,val,nf=farkas(Q[P],Y[P]); print("min lam.y %.2e"%val,"reachable sets",nf)
XIc=np.vstack([XI[PA],XI[PB]+np.array([DX,DY])]); s=sc3(sw)
for a,p in zip(lam,P):
    if abs(a)>1e-6:
        i=p//2; print("  %+.3f c%d s%d%s s_c=%d xi=(%.2f,%.2f) t=%.2f y %.6f"%(a,i//n1,i%n1,"t" if p%2==0 else "b",s[i],XIc[p,0],XIc[p,1],XIc[p,1]-XIc[p,0],Y[p]))
