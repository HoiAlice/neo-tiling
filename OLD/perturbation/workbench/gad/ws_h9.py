"""Hierarchical (staircase) y: copy 2 = local single-copy profile, copy 1 = local profile + offset (>= local mass). Whole-instance flow LP at large separations, h in {0.2, 0.02}."""
import sys,os; sys.path.insert(0,".")
from ws_h import *
DX=DY=float(os.environ.get("D","30")); N=int(os.environ.get("N","6")); h=float(os.environ.get("H","0.2"))
rng=np.random.default_rng(3); sel=[(PATS[a],PATS[b]) for a,b in zip(rng.integers(0,16,N),rng.integers(0,16,N))]
sw1=list(sw3)
def eta_loc(c1,c2,gap):
    s=sc3(sw1); smax=s.max(); fb=np.array([Fpw(v,[4],[c1,c2],smax) for v in s]); return np.concatenate([[b+gap,b] for b in fb])
def y_hier(off_factor,c1=0.02,c2=0.12,gap=0.002):
    e=eta_loc(c1,c2,gap); off=e.max()*off_factor; eta=np.concatenate([e+off,e]); return 1+0.3*eta/eta.max()
for of in [float(v) for v in os.environ.get('OF','1.05,1.5,3.0').split(',')]:
    Y=y_hier(of)
    ok=sum(bool(weakly_solvable(Qcat(h,DX,DY,pa,pb),Y)) for pa,pb in sel)
    print("h",h,"D",DX,"offset factor",of,"pass",ok,"of",N,flush=True)
