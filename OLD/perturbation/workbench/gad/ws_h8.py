import sys,os; sys.path.insert(0,".")
from ws_h import *
DX=DY=float(os.environ.get("D","12")); N=int(os.environ.get("N","6")); h=float(os.environ.get("H","0.02"))
rng=np.random.default_rng(3); sel=[(PATS[a],PATS[b]) for a,b in zip(rng.integers(0,16,N),rng.integers(0,16,N))]
sw1=list(sw3)
def eta_loc(c1,c2,gap):
    s=sc3(sw1); smax=s.max(); fb=np.array([Fpw(v,[4],[c1,c2],smax) for v in s]); return np.concatenate([[b+gap,b] for b in fb])
def y_clusters(w2,extra,c1=0.02,c2=0.08,gap=0.002):
    e=eta_loc(c1,c2,gap); e2=w2*e; off=e2.max()*(1+extra)
    eta=np.concatenate([e+off,e2]); return 1+0.3*eta/eta.max()
for w2 in (1,3,10):
    for extra in (0.05,0.5):
        Y=y_clusters(w2,extra)
        ok=sum(bool(weakly_solvable(Qcat(h,DX,DY,pa,pb),Y)) for pa,pb in sel)
        print("h",h,"D",DX,"w2",w2,"extra",extra,"pass",ok,"of",N,flush=True)
