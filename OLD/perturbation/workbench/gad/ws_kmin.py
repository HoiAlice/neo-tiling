"""Minimal base kappa such that kappa*1 + eta_loc is weakly solvable (cluster type requirement for the staircase), eta_loc = local profile; units of eta_loc.max()."""
import sys,os; sys.path.insert(0,".")
from ws_h import *
h=float(os.environ.get("H","0.2"))
s=sc3(list(sw3)); smax=s.max()
for (c1,c2,gap) in [(0.02,0.12,0.002),(0.02,0.08,0.01),(0.02,0.62,0.002)]:
    fb=np.array([Fpw(v,[4],[c1,c2],smax) for v in s]); e=np.concatenate([[b+gap,b] for b in fb]); mx=e.max(); e=e/mx
    worst=0; res=[]
    for p in PATS:
        Q=np.exp(h*XI[p]); lo,hi=0.0,2.0
        if not weakly_solvable(Q,hi+e): res.append((p,"fails even at kappa=2")); continue
        for _ in range(9):
            mid=(lo+hi)/2
            if weakly_solvable(Q,mid+e): hi=mid
            else: lo=mid
        res.append((p,round(hi,3)))
    kap=[r[1] for r in res if not isinstance(r[1],str)]
    print("h",h,"profile (c1,c2,gap)=",(c1,c2,gap),"kappa_min/range: max over 16 patterns %.3f, median %.3f, min %.3f"%(max(kap),np.median(kap),min(kap)),[r for r in res if isinstance(r[1],str)],flush=True)
