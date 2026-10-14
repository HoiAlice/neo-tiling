"""Multiplicative rule: kinks at s* (crossing levels), slope x rho per kink toward NE, local gap g(s)=gfac*slope(s). Two cprime copies."""
import sys,os; sys.path.insert(0,".")
from ws_h import *
h=float(os.environ.get("H","0.2")); D=float(os.environ.get("D","12")); N=int(os.environ.get("N","6")); rho=float(os.environ.get("RHO","11")); gfac=float(os.environ.get("GF","0.1"))
sw=two(D,D); kinks=[4,4+2*D]
def slopes_at(s): 
    k=sum(1 for q in kinks if s>q); return 0.02*rho**k
def y_mult():
    s=sc3(sw); smax=s.max()
    # F(v)= integral from v to smax of slope(u) du (slope constant on each region)
    def F(v):
        val=0.0; cuts=[-1e9]+kinks+[1e9]
        for i in range(len(kinks)+1):
            lo=max(cuts[i],v); hi=min(cuts[i+1],smax)
            if hi>lo: val+=0.02*rho**i*(hi-lo)
        return val
    fb=np.array([F(v) for v in s]); gap=np.array([gfac*slopes_at(v) for v in s])
    eta=np.concatenate([[b+g_,b] for b,g_ in zip(fb,gap)]); return 1+0.3*eta/eta.max()
Y=y_mult()
rng=np.random.default_rng(3); sel=[(PATS[a],PATS[b]) for a,b in zip(rng.integers(0,16,N),rng.integers(0,16,N))]
ok=sum(bool(weakly_solvable(Qcat(h,D,D,pa,pb),Y)) for pa,pb in sel)
print("h",h,"D",D,"rho",rho,"gfac",gfac,"pass",ok,"of",N,flush=True)
