"""Scaling in h: two cprime copies at G* (phi=r^2, glued optimum in grid units xi = x/h independent of h), prices Q = exp(h*xi).
tests: free-y feasibility (max-min-gap LP), final rule weak solvability, gmax, for h in a list and shifts (DX,DY)."""
import sys, os, itertools
PHI='/Users/olegoleg/Code/neo-tiling/perturbation/workbench/phi'
sys.path.insert(0,PHI); sys.path.insert(0,"."); sys.path.insert(0,"/Users/olegoleg/Code/neo-tiling/poly-hardness")
import numpy as np
cwd=os.getcwd()
import ws_g as G
import phi_dual as pd
os.chdir(cwd)
from ws_gap import solve
from core import weakly_solvable
U,ATT,AW=2.5,3.0,3.75
sw3=G.build_cp(U,ATT,AW)
def xis():
    pd.set_phi('sq',h=0.2); out={}
    for pat in itertools.product((0,1),repeat=4): out[pat]=G.glued_x(sw3,U,pat)[0]/pd.H
    return out
XI=xis(); PATS=sorted(XI)
def sc3(sw): return np.array([bx+by+d for bx,by,d in sw],float)
def two(DX,DY):
    sw=list(sw3)+[(bx+DX,by+DY,d) for bx,by,d in sw3]; return sw
def Fpw(v,kinks,slopes,smax):
    cuts=[-1e9]+list(kinks)+[1e9]; val=0.0
    for i,sl in enumerate(slopes):
        lo=max(cuts[i],v); hi=min(cuts[i+1],smax)
        if hi>lo: val+=sl*(hi-lo)
    return val
def y_rule(sw,kinks,slopes,gap,eps):
    s=sc3(sw); smax=s.max(); fb=np.array([Fpw(v,kinks,slopes,smax) for v in s]); top=fb+gap
    eta=np.concatenate([[t,b] for t,b in zip(top,fb)]); return 1+eps*eta/eta.max()
def Qcat(h,DX,DY,pa,pb): return np.exp(h*np.vstack([XI[pa],XI[pb]+np.array([DX,DY])]))
if __name__=="__main__":
    DX=float(os.environ.get("DX","10")); DY=float(os.environ.get("DY","10")); hs=[float(v) for v in os.environ.get("HS","0.2,0.1,0.05,0.02").split(",")]
    N=int(os.environ.get("N","4")); rng=np.random.default_rng(int(os.environ.get("SEED","1")))
    sw=two(DX,DY); K=[4,4+DX+DY]; Y=y_rule(sw,K,[0.02,0.62,1.22],0.002,0.3)
    sel=[(PATS[a],PATS[b]) for a,b in zip(rng.integers(0,16,N),rng.integers(0,16,N))]
    for h in hs:
        free=[]; rule=[]
        for pa,pb in sel:
            Q=Qcat(h,DX,DY,pa,pb); r=solve([Q],Y); free.append(0.0 if r is None else r[2]/1e-3); rule.append(bool(weakly_solvable(Q,Y)))
        print("shift",DX,DY,"h",h,"free-y t (per pattern):",[round(t,5) for t in free],"| final rule weakly solvable:",sum(rule),"of",N,flush=True)
