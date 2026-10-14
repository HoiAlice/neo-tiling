"""Sufficiency with reproducible instances; on failure, retry with larger margins and save."""
import sys, json
import numpy as np
from t_suf import search
from lp_box import kappa_lp
from pair import rho_pair
seed=int(sys.argv[1]);N=int(sys.argv[2]);Tmax=int(sys.argv[3]);eps=float(sys.argv[4])
tested=0;found=0;ndom=0;fails=[]
for it in range(N):
    r=np.random.default_rng([seed,it]); T=int(r.integers(3,Tmax+1)); P=r.uniform(0.5,4,(T,2)); y=np.round(r.uniform(0,3,T),2)
    k=kappa_lp(P,y); kd=float(np.exp(rho_pair(np.log(P),y)))
    assert k>=kd-1e-6
    if k==1.0: continue
    tested+=1; ndom+= abs(k-kd)<1e-6
    sr=np.random.default_rng([seed,it,1])
    b=search(P,y,k*(1+eps),sr)
    if b<1e-8: found+=1
    else:
        # escalate
        res=[(m,search(P,y,k*(1+m),sr,restarts=80)) for m in (0.02,0.05,0.1)]
        fails.append((it,T,k,res)); print("FAIL",it,T,k,res,flush=True)
        json.dump(dict(P=P.tolist(),y=y.tolist(),k=k),open(f"fail_{seed}_{it}.json","w"))
print("seed",seed,"tested",tested,"found",found,"kappa==kdom",ndom,"fails",len(fails))
