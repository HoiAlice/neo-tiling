import sys
sys.argv=["x","1","0"]
exec(open("t_fin3.py").read().split("rng=np.random")[0])
import numpy as np
rng=np.random.default_rng(1)
for it in range(4):
    T=int(rng.integers(3,5))
    P=[(F(int(a),4),F(int(b),4)) for a,b in rng.integers(2,17,(T,2))]
    y=[F(int(v)) for v in rng.integers(0,4,T)]
    if it==3:
        cr=[c for c in critical_kappas([(float(a),float(b)) for a,b in P]) if c>=1.0]
        print(P,y); print(cr)
        kc=1.0954451150103321
        for k in [kc*(1-1e-9),kc,kc*(1+1e-9),kc*(1+1e-6)]: print(k,dec(P,y,k))
