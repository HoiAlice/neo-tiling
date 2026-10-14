import sys
sys.path.insert(0,"/Users/olegoleg/Code/neo-tiling/poly-hardness")
import numpy as np, planar
from fractions import Fraction
from lp_box import lp_box
seed=int(sys.argv[1]);N=int(sys.argv[2]);G=int(sys.argv[3]);agree=0;dis=[];nsol=0
for it in range(N):
    r=np.random.default_rng([seed,it]);T=int(r.integers(3,7))
    P=r.integers(1,G+1,(T,2)).astype(float);y=r.integers(0,4,T).astype(float)
    Pf=[(Fraction(a),Fraction(b)) for a,b in P];yf=[Fraction(v) for v in y]
    ws=planar.flow_lp(Pf,yf,strict=False).feasible
    lp=lp_box(P,y,1.0)[0]
    nsol+=ws
    if ws==lp: agree+=1
    else: dis.append((P.tolist(),y.tolist(),ws,lp))
print("agree",agree,"of",N,"solvable",nsol)
for d in dis[:5]: print(d)
