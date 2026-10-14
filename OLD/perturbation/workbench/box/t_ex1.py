import sys,time
sys.path.insert(0,"/Users/olegoleg/Code/neo-tiling/poly-hardness")
import numpy as np, planar
from fractions import Fraction as F
from exactbox import *
# fixed prices vs planar
seed=int(sys.argv[1]);N=int(sys.argv[2]);G=int(sys.argv[3]);agree=0;ns=0;t0=time.time()
for it in range(N):
    r=np.random.default_rng([seed,it]);T=int(r.integers(2,6))
    P=[(F(int(a)),F(int(b))) for a,b in r.integers(1,G+1,(T,2))];y=[F(int(v)) for v in r.integers(0,4,T)]
    ws=planar.flow_lp(P,y,strict=False).feasible
    ex=decide(P,P,y)
    ns+=ws; agree+=(ws==ex)
    if ws!=ex: print("DISAGREE",P,y,ws,ex)
print("fixed prices (zero-width boxes): agree",agree,"of",N,"solvable",ns,"time %.0fs"%(time.time()-t0))
