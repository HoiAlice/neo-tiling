import sys,time
sys.path.insert(0,"/Users/olegoleg/Code/neo-tiling/poly-hardness")
import numpy as np
from fractions import Fraction as F
from exactbox import *
rng=np.random.default_rng(int(sys.argv[1]));N=int(sys.argv[2]);dis=0;nt=0;nf=0
for it in range(N):
    T=int(rng.integers(3,6));G=int(rng.integers(3,7))
    L=[tuple(F(int(v)) for v in rng.integers(1,G,2)) for _ in range(T)]
    U=[tuple(L[t][i]+F(int(rng.integers(0,2)))*F(int(rng.integers(0,2))) for i in range(2)) for t in range(T)]
    y=[F(int(v)) for v in rng.integers(0,int(sys.argv[3]),T)]
    a=decide(L,U,y); c=decide_W(corners(L,U,0),y,T)
    nt+=a;nf+=(not a)
    if a!=c: dis+=1;print("LP_closed != LP(E_delta):",L,U,y,a,c)
print("instances",N,"BOX true",nt,"false",nf,"LP_closed(W_0) disagreements with exact decision:",dis)
