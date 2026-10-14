import sys
sys.path.insert(0,"/Users/olegoleg/Code/neo-tiling/poly-hardness")
import numpy as np, planar
from fractions import Fraction as F
from exactbox import *
for T in (2,3,4,5,6,8,10):
    r=np.random.default_rng(T);L=[(F(int(a)),F(int(b))) for a,b in r.integers(1,50,(T,2))];U=[(a+3,b+3) for a,b in L]
    d=delta_bound(L,U);W=corners(L,U,d);G=planar.chain_graph(W)
    print("T",T,"points",2*T,"nodes",len(G.nodes),"arcs",len(G.arcs),"delta bits",d.denominator.bit_length())
