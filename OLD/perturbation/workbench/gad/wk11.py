from yv import *
import itertools, sys
import planar
from fractions import Fraction
g,h=float(sys.argv[1]),float(sys.argv[2]); fx=tuple(int(c) for c in sys.argv[3])
S=tuple(int(c) for c in sys.argv[4].split(','))
nU,nV=4,3
sw=build3(nU,nV,3,4,1,5,g,h)
A,Y,conf,ks=cx2.setup(sw); idx=[0,nU-1,nU,nU+nV-1]
r=solve_dom(A,Y,fixed=dict(zip([ks[i] for i in idx],fx)),conflicts=conf,time_limit=120)
cm,u=polish_margin(A,conf,r[1],1e-6); Q=np.exp(u)
ii=[2*i+j for i in S for j in (0,1)]
Pf=[tuple(Fraction(float(v)).limit_denominator(10**9) for v in row) for row in Q[ii]]
yf=[Fraction(float(v)).limit_denominator(10**9) for v in Y[ii]]
res=planar.flow_lp(Pf,yf)
np.set_printoptions(precision=4,suppress=True)
print("grid pts"); print(np.log(Q[ii])/0.2)
print("y",Y[ii]); print("w",res.w, "w.y",res.w@Y[ii])
