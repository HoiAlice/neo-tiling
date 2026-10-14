from bias import *
from core import polish_margin, weakly_solvable
import itertools
sw=[(-3*i,3*i)+((4,5) if i%2==0 else (5,4)) for i in range(4)]
n=4; pts=[]
for (cx,cy,g0,g1) in sw: pts += [(cx+g0,cy+g1),(cx,cy)]
a=EPS*np.array(pts,float); y=np.array([2.,1.]*n); conf=conflicts_of(y)
r=solve_dom(a,y,conflicts=conf); sg=r[1]; print("sigma",sg)
for m in [1e-6,1e-4,1e-3,1e-2,3e-2]:
    cost,u=polish_margin(a,conf,sg,m); print(m,cost,weakly_solvable(np.exp(u),y))
# alternatives: all near-optimal switch patterns
for pat in itertools.product((0,1),repeat=4):
    ks=[conf.index((2*i,2*i+1)) for i in range(n)]
    r=solve_dom(a,y,fixed=dict(zip(ks,pat)),conflicts=conf)
    cost,u=polish_margin(a,conf,r[1],1e-6)
    print(pat,"%.5f"%r[2],weakly_solvable(np.exp(u),y))
