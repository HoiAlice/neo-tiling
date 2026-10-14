from bias import *
from core import polish_margin, weakly_solvable
sw=[(-3*i,3*i)+((4,5) if i%2==0 else (5,4)) for i in range(4)]
n=4; pts=[]
for (cx,cy,g0,g1) in sw: pts += [(cx+g0,cy+g1),(cx,cy)]
a=EPS*np.array(pts,float); y=np.array([2.,1.]*n); conf=conflicts_of(y)
r=solve_dom(a,y,conflicts=conf); cost,u=polish_margin(a,conf,r[1],1e-6); Q=np.exp(u)
print("Q (log2d)",np.round(u,4).tolist())
for top in [1.01,1.2,1.5,1.9,2.0,2.1,3,5,10]:
    yy=np.array([top,1.]*n); print(top,weakly_solvable(Q,yy))
# per-switch ratios
for ys in [[2,1,3,1,2,1,3,1],[3,1,2,1,3,1,2,1],[2,1,2,1,3,1,3,1],[1.5,1,2,1,1.5,1,2,1]]:
    print(ys,weakly_solvable(Q,np.array(ys,float)))
# sub-chains
for lo,hi in [(0,3),(1,4)]:
    sl=slice(2*lo,2*hi); yy=np.array([2.,1.]*(hi-lo)); print("sub",lo,hi,weakly_solvable(Q[sl],yy))
