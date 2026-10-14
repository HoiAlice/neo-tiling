from full1 import build
from core import *
for name,cs,d in [("P3",[(0,0),(-3,3),(-6,6)],4),("K3",[(0,0),(-4,4),(-8,8)],11.17)]:
    a,y=build(cs,d); conf=conflicts_of(y)
    r=solve_dom(a,y)
    for m in (1e-7,1e-5,1e-4):
        c,u=polish_margin(a,conf,r[1],m)
        Q=np.exp(u)
        print(name,"margin",m,"cost",round(c,6),"rho_dom",round(r[2],6),"weak solv:",weakly_solvable(Q,y))
