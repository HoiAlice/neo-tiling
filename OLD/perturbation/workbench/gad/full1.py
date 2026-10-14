from core import *
import sys
def build(cs,d,eps=0.2):
    pts=[]
    for c in cs: pts += [(c[0]+d,c[1]+d),c]
    y=np.array([2.0,1.0]*len(cs)); a=eps*np.array(pts,float)
    return a,y
for name,cs,d in [("P3",[(0,0),(-3,3),(-6,6)],4),("K3",[(0,0),(-4,4),(-8,8)],11.17)]:
    a,y=build(cs,d)
    r=solve_dom(a,y)
    print(name,"rho_dom=",r[2],"milp lb",r[0],"sigma",r[1])
    Q=np.exp(r[3])
    for nud in (0,1e-9,1e-6):
        # nudge: shrink tops slightly? just rounding
        print(" weakly solvable at Q:",weakly_solvable(Q,y), end=" | ")
        break
    print()
