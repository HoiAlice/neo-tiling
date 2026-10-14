import sys; sys.path.insert(0,".")
import numpy as np, scheme2
for name,n,E in [("K4",4,[(0,1),(0,2),(0,3),(1,2),(1,3),(2,3)]),("K33",6,[(0,3),(0,4),(0,5),(1,3),(1,4),(1,5),(2,3),(2,4),(2,5)])]:
    try: L=scheme2.build(n,E,6,16)
    except Exception as ex: print(name,"build failed",ex); continue
    pts=[]; sck=[]
    for (bx,by,d) in L.sw:
        bx,by=float(bx),float(by); pts+= [(bx+d,by+d),(bx,by)]; sck+=[bx+by+d]*2
    P=np.array(pts); sck=np.array(sck); N=len(P)
    print(name,"switches",len(L.sw),"points",N)
    for gap in (24,):
        # pairs t,s with s_c(s) >= s_c(t)+gap (s in a higher slab, TARGET T-side) and s strictly NW or SE of t
        higher=sck[None,:]>=sck[:,None]+gap
        dx=P[None,:,0]-P[:,None,0]; dy=P[None,:,1]-P[:,None,1]
        nw=(higher&(dx<0)&(dy>0)).sum(); se=(higher&(dx>0)&(dy<0)).sum(); tot=higher.sum()
        print("  pairs with s_c gap >= %d: %d ; of which s strictly NW of t: %d, SE of t: %d (fraction %.2f)"%(gap,tot,nw,se,(nw+se)/tot))
        # how many points t have at least one higher-slab point NW or SE of them
        has=((higher&(dx<0)&(dy>0))|(higher&(dx>0)&(dy<0))).any(axis=1).sum(); print("  points t with some NW/SE point in a higher slab:",has,"of",N)
