import sys, numpy as np, time
import scheme2, descW
from enum2 import window
def ffcheck(R,RE,G,thr=None,verbose=True):
    thr=R+6.4 if thr is None else thr
    n,edges,order=descW.witness(); L=scheme2.build(n,edges,RE,G,RW=int(R))
    pts=np.zeros((2*len(L.sw),2))
    for i,(bx,by,d) in enumerate(L.sw): pts[2*i]=(float(bx+d),float(by+d)); pts[2*i+1]=(float(bx),float(by))
    cen=np.array([[float(bx+d/2),float(by+d/2)] for bx,by,d in L.sw]); dd=np.array([float(d) for _,_,d in L.sw])
    minNW=1e9; minSE=1e9; viol=0; nSW=0; worst=None; tot=0
    for a in range(len(L.sw)):
        ids=window(L,a,R); inw=np.zeros(len(L.sw),bool); inw[ids]=True
        out_pts=np.concatenate([[2*j,2*j+1] for j in np.nonzero(~inw)[0]]).astype(int)
        O=pts[out_pts]
        for t in (pts[2*a],pts[2*a+1]):
            u=O[:,0]-t[0]; v=O[:,1]-t[1]
            nw=(u<0)&(v>=0); se=(v<0)&(u>=0); sw_=(u<0)&(v<0)
            nSW+=int(sw_.sum())
            if nw.any():
                m=v[nw].min(); 
                if m<minNW: minNW=m
                bad=int((v[nw]<thr).sum()); viol+=bad
                if bad and worst is None: worst=('NW',a,float(m))
            if se.any():
                m=u[se].min()
                if m<minSE: minSE=m
                bad=int((u[se]<thr).sum()); viol+=bad
                if bad and worst is None: worst=('SE',a,float(m))
    if verbose: print("R",R,"(RE,G)",(RE,G),"threshold R+6.4 =",thr,"| min long-coordinate of outside NW points: %.2f, SE points: %.2f | violating (central point, outside point) pairs: %d | outside SW pairs (to be cut): %d"%(minNW,minSE,viol,nSW),"| first violation",worst,flush=True)
    return minNW,minSE,viol
if __name__=="__main__":
    ffcheck(float(sys.argv[1]),int(sys.argv[2]),int(sys.argv[3]))
