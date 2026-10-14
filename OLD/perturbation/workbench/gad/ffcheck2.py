import sys, numpy as np, time
import scheme2, descW
from enum2 import window
def key(m):
    k=m['kind']
    if k=='bus': return ('bus',m['v'])
    if k=='arm': return ('arm',m['e'],m['u'])
    return ('track',m['e'])
def ffcheck2(R,RE,G,verbose=True,L=None):
    if L is None:
        n,edges,order=descW.witness(); L=scheme2.build(n,edges,RE,G,RW=int(R))
    pts=np.zeros((2*len(L.sw),2))
    for i,(bx,by,d) in enumerate(L.sw): pts[2*i]=(float(bx+d),float(by+d)); pts[2*i+1]=(float(bx),float(by))
    keys=[key(m) for m in L.meta]; kid={}; kids=np.array([kid.setdefault(k,len(kid)) for k in keys])
    ptkid=np.repeat(kids,2)
    minLc=1e9; minOG=1e9; badLc=0; badOG=0; where=None
    for a in range(len(L.sw)):
        ids=window(L,a,R); inw=np.zeros(len(L.sw),bool); inw[ids]=True
        winchains=set(kids[ids]); inchain=np.isin(kids,list(winchains))
        out_sw=np.nonzero(~inw)[0]
        cont_sw=out_sw[inchain[out_sw]]; oth_sw=out_sw[~inchain[out_sw]]
        pc=np.concatenate([[2*j,2*j+1] for j in cont_sw]).astype(int) if len(cont_sw) else np.array([],int)
        po=np.concatenate([[2*j,2*j+1] for j in oth_sw]).astype(int) if len(oth_sw) else np.array([],int)
        for t in (pts[2*a],pts[2*a+1]):
            if len(pc):
                u=pts[pc,0]-t[0]; v=pts[pc,1]-t[1]
                nw=(u<0)&(v>=0); se=(v<0)&(u>=0)
                if nw.any(): minLc=min(minLc,float(v[nw].min()))
                if se.any(): minLc=min(minLc,float(u[se].min()))
            if len(po):
                d=np.maximum(np.abs(pts[po,0]-t[0]),np.abs(pts[po,1]-t[1]))
                m=float(d.min())
                if m<minOG: minOG=m; where=(a,L.meta[a]['kind'],L.meta[int(po[int(np.argmin(d))])//2]['kind'])
    if verbose: print("R",R,"(RE,G)",(RE,G),"| other-gadget points: min L-inf distance to a central point %.2f (need >= R+6.4 = %.1f) at %s | continuation points of chains through the window: min long coordinate of NW/SE points %.2f (effective R_FF)"%(minOG,R+6.4,where,minLc),flush=True)
    return minOG,minLc
if __name__=="__main__":
    ffcheck2(float(sys.argv[1]),int(sys.argv[2]),int(sys.argv[3]))
