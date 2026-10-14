import itertools, sys
from core import *
EPS=0.2
def table(sw, eps=EPS, tl=30):
    """sw: list of (bx,by,d,ytop,ybot). returns dict sigma-tuple -> cost (min over free conflicts)."""
    pts=[];y=[]
    for bx,by,d,yt,yb in sw:
        pts+=[(bx+d,by+d),(bx,by)]; y+=[yt,yb]
    a=eps*np.array(pts,float); y=np.array(y,float); conf=conflicts_of(y)
    ks=[conf.index((2*i,2*i+1)) for i in range(len(sw))]
    tb={}
    for sg in itertools.product((0,1),repeat=len(sw)):
        r=solve_dom(a,y,fixed=dict(zip(ks,sg)),conflicts=conf,time_limit=tl)
        tb[sg]=r[2]
    return tb
def show(tb):
    for k,v in sorted(tb.items()): print(" ",''.join(map(str,k)),round(v,5))
if __name__=="__main__":
    a=3;d=4
    for c in (-1,0,1,2,3):
        sw=[(a/2,-a/2,d,2,1),(-a/2,a/2,d,2,1),(c,c,d,2,1)]
        print("c",c); show(table(sw))
