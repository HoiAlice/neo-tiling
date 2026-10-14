import itertools, sys
from core import *
from multiprocessing import Pool
EPS=float(sys.argv[1]) if len(sys.argv)>1 else 0.2
def ev(args):
    d,d2,ox,oy,ytop = args
    pts=[(d,d),(0,0),(ox+d2,oy+d2),(ox,oy)]
    if len(set(pts))<4: return None
    y=np.array([ytop[0],1.0,ytop[1],1.0])
    a=EPS*np.array(pts,float)
    conf=conflicts_of(y)
    try: k1=conf.index((0,1)); k2=conf.index((2,3))
    except: return None
    tb={}
    for s1 in (0,1):
        for s2 in (0,1):
            r=solve_dom(a,y,fixed={k1:s1,k2:s2},conflicts=conf,time_limit=10)
            tb[(s1,s2)]=r[2]
    I=tb[(0,0)]+tb[(1,1)]-tb[(0,1)]-tb[(1,0)]
    return (I,args,tb)
if __name__=="__main__":
    jobs=[(d,d2,ox,oy,yt) for d in (1,2,3) for d2 in (1,2,3) for ox in range(-5,6) for oy in range(-5,6) for yt in [(2,2),(2,3)]]
    with Pool(8) as p: res=[r for r in p.map(ev,jobs,chunksize=8) if r]
    res.sort(key=lambda r:-r[0])
    print("antiferro top"); 
    for r in res[:10]: print(round(r[0],4), r[1], {k:round(v,3) for k,v in r[2].items()})
    print("ferro top")
    for r in res[-5:]: print(round(r[0],4), r[1], {k:round(v,3) for k,v in r[2].items()})
