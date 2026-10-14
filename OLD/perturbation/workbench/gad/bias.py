import itertools, sys
from core import *
EPS=0.2
def table(sw, eps=EPS):
    """sw: list of (cx,cy,g0,g1): bottom at (cx,cy), top at (cx+g0,cy+g1) in grid units."""
    n=len(sw); pts=[]
    for (cx,cy,g0,g1) in sw: pts += [(cx+g0,cy+g1),(cx,cy)]
    y=np.array([2.0,1.0]*n); a=eps*np.array(pts,float); conf=conflicts_of(y)
    ks=[conf.index((2*i,2*i+1)) for i in range(n)]
    tb={}
    for sg in itertools.product((0,1),repeat=n):
        r=solve_dom(a,y,fixed=dict(zip(ks,sg)),conflicts=conf,time_limit=20)
        tb[sg]=r[2]
    return tb
def fit(tb,n,pairs=None):
    pairs = pairs if pairs is not None else list(itertools.combinations(range(n),2))
    rows=[];rhs=[]
    for k,v in tb.items():
        s=[1-2*x for x in k]
        rows.append([1]+[s[i] for i in range(n)]+[s[i]*s[j] for i,j in pairs]); rhs.append(v)
    A=np.array(rows,float); c=np.linalg.lstsq(A,np.array(rhs),rcond=None)[0]
    return c, float(max(abs(A@c-np.array(rhs))))
if __name__=="__main__":
    for g0,g1 in [(4,4),(4,5),(4,6),(5,4)]:
        tb=table([(0,0,g0,g1)]); print("single",g0,g1,{k:round(v,5) for k,v in tb.items()})
