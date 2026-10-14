# (A) ferro chain with y-separated levels; (B) rho_dom vs full weak solvability for biased AF chain
from bias import *
import bias
from core import polish_margin, weakly_solvable
def table_y(sw, yv, eps=EPS):
    n=len(sw); pts=[]
    for (cx,cy,g0,g1) in sw: pts += [(cx+g0,cy+g1),(cx,cy)]
    y=np.array(yv,float); a=eps*np.array(pts,float); conf=conflicts_of(y)
    ks=[conf.index((2*i,2*i+1)) for i in range(n)]
    tb={}
    for sg in itertools.product((0,1),repeat=n):
        tb[sg]=solve_dom(a,y,fixed=dict(zip(ks,sg)),conflicts=conf,time_limit=20)[2]
    return tb
if __name__=="__main__":
    G1=(4,5)
    for step in [(1,1),(2,2),(3,3)]:
        n=4; sw=[(step[0]*i,step[1]*i)+G1 for i in range(n)]
        yv=[]
        for i in range(n): c=-0.5*i; yv+=[c+1,c]
        tb=table_y(sw,yv); c1,e1=fit(tb,n,[(i,i+1) for i in range(n-1)]); c2,e2=fit(tb,n)
        print("ferro y-sep",step,"E0=%.4f h=%s J=%s NNresid=%.2e allresid=%.2e"%(c1[0],np.round(c1[1:1+n],4),np.round(c1[1+n:],4),e1,e2))
    # (B) full solvability of margin-polished optimum, AF mixed chain n=4
    n=4; sw=[(-3*i,3*i)+((4,5) if i%2==0 else (5,4)) for i in range(n)]
    pts=[]
    for (cx,cy,g0,g1) in sw: pts += [(cx+g0,cy+g1),(cx,cy)]
    a=EPS*np.array(pts,float); y=np.array([2.,1.]*n); conf=conflicts_of(y)
    r=solve_dom(a,y,conflicts=conf); sigma=r[1]
    print("AF mixed n=4 rho_dom=%.5f (exact polish %.5f)"%(r[2],r[2]))
    for m in [1e-4,1e-6,1e-7]:
        cost,u=polish_margin(a,conf,sigma,m)
        Q=np.exp(u)
        print(" margin",m,"cost %.6f"%cost,"weakly solvable:",weakly_solvable(Q,y))
    # also asymmetric single switch & pair
    for sw2 in [[(0,0,4,5)],[(0,0,4,5),(-3,3,5,4)]]:
        n2=len(sw2); pts=[]
        for (cx,cy,g0,g1) in sw2: pts += [(cx+g0,cy+g1),(cx,cy)]
        a=EPS*np.array(pts,float); y=np.array([2.,1.]*n2); conf=conflicts_of(y)
        r=solve_dom(a,y,conflicts=conf); cost,u=polish_margin(a,conf,r[1],1e-6)
        print(sw2,"dom %.5f margin-cost %.6f solvable %s"%(r[2],cost,weakly_solvable(np.exp(u),y)))
