"""y from geometry: y_bottom = F(s_c), y_top = y_bottom + g, s_c = x+y of switch centre (grid units) = bx+by+d."""
import sys; sys.path.insert(0,".")
import numpy as np, cx2, cprime, k3
from core import conflicts_of
g=0.01
def sc(sw): return np.array([bx+by+d for bx,by,d,yt,yb in sw],float)
def y_rule(sw,c,F="lin",gap=g,base=1.0,s0=None):
    s=sc(sw); s0=s.max() if s0 is None else s0
    if F=="lin": fb=base+c*(s0-s)
    elif F=="conc": fb=base+c*(s0-s)-0.01*c*(s0-s)**2/ (s0-s.min())   # concave decreasing (variant)
    elif F=="conv": fb=base+c*(s0-s)+0.01*c*(s0-s)**2/(s0-s.min())
    y=[];  
    for b in fb: y+= [b+gap,b]
    return np.array(y)
def setup_with(sw,Y):
    pts=[]
    for bx,by,dd,yt,yb in sw: pts+=[(bx+dd,by+dd),(bx,by)]
    A=cx2.EPS*np.array(pts,float)
    conf=[(t,u) for (t,u) in conflicts_of(Y) if not (max(A[u,0]-A[t,0],A[u,1]-A[t,1])>=1.2)]
    return A,conf
def build(kind): return cprime.build_c()[0] if kind=="cp" else k3.build()[0]
if __name__=="__main__":
    for kind in ("cp","k3"):
        sw=build(kind); A,Y,conf,ks=cx2.setup(sw); S=set(conf)
        print(kind,"hand-set conflicts",len(S),"s_c range",sc(sw).min(),sc(sw).max())
        for c in (0.011,0.015,0.02,0.03,0.05):
            for F in ("lin","conc"):
                Yr=y_rule(sw,c,F); A2,conf2=setup_with(sw,Yr); R=set(conf2)
                print("  c",c,F,"ratio %.3f"%(Yr.max()/Yr.min()),"conflicts",len(R),"only-hand",len(S-R),"only-rule",len(R-S))
