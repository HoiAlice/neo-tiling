import sys, itertools, numpy as np
import cx2, term
from core import solve_dom, polish_margin, weakly_solvable
from ysolve import find_y
g=0.01; SV=0.02; B0=1.0
def lev(base): return (base+g, base)
def vertex_sw(bx,by,base):                 # vertex centre switch d=5, bottom (bx,by)
    t,b=lev(base); return (bx,by,5,t,b)
def corner_edge(K,dirU,n,armsteps,base):
    """V chain j=0..n-1 from K going NE (d=5), then V-end vertex at j=n (returned separately).
    U arm from K along dirU with steps armsteps; last step ends at the A vertex (returned separately)."""
    sw=[]
    for j in range(n):
        sw.append((K[0]+j,K[1]+j,5,base+g-SV*(j+1),base-SV*(j+1)))
    sw.append((K[0],K[1],4)+lev(base))     # u0 at K
    p=0
    for st in armsteps[:-1]:
        p+=st; sw.append((K[0]+dirU[0]*p,K[1]+dirU[1]*p,4)+lev(base))
    P=sum(armsteps)
    Bv=(K[0]+n,K[1]+n)                      # V-end vertex bottom
    Av=(K[0]+dirU[0]*P-0.5,K[1]+dirU[1]*P-0.5)
    return sw,Bv,Av
def build(n=6,arm=(3,3.75,3)):
    P=sum(arm)
    sw=[]
    K1=(0.0,0.0); K2=(2*P,-2*P)
    e1,Y,X1=corner_edge(K1,(1,-1),n,arm,B0)
    e2,Z,X2=corner_edge(K2,(-1,1),n,arm,B0)
    assert abs(X1[0]-X2[0])<1e-9 and abs(X1[1]-X2[1])<1e-9
    sw+=e1+e2
    iX=len(sw); sw.append(vertex_sw(X1[0],X1[1],B0))
    yb=B0-SV*(n+1)
    iY=len(sw); sw.append(vertex_sw(Y[0],Y[1],yb))
    iZ=len(sw); sw.append(vertex_sw(Z[0],Z[1],yb))
    # pure U edge Y -> Z along (1,-1) in centre coordinates; vertex centre = bottom+2.5
    m=2*P; s=(m-3.75)/6
    steps=[s,s,s,3.75,s,s,s]
    cy=(Y[0]+2.5,Y[1]+2.5); p=0
    for st in steps[:-1]:
        p+=st; c=(cy[0]+p,cy[1]-p); sw.append((c[0]-2,c[1]-2,4)+lev(yb))
    zc=(Z[0]+2.5,Z[1]+2.5); assert abs(zc[0]-(cy[0]+m))<1e-9 and abs(zc[1]-(cy[1]-m))<1e-9
    return sw,[iX,iY,iZ]
def run(fx_list,tl=500):
    sw,idx=build(); A,Y,conf,ks=cx2.setup(sw); return sw,idx,A,Y,conf,ks
if __name__=="__main__":
    sw,idx=build()
    print("switches",len(sw),"terminals",idx)
    for i,s in enumerate(sw): print(i,tuple(round(float(x),3) for x in s))
    A,Y,conf,ks=cx2.setup(sw); print("points",len(A),"conflicts",len(conf),flush=True)
