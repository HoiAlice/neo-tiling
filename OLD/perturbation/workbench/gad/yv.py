from cx3 import *
import cx2
def build3(nU,nV,a,du,k,dv,g,h,base=1.0):
    sw=[]
    for i in range(nU):
        t=i-(nU-1)/2
        sw.append((a*t-du/2+2,-a*t-du/2+2,du,base+g,base))
    for j in range(nV):
        s=j-(nV-1)/2
        sw.append((k*s-dv/2+2,k*s-dv/2+2,dv,base+g-s*h,base-s*h))
    return sw
def wcheck(sw,idx,fx,m=1e-6):
    A,Y,conf,ks=cx2.setup(sw)
    r=solve_dom(A,Y,fixed=dict(zip([ks[i] for i in idx],fx)),conflicts=conf,time_limit=120)
    cm,u=polish_margin(A,conf,r[1],m); Q=np.exp(u)
    return cm,Y,weakly_solvable(Q,Y)
if __name__=="__main__":
    import sys
    nU,nV=int(sys.argv[1]),int(sys.argv[2])
    for g,h in [(0.1,0.1),(0.1,0.2),(0.1,0.3),(0.05,0.2),(0.02,0.2)]:
        sw=build3(nU,nV,3,4,1,5,g,h,base=1.0)
        idx=[0,nU-1,nU,nU+nV-1]
        out=[]
        for fx in [(0,(nU-1)%2,0,0),(1,1-(nU-1)%2,0,0),(0,(nU-1)%2,1,1),(1,1-(nU-1)%2,1,1)]:
            cm,Y,w=wcheck(sw,idx,fx); out.append((round(cm,4),w))
        print("g,h",g,h,"Y range",Y.min(),Y.max(),out,flush=True)
