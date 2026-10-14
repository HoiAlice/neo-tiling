from cx3 import *
import cx2
def check(sw,fx_idx,fx,m=1e-6,ycomp=0.1):
    A,Y0,conf,ks=cx2.setup(sw); Y=1.5+(Y0-1.5)*ycomp
    r=solve_dom(A,Y0,fixed=dict(zip([ks[i] for i in fx_idx],fx)),conflicts=conf,time_limit=120)
    cm,u=polish_margin(A,conf,r[1],m); Q=np.exp(u)
    # dominance violations over ALL conflicts
    viol=[(t,s) for (t,s) in conflicts_of(Y0) if (Q[t]>Q[s]).all()]
    return cm,viol,weakly_solvable(Q,Y),Q,Y
if __name__=="__main__":
    # P3 gadget known True
    sw=[(0,0,4,2,1),(-3,3,4,2,1),(-6,6,4,2,1)]
    cm,v,w,_,_=check(sw,[0],[0]); print("P3",cm,len(v),w)
    sw=build2(2,3,3,4,1,5,1.0)
    cm,v,w,Q,Y=check(sw,[0],[0]); print("2U3V",cm,v,w)
    for (nu,nv) in [(2,5),(4,3),(4,5)]:
        sw=build2(nu,nv,3,4,1,5,1.0)
        cm,v,w,Q,Y=check(sw,[0],[0]); print(nu,nv,round(cm,5),"viol",v,"weak",w,flush=True)
