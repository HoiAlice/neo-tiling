from cx3 import *
import cx2
if __name__=="__main__":
    nU,nV=4,5
    sw=build2(nU,nV,3,4,1,5,1.0)
    A,Y,conf,ks=cx2.setup(sw)
    Y0=Y.copy(); Y=1.5+(Y-1.5)*0.1; print('y range',Y.min(),Y.max())
    # terminal pattern valid: U_in=0 U_out=1 V=0 V=0
    for fx in [(0,1,0,0),(1,0,1,1)]:
        idx=[0,nU-1,nU,nU+nV-1]
        r=solve_dom(A,Y,fixed=dict(zip([ks[i] for i in idx],fx)),conflicts=conf,time_limit=120)
        c,sg=r[2],r[1]
        print("terminals",fx,"rho_dom",round(c,6))
        for m in (1e-6,1e-5):
            cm,u=polish_margin(A,conf,sg,m); Q=np.exp(u)
            print(" margin",m,"cost",round(cm,6),"weakly solvable:",weakly_solvable(Q,Y))
    # negative control: original P
    print("original P weakly solvable (expect False):",weakly_solvable(np.exp(A),Y))
