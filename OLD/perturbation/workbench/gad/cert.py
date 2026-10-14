from cprime import *
import planar
from fractions import Fraction
if __name__=="__main__":
    sw,idx=build_c()
    A,Y,conf,ks=cx2.setup(sw)
    fx=(1,0,1,0)
    r=solve_dom(A,Y,fixed=dict(zip([ks[i] for i in idx],fx)),conflicts=conf,time_limit=500)
    cm,u=polish_margin(A,conf,r[1],1e-6); Q=np.exp(u)
    np.savez("cprime_Q_1010.npz",Q=Q,Y=Y,A=A)
    S=(10,20,21); ii=[2*i+j for i in S for j in (0,1)]
    print("grid pts"); print(np.round(np.log(Q[ii])/0.2,3)); print("y",Y[ii])
    Pf=[tuple(Fraction(float(v)).limit_denominator(10**9) for v in row) for row in Q[ii]]
    res=planar.flow_lp(Pf,[Fraction(float(v)).limit_denominator(10**9) for v in Y[ii]])
    print("feasible",res.feasible,"w",None if res.w is None else np.round(res.w,3))
    print("orig positions"); print(np.round(A[ii]/0.2,2))
