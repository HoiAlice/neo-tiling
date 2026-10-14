from cprime import *
import json
if __name__=="__main__":
    sw,idx=build_c()
    A,Y,conf,ks=cx2.setup(sw); Qs=[]
    for fx in [(0,1,0,1),(0,1,1,0),(1,0,0,1),(1,0,1,0)]:
        r=solve_dom(A,Y,fixed=dict(zip([ks[i] for i in idx],fx)),conflicts=conf,time_limit=500)
        cm,u=polish_margin(A,conf,r[1],1e-6); Qs.append(np.exp(u)); print(fx,round(cm,5),flush=True)
    y=find_y(Qs,Y,1e-6,100)
    np.savez("cprime_yfound.npz",y=y,Y=Y,Qs=np.array(Qs))
    print("ratio",y.max()/y.min()); print("y levels",sorted(set(np.round(y/y.min(),5))))
    print("weak",[weakly_solvable(Q,y) for Q in Qs])
