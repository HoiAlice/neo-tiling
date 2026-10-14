from k3 import *
if __name__=="__main__":
    sw,idx=build(); A,Y,conf,ks=cx2.setup(sw); Qs=[]
    for fx in [(0,0,1),(0,1,0),(0,1,1),(1,0,0),(1,0,1),(1,1,0)]:
        r=solve_dom(A,Y,fixed=dict(zip([ks[i] for i in idx],fx)),conflicts=conf,time_limit=500)
        cm,u=polish_margin(A,conf,r[1],1e-6); Qs.append(np.exp(u)); print(fx,round(cm,5),flush=True)
    for rt in (1.9,1.3):
        y=find_y(Qs,Y,1e-6,rt); print("ratio cap",rt,"feasible",y is not None,flush=True)
        if y is not None:
            print("max/min",y.max()/y.min(),"weak",[weakly_solvable(Q,y) for Q in Qs],flush=True)
            np.savez("k3_yfound_%s.npz"%rt,y=y,Y=Y)
