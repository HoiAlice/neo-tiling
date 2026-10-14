from asm import *
from ysolve import find_y
import cx2
if __name__=="__main__":
    sw,idx=build_asm()
    A,Y,conf,ks=cx2.setup(sw)
    Qs=[];
    for fx in [(0,1,0,1),(0,1,1,0),(1,0,0,1),(1,0,1,0)]:
        r=solve_dom(A,Y,fixed=dict(zip([ks[i] for i in idx],fx)),conflicts=conf,time_limit=120)
        cm,u=polish_margin(A,conf,r[1],1e-6); Qs.append(np.exp(u))
    y=find_y(Qs,Y)
    print("y found:",None if y is None else np.round(y,4))
    if y is not None:
        print("all weakly solvable at new y:",[weakly_solvable(Q,y) for Q in Qs])
        # same order pattern => same conflicts
        print("same order:",all((np.sign(Y[i]-Y[j])==np.sign(y[i]-y[j])) for i in range(len(Y)) for j in range(len(Y))))
