from asm import *
from ysolve import find_y
import cx2
if __name__=="__main__":
    sw,idx=build_asm(aw=3.4)
    nVs=4; s=-nVs; sh=0.01*nVs-0.04
    cen=(s+2,s+2+4.5)
    sw[-1]=(cen[0]-2,cen[1]-2,4,1+0.01+sh,1+sh)
    A,Y,conf,ks=cx2.setup(sw)
    tb=term.term_table(sw,list(idx),procs=6); mn=min(tb.values())
    for s_,v in sorted(tb.items()): print(s_,"unsat",(s_[0]==s_[1])+(s_[2]==s_[3]),round(v-mn,5),flush=True)
    Qs=[]
    for fx in [(0,1,0,1),(0,1,1,0),(1,0,0,1),(1,0,1,0)]:
        r=solve_dom(A,Y,fixed=dict(zip([ks[i] for i in idx],fx)),conflicts=conf,time_limit=120)
        cm,u=polish_margin(A,conf,r[1],1e-6); Qs.append(np.exp(u)); print(fx,"cost",round(cm,5))
    for i,Q in enumerate(Qs): print("combo",i,"y-feasible:",find_y([Q],Y,1e-6,100) is not None)
    print("joint",find_y(Qs,Y,1e-6,100) is not None)
    y=find_y(Qs,Y,1e-6,100)
    if y is not None: print("weak solvable at found y:",[weakly_solvable(Q,y) for Q in Qs])
