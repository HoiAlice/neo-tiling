from bias import *
from core import polish_margin, weakly_solvable
def run(sw,label):
    n=len(sw); pts=[]
    for (cx,cy,g0,g1) in sw: pts += [(cx+g0,cy+g1),(cx,cy)]
    a=EPS*np.array(pts,float); y=np.array([2.,1.]*n); conf=conflicts_of(y)
    r=solve_dom(a,y,conflicts=conf); sg=r[1]
    cost,u=polish_margin(a,conf,sg,1e-6)
    viol=max(min(u[s,i]-u[t,i] for _ in [0]) for (t,s),i in zip(conf,sg)) 
    worst=min(u[s,i]-u[t,i] for (t,s),i in zip(conf,sg))
    print(label,"dom %.5f marg %.5f minslack %.2e solvable %s"%(r[2],cost,worst,weakly_solvable(np.exp(u),y)))
run([(-3*i,3*i,4,4) for i in range(3)],"AF n3 sym")
run([(-3*i,3*i,4,4) for i in range(4)],"AF n4 sym")
run([(-3*i,3*i)+((4,5) if i%2==0 else (5,4)) for i in range(3)],"AF n3 mixed")
run([(-3*i,3*i)+((4,5) if i%2==0 else (5,4)) for i in range(4)],"AF n4 mixed")
run([(-3*i,3*i)+(4,5) for i in range(4)],"AF n4 (4,5)")
