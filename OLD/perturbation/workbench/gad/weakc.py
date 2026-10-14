from yv import *
import cx2
if __name__=="__main__":
    g=0.05
    steps=[3,3,3.75,3,3]   # 6 switches; weak coupler is link 3 (0-indexed 2)
    pos=[0]
    for s in steps: pos.append(pos[-1]+s)
    sw=[(-p,p,4,1+g,1) for p in pos]
    tb=cx2.full_table(sw,4)
    mn=min(tb.values())
    n=len(sw)
    print("min",round(mn,5))
    for s,v in sorted(tb.items(), key=lambda x:x[1])[:8]:
        kinks=[i for i in range(n-1) if s[i]==s[i+1]]
        print(''.join(map(str,s)),"kinks at links",kinks,round(v-mn,5))
    # weak solvability at the optimum for the alternating phase, and a 1-kink at the weak link
    A,Y,conf,ks=cx2.setup(sw)
    for pat in [(0,1,0,1,0,1),(0,1,0,0,1,0)]:
        r=solve_dom(A,Y,fixed=dict(zip(ks,pat)),conflicts=conf,time_limit=60)
        cm,u=polish_margin(A,conf,r[1],1e-6); print(pat,"cost",round(cm,6),"weak solvable:",weakly_solvable(np.exp(u),Y),flush=True)
