from yv2 import *
import term, cx2, sys, itertools
def run(nU,nV,g=0.05,h2=0.2,dv=5,k=1,a=3,du=4):
    sw=build4(nU,nV,a,du,k,dv,g,g,h2)
    idx=[0,nU-1,nU,nU+nV-1]
    tb=term.term_table(sw,idx,procs=5)
    mn=min(tb.values())
    print(f"nU={nU} nV={nV} g={g} h0=g h2={h2} dv={dv} k={k} a={a} du={du}")
    print("switches (bx,by,d,ytop,ybot):")
    for s in sw: print("  ",tuple(round(float(v),4) for v in s))
    print("min rho_dom = %.6f"%mn)
    print("U_in U_out V_in V_out : excess over min")
    par=(nU-1)%2
    for s,v in sorted(tb.items()):
        valid=(s[1]==(s[0]^par)) and (s[3]==s[2])
        print(s,"valid" if valid else "     ",round(v-mn,5))
    for fx in [s for s in tb if (s[1]==(s[0]^par)) and (s[3]==s[2])]:
        cm,Y,w=wcheck(sw,idx,fx); print("weak solvable at margin-1e-6 optimum, terminals",fx,":",w,"cost",round(cm,6),flush=True)
if __name__=="__main__":
    run(int(sys.argv[1]),int(sys.argv[2]))
