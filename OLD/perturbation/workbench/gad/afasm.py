"""Alternative attachment: V wire's SW end -> corner -> U2 wire with weak link INSIDE the U segment. No weak attachment to V."""
from yv2 import *
import term, cx2, sys, itertools
def build(g=0.01,h0=0.01,h2=0.04,aw=3.75,nVs=4,off=0.01,nU2=4,rev=False):
    sw=[]
    for t in (-1.5,-0.5,0.5,1.5,2.5): sw.append((3*t,-3*t,4,1+g,1))
    tb=2.5+aw/3; sw.append((3*tb,-3*tb,4,1+g,1))
    iA,iB=0,5
    for s in range(-nVs,nVs+1):
        sh = h0*(-s) if s<0 else -h2*s
        sw.append((s-0.5,s-0.5,5,1+g+sh,1+sh))
    iD=len(sw)-1
    # corner U2 wire: first U2 switch coincides with V_{-nVs} bottom, going NW
    bx=-nVs-0.5; by=bx; sh=h0*nVs
    top=1+g+sh+off
    # U2 chain from the corner outward: positions bx-3k, by+3k ; last one beyond weak link
    pos=[(bx-3*k,by+3*k) for k in range(nU2)]
    # weak link at the far end: last spacing aw
    pos[-1]=(bx-3*(nU2-2)-aw,by+3*(nU2-2)+aw)
    for p in pos: sw.append((p[0],p[1],4,top,top-g))
    iC=len(sw)-1
    return sw,(iA,iB,iC,iD)
if __name__=="__main__":
    off=float(sys.argv[1]) if len(sys.argv)>1 else 0.01
    sw,idx=build(off=off)
    for i,s in enumerate(sw): print(i,tuple(round(float(v),3) for v in s))
    tb=term.term_table(sw,list(idx),procs=10); mn=min(tb.values())
    print("min",round(mn,5))
    for s,v in sorted(tb.items()):
        unsat=(s[0]==s[1])+(s[2]!=s[3]) if False else None
        print(s,"excess",round(v-mn,5),flush=True)
