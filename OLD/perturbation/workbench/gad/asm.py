from yv2 import *
import term, cx2, sys, itertools
def build_asm(g=0.01,h0=0.01,h2=0.04,aw=3.75,nVs=4,aC=4.25):
    sw=[]
    # U: t=-1.5..2.5, then B
    for t in (-1.5,-0.5,0.5,1.5,2.5): sw.append((3*t,-3*t,4,1+g,1))
    tb=2.5+aw/3; sw.append((3*tb,-3*tb,4,1+g,1))        # B (weak link)
    iA,iB=0,5
    # V: s=-nVs..nVs
    for s in range(-nVs,nVs+1):
        sh = h0*(-s) if s<0 else -h2*s
        sw.append((s-0.5,s-0.5,5,1+g+sh,1+sh))
    iD=len(sw)-1
    # C attached NW of first V switch (center (s+2,s+2) with s=-nVs)
    c=(-nVs+2.5-0.5-aC, -nVs+2.5-0.5+aC); sh=h0*nVs
    sw.append((c[0]-2,c[1]-2,4,1+g+sh,1+sh)); iC=len(sw)-1
    return sw,(iA,iB,iC,iD)
if __name__=="__main__":
    sw,idx=build_asm()
    for i,s in enumerate(sw): print(i,tuple(round(float(v),3) for v in s))
    tb=term.term_table(sw,list(idx),procs=6); mn=min(tb.values())
    print("min",round(mn,5))
    for s,v in sorted(tb.items()):
        unsat=(s[0]==s[1])+(s[2]==s[3])
        print(s,"unsat",unsat,"excess",round(v-mn,5),flush=True)
    for fx in [s for s in tb if s[0]!=s[1] and s[2]!=s[3]]:
        cm,Y,w=wcheck(sw,list(idx),fx); print("weak",fx,w,round(cm,5),flush=True)
