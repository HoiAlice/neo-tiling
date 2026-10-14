"""Layout generator: graph (max degree 3) -> switch list.  Pipeline: MILP over segment types/arms/lengths (milp_layout) -> geometry -> levels y = F(s)."""
import itertools, numpy as np, sys
from milp_layout import solve_layout
G_GAP=0.01; SLOPE=0.02; L0=5.0; WEAK=3.75; SMIN,SMAX=2.6,3.5
def reflect_sw(sw):
    return [(-bx-d,-by-d,d) for (bx,by,d) in sw]
def arm_steps(P,weak):
    """list of link lengths from the corner end to the vertex"""
    if weak is None:       # all strong: choose link count l with P/l in [SMIN,SMAX], prefer 3 links
        for l in range(3,20):
            if SMIN<=P/l<=SMAX: return [P/l]*l
        return None
    l=weak   # number of links (odd) incl the weak middle one
    s=(P-WEAK)/(l-1)
    if not (SMIN<=s<=SMAX): return None
    h=(l-1)//2; return [s]*h+[WEAK]+[s]*h
def ce_switches(typ,Apos,Bpos,n,P,steps):
    """internal switches (bx,by,d) of corner edge; vertex switches NOT included."""
    aa,bb=typ
    base_dir=(1,-1) if aa=="NW" else (-1,1)      # T1/T4 template uses dir (1,-1) for (NW,SW)->T1 ; (SE,SW)->T2 dir (-1,1)
    refl = (bb=="NE")
    # template (non reflected) is T1 for (NW,SW),(SE,NE) ; T2 for (SE,SW),(NW,NE)
    if not refl: dirv=(1,-1) if aa=="NW" else (-1,1)
    else: dirv=(1,-1) if aa=="SE" else (-1,1)     # (SE,NE)=reflect(T1) ; (NW,NE)=reflect(T2)
    K=(0.0,0.0); sw=[]
    for j in range(n): sw.append((K[0]+j,K[1]+j,5))
    sw.append((K[0],K[1],4)); p=0
    for st in steps[:-1]:
        p+=st; sw.append((K[0]+dirv[0]*p,K[1]+dirv[1]*p,4))
    a0=(K[0]+dirv[0]*P-0.5,K[1]+dirv[1]*P-0.5); b0=(K[0]+n,K[1]+n)
    if refl:
        sw=reflect_sw(sw); a0=(-a0[0]-5,-a0[1]-5); b0=(-b0[0]-5,-b0[1]-5)
    shift=(Apos[0]-a0[0],Apos[1]-a0[1])
    chk=(b0[0]+shift[0],b0[1]+shift[1])
    assert abs(chk[0]-Bpos[0])<1e-6 and abs(chk[1]-Bpos[1])<1e-6,(typ,chk,Bpos)
    return [(bx+shift[0],by+shift[1],d) for (bx,by,d) in sw]
def pure_switches(Ppos,Qpos,m,steps):
    c=(Ppos[0]+2.5,Ppos[1]+2.5); p=0; sw=[]
    for st in steps[:-1]:
        p+=st; cc=(c[0]+p,c[1]-p); sw.append((cc[0]-2,cc[1]-2,4))
    p+=steps[-1]; assert abs(Ppos[0]+p-Qpos[0])<1e-6 and abs(Ppos[1]-p-Qpos[1])<1e-6,(Ppos,Qpos,p)
    return sw
def levels(sw):
    out=[]
    for (bx,by,d) in sw:
        sc=bx+by+d; b=round(L0-SLOPE*sc,9); out.append((bx,by,d,round(b+G_GAP,9),b))
    return out
def overlaps(parts,tol=0.0):
    """parts: list of (label, [(bx,by,d)...]) ; returns list of (labelA,labelB,count)"""
    found={}
    for (la,sa),(lb,sb) in itertools.combinations(parts,2):
        c=0
        for (x1,y1,d1) in sa:
            for (x2,y2,d2) in sb:
                if abs((x1+d1/2)-(x2+d2/2))<(d1+d2)/2-tol and abs((y1+d1/2)-(y2+d2/2))<(d1+d2)/2-tol: c+=1
        if c: found[(la,lb)]=c
    return found

def link_options(P,weak,kind):
    """possible (link count, steps) for a segment of arm length P"""
    opts=[]
    if weak:
        for l in range(3,16,2):
            st=arm_steps(P,l)
            if st: opts.append((l,st))
    else:
        for l in range(3,20):
            if SMIN<=P/l<=SMAX: opts.append((l,[P/l]*l))
    return opts
def build_instance(sol,edges,relay_edges,nv_orig,verbose=True):
    verts=sol["verts"]
    pos=[((s-t)/2,(s+t)/2) for (s,t) in verts]
    segs=sol["segs"]
    by_edge={}
    for k,((p,q,e),op,n,L) in enumerate(segs): by_edge.setdefault(e,[]).append(k)
    choice={}
    for e,ks in by_edge.items():
        best=None
        for wk in ks:
            per=[]
            for k in ks:
                P=segs[k][3]
                per.append(link_options(P,k==wk,segs[k][1]["kind"]))
            if any(len(o)==0 for o in per): continue
            for combo in itertools.product(*per):
                if sum(c[0] for c in combo)%2==1:
                    cost=sum(c[0] for c in combo)
                    if best is None or cost<best[0]: best=(cost,wk,combo)
        if best is None: return None,"no link choice for edge %d"%e
        choice[e]=best
    sw=[]; parts=[]; vidx={}
    for v,(x,y) in enumerate(pos):
        vidx[v]=len(sw); sw.append((x,y,5)); parts.append(("V%d"%v,[(x,y,5)]))
    for e,(cost,wk,combo) in choice.items():
        for k,(l,st) in zip(by_edge[e],combo):
            (p,q,_),op,n,L=segs[k]
            A,B=op["A"],op["B"]
            if op["kind"]=="pure":
                internal=pure_switches(pos[A],pos[B],L,st)
            else:
                internal=ce_switches((op["aa"],op["bb"]),pos[A],pos[B],n,L,st)
            parts.append(("S%d(e%d)"%(k,e),internal)); sw+=internal
    return dict(sw=sw,parts=parts,choice=choice,pos=pos,vidx=vidx,nv_total=len(verts)),None
def bad_collisions(inst,edges,relay_edges,nv_orig):
    """overlapping part pairs that do not share a vertex (segment-segment) or are not incident (vertex-segment)"""
    ov=overlaps(inst['parts']); bad={}
    return ov
if __name__=="__main__":
    K4=[(0,1),(0,2),(0,3),(1,2),(1,3),(2,3)]
    sol=solve_layout(4,K4,{0},time_limit=60)
    inst,err=build_instance(sol,K4,{0},4)
    print(err)
    if inst:
        print("switches",len(inst["sw"]))
        for e,(c,wk,combo) in inst["choice"].items(): print("edge",e,"weak seg",wk,"links",[x[0] for x in combo])
        ov=overlaps(inst["parts"]); 
        print("overlapping part pairs:",ov)

def collisions(inst,sol):
    segs=sol["segs"]; pos=inst["pos"]
    sw_of={lab:sw for lab,sw in inst["parts"]}
    bad=[]
    labs=[lab for lab,_ in inst["parts"]]
    def vs(lab):
        if lab.startswith("V"): return {int(lab[1:])}
        k=int(lab[1:lab.index("(")]); (p,q,e)=segs[k][0]; return {p,q}
    for la,lb in itertools.combinations(labs,2):
        sa,sb=sw_of[la],sw_of[lb]; shared=vs(la)&vs(lb)
        if la.startswith("V") and lb.startswith("V"): 
            continue
        for (x1,y1,d1) in sa:
            for (x2,y2,d2) in sb:
                if abs((x1+d1/2)-(x2+d2/2))<(d1+d2)/2 and abs((y1+d1/2)-(y2+d2/2))<(d1+d2)/2:
                    c1=(x1+d1/2,y1+d1/2); c2=(x2+d2/2,y2+d2/2)
                    ok=False
                    for v in shared:
                        pv=(pos[v][0]+2.5,pos[v][1]+2.5)
                        if max(abs(c1[0]-pv[0]),abs(c1[1]-pv[1]))<=7.5 and max(abs(c2[0]-pv[0]),abs(c2[1]-pv[1]))<=7.5: ok=True
                    if not ok: bad.append((la,lb,c1,c2)); 
    return bad
def random_search(nv,edges,rsets,trials=20,tl=40):
    best=None
    for rs in rsets:
        for tr in range(trials):
            sol=solve_layout(nv,edges,set(rs),time_limit=tl,seed=tr+1)
            if sol is None: continue
            inst,err=build_instance(sol,edges,set(rs),nv)
            if inst is None: continue
            bc=collisions(inst,sol)
            key=len(bc)
            if best is None or key<best[0]:
                best=(key,rs,tr,sol,inst); print("relays",rs,"seed",tr+1,"collisions",key,"switches",len(inst['sw']),flush=True)
            if key==0: return best
    return best
