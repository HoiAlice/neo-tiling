import sys, pickle, itertools, numpy as np, cx2
from layout import *
from iso_scipy import iso_cost
def get(path="lay_k4_best.pkl"):
    key,rs,tr,sol,inst=pickle.load(open(path,"rb"))
    return sol,inst,levels(inst["sw"])
def build_chains(sol,inst):
    """per segment: (list of global switch indices A->B, list of link kinds A->B)"""
    segs=sol["segs"]; choice=inst["choice"]; off=len(inst["pos"]); chains={}
    by_edge={}
    for k,((p,q,e),op,n,L) in enumerate(segs): by_edge.setdefault(e,[]).append(k)
    # offsets: internal lists appended in order of parts after the vertices; parts order = choice iteration order of edges then segments
    pos=off
    starts={}
    for e,(cost,wk,combo) in choice.items():
        for k,(l,st) in zip(by_edge[e],combo):
            (p,q,_),op,n,L=segs[k]
            cnt = (len(st)-1+0) if op["kind"]=="pure" else (n+l)
            if op["kind"]=="pure": cnt=len(st)-1
            starts[k]=(pos,cnt,l,wk); pos+=cnt
    for e,(cost,wk,combo) in choice.items():
        for k,(l,st) in zip(by_edge[e],combo):
            (p,q,_),op,n,L=segs[k]; s0,cnt,l,wk=starts[k]
            A,B=op["A"],op["B"]; vi=inst["vidx"]
            arm=['W' if (k==wk and i==(l-1)//2) else 'AF' for i in range(l)]
            if op["kind"]=="pure":
                ids=[vi[A]]+list(range(s0,s0+cnt))+[vi[B]]; kinds=arm
            else:
                V=list(range(s0,s0+n)); U=list(range(s0+n,s0+n+l))     # u0..u_{l-1}
                ids=[vi[A]]+U[::-1]+V+[vi[B]]; kinds=arm[::-1]+['C']*(n+1)
                assert len(ids)==len(kinds)+1,(len(ids),len(kinds))
            chains[k]=(ids,kinds,A,B,(k==wk))
    return chains,by_edge
def propagate(chain,a,b):
    ids,kinds,A,B,hasweak=chain
    exp=a
    for kd in kinds:
        if kd in('AF','W'): exp^=1
    bits=[a]; cur=a; kinks=[]
    mismatch=(exp!=b)
    placed=False
    for i,kd in enumerate(kinds):
        if kd=='C': nxt=cur
        elif kd=='W' and mismatch and not placed: nxt=cur; placed=True; kinks.append(('W',i))
        elif kd=='AF' and mismatch and not hasweak and not placed: nxt=cur; placed=True; kinks.append(('S',i))
        else: nxt=cur^1
        bits.append(nxt); cur=nxt
    return bits,kinks
def intended(sol,inst,chains,by_edge,pat,n_orig=4):
    segs=sol["segs"]; vbit={v:pat[v] for v in range(n_orig)}
    nbits=len(inst["sw"]); sig=[None]*nbits; strong=0; weak=0
    for e,ks in by_edge.items():
        verts=[]; 
        for k in ks:
            for v in segs[k][0][:2]:
                if v not in verts: verts.append(v)
        relay=[v for v in verts if v>=n_orig]
        best=None
        for rb in ([0,1] if relay else [None]):
            vb=dict(vbit)
            if relay: vb[relay[0]]=rb
            tot=[];res=[]
            for k in ks:
                ids,kinds,A,B,hw=chains[k]
                bits,kinks=propagate(chains[k],vb[A],vb[B]); res.append((ids,bits,kinks))
                for kk in kinks: tot.append(kk[0])
            cost=sum(10 if t=='S' else 1 for t in tot)
            if best is None or cost<best[0]: best=(cost,res,tot)
        for ids,bits,kinks in best[1]:
            for i,b in zip(ids,bits): sig[i]=b if sig[i] is None else sig[i]
        strong+=best[2].count('S'); weak+=best[2].count('W')
    for v in range(n_orig): sig[inst["vidx"][v]]=pat[v]
    return sig,strong,weak
def ub_cost(A,Y,conf,ks,sig,verbose=False):
    n=len(sig); T=len(A)
    own={k:sig[i] for i,k in enumerate(ks)}
    assign=[]
    for k,(t,s) in enumerate(conf):
        if k in own: assign.append(own[k])
        else:
            m0=A[s,0]-A[t,0]; m1=A[s,1]-A[t,1]; assign.append(0 if m0>=m1 else 1)
    edges=[[],[]]
    for (t,s),c in zip(conf,assign): edges[c].append((t,s))
    c0,_=iso_cost(A[:,0],edges[0]); c1,_=iso_cost(A[:,1],edges[1])
    return c0+c1
if __name__=="__main__":
    sol,inst,lv=get(); A,Y,conf,ks=cx2.setup(lv)
    chains,by_edge=build_chains(sol,inst)
    K4=[(0,1),(0,2),(0,3),(1,2),(1,3),(2,3)]
    res={}
    for pat in itertools.product((0,1),repeat=4):
        sig,strong,weak=intended(sol,inst,chains,by_edge,pat)
        c=ub_cost(A,Y,conf,ks,sig)
        uncut=sum(1 for (u,v) in K4 if pat[u]==pat[v])
        res[pat]=(c,uncut,strong,weak); print(pat,"uncut",uncut,"kinks strong/weak",strong,weak,"UB",round(c,5),flush=True)
    base=min(v[0]-0.0505*v[1] for v in res.values())
    print("excess over (S0 + J_e*uncut) with S0=min:",{p:round(v[0]-0.05063*v[1]-base,4) for p,v in res.items()})
