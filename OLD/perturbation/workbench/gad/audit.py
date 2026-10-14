"""audit.py -- explicit tilings P1, P2 of scheme layouts, relations with credits, block types, Lemma C (averaged) check.
Chain model: for every edge e the chain  star_i, arm_i (a_1..a_n), track (V_0..V_N), arm_j reversed, star_j ; bus chains separately.
Cores: star core {centre, a_1, SW, NE}, crossing core K (4U+5V).  Plain stretches between cores are tiled by np_tiling.construct."""
import sys, itertools, math, collections
import numpy as np
import scheme, np_tiling
from fractions import Fraction
from scheme import H
JE=2*(math.exp(H/8)-1)
def build_model(L):
    n=len(L.sw)
    core_star={}     # switch -> star id
    cores=[]         # list of dict(kind, members(list), neighbors per arm: list of (core_member, neighbor_idx))
    star_centres=set(L.star.values())
    # bus indexing
    bus_pos={}
    for v,chain in enumerate(L.bus):
        for p,i in enumerate(chain): bus_pos[i]=(v,p)
    star_cores=[]
    for (v,k),c in L.star.items():
        e_arm=[a for (e,u),a in L.arm.items() if a['star']==c][0]
        a1=e_arm['idx'][0]; v_,p=bus_pos[c]; chain=L.bus[v_]
        mem=[c,a1,chain[p-1],chain[p+1]]
        star_cores.append(dict(kind='star',members=mem,centre=c,arm=e_arm,bus=(v_,p)))
    cross_cores=[]
    for cr in L.crossings:
        cross_cores.append(dict(kind='K',members=cr['uidx']+cr['vcore'],cr=cr))
    return star_cores,cross_cores,bus_pos
def chains_of(L):
    """returns dict name -> (ids, relations) ; relation = (id_i,id_j,kind,weak)"""
    out={}
    for e,(i,j) in enumerate(L.edges):
        ai=L.arm[(e,i)]; aj=L.arm[(e,j)]
        ids=[ai['star']]+ai['idx']+L.track[e]['idx']+list(reversed(aj['idx']))+[aj['star']]
        rel=[]
        for a,b in zip(ids,ids[1:]):
            ma,mb=L.meta[a],L.meta[b]
            ka,kb=ma['kind'],mb['kind']
            kind='ne' if (ka=='arm' or kb=='arm') and not (ka=='arm' and kb=='track') and not (ka=='track' and kb=='arm') else 'eq'
            weak=False
            pl=L.plan[e]; hold=(i,j)[pl['hold']]; h=L.arm[(e,hold)]
            if h['weak'] is not None and {a,b}=={h['idx'][h['weak']],h['idx'][h['weak']+1]}: weak=True
            rel.append((a,b,kind,weak))
        out[('edge',e)]=(ids,rel)
    for v,chain in enumerate(L.bus):
        out[('bus',v)]=(list(chain),[(a,b,'eq',False) for a,b in zip(chain,chain[1:])])
    return out

def tilings(L):
    """returns blocks1, blocks2: lists of dict(kind, members(list of switch ids), rels=[(i,j,kind,credit)]) and the relation table
    rels[(a,b)] = dict(kind, weak, owner, c1, c2)  (credits in units of J_e)"""
    star_cores,cross_cores,bus_pos=build_model(L)
    ch=chains_of(L)
    core_of={}                      # switch -> core object
    for c in star_cores+cross_cores:
        for m in c['members']: core_of[m]=c
    P1=[]; P2=[]
    relt={}                         # (a,b) -> info ; a,b consecutive in chain
    def rel_add(a,b,kind,weak,owner):
        relt[(a,b)]=dict(kind=kind,weak=weak,owner=owner,c1=0,c2=0)
    # core blocks (both tilings), enlarged versions get neighbours appended below
    kplus={}; splus={}
    for c in star_cores+cross_cores:
        P2.append(dict(kind=c['kind'],members=list(c['members']),rels=[],core=c))
    blocks_plain1=[]; blocks_plain2=[]
    owner_rel=collections.defaultdict(list)
    # chains: edges (rep-bus paths added to the edge); bus chains handled for bus stretches
    for key,(ids,rel) in ch.items():
        if key[0]=='bus': continue
        e=key[1]
        pos={s:k for k,s in enumerate(ids)}
        for (a,b,kind,weak) in rel: rel_add(a,b,kind,weak,('edge',e))
    # bus links owned by edges: rep star = middle star of the bus (index 1 of 3, else the first)
    bus_owner={}
    for v,chain in enumerate(L.bus):
        stars=[(bp[1],i) for i,bp in bus_pos.items() if bp[0]==v and i in set(L.star.values())]
        stars.sort(); rep=stars[len(stars)//2][1]
        rp=bus_pos[rep][1]
        for (p,i) in stars:
            if i==rep: continue
            lo,hi=sorted((p,rp))
            # owning edge = the edge whose arm starts at this star
            e_arm=[(e,u) for (e,u),a in L.arm.items() if a['star']==i][0]
            for q in range(lo,hi): bus_owner[(chain[q],chain[q+1])]=('edge',e_arm[0])
    for v,chain in enumerate(L.bus):
        for a,b in zip(chain,chain[1:]): rel_add(a,b,'eq',False,bus_owner.get((a,b),('bus-free',v)))
    # stretches: along each chain, cores split it; star cores contain chain[1..] of bus?  Build "node sequences" per chain
    def stretches_of(ids,coreset):
        out=[]; cur=[]; lastcore=None
        for k,s in enumerate(ids):
            if s in coreset:
                if lastcore is not None and cur: out.append((lastcore,cur,s))
                lastcore=s; cur=[]
            else:
                if lastcore is not None: cur.append(s)
        if lastcore is not None and cur: out.append((lastcore,cur,None))   # dangling end
        return out
    coreset=set(core_of)
    allchains=[(key,ids) for key,(ids,rel) in ch.items()]
    seen=set()
    def tile_stretch(w0,plain,w1):
        r=len(plain)
        if r==0: return
        ids=[w0]+plain+([w1] if w1 is not None else [])
        wk=None
        for q in range(len(ids)-1):
            ri=relt.get((ids[q],ids[q+1]))
            if ri and ri['weak']: wk=q            # link l_q = (w_q, w_{q+1}); left switch index q
        jj=wk if (wk is not None) else None
        if r<2: raise AssertionError("r<2")
        P2b,P1b=np_tiling.construct(r,jj)
        for (a,b) in P2b: blocks_plain2.append([plain[x-1] for x in range(a,b+1)])
        for (a,b) in P1b: blocks_plain1.append([plain[x-1] for x in range(a,b+1)])
        return r,jj
    stat=[]
    for key,ids in allchains:
        # for edge chains collapse: crossing cores on the chain are cores of the same chain automatically (core members present)
        for (w0,plain,w1) in stretches_of(ids,coreset):
            k=(w0,plain[0],plain[-1],w1)
            if k in seen: continue
            seen.add(k); r_j=tile_stretch(w0,plain,w1); stat.append((key,len(plain),r_j))
    # relation credits
    def block_rels(members):
        out=[]
        for a,b in zip(members,members[1:]):
            ri=relt.get((a,b)) or relt.get((b,a))
            if ri: out.append((a,b,ri['kind'],1 if ri['weak'] else 2))
        return out
    for blk in blocks_plain2:
        for (a,b,kind,c) in block_rels(blk):
            (relt.get((a,b)) or relt.get((b,a)))['c2']+=c
    for blk in blocks_plain1:
        for (a,b,kind,c) in block_rels(blk):
            (relt.get((a,b)) or relt.get((b,a)))['c1']+=c
    # core-adjacent links l_0 / l_r : credit 2 in P1 (enlarged core)
    for (a,b),ri in relt.items():
        ca=core_of.get(a); cb=core_of.get(b)
        if (ca is None)!=(cb is None):
            ri['c1']+=2
    # core internal relations: credit 1 in both tilings (per core relation; collapsed to the core terminal relation)
    core_int=[]
    for c in star_cores:
        core_int.append((c['centre'],c['members'][1],'ne',1)); core_int.append((c['centre'],c['members'][2],'eq',1)); core_int.append((c['centre'],c['members'][3],'eq',1))
    for c in cross_cores:
        cr=c['cr']; core_int.append((cr['uidx'][0],cr['uidx'][-1],'ne',1)); core_int.append((cr['vcore'][0],cr['vcore'][-1],'eq',1))
    return dict(P1plain=blocks_plain1,P2plain=blocks_plain2,rel=relt,star_cores=star_cores,cross_cores=cross_cores,core_int=core_int,stretches=stat,core_of=core_of,chains=ch,bus_owner=bus_owner)

def edge_sequence(L,T,e):
    """full node/relation sequence of edge e: rep_u .. star_u arm_i track arm_j star_v .. rep_v ; returns nodes, rels(kind,weight(J_e units, avg of tilings))"""
    core_of=T['core_of']; relt=T['rel']; bus_pos=L.bus_pos if hasattr(L,'bus_pos') else None
    i,j=L.edges[e]
    ai=L.arm[(e,i)]; aj=L.arm[(e,j)]
    def bus_path(star_idx,v):
        chain=L.bus[v]; bp={s:k for k,s in enumerate(chain)}
        stars=sorted((bp[s],s) for (vv,k),s in L.star.items() if vv==v)
        rep=stars[len(stars)//2][1]
        p=bp[star_idx]; rp=bp[rep]
        seg=chain[min(p,rp):max(p,rp)+1]
        if rp<p: seg=seg[::-1]; seg=seg[::-1]     # rep -> star order = increasing index
        # order rep -> star
        return chain[rp:p+1] if rp<=p else chain[p:rp+1][::-1]
    pu=bus_path(ai['star'],i)            # rep_u ... star_u
    pv=bus_path(aj['star'],j)[::-1]      # star_v ... rep_v
    nodes=pu[:-1]+[ai['star']]+ai['idx']+L.track[e]['idx']+list(reversed(aj['idx']))+[aj['star']]+pv[1:]
    rels=[]; k=0
    seq=[nodes[0]]; w=[]
    # collapse crossing cores
    Kterm={}
    for c in T['cross_cores']:
        cr=c['cr']
        Kterm[cr['uidx'][0]]=(cr['uidx'][-1],'ne',cr['uidx'])
        Kterm[cr['uidx'][-1]]=(cr['uidx'][0],'ne',cr['uidx'])
        Kterm[cr['vcore'][0]]=(cr['vcore'][-1],'eq',cr['vcore'])
        Kterm[cr['vcore'][-1]]=(cr['vcore'][0],'eq',cr['vcore'])
    out_nodes=[nodes[0]]; out_rels=[]
    q=0
    while q<len(nodes)-1:
        a=nodes[q]; b=nodes[q+1]
        if a in Kterm and b in Kterm[a][2] and (q+1<len(nodes)):
            tgt,kind,mem=Kterm[a]
            # jump to the other terminal along the chain
            qq=q+1
            while nodes[qq]!=tgt: qq+=1
            out_rels.append((kind,1.0)); out_nodes.append(tgt); q=qq; continue
        ca=core_of.get(a); cb=core_of.get(b)
        ri=relt.get((a,b)) or relt.get((b,a))
        if ca is not None and cb is not None and ca is cb and ca['kind']=='star':
            wgt=1.0; kind=ri['kind']
        elif ca is not None and cb is not None and ca is not cb:
            raise AssertionError("adjacent distinct cores")
        else:
            wgt=(ri['c1']+ri['c2'])/2; kind=ri['kind']
        out_rels.append((kind,wgt)); out_nodes.append(b); q+=1
    return out_nodes,out_rels
def edge_dp(rels):
    """min over internal bits of sum weight*viol, for endpoint bits (0/1)^2"""
    INF=1e9; res={}
    for b0 in (0,1):
        cost={b0:0.0,1-b0:INF}
        for kind,w in rels:
            new={0:INF,1:INF}
            for cur in (0,1):
                if cost[cur]>=INF: continue
                for nxt in (0,1):
                    viol=((cur==nxt)!=(kind=='eq'))
                    new[nxt]=min(new[nxt],cost[cur]+w*viol)
            cost=new
        for b1 in (0,1): res[(b0,b1)]=cost[b1]
    return res
def lemmaC(L,T,name):
    dps=[]; par=[]
    for e in range(len(L.edges)):
        nodes,rels=edge_sequence(L,T,e); dps.append(edge_dp(rels))
        par.append(sum(1 for k,w in rels if k=='ne')%2)
    worst=1e9; n=L.n
    for vb in itertools.product((0,1),repeat=n):
        lb=sum(dps[e][(vb[i],vb[j])] for e,(i,j) in enumerate(L.edges))
        unc=sum(1 for (i,j) in L.edges if vb[i]==vb[j])
        worst=min(worst,lb-unc)
    mincred=min(w for e in range(len(L.edges)) for k,w in edge_sequence(L,T,e)[1])
    print(name,"edges",len(L.edges),"parity (ne count mod 2) per edge",par,"min relation weight (J_e units)",mincred,
          "| min over all",2**n,"vertex patterns of [avg LB - S0]/J_e - #uncut =",round(worst,9),flush=True)
    return worst
if __name__=="__main__":
    from schemerun import GRAPHS
    for g in ("K3","K4","K33"):
        n,edges=GRAPHS[g]; L=scheme.build(n,edges); T=tilings(L)
        # tiling listing
        print(g,"switches",len(L.sw),"stretches",len(T['stretches']),"plain blocks P1",len(T['P1plain']),"P2",len(T['P2plain']),"star cores",len(T['star_cores']),"crossing cores",len(T['cross_cores']),flush=True)
        lemmaC(L,T,g)
