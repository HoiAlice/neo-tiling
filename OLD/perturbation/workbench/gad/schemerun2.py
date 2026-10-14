import sys, itertools, time, numpy as np
import scheme, scheme2, qstar
GRAPHS={"K3":(3,[(0,1),(0,2),(1,2)]),
 "K4":(4,[(0,1),(0,2),(0,3),(1,2),(1,3),(2,3)]),
 "K33":(6,[(0,3),(0,4),(0,5),(1,3),(1,4),(1,5),(2,3),(2,4),(2,5)]),
 "Q3":(8,[(0,1),(0,2),(0,4),(1,3),(1,5),(2,3),(2,6),(3,7),(4,5),(4,6),(5,7),(6,7)]),
 "Petersen":(10,sorted(tuple(sorted(e)) for e in [(0,1),(1,2),(2,3),(3,4),(0,4),(0,5),(1,6),(2,7),(3,8),(4,9),(5,7),(7,9),(9,6),(6,8),(8,5)]))}
def surrogate_Y(L):
    sc=np.array([float(x[0]+x[1]+x[2]) for x in L.sw]); Y=np.zeros(2*len(sc)); Y[1::2]=-sc; Y[0::2]=-sc+0.1; return Y
def maxcuts(n,edges,limit=None):
    best=-1; cuts=[]
    for p in itertools.product((0,1),repeat=n):
        c=sum(1 for (i,j) in edges if p[i]!=p[j])
        if c>best: best=c; cuts=[p]
        elif c==best: cuts.append(p)
    return best,cuts
def run(name,RE,G,patterns="all",maxpat=64):
    n,edges=GRAPHS[name]; t0=time.time()
    L=scheme2.build(n,edges,RE,G); lib=qstar.library(); A,dsz=qstar.point_arrays(L); Y=surrogate_Y(L)
    sumB=sum(qstar.Bd(d) for d in dsz); X=lib['core'][(0,0)]['X']; J=lib['kink'][0]['J']
    print(name,"RE",RE,"G",G,"switches",len(L.sw),"points",len(A),"crossings",len(L.crossings),"build",round(time.time()-t0),"s",flush=True)
    if patterns=="all": pats=list(itertools.product((0,1),repeat=n))
    else:
        import random; random.seed(1); best,cuts=maxcuts(n,edges); pats=cuts[:4]+[tuple(random.randint(0,1) for _ in range(n)) for _ in range(maxpat-4)]
    pats=pats[:maxpat]
    worst=1e9; tv=0; md=0
    for vb in pats:
        sig,act=scheme.intended_bits(L,list(vb)); D=qstar.assemble(L,sig,act,lib,A,dsz)
        chk=qstar.check(A,D,Y,chunk=300); c=qstar.cost(D); unc=sum(1 for (i,j) in L.edges if vb[i]==vb[j])
        exp=sumB+len(L.crossings)*X+unc*J; worst=min(worst,chk['min_slack']); tv+=chk['violations']; md=max(md,abs(c-exp))
    print(name,"SUMMARY patterns",len(pats),"conflicts/pattern",chk['n_conf'],"violations",tv,"min slack %.2e"%worst,"max |cost-closed| %.2e"%md,"time",round(time.time()-t0),"s",flush=True)
    return L
if __name__=="__main__":
    run(sys.argv[1],int(sys.argv[2]),int(sys.argv[3]),sys.argv[4] if len(sys.argv)>4 else "all",int(sys.argv[5]) if len(sys.argv)>5 else 64)
