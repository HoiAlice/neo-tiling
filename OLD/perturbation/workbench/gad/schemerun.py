import sys, itertools, time, numpy as np
import scheme, qstar
GRAPHS={"K3":(3,[(0,1),(0,2),(1,2)]),
 "K4":(4,[(0,1),(0,2),(0,3),(1,2),(1,3),(2,3)]),
 "K33":(6,[(0,3),(0,4),(0,5),(1,3),(1,4),(1,5),(2,3),(2,4),(2,5)])}
def run(name,maxpat=None):
    n,edges=GRAPHS[name]; t0=time.time()
    L=scheme.build(n,edges); lib=qstar.library()
    A,dsz=qstar.point_arrays(L); yt,yb,kinks=scheme.levels(L)
    Y=np.zeros(len(A)); Y[0::2]=yt; Y[1::2]=yb
    sumB=sum(qstar.Bd(d) for d in dsz); X=lib['core'][(0,0)]['X']; J=lib['kink'][0]['J']
    print(name,"switches",len(L.sw),"points",len(A),"crossings",len(L.crossings),"kinks(levels)",len(kinks),"build",round(time.time()-t0),"s",flush=True)
    pats=list(itertools.product((0,1),repeat=n))
    if maxpat: pats=pats[:maxpat]
    worst_all=1e9; tot_viol=0; maxdev=0
    for vb in pats:
        sig,active=scheme.intended_bits(L,list(vb))
        D=qstar.assemble(L,sig,active,lib,A,dsz)
        chk=qstar.check(A,D,Y)
        c=qstar.cost(D); unc=sum(1 for (i,j) in L.edges if vb[i]==vb[j])
        exp=sumB+len(L.crossings)*X+unc*J
        worst_all=min(worst_all,chk['min_slack']); tot_viol+=chk['violations']; maxdev=max(maxdev,abs(c-exp))
        print(vb,"uncut",unc,"cost-closed %.2e"%(c-exp),"conflicts",chk['n_conf'],"violations",chk['violations'],"min slack %.3e"%chk['min_slack'],chk['worst'][:2],flush=True)
    print(name,"SUMMARY patterns",len(pats),"total violations",tot_viol,"min slack",worst_all,"max |cost-closed|",maxdev,"time",round(time.time()-t0),flush=True)
if __name__=="__main__":
    run(sys.argv[1],int(sys.argv[2]) if len(sys.argv)>2 else None)
