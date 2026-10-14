"""2-SAT relaxation of BOXdom(r): color per conflict edge, units from bad pairs, 2-clauses from 3-chains."""
import numpy as np, itertools
from scipy.sparse import coo_matrix
from scipy.sparse.csgraph import connected_components

def feasible_2sat(a, y, r, eps=1e-9):
    a=np.asarray(a,float); T=len(a)
    E=[(p,q) for p in range(T) for q in range(T) if y[p]>y[q]]
    idx={e:k for k,e in enumerate(E)}; n=len(E)
    # var k true <=> color 1 (y-coordinate). literal 2k = true, 2k+1 = false
    cl=[]
    def lit(e,c,neg=False):  # literal "color(e)==c"
        k=idx[e]; v=(c==1)
        return 2*k+(0 if v else 1)
    bad=lambda p,q,i: a[p,i]-a[q,i] > 2*r+eps
    for (p,q) in E:
        b0,b1=bad(p,q,0),bad(p,q,1)
        if b0 and b1: return False
        if b0: cl.append((lit((p,q),1),lit((p,q),1)))   # color must be 1
        if b1: cl.append((lit((p,q),0),lit((p,q),0)))
    for (p,q) in E:
        for c in range(T):
            if y[p]>y[c]>y[q]:
                for i in range(2):
                    if bad(p,q,i):
                        # not (col(p,c)=i and col(c,q)=i)
                        cl.append((lit((p,c),1-i),lit((c,q),1-i)))
    rows=[];cols=[]
    for (l1,l2) in cl:
        rows+= [l1^1,l2^1]; cols+=[l2,l1]   # not l1 -> l2 ; not l2 -> l1
    g=coo_matrix((np.ones(len(rows)),(rows,cols)),shape=(2*n,2*n))
    _,lab=connected_components(g,directed=True,connection='strong')
    return all(lab[2*k]!=lab[2*k+1] for k in range(n))

def rho_2sat(a,y):
    a=np.asarray(a,float);T=len(a)
    cand=sorted({0.0}|{abs(a[p,i]-a[q,i])/2 for p in range(T) for q in range(T) for i in range(2)})
    lo,hi=0,len(cand)-1
    while lo<hi:
        m=(lo+hi)//2
        if feasible_2sat(a,y,cand[m]): hi=m
        else: lo=m+1
    return cand[lo]
