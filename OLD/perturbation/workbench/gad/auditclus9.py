import sys, itertools, collections
import schemerun
GR=dict(schemerun.GRAPHS)
GR["Q3"]=(8,[(0,1),(0,2),(0,4),(1,3),(1,5),(2,3),(2,6),(3,7),(4,5),(4,6),(5,7),(6,7)])
GR["Petersen"]=(10,[(0,1),(1,2),(2,3),(3,4),(0,4),(0,5),(1,6),(2,7),(3,8),(4,9),(5,7),(7,9),(9,6),(6,8),(8,5)])
GR["Prism"]=(6,[(0,1),(1,2),(0,2),(3,4),(4,5),(3,5),(0,3),(1,4),(2,5)])
for k in list(GR): GR[k]=(GR[k][0],[tuple(sorted(e)) for e in GR[k][1]])
schemerun.GRAPHS.clear(); schemerun.GRAPHS.update(GR)
import auditclus, auditclus8
auditclus.GRAPHS=schemerun.GRAPHS; auditclus8.GRAPHS=schemerun.GRAPHS
from multiprocessing import Pool
import scheme
if __name__=="__main__":
    R=float(sys.argv[1]); rho=float(sys.argv[2])
    t=auditclus.enum(R,graphs=tuple(GR.keys())); jobs=[]
    for (kind,sig),occ in t.items():
        g,a,nn=occ[0]; n,edges=GR[g]; L=scheme.build(n,edges); ids=auditclus.window(L,a,R); seen={}
        for vb in itertools.product((0,1),repeat=min(n,10)):
            vb=vb+(0,)*(n-len(vb))
            s_,act=scheme.intended_bits(L,list(vb)); key=tuple(s_[i] for i in ids)
            if key not in seen: seen[key]=vb
        for key,vb in seen.items(): jobs.append((g,a,ids,vb,kind,rho))
    print("window types",len(t),"LPs",len(jobs),flush=True)
    with Pool(6) as p: out=p.map(auditclus8.job,jobs,chunksize=1)
    bad=[o for o in out if not o[4]]
    print("geometric slope rule rho",rho,"all graphs: LPs",len(out),"failures",len(bad),[(o[0],o[1],o[2]) for o in bad[:8]],flush=True)
