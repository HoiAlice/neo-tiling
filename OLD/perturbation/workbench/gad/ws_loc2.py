"""Counterexample to 'windows pass => whole passes': hierarchical y with a too-small inter-cluster offset."""
import sys,os; sys.path.insert(0,".")
from ws_h import *
h=0.2; D=30.0
sw=two(D,D); n=len(sw3)
def eta_loc(c1,c2,gap):
    s=sc3(list(sw3)); smax=s.max(); fb=np.array([Fpw(v,[4],[c1,c2],smax) for v in s]); return np.concatenate([[b+gap,b] for b in fb])
e=eta_loc(0.02,0.12,0.002)
cen=np.array([[bx+d/2,by+d/2] for bx,by,d in sw]); dd=np.array([d for _,_,d in sw])
pa,pb=PATS[3],PATS[9]; Q=Qcat(h,D,D,pa,pb)
for of in (1.05,1.5):
    off=e.max()*of; eta=np.concatenate([e+off,e]); Y=1+0.3*eta/eta.max()
    whole=bool(weakly_solvable(Q,Y)); res=[]
    for R in (13,24):
        bad=0
        for i in range(len(sw)):
            ids=[j for j in range(len(sw)) if abs(cen[j,0]-cen[i,0])<=R+(dd[i]+dd[j])/4 and abs(cen[j,1]-cen[i,1])<=R+(dd[i]+dd[j])/4]
            rows=[r for j in ids for r in (2*j,2*j+1)]
            if not weakly_solvable(Q[rows],Y[rows]): bad+=1
        res.append((R,bad))
    print("offset factor",of,"whole:",whole,"| every-switch windows failing (R, of %d):"%len(sw),res,flush=True)
