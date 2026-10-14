"""Locality test: whole instance fails, do all every-switch windows (L-inf box of half-width R in grid units around a switch centre, + (d+d')/4) pass?"""
import sys,os; sys.path.insert(0,".")
from ws_h import *
import ws_rho as RH
h=float(os.environ.get("H","0.02")); D=float(os.environ.get("D","12")); rho=float(os.environ.get("RHO","11"))
sw=two(D,D); n=len(sw3); Y=RH.y_mult()
N=int(os.environ.get("N","6")); rng=np.random.default_rng(3); sel=[(PATS[a],PATS[b]) for a,b in zip(rng.integers(0,16,N),rng.integers(0,16,N))]
cen=np.array([[bx+d/2,by+d/2] for bx,by,d in sw]); dd=np.array([d for _,_,d in sw])
for pa,pb in sel:
    Q=Qcat(h,D,D,pa,pb); whole=bool(weakly_solvable(Q,Y))
    row=[]
    for R in (13,24,40):
        bad=0
        for i in range(len(sw)):
            ids=[j for j in range(len(sw)) if abs(cen[j,0]-cen[i,0])<=R+(dd[i]+dd[j])/4 and abs(cen[j,1]-cen[i,1])<=R+(dd[i]+dd[j])/4]
            rows=[r for j in ids for r in (2*j,2*j+1)]
            if not weakly_solvable(Q[rows],Y[rows]): bad+=1
        row.append((R,bad))
    print("h",h,"D",D,pa,pb,"whole:",whole,"| windows failing per radius (of %d switches):"%len(sw),row,flush=True)
