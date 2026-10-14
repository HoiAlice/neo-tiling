import sys,os; sys.path.insert(0,".")
from ws_h import *
DX=DY=12.0; N=6; h=float(os.environ.get("H","0.02"))
rng=np.random.default_rng(3); sel=[(PATS[a],PATS[b]) for a,b in zip(rng.integers(0,16,N),rng.integers(0,16,N))]
sw=two(DX,DY); K=[4,4+DX+DY]; Y=y_rule(sw,K,[0.02,0.62,3.74],0.002,0.3)
Qs=[Qcat(h,DX,DY,pa,pb) for pa,pb in sel]
r=solve(Qs,Y); levels,z,t=r; print("h",h,"joint free-y over",N,"patterns t=",t/1e-3)
lev=[levels.index(round(v,9)) for v in Y]; eta=np.array([(z[l]-z.min())/(z.max()-z.min()) for l in lev])
s=sc3(sw); n=len(sw3)
rows={}
for i in range(len(sw)):
    rows.setdefault(int(s[i]),[]).append((round(eta[2*i+1],4),round(eta[2*i]-eta[2*i+1],4),"c%d s%d"%(i//n,i%n)))
for k in sorted(rows): print("s_c",k,sorted(set((a,b) for a,b,_ in rows[k])),[c for _,_,c in rows[k]][:6])
