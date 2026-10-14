import sys,os; sys.path.insert(0,".")
from ws_h import *
h=float(os.environ.get("H","0.02")); DX=DY=float(os.environ.get("D","12")); N=int(os.environ.get("N","4"))
rng=np.random.default_rng(3); sel=[(PATS[a],PATS[b]) for a,b in zip(rng.integers(0,16,N),rng.integers(0,16,N))]
sw=two(DX,DY); K=[4,4+DX+DY]
for gap in (0.002,0.0005,0.0001):
    row=[]
    for M in (6,12,24,48):
        Y=y_rule(sw,K,[0.02,0.02+0.05*M,0.02+0.10*M],gap,0.3)
        ok=sum(bool(weakly_solvable(Qcat(h,DX,DY,pa,pb),Y)) for pa,pb in sel); row.append((M,ok))
    print("h",h,"D",DX,"gap",gap,"(M, #pass of %d):"%N,row,flush=True)
