from wk2 import *
import itertools
sw=build2(4,3,3,4,1,5,1.0)
cm,v,w,Q,Y=check(sw,[0],[0],ycomp=0.1)
n=len(sw)
print("switches",sw)
fails=[]
for r in range(2,n+1):
    for S in itertools.combinations(range(n),r):
        if any(set(f)<=set(S) for f in fails): continue
        idx=[2*i+j for i in S for j in (0,1)]
        ok=weakly_solvable(Q[idx],Y[idx])
        if not ok: fails.append(S); print("minimal failing subset",S,flush=True)
    if fails and r>=4: break
print(Q[[2*i+j for i in fails[0] for j in (0,1)]] if fails else None, Y)
