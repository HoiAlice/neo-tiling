from yv import *
import itertools, sys
g,h=float(sys.argv[1]),float(sys.argv[2]); fx=tuple(int(c) for c in sys.argv[3])
nU,nV=4,3
sw=build3(nU,nV,3,4,1,5,g,h)
A,Y,conf,ks=cx2.setup(sw); idx=[0,nU-1,nU,nU+nV-1]
r=solve_dom(A,Y,fixed=dict(zip([ks[i] for i in idx],fx)),conflicts=conf,time_limit=120)
cm,u=polish_margin(A,conf,r[1],1e-6); Q=np.exp(u)
n=len(sw); fails=[]
print("sw",sw)
for r_ in range(1,n+1):
    for S in itertools.combinations(range(n),r_):
        if any(set(f)<=set(S) for f in fails): continue
        ii=[2*i+j for i in S for j in (0,1)]
        if not weakly_solvable(Q[ii],Y[ii]): fails.append(S); print("minimal failing",S,flush=True)
