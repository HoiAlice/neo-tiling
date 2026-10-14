from wk2 import *
from scipy.optimize import linprog
import itertools
sw=build2(4,3,3,4,1,5,1.0)
cm,v,w,Q,Y=check(sw,[0],[0],ycomp=0.1)
S=(1,2,6); idx=[2*i+j for i in S for j in (0,1)]
Qs=Q[idx]; Ys=Y[idx]
gens=[]
for m in range(1,64):
    ind=np.array([(m>>k)&1 for k in range(6)],float)
    if weakly_solvable(Qs,ind): gens.append(ind)
print("reachable sets:",[''.join(str(int(x)) for x in g) for g in gens])
G=np.array(gens)
# Farkas: max w.Ys s.t. G w <= 0, -1<=w<=1
res=linprog(-Ys,A_ub=G,b_ub=np.zeros(len(G)),bounds=[(-1,1)]*6)
print("w",res.x,"w.y",-res.fun)
