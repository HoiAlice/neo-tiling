"""Route A check: optimal Q of rho_dom (4Ux5V) in both U-phases; slack of the 12 asymmetric pairs and displacement stats."""
import sys
sys.path.insert(0,"/Users/olegoleg/Code/neo-tiling/perturbation/workbench/gad")
from yv2 import *
import cx2
nU,nV=4,5
sw=build4(nU,nV,3,4,1,5,0.05,0.05,0.2)
A,Y,conf,ks=cx2.setup(sw)
names=[]
for j in range(nU): names+= [f"Ut{j+1}",f"Ub{j+1}"]
for s in range(-2,3): names+= [f"Vt{s}",f"Vb{s}"]
ix={n:i for i,n in enumerate(names)}
def tau(n):
    k,i=n[:2],n[2:]
    if k[0]=='U': return ('Ub' if k[1]=='t' else 'Ut')+str(5-int(i))
    return ('Vb' if k[1]=='t' else 'Vt')+str(-int(i))
full=[(t,s) for t in range(len(Y)) for s in range(len(Y)) if Y[t]>Y[s]]
C=set((names[t],names[s]) for t,s in full)
CP=set((tau(b),tau(a)) for a,b in C)
asym=sorted(C-CP)
print(len(C),len(CP),len(asym))
for conflicts,label in ((conf,"pruned"),(full,"full")):
  ks2=[conflicts.index((2*i,2*i+1)) for i in range(len(sw))]
  for phi,fx in ((0,(0,1,0,0)),(1,(1,0,0,0))):
    r=solve_dom(A,Y,fixed=dict(zip([ks2[i] for i in (0,nU-1,nU,nU+nV-1)],fx)),conflicts=conflicts,time_limit=300)
    cost,u=r[2],r[3]
    d=u-A
    print(label,"phase",phi,"milp",round(r[0],6),"cost",round(cost,6),"max|disp|",round(abs(d).max(),4),"(grid steps %.2f)"%(abs(d).max()/0.2))
    sl=[]
    for a,b in asym:
        ua,ub=u[ix[a]],u[ix[b]]
        sl.append((max(ub-ua),a,b))   # satisfied if >=0
    sl.sort()
    print("  min slack over 12 pairs (log):",[(round(s,3),a,b) for s,a,b in sl[:3]])
    print("  all >=0:",all(s[0]>=-1e-9 for s in sl))
