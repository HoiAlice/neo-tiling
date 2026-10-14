import numpy as np, sys
sys.path.insert(0,'pc')
from land import lp_cost
from scipy.optimize import minimize
P=np.array([[1.96, 4.71], [2.73, 2.55], [4.37, 2.2], [3.15, 4.17], [3.2, 2.6]]); nl=3; h1,h2=3,4
G=np.linspace(0.01,0.99,50)
for hh in (h1,h2):
    idx=[0,1,2,hh]; c=[lp_cost(P[idx],[3],[0,1,2],{3:g}) for g in G]
    lm=[round(G[i],2) for i in range(1,len(G)-1) if c[i]<c[i-1]-1e-7 and c[i]<=c[i+1]+1e-9]
    print("heavy",hh,"local min",lm,[round(c[G.tolist().index(G[i])],3) for i in range(1,len(G)-1) if c[i]<c[i-1]-1e-7 and c[i]<=c[i+1]+1e-9])
    cc=np.array(c); print(np.round(cc[::3],3))
G=np.linspace(0.02,0.98,33)
M=np.array([[lp_cost(P,[3,4],[0,1,2],{3:a,4:b}) for b in G] for a in G])
cut1=np.argmax(G>0.53); cut2=np.argmax(G>0.45)
# cut chosen near barrier peaks
def F(a,b):
    r1=slice(0,cut1) if a==0 else slice(cut1,None); r2=slice(0,cut2) if b==0 else slice(cut2,None)
    return M[r1,r2].min()
f={(a,b):F(a,b) for a in (0,1) for b in (0,1)}
print({k:round(v,4) for k,v in f.items()}, "d=",f[0,0]+f[1,1]-f[0,1]-f[1,0])
