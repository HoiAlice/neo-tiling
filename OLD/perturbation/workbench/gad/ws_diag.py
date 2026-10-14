import sys,os; sys.path.insert(0,".")
from ws_h import *
h=0.2; DX=DY=30.0
def eta_loc(c1,c2,gap):
    s=sc3(list(sw3)); smax=s.max(); fb=np.array([Fpw(v,[4],[c1,c2],smax) for v in s]); return np.concatenate([[b+gap,b] for b in fb])
e=eta_loc(0.02,0.12,0.002); off=e.max()*1.5; eta=np.concatenate([e+off,e]); Y=1+0.3*eta/eta.max()
pa,pb=(0,0,1,0),(0,1,1,1)
Q=Qcat(h,DX,DY,pa,pb)
print("whole instance weak:",weakly_solvable(Q,Y))
n1=2*len(sw3)
print("copy1 alone (y values as in the whole):",weakly_solvable(Q[:n1],Y[:n1]))
print("copy2 alone:",weakly_solvable(Q[n1:],Y[n1:]))
print("copy1 alone, y minus offset c=min over copy1-... :")
for sub in (0.0,):
    pass
M2=0.3*e.max()/eta.max()  # rough mass scale of copy2 profile
for frac in (0.9,0.95,1.0,1.05):
    c=frac*0.3*e.max()/eta.max()
    print(" c=%.4f frac %.2f min y'(copy1)=%.4f"%(c,frac,(Y[:n1]-1).min()-c),"weak(copy1, y-1-c)" ,weakly_solvable(Q[:n1],np.maximum(Y[:n1]-1-c,1e-12)) if (Y[:n1]-1).min()-c>=0 else "neg")
