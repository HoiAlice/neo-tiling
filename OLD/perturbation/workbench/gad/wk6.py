from wk2 import *
sw=build2(4,3,3,4,1,5,1.0)
cm,v,w,Q,Y=check(sw,[0],[0],ycomp=0.1)
S=(1,2,6); idx=[2*i+j for i in S for j in (0,1)]
Qs=Q[idx]; Ys=Y[idx]; print(Qs,Ys)
print("as is",weakly_solvable(Qs,Ys))
print("all ones",weakly_solvable(Qs,np.ones(6)))
for k in range(6):
    y=np.ones(6); y[k]=1.5; print("bump",k,weakly_solvable(Qs,y))
for k in range(6):
    y=np.ones(6); y[k]=3; print("bump3",k,weakly_solvable(Qs,y))
