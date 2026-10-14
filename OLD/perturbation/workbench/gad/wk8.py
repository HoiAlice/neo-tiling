from wk2 import *
sw=build2(4,3,3,4,1,5,1.0)
cm,v,w,Q,Y=check(sw,[0],[0],ycomp=0.1)
S=(1,2,6); idx=[2*i+j for i in S for j in (0,1)]
Qs=Q[idx]
np.set_printoptions(precision=5,suppress=True)
print(np.log(Qs)/0.2)
for k in range(6):
    y=np.zeros(6); y[k]=1; print("e",k,weakly_solvable(Qs,y))
