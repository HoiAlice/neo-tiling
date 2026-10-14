from cprime import *
sw,idx=build_c()
A,Y,conf,ks=cx2.setup(sw)
n1=15
for (t,s) in conf:
    if (A[t]>A[s]).all():
        st,ss=t//2,s//2
        if st!=ss and ((st<n1)!=(ss<n1)):
            print("cross violation",(t,s),"sw",st,ss,"pts",np.round(A[t]/0.2,2),np.round(A[s]/0.2,2),"y",Y[t],Y[s])
