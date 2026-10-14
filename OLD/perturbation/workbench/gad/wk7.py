from wk2 import *
import itertools, sys
nU,nV=int(sys.argv[1]),int(sys.argv[2])
for dv,k in itertools.product((4,4.5,5,5.5,6,7),(0.5,1,1.5)):
    sw=build2(nU,nV,3,4,k,dv,1.0)
    idx=[0,nU-1,nU,nU+nV-1]
    out=[]
    for fx in [(0,(nU-1)%2,0,0),(1,1-(nU-1)%2,0,1 if False else 0)]:
        cm,v,w,Q,Y=check(sw,idx,fx); out.append((round(cm,4),w))
    print(nU,nV,"dv",dv,"k",k,out,flush=True)
