from yv2 import *
nU,nV=4,3
for g,h0,h2 in [(0.002,0.002,0.008),(0.01,0.01,0.03),(0.01,0.01,0.025),(0.01,0.02,0.05),(0.01,0.02,0.04)]:
    sw=build4(nU,nV,3,4,1,5,g,h0,h2)
    idx=[0,nU-1,nU,nU+nV-1]
    out=[]
    for fx in [(0,1,0,0),(1,0,1,1)]:
        cm,Y,w=wcheck(sw,idx,fx); out.append((round(cm,4),w))
    print("g,h0,h2",g,h0,h2,out,flush=True)
