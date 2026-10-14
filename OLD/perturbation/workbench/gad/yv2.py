from yv import *
def build4(nU,nV,a,du,k,dv,g,h0,h2,base=1.0):
    sw=[]
    for i in range(nU):
        t=i-(nU-1)/2
        sw.append((a*t-du/2+2,-a*t-du/2+2,du,base+g,base))
    for j in range(nV):
        s=j-(nV-1)/2
        sh = h0*(-s) if s<0 else -h2*s
        sw.append((k*s-dv/2+2,k*s-dv/2+2,dv,base+g+sh,base+sh))
    return sw
if __name__=="__main__":
    import sys
    nU,nV=int(sys.argv[1]),int(sys.argv[2])
    for g,h2 in [(0.05,0.2),(0.05,0.3),(0.02,0.1),(0.1,0.4)]:
        sw=build4(nU,nV,3,4,1,5,g,g,h2)
        idx=[0,nU-1,nU,nU+nV-1]
        out=[]
        for fx in [(0,(nU-1)%2,0,0),(1,1-(nU-1)%2,0,0),(0,(nU-1)%2,1,1),(1,1-(nU-1)%2,1,1)]:
            cm,Y,w=wcheck(sw,idx,fx); out.append((round(cm,4),w))
        print("g,h2",g,h2,"Y range",Y.min(),Y.max(),out,flush=True)
