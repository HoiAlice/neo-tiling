from cx2 import *
def build2(nU,nV,a,du,k,dv,ystep=1.0,yU=(2,1)):
    sw=[]
    for i in range(nU):
        t=i-(nU-1)/2
        sw.append((a*t-du/2+2,-a*t-du/2+2,du,yU[0],yU[1]))   # box center at (2,2)+(a t,-a t)
    for j in range(nV):
        s=j-(nV-1)/2
        sw.append((k*s-dv/2+2,k*s-dv/2+2,dv,2-ystep*s,1-ystep*s))
    return sw
def classify(tb,nU,nV):
    out={}
    def isalt(u): return all(u[i]!=u[i+1] for i in range(len(u)-1))
    def isuni(v): return len(set(v))==1
    for s,v in tb.items():
        u,w=s[:nU],s[nU:]
        key=('Ualt' if isalt(u) else 'Ukink', 'Vuni' if isuni(w) else 'Vkink')
        out.setdefault(key,[]).append(v)
    return {k:(round(min(v),5),round(max(v),5)) for k,v in out.items()}
if __name__=="__main__":
    nU,nV=int(sys.argv[1]),int(sys.argv[2]); a,du,k,dv=map(float,sys.argv[3:7]); ys=float(sys.argv[7]) if len(sys.argv)>7 else 1.0
    sw=build2(nU,nV,a,du,k,dv,ys); 
    tb=full_table(sw); mn=min(tb.values())
    print("min",round(mn,5)); 
    c=classify(tb,nU,nV)
    for kk,v in sorted(c.items()): print(kk,"min-gs",round(v[0]-mn,5),"max-gs",round(v[1]-mn,5))
