import sys, itertools
from cx2 import *
def zig(n, s, de, d, g=0.05):
    """2n switches; virtual nodes are odd-index? switch 2j = mid, 2j+1 = virtual. returns sw list (bx,by,d,yt,yb)"""
    sw=[]
    for j in range(n):
        c=(s*j,s*j)
        sw.append((c[0]+de-d/2, c[1]-de-d/2, d,1+g,1))          # mid (SE of centre)
        sw.append((c[0]+s/2-de-d/2, c[1]+s/2+de-d/2, d,1+g,1))   # virtual (NW)
    return sw
def virt_table(tb,n):
    vt={}
    for k,v in tb.items():
        vb=tuple(k[2*j+1] for j in range(n))
        vt[vb]=min(vt.get(vb,1e9),v)
    return vt
def fitv(vt,n,allpairs=False):
    pairs=list(itertools.combinations(range(n),2)) if allpairs else [(i,i+1) for i in range(n-1)]
    rows=[];rhs=[]
    for k,v in vt.items():
        sg=[1-2*x for x in k]
        rows.append([1]+sg+[sg[i]*sg[j] for i,j in pairs]); rhs.append(v)
    A=np.array(rows,float); c=np.linalg.lstsq(A,np.array(rhs),rcond=None)[0]
    return c,float(abs(A@c-np.array(rhs)).max())
if __name__=="__main__":
    n=int(sys.argv[1]); s,de,d=map(float,sys.argv[2:5])
    sw=zig(n,s,de,d)
    tb=full_table(sw,10)
    vt=virt_table(tb,n)
    c,r=fitv(vt,n); print("params s,de,d",s,de,d,"NN resid",r,"coef",np.round(c,4))
    c,r=fitv(vt,n,True); print("allpairs resid",r,np.round(c,4))
