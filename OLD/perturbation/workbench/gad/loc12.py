import numpy as np
Je=0.050630241048857716; c2=2*Je
P1=[(1,2,'eq',c2),(6,7,'eq',c2),(18,19,'ne',c2),(22,23,'ne',c2),(2,6,'eq',Je),(19,22,'ne',Je),
    (0,9,'eq',c2),(11,12,'ne',Je),(13,14,'ne',c2),(16,17,'ne',Je)]
P2=[(2,6,'eq',Je),(19,22,'ne',Je),(0,1,'eq',c2),(9,10,'ne',c2),(10,11,'ne',c2),(11,12,'ne',Je),(12,13,'ne',c2),
    (7,8,'eq',c2),(15,16,'ne',c2),(16,17,'ne',Je),(17,18,'ne',c2),(23,24,'ne',c2)]
N=25; worst=1e9; arg=None; cnt=0
CH=1<<21
for start in range(0,1<<N,CH):
    n=np.arange(start,start+CH,dtype=np.int64)
    b=[((n>>i)&1) for i in range(N)]
    def credit(P):
        s=np.zeros(CH)
        for a,c,k,cr in P:
            v=(b[a]!=b[c]) if k=='eq' else (b[a]==b[c])
            s+=cr*v
        return s
    lb=np.maximum(credit(P1),credit(P2))
    rhs=Je*((b[8]==b[14]).astype(float)+(b[15]==b[24]))
    d=lb-rhs; i=d.argmin()
    if d[i]<worst: worst=d[i]; arg=int(n[i])
print("min over all 2^25 bit patterns of max_j LB_j - S0 - Je*uncut =",worst,"at",arg, "bits",[(arg>>i)&1 for i in range(N)])
