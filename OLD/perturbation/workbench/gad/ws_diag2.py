import sys,os; sys.path.insert(0,".")
from ws_h import *
from fractions import Fraction as Fr
from ws_exact2 import Fq
from ws_exact3 import certify3
h=0.2; DX=DY=30.0
def eta_loc(c1,c2,gap):
    s=sc3(list(sw3)); smax=s.max(); fb=np.array([Fpw(v,[4],[c1,c2],smax) for v in s]); return np.concatenate([[b+gap,b] for b in fb])
e=eta_loc(0.02,0.12,0.002); off=e.max()*3; eta=np.concatenate([e+off,e]); Y=1+0.3*eta/eta.max()
pa,pb=(0,0,1,0),(0,1,1,1)
Q=Qcat(h,DX,DY,pa,pb); n1=2*len(sw3)
P=[(Fq(a),Fq(b)) for a,b in Q]; yv=[Fr(float(v)).limit_denominator(10**12) for v in Y]
kap=Fr(1,100); yp=[v-(1-kap) for v in yv]
c2,m2,_=certify3(P[n1:],yp[n1:]); print('msg',m2); M2=sum(m for _,m in c2); print("cluster2 min mass",float(M2),"max y'",float(max(yp[n1:])))
nu=[v-M2 for v in yp[:n1]]; print("min nu",float(min(nu)),"max nu",float(max(nu)))
for name,pts in (("no context",list(range(n1))),("with copy2 context",list(range(len(P))))):
    cert,msg,fun=certify3([P[p] for p in pts],nu+[Fr(0)]*(len(pts)-n1))
    print(name,msg,"min total mass",fun)
# what if M2 replaced by M2*0.5 ?
for fr in (Fr(1,2),Fr(3,4)):
    nu2=[v-M2*fr for v in yp[:n1]]
    cert,msg,fun=certify3(P,nu2+[Fr(0)]*(len(P)-n1)); print("offset fraction",float(fr),"with context:",msg)
