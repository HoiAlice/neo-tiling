import sys; sys.path.insert(0,"."); sys.path.insert(0,"../gad"); sys.path.insert(0,"/Users/olegoleg/Code/neo-tiling/poly-hardness")
import numpy as np
from axcone import cone_lp, check_decomp, AX
import planar
# two x-type switches on an anti-diagonal: NW at (0,+-2), SE at (D,-D+-2), y=(2g,g,2g,g)+b
D=10.; g=0.01
Q=np.exp(0.2*np.array([(0,2),(0,-2),(D,-D+2),(D,-D-2)]))
y=np.array([2*g,g,2*g,g])+1
print("two-switch:",cone_lp(Q,y,AX,margin=True)[0], planar.flow_lp([tuple(map(float,q)) for q in Q],y).feasible)
# V chain of 9 vertical switches, levels F(s_c)=1-0.02*s_c, gap 0.01
pts=[];yy=[]
for k in range(-4,5):
    cx=k+2; cy=k+2; sc=2*cx
    pts+=[(cx,cy+2.5),(cx,cy-2.5)]; b=1-0.02*sc; yy+=[b+0.01,b]
Q=np.exp(0.2*np.array(pts)); y=np.array(yy)
ok,info=cone_lp(Q,y,AX,margin=True); print("V chain vertical:",ok,info['t'], planar.flow_lp([tuple(map(float,q)) for q in Q],y).feasible)
# V chain all horizontal
pts=[];
for k in range(-4,5):
    cx=k+2; cy=k+2; pts+=[(cx+2.5,cy),(cx-2.5,cy)]
Q=np.exp(0.2*np.array(pts)); ok,info=cone_lp(Q,y,AX,margin=True); print("V chain horizontal:",ok,info['t'])
# U wire alternating, 8 switches d=4 at centres (3i,-3i), same level
pts=[];yy=[]
for i in range(8):
    cx,cy=3*i,-3*i
    if i%2==0: pts+=[(cx,cy+2),(cx,cy-2)]
    else: pts+=[(cx+2,cy),(cx-2,cy)]
    yy+=[1.01,1.0]
Q=np.exp(0.2*np.array(pts)); y=np.array(yy)
ok,info=cone_lp(Q,y,AX,margin=True); print("U wire alternating:",ok,info['t'], planar.flow_lp([tuple(map(float,q)) for q in Q],y).feasible)
pts2=[]
for i in range(8):
    cx,cy=3*i,-3*i
    if i%2==1: pts2+=[(cx,cy+2),(cx,cy-2)]
    else: pts2+=[(cx+2,cy),(cx-2,cy)]
Q=np.exp(0.2*np.array(pts2)); ok,info=cone_lp(Q,y,AX,margin=True); print("U wire alternating (other phase):",ok,info['t'], planar.flow_lp([tuple(map(float,q)) for q in Q],y).feasible)
