from core import *
pts=[]
for c in [(0,0),(-3,3),(-6,6)]: pts+=[(c[0]+4,c[1]+4),c]
P=np.exp(0.2*np.array(pts,float)); y=np.array([2,1]*3,float)
print("P3 gadget at original P weakly solvable (expect False):",weakly_solvable(P,y))
# switch alone
for sg in (0,1):
    a=0.2*np.array([(4,4),(0,0)],float); y2=np.array([2.,1.])
    r=solve_dom(a,y2,fixed={0:sg}); print("single switch sigma",sg,"cost",r[2], "formula",2*(np.exp(0.4)-1))
# 2-switch coupler table
a=0.2*np.array([(4,4),(0,0),(1,7),(-3,3)],float); y4=np.array([2,1,2,1.])
conf=conflicts_of(y4); ks=[conf.index((0,1)),conf.index((2,3))]
for s1 in (0,1):
  for s2 in (0,1):
    r=solve_dom(a,y4,fixed={ks[0]:s1,ks[1]:s2},conflicts=conf); print("coupler",s1,s2,round(r[2],5))
