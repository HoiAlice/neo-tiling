import random, time, sys
from core import *
random.seed(int(sys.argv[1]) if len(sys.argv)>1 else 0)
eps = float(sys.argv[2]) if len(sys.argv)>2 else 0.3
N = int(sys.argv[3]) if len(sys.argv)>3 else 300
G = 6
def table(a, y, k1, k2, conf):
    tb = {}
    for s1 in (0,1):
        for s2 in (0,1):
            r = solve_dom(a, y, fixed={k1:s1, k2:s2}, conflicts=conf, time_limit=10)
            if r is None: return None
            tb[(s1,s2)] = r[2]
    return tb
found=[]
t0=time.time()
for it in range(N):
    nx = random.choice([1,2])
    d = random.randint(1,3)
    # switch U at (0..), V placed randomly; symmetric gaps d
    pts=[]
    uU = (random.randint(0,G),random.randint(0,G)); uV=(random.randint(0,G),random.randint(0,G))
    pts=[(uU[0]+d,uU[1]+d),uU,(uV[0]+d,uV[1]+d),uV]
    for _ in range(nx): pts.append((random.randint(0,G+3),random.randint(0,G+3)))
    if len(set(pts))<len(pts): continue
    T=len(pts)
    y = np.array([4.0,3.0,4.0,3.0]+[random.choice([1,2,3,3.5,4,5]) for _ in range(nx)])
    # y-levels: tops of switches above bottoms; slight tie breaks irrelevant
    # to avoid unintended conflict between U and V pieces, keep as is (conflicts via y>)
    a = eps*np.array(pts,float)
    conf = conflicts_of(y)
    try:
        k1 = conf.index((0,1)); k2 = conf.index((2,3))
    except ValueError: continue
    tb = table(a,y,k1,k2,conf)
    if tb is None: continue
    I = tb[(0,0)]+tb[(1,1)]-tb[(0,1)]-tb[(1,0)]
    asym = abs(tb[(0,0)]-tb[(1,1)])+abs(tb[(0,1)]-tb[(1,0)])
    found.append((I,asym,pts,list(y),tb))
found.sort(key=lambda r:-r[0]+0.5*r[1])
print(len(found), time.time()-t0)
for r in found[:12]:
    print(round(r[0],4), round(r[1],4), r[2], r[3], {k:round(v,3) for k,v in r[4].items()})
