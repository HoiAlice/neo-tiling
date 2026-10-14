import sys; sys.path.insert(0,'.')
import numpy as np, scheme, np_tiling
from schemerun import GRAPHS
def check(name):
    n,edges=GRAPHS[name]; L=scheme.build(n,edges)
    core=set()
    for (e,u),a in L.arm.items(): core.add(a['idx'][0])
    for cr in L.crossings:
        core.update(cr['uidx']); core.update(cr['vcore'])
    rmin=1e9; stretches=0; fails=[]; weakjs=[]
    for e,(i,j) in enumerate(edges):
        ai=L.arm[(e,i)]; aj=L.arm[(e,j)]
        chain=list(ai['idx'])+L.track[e]['idx']+list(reversed(aj['idx']))
        # weak link position: between idx weak and weak+1 of the holder arm
        pl=L.plan[e]; hold=(i,j)[pl['hold']]; h=L.arm[(e,hold)]
        wl=(h['idx'][h['weak']],h['idx'][h['weak']+1])
        pos={s:k for k,s in enumerate(chain)}
        cuts=[k for k,s in enumerate(chain) if s in core]
        # also crossings cores along the V track are in 'core'; the end cores: first/last arm switch
        for a,b in zip(cuts,cuts[1:]):
            r=b-a-1
            if r<=0: continue
            stretches+=1; rmin=min(rmin,r)
            jw=None
            for q in (0,1):
                pass
            if pos[wl[0]]>a and pos[wl[1]]<b:
                jw=pos[wl[0]]-a          # link l_j = (w_j,w_{j+1}) with w_0 = chain[a]
                weakjs.append((e,r,jw))
            ok = r>=2 and (jw is None or 2<=jw<=r-2)
            if not ok: fails.append((e,a,b,r,jw))
            else:
                np_tiling.verify(r,jw)
    print(name,"edges",len(edges),"stretches",stretches,"min plain run r",rmin,"weak links (edge,r,j):",weakjs,"failures",fails)
for g in ("K3","K4","K33"): check(g)
