import sys, pickle, collections
import numpy as np
import scheme2
from enum2 import GR, window
from schemerun2 import surrogate_Y
which=sys.argv[1]; RE,G,R=((6,16,13.0) if which=="13" else (10,26,24.0))
types=pickle.load(open("enum2_types.pkl" if which=="13" else "enum24_types.pkl","rb"))
byk=collections.defaultdict(list)
for (kind,sg),d in types.items():
    bk,(g,p,a)=next(iter(d.items())); n,edges=GR[g]; L=scheme2.build(n,edges,RE,G); ids=window(L,a,R)
    cnt=collections.Counter(L.meta[i]['kind'] for i in ids)
    # arm position of anchor if tail
    info=""
    if kind=='tail':
        m=L.meta[a]; arm=L.arm[(m['e'],m['u'])]; ap=[x for x in L.plan[m['e']]['arms'] if x['u']==m['u']][0]
        info="role=%s pos=%d head=%d len=%d weakpos=%s d=%d"%("holder" if ap['weakpos'] is not None else "other",m['pos'],ap['head'],len(arm['idx']),ap['weakpos'],ap['d'])
    byk[kind].append((len(ids),dict(cnt),g,info))
for kind in ("star","corner","kink","cross"):
    print(kind)
    for x in sorted(byk[kind]): print("  ",x)
