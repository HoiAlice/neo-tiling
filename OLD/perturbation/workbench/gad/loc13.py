import numpy as np
from multiprocessing import Pool
from loc11 import star, star_rels, job
arms={"NW":(1,5),"SE":(2,6),"SW":(3,7),"NE":(4,8)}
def variant(drop):
    sw=star(3.0,True); rel=star_rels(True)
    gone=set(arms[drop]); keep=[i for i in range(9) if i not in gone]; ix={o:n for n,o in enumerate(keep)}
    r=[(ix[a],ix[b],k,c) for a,b,k,c in rel if a in ix and b in ix]
    return ("deg3-no"+drop,[sw[i] for i in keep],r)
if __name__=="__main__":
    with Pool(4) as p: out=p.map(job,[variant(d) for d in arms])
    for n,S,C in out: print(n,"S=%.6f cert=%.6f margin=%.2e"%(S[0],C[0],C[0]-S[0]),S[2],C[2],flush=True)
