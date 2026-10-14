from yv2 import *
import term
if __name__=='__main__':
    nU,nV=4,5
    for shift in (0.0,0.25,0.5):
        sw=build4(nU,nV,3,4,1,5,0.05,0.05,0.2)
        sw=[(s[0]+shift,s[1]+shift)+tuple(s[2:]) if i>=nU else s for i,s in enumerate(sw)]
        idx=[0,nU-1,nU,nU+nV-1]
        tb=term.term_table(sw,idx,procs=5); 
        val=[(0,1,0,0),(0,1,1,1),(1,0,0,0),(1,0,1,1)]
        print("shift",shift,"valid combos energies:",[round(tb[v],5) for v in val],"spread",round(max(tb[v] for v in val)-min(tb[v] for v in val),5),flush=True)
