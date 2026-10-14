from k3 import *
import term, edge
if __name__=="__main__":
    sw,idx=build()
    tb=term.term_table(sw,idx,procs=4)
    mn=min(tb.values())
    for s,v in sorted(tb.items()):
        mono=(s[0]==s[1])+(s[1]==s[2])+(s[0]==s[2])   # pairs equal: 3 if constant, 1 otherwise
        print(s,"mono-edges",mono if mono==3 else 1,"excess",round(v-mn,5),flush=True)
    opt=[s for s,v in tb.items() if v-mn<0.02]
    print("optimal patterns",opt,flush=True)
    np.save("k3_table.npy",np.array([[*s,tb[s]] for s in sorted(tb)]))
    print(edge.solv(sw,idx,opt),flush=True)
