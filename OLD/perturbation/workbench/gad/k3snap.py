from k3 import *
import snapw
if __name__=="__main__":
    sw,idx=build()
    print(snapw.snapped_solv(sw,idx,[(0,0,1),(0,1,0),(0,1,1),(1,0,0),(1,0,1),(1,1,0)],tl=500)[0],flush=True)
    print("unsat patterns:",snapw.snapped_solv(sw,idx,[(0,0,0),(1,1,1)],tl=500)[0],flush=True)
