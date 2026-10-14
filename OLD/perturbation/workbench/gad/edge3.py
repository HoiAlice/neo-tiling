from edge2 import *
import edge2
if __name__=="__main__":
    for sv in (0.02,0.04,0.08):
        sw,idx=build_b()
        # relevel V chain (indices of V switches: last 5)
        n=len(sw)
        for j in range(5):
            b,by,d,_,_=sw[n-5+j]
            sw[n-5+j]=(b,by,d,BASE+g-sv*(j+1)+ (g if False else 0),BASE-sv*(j+1)+g*0 - 0)
            # keep top-bottom gap g
            sw[n-5+j]=(b,by,d,BASE-sv*(j+1)+g,BASE-sv*(j+1))
        tb,mn=table(sw,list(idx),verbose=False)
        print("sv",sv,{k:round(v-mn,4) for k,v in tb.items()})
        print(solv(sw,list(idx),[(0,1),(1,0)]),flush=True)
