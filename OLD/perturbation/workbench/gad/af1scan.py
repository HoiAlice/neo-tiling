from af1 import *
import sys
if __name__=="__main__":
  n=3
  for e in (3,4):
    for c in (0.5,1,2):
      for dd in (0.5,1.5):
          s=e-c; de=(e-s/2)/2; d=e+dd
          sw=zig(n,s,de,d); tb=full_table(sw,10); vt=virt_table(tb,n)
          c1,r1=fitv(vt,n); c2,r2=fitv(vt,n,True)
          print("e",e,"c",c,"d",d,"NNres",round(r1,5),"allres",round(r2,6),np.round(c2,3),flush=True)
  