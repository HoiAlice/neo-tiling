from cx2 import *
def Jof(tb):
    return tb[(0,0)]+tb[(1,1)]-tb[(0,1)]-tb[(1,0)]
if __name__=="__main__":
    print("antiferro J(a), d=4")
    for a in (2,2.5,3,3.25,3.5,3.75):
        sw=[(a/2,-a/2,4,2,1),(-a/2,a/2,4,2,1)]
        tb=full_table(sw,4); print(a,{''.join(map(str,s)):round(v,4) for s,v in tb.items()}, "J",round(Jof(tb),4))
    print("ferro with k,dv (levels step 1)")
    for dv in (4,6,8):
      for k in (1,2,3):
        sw=[(0,0,dv,2,1),(k,k,dv,1,0)]
        tb=full_table(sw,4); print(dv,k,{''.join(map(str,s)):round(v,4) for s,v in tb.items()}, "J",round(Jof(tb),4))
