from chain3 import *
def f(d):
    tb=table([(0,0),(-4,4),(-8,8)],d)
    return tb[(0,1,0)]-tb[(0,0,1)], tb
lo,hi=11.0,11.5
flo=f(lo)[0]
for _ in range(14):
    mid=(lo+hi)/2; fm,tb=f(mid)
    if (fm>0)==(flo>0): lo=mid
    else: hi=mid
d=(lo+hi)/2; fm,tb=f(d)
print("d*",d,"spread",fm)
for k,v in tb.items(): print("".join(map(str,k)),round(v,5))
