from cx2 import *
import sys
def classify(tb,nU,nV):
    mn=min(tb.values()); res=[]
    for s,v in sorted(tb.items(), key=lambda x:x[1])[:8]: res.append((''.join(map(str,s[:nU])),''.join(map(str,s[nU:])),round(v-mn,4)))
    return res
if __name__=="__main__":
    g=0.05
    for c,dv,dl in [(0,4,1),(0.5,4,1),(0,5,1),(0.5,5,1),(0,6,1),(0.5,6,1),(-0.5,5,1),(-1,5,1)]:
        nU,nV=3,3
        sw=[(-6+3*i*2/2*0+(-3)*(2-i)*(-1)*0 ,0,0,0,0) for i in range(0)]
        sw=[(-6,6,4,1+g,1),(-3,3,4,1+g,1),(0,0,4,1+g,1)]
        for j in range(nV):
            sw.append((c+j,c+j,dv,1+g-dl*g*(j+1),1-dl*g*(j+1)))
        tb=full_table(sw,4)
        print("c",c,"dv",dv,"dl",dl,classify(tb,nU,nV),flush=True)
