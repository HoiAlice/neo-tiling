from cx2 import *
import sys
def cor(nV=3,step=0.05,gu=0.05,aw=None,nU=3):
    sw=[(-3*(nU-1-i),3*(nU-1-i),4,1+gu,1) for i in range(nU)]
    for j in range(nV): sw.append((j,j,5,1-step*j,1-step*j-0.05))
    return sw
if __name__=="__main__":
    for nV,step,gu in [(3,0.05,0.05),(5,0.05,0.05),(5,0.01,0.01),(5,0.01,0.05)]:
        sw=cor(nV,step,gu); nU=3
        tb=full_table(sw,10); mn=min(tb.values())
        top=sorted(tb.items(),key=lambda x:x[1])[:5]
        print(nV,step,gu,[(''.join(map(str,k[:nU])),''.join(map(str,k[nU:])),round(v-mn,4)) for k,v in top],flush=True)
