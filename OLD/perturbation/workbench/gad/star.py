from cx2 import *
import sys
def tab(a,g=0.05,h0=0.05,h2=0.2,du=4,dv=5,k=1):
    sw=[(0,0,dv,1+g,1)]                       # 0 center
    sw+=[(0.5+dv/2-du/2-a+ (du-dv)/2*0 -0.5 +0.5-0.5 ,0,0,0,0)][:0]
    cx=dv/2  # center of box
    # attachment boxes: centers (cx-a, cx+a) and (cx+a, cx-a)
    for sgn in (-1,1):
        c=(cx+sgn*a, cx-sgn*a); sw.append((c[0]-du/2,c[1]-du/2,du,1+g,1))
    # V neighbours SW (s=-1), NE (s=+1)
    sw.append((-k,-k,dv,1+g+h0,1+h0))
    sw.append((k,k,dv,1+g-h2,1-h2))
    return sw
if __name__=="__main__":
    for a in (2.5,3,3.5,4):
        sw=tab(a); tb=full_table(sw,4); mn=min(tb.values())
        # bits order: center, NW, SE, SW, NE
        top=sorted(tb.items(), key=lambda x:x[1])[:6]
        print("a",a,[(''.join(map(str,s)),round(v-mn,4)) for s,v in top],flush=True)
