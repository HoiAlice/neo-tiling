import numpy as np
from edge import g
import loc7
def build_inst(aW=3.75):
    """cprime instance with weak step aW (grid steps) in both edges. returns switch list, dict of indices."""
    h0c,h2c=0.02,0.04
    def vlev(s,b=1.0):
        sh=-h0c*s if s<0 else -h2c*s
        return (b+g+sh,b+sh)
    sw=[]
    for s in range(-4,5):
        t,b=vlev(s); sw.append((s-0.5,s-0.5,5,t,b))
    ytop,ybot=vlev(-4); ub=ytop
    steps=[3,3,aW,3,3]; p=0
    sw.append((-4.5,-4.5,4,ub+g,ub))
    for st in steps[:-1]:
        p+=st; sw.append((-4.5-p,-4.5+p,4,ub+g,ub))
    P=sum(steps); c=(-4.5-P+2,-4.5+P+2); sw.append((c[0]-2.5,c[1]-2.5,5,ub+g,ub))
    def vert(t): return (3*t+2-2.5,-3*t+2-2.5,5,1+g,1.0)
    def usw(t): return (3*t,-3*t,4,1+g,1.0)
    w=aW/3.0
    sw.append(vert(-3.5-w-1.0))
    sw.append(usw(-3.5-w))
    for t in (-3.5,-2.5,-1.5,-0.5,0.5,1.5,2.5): sw.append(usw(t))
    sw.append(vert(3.5))
    return sw
if __name__=="__main__":
    sw=build_inst(3.75)
    import cprime
    sw0,idx=cprime.build_c()
    print(len(sw),len(sw0), max(abs(np.array(a[:3])-np.array(b[:3])).max() for a,b in zip(sw,sw0)))
