from edge import *
import edge, itertools, sys
h0c,h2c=0.02,0.04
def vlev(s,b=1.0):
    sh = -h0c*s if s<0 else -h2c*s
    return (b+g+sh,b+sh)
def build_c(weakE1=3.75,weakE2=1.25):
    sw=[]; ids={}
    # V chain s=-4..4, d=5, bottom (s-0.5)
    for s in range(-4,5):
        t,b=vlev(s); sw.append((s-0.5,s-0.5,5,t,b))
    ids['v1']=len(sw)-1
    ytop,ybot=vlev(-4)
    ub=ytop            # U corner bottom level = V first top
    # corner U chain from V first bottom (-4.5,-4.5) going NW with steps
    steps=[3,3,weakE1,3,3]; p=0
    sw.append((-4.5,-4.5,4,ub+g,ub))
    for st in steps[:-1]:
        p+=st; sw.append((-4.5-p,-4.5+p,4,ub+g,ub))
    P=sum(steps)
    # vertex2 centre: U-switch centre convention: centre of bottom (-4.5-P,-4.5+P) d=4 is +2
    c=(-4.5-P+2,-4.5+P+2); sw.append((c[0]-2.5,c[1]-2.5,5,ub+g,ub)); ids['v2']=len(sw)-1
    # E2: A(vertex), u..., B(vertex); U switch t has bottom (3t,-3t), centre (3t+2,-3t+2)
    def vert(t): return (3*t+2-2.5,-3*t+2-2.5,5,1+g,1.0)
    def usw(t): return (3*t,-3*t,4,1+g,1.0)
    sw.append(vert(-5.75)); ids['A']=len(sw)-1
    for t in (-4.75,-3.5,-2.5,-1.5,-0.5,0.5,1.5,2.5): sw.append(usw(t))
    sw.append(vert(3.5)); ids['B']=len(sw)-1
    return sw,[ids['v1'],ids['v2'],ids['A'],ids['B']]
if __name__=="__main__":
    sw,idx=build_c()
    for i,s in enumerate(sw): print(i,tuple(round(float(x),3) for x in s))
    print("terminals",idx,flush=True)
    tb,mn=table(sw,idx,procs=4,verbose=False)
    for s,v in sorted(tb.items()):
        uns=(s[0]==s[1])+(s[2]==s[3]); print(s,"unsat",uns,round(v-mn,5),flush=True)
    sat=[s for s in tb if s[0]!=s[1] and s[2]!=s[3]]
    print(solv(sw,idx,sat),flush=True)
