from edge import *
def build_b(steps=(3,3,3.75,3,3),m=4,vj=3):
    sw=[]
    # U chain from corner going NW: u0 at (0,0) then bottoms (-p,p)
    sw.append((0,0,4,BASE+g,BASE)); iu0=0
    p=0
    for s in steps[:-1]:
        p+=s; sw.append((-p,p,4,BASE+g,BASE))
    P=sum(steps)
    cx,cy=-P+2,P+2                      # vertex2 box centre
    sw+=vertex(cx,cy)
    iv2=len(sw)-3
    # V chain NE from corner: bottoms (j,j) d=5 levels step g down
    iv1=None
    for j in range(m+1):
        if j==vj: iv1=len(sw)
        sw.append((j,j,5,BASE+g-g*(j+1),BASE-g*(j+1)))
    return sw,(iv1,iv2)
if __name__=="__main__":
    sw,idx=build_b()
    for i,s in enumerate(sw): print(i,tuple(round(float(x),3) for x in s))
    tb,mn=table(sw,list(idx))
    print(solv(sw,list(idx),[(0,1),(1,0)]))
