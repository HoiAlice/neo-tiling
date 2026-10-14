from edge2 import *
import edge, term
def reflect(sw,Cy):
    out=[]
    for (bx,by,d,yt,yb) in sw:
        out.append((-bx-d,-by-d,d,Cy-yb,Cy-yt))
    return out
if __name__=="__main__":
    sv=float(sys.argv[1]) if len(sys.argv)>1 else 0.04
    sw,idx=build_b()
    n=len(sw)
    for j in range(5):
        b,by,d,_,_=sw[n-5+j]; sw[n-5+j]=(b,by,d,BASE-sv*(j+1)+g,BASE-sv*(j+1))
    Cy=2*BASE+g
    sw2=reflect(sw,Cy)
    tb,mn=table(sw2,list(idx),verbose=False)
    print("reflected corner edge, sv",sv,{k:round(v-mn,5) for k,v in sorted(tb.items())},flush=True)
    for s in sw2[-5:]: print(tuple(round(float(x),3) for x in s))
    print(solv(sw2,list(idx),[(0,1),(1,0)]),flush=True)
