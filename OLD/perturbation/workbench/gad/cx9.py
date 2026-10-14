from cprime import *
if __name__=="__main__":
    nVs=int(sys.argv[1]); h0=float(sys.argv[2]); h2=float(sys.argv[3])
    import cprime; cprime.h0c,cprime.h2c=h0,h2
    sw=[]
    for s in range(-nVs,nVs+1):
        t,b=cprime.vlev(s); sw.append((s-0.5,s-0.5,5,t,b))
    nv=len(sw); 
    for t in (-1.5,-0.5,0.5,1.5): sw.append((3*t,-3*t,4,1+g,1.0))
    idx=[nv,nv+3,0,nv-1]   # U_in,U_out,V_in,V_out
    tb,mn=table(sw,idx,procs=6,verbose=False)
    print("nVs",nVs,"h0,h2",h0,h2)
    for s,v in sorted(tb.items()):
        ok=(s[1]!=s[0]) and s[2]==s[3]
        print(s,"valid" if ok else "     ",round(v-mn,5),flush=True)
