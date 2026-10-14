from bus import *
if __name__=="__main__":
    ns=3; sw,chains=build(ns)
    sc_arm=sorted({sw[ch[0][0]][0]+sw[ch[0][0]][1]+4 for name,ch in chains.items() if ch[1]=='arm'})
    print("arm levels",sc_arm)
    for kinks in ([],sc_arm,sc_arm[:1],sc_arm[-1:]):
        swl=rule_levels(sw,kinks); A,Y,conf,ks=setup(swl); n=len(sw)
        out=[]
        for b in (0,1):
            sig=bitsof(chains,n,b); u,c,nv=glue(A,conf,ks,sig); Q=np.exp(snap(u,1e-5)); out.append(weak(Q,Y))
        print("kinks",kinks,"weak bit0,bit1:",out,flush=True)
