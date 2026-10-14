from refl import *
if __name__=="__main__":
    sv=float(sys.argv[1]); 
    sw,idx=build_b()
    n=len(sw)
    for j in range(5):
        b,by,d,_,_=sw[n-5+j]; sw[n-5+j]=(b,by,d,BASE-sv*(j+1)+g,BASE-sv*(j+1))
    # drop vertex2 stubs: indices idx[1]+1, idx[1]+2
    i2=idx[1]; keep=[k for k in range(len(sw)) if k not in (i2+1,i2+2)]
    newidx=[keep.index(idx[0]),keep.index(idx[1])]; sw=[sw[k] for k in keep]
    for name,s_ in (("plain",sw),("reflected",reflect(sw,2*BASE+g))):
        tb,mn=table(s_,newidx,verbose=False)
        print(name,"sv",sv,{k:round(v-mn,5) for k,v in sorted(tb.items())},flush=True)
        print(solv(s_,newidx,[(0,1),(1,0)]),flush=True)
