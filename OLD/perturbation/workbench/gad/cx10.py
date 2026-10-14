from cprime import *
if __name__=="__main__":
    sw,idx=build_c()
    which=sys.argv[1]
    if which=="E1":
        sw=sw[:15]; idx=idx[:2]
    elif which=="E2":
        sw=sw[15:]; idx=[idx[2]-15,idx[3]-15]
    elif which=="E1V":   # E1 without its U arm beyond corner? keep V + corner + 1 U
        sw=sw[:9]+sw[9:11]; idx=[8,10]
    tb,mn=table(sw,idx,procs=6,verbose=False)
    print(which,{k:round(v-mn,4) for k,v in sorted(tb.items())},flush=True)
