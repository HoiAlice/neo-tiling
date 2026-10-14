from chain3 import *
def job(args):
    n,a,d=args
    return args,table([(-a*i,a*i) for i in range(n)],d)
if __name__=="__main__":
    jobs=[(4,4,d) for d in (13,15,17,19)]+[(5,4,d) for d in (17,21)]
    with Pool(6) as p: res=p.map(job,jobs)
    for (n,a,d),tb in res:
        byk={}
        for k,v in tb.items(): byk.setdefault(sum(k),[]).append(v)
        print(n,a,d,{k:(round(min(v),3),round(max(v),3)) for k,v in sorted(byk.items())})
