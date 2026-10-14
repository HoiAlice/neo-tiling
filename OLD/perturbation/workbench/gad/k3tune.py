from chain3 import *
def jb(args):
    a,b,d=args
    tb=table([(0,0),(-a,a),(-a-b,a+b)],d)
    return args,tb
if __name__=="__main__":
    jobs=[(4,4,d) for d in [11,11.5,12,12.5,13,14]]+[(5,5,d) for d in [13,14,15,16]]
    with Pool(8) as p: res=p.map(jb,jobs)
    for (a,b,d),tb in res:
        print(a,b,d,{"".join(map(str,k)):round(v,3) for k,v in tb.items() if k[0]==0})
