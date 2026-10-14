from chain3 import *
def job2(args):
    a,b,d=args
    tb=table([(0,0),(-a,a),(-a-b,a+b)],d)
    return args,tb
if __name__=="__main__":
    jobs=[(a,b,d) for a in range(2,6) for b in range(2,8) for d in range(max(a,b)+1, a+b+4)]
    with Pool(8) as p: res=p.map(job2,jobs)
    out=[]
    for (a,b,d),tb in res:
        N=[tb[(0,0,1)],tb[(0,1,0)],tb[(1,0,0)]]
        C=tb[(0,0,0)]
        out.append((C-max(N), max(N)-min(N), (a,b,d), tb))
    out.sort(key=lambda r:-(r[0]-3*r[1]))
    for r in out[:15]:
        tb=r[3]; print(round(r[0],3), round(r[1],3), r[2], {"".join(map(str,k)):round(v,3) for k,v in tb.items() if k[0]==0})
