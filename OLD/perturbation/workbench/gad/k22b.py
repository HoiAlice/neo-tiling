from k22 import *
if __name__=="__main__":
    jobs=[(d,d2,ox,-ox,yt) for d in (1,2,3,4) for d2 in (1,2,3,4) for ox in range(-6,7) for yt in [(2,2),(2,3),(3,2)]]
    with Pool(8) as p: res=[r for r in p.map(ev,jobs,chunksize=4) if r]
    res.sort(key=lambda r:-r[0])
    for r in res[:14]: print(round(r[0],4), r[1], {k:round(v,3) for k,v in r[2].items()})
