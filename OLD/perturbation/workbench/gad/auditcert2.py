import pickle, sys, time
from multiprocessing import Pool
from auditcert import *
def work(sig):
    t=time.time(); r=cert_sig(sig); r['t']=round(time.time()-t); return sig,r
if __name__=="__main__":
    allsig=pickle.load(open("audit_sigs.pkl","rb")); sigs=list(allsig)
    with Pool(6) as p: out=p.map(work,sigs,chunksize=1)
    worst=1e9
    for sig,r in sorted(out,key=lambda x:(len(x[0][0]),x[1]['margin'])):
        geo,rank,rels=sig
        steps=[round(((geo[i+1][0]-geo[i][0])**2+(geo[i+1][1]-geo[i][1])**2)**0.5/1.41421356,3) if geo[i][2]==geo[i+1][2]==4 else None for i in range(len(geo)-1)]
        print("n",r['n'],"d",[g[2] for g in geo],"step(for U)",steps,"rels",rels,"occ",allsig[sig],"S-sumB %.1e"%r['S_minus_sumB'],"margin %.4f"%r['margin'],"at",r['at'],"t",r['t'],"s",flush=True)
        worst=min(worst,r['margin'])
    print("MIN margin over all plain block types:",worst)
