import sys,time,numpy as np
sys.argv=['x','0','0']
exec(open('t2.py').read().split("rng=np.random")[0])
base=np.array([[4,1],[3,3],[1,4]],float); y0=[1,5,3]
cases={"tri":([],[]),"+far high-y low corner":([[5,5]],[2]),"+light near mid":([[2.5,2.5]],[4]),"+second triangle copy shifted":([[3,1.5]],[6])}
for name,(p,yy) in cases.items():
    P=np.vstack([base]+[np.array(p,float)]) if p else base; y=np.array(y0+yy,float)
    t0=time.time(); d=rho_dom_true(P,y); f=rho_exact(P,y,max_fam=4 if len(P)==4 else 3,time_limit=15)[0]
    print(name,"dom=%.5f full=%.5f diff=%.5f (%.0fs)"%(d,f,f-d,time.time()-t0),flush=True)
