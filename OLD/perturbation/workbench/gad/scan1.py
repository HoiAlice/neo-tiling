from cx3 import *
import itertools
if __name__=="__main__":
    rows=[]
    for a,du,dv,k,ys in itertools.product((3,),(4,),(5,6,7,8),(1,1.5,2,2.5),(1.0,)):
        sw=build2(2,3,a,du,k,dv,ys)
        tb=full_table(sw,5); mn=min(tb.values()); c=classify(tb,2,3)
        dev=c[('Ualt','Vuni')][1]-mn
        ku=c[('Ukink','Vuni')][0]-mn; kv=c[('Ualt','Vkink')][0]-mn
        print(a,du,dv,k,ys,"dev",round(dev,5),"Ukink",round(ku,4),"Vkink",round(kv,4),flush=True)
