from gluelib import *
import cx2
if __name__=="__main__":
    for k in (1.0,0.5):
        sw=[(0,0,5),(k,k,5)]
        swl=rule_levels(sw,[])
        tb=cx2.full_table(swl,2)
        mn=min(tb.values()); print("V pair step",k,{s:round(v-mn,5) for s,v in tb.items()},"J_e=%.5f 2J_e=%.5f"%(2*(math.exp(H/8)-1),4*(math.exp(H/8)-1)),flush=True)
