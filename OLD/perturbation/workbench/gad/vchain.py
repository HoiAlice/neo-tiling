from cx2 import *
if __name__=="__main__":
    for k in (0.5,1,1.5,2,3):
        sw=[(0,0,4,2,1),(k,k,4,1,0)]
        tb=full_table(sw,4)
        print(k,{''.join(map(str,s)):round(v,4) for s,v in tb.items()})
