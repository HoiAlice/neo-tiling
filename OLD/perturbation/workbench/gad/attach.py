from cx2 import *
if __name__=="__main__":
    g=0.01
    for a in (3.75,4.0,4.25,4.5,4.75):
        cx=2.5; c=(cx-a,cx+a)
        sw=[(0,0,5,1+g,1),(c[0]-2,c[1]-2,4,1+g,1)]
        tb=full_table(sw,2)
        print(a,"kink cost",round(tb[(0,0)]-tb[(0,1)],5),flush=True)
