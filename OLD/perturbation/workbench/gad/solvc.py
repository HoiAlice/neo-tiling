from cprime import *
if __name__=="__main__":
    sw,idx=build_c()
    print(solv(sw,idx,[(0,1,0,1),(0,1,1,0),(1,0,0,1),(1,0,1,0)]),flush=True)
