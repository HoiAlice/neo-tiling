from layout import *
K4=[(0,1),(0,2),(0,3),(1,2),(1,3),(2,3)]
rsets=[rs for k in (1,2) for rs in itertools.combinations(range(6),k)]
b=random_search(4,K4,rsets,trials=8,tl=30)
print("best collisions",b[0] if b else None, b[1:3] if b else None)
import pickle; pickle.dump(b,open("lay_k4_best.pkl","wb"))
