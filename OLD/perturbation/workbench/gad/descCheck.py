import sys, pickle, collections
import enum2
R=float(sys.argv[1]); RE=int(sys.argv[2]); G=int(sys.argv[3])
enum2.R=R
W=pickle.load(open("descW_types_%d.pkl"%int(R),"rb"))
graphs="P3,Star13,C4,C5,K3,K4-e,Theta,Bull,K4,Prism,K33,Q3,Petersen".split(",")
types,growth=enum2.collect(graphs,RE=RE,G=G,verbose=False)
missT=[k for k in types if k not in W]; missB=[(k,b) for k,d in types.items() if k in W for b in d if b not in W[k]]
print("R",R,"graphs types",len(types),"witness types",len(W),"types NOT in witness set:",len(missT),"local bit patterns not in witness set:",len(missB),"witness types not seen in graphs:",len([k for k in W if k not in types]))
