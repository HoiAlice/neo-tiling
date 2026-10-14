import sys, pickle
import enum2
enum2.R=24.0
graphs=sys.argv[1].split(",")
types,growth=enum2.collect(graphs,RE=10,G=26)
pickle.dump(types,open("enum24_types.pkl","wb"))
print("TOTAL types",len(types),"(type,bits) pairs",sum(len(v) for v in types.values()))
