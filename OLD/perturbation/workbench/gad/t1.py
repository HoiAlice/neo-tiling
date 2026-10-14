from core import *
P = np.array([[4,1],[3,3],[1,4]], float); y = np.array([1,5,3], float)
print(solve_dom(np.log(P), y))
P2 = np.array([[1,1],[2,2],[3,3]], float); y2 = np.array([3,2,1], float)
print(solve_dom(np.log(P2), y2))
print(weakly_solvable(P,y))
