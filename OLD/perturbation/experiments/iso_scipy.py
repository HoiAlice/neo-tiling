"""Fast isotonic regression with convex loss f(x) = e^|x| - 1 via scipy minimize.

Also fast rho_dom via enumeration over sigma, using the scipy version internally.
"""
from __future__ import annotations
import math, itertools
import numpy as np
from scipy.optimize import minimize

def iso_cost(a: np.ndarray, edges: list[tuple[int, int]]) -> tuple[float, np.ndarray]:
    """min sum (e^|u_t - a_t| - 1) subject to u_t <= u_s for (t, s) in edges.
    Edges are u_t <= u_s. Returns (cost, u)."""
    T = len(a)
    if not edges:
        return 0.0, a.copy()
    def f(u):
        return np.sum(np.exp(np.abs(u - a)) - 1)
    def fp(u):
        d = u - a
        return np.exp(np.abs(d)) * np.sign(d)
    cons = []
    for t, s in edges:
        cons.append({"type": "ineq", "fun": lambda u, t=t, s=s: u[s] - u[t], "jac": lambda u, t=t, s=s: np.eye(T)[s] - np.eye(T)[t]})
    res = minimize(f, a.copy(), jac=fp, constraints=cons, method="SLSQP", options=dict(ftol=1e-12, maxiter=500))
    return float(res.fun), res.x


def rho_dom_fast(P: np.ndarray, y: np.ndarray) -> tuple[float, list[int], list[tuple[int, int]], np.ndarray]:
    """Rho_dom at d=2 via enumeration of sigma."""
    T = len(P)
    a = [np.log(P[:, 0]), np.log(P[:, 1])]  # log-coords
    conflicts = [(t, s) for t in range(T) for s in range(T) if y[t] > y[s]]
    if not conflicts:
        return 0.0, [], [], P.copy()
    best = (math.inf, None, None, None)
    for sigma in itertools.product((0, 1), repeat=len(conflicts)):
        edges = [[], []]
        for (t, s), i in zip(conflicts, sigma):
            edges[i].append((t, s))
        c0, u0 = iso_cost(a[0], edges[0])
        c1, u1 = iso_cost(a[1], edges[1])
        total = c0 + c1
        if total < best[0] - 1e-10:
            Q = np.exp(np.column_stack([u0, u1]))
            best = (total, list(sigma), conflicts, Q)
    return best


def pi(p, q): return max(q/p, p/q) - 1
def total_pi(P, Q): return sum(pi(P[t,i], Q[t,i]) for t in range(len(P)) for i in range(2))


if __name__ == "__main__":
    # Triangle
    P = np.array([[4,1],[3,3],[1,4]], float); y = np.array([1,5,3], float)
    r = rho_dom_fast(P, y)
    print(f"triangle rho_dom = {r[0]:.6f} (expected 0.0)  verify={total_pi(P, r[3]):.6f}")
    # T=3 chain forcing a triangle of conflicts
    P2 = np.array([[1,1],[2,2],[3,3]], float); y2 = np.array([3,2,1], float)
    r2 = rho_dom_fast(P2, y2)
    print(f"3-chain (dominated) rho_dom = {r2[0]:.6f}  sigma = {r2[1]}  conflicts = {r2[2]}  Q = {r2[3].tolist()}")
