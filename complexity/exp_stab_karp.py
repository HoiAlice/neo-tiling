"""Experiment (idea for a Karp reduction): (1/3)*1 in STAB(G x K3) iff G is 3-colourable.

G x K3 (Cartesian product): vertices (v, c), triangles {(v,0),(v,1),(v,2)} and edges
(u,c)-(v,c) for uv in E.  Clique inequalities force every stable set in a decomposition of
(1/3)*1 to pick one vertex per triangle (a proper colouring); conversely the three cyclic
colour shifts of a colouring average to (1/3)*1.  Checked by brute force on small graphs:
membership by an LP over all maximal-or-not stable sets of G x K3."""
import itertools
import random

from wsolv import in_cone


def stable_sets(n, edges):
    adj = [set() for _ in range(n)]
    for u, v in edges:
        adj[u].add(v)
        adj[v].add(u)
    out = []

    def rec(i, cur):
        if i == n:
            out.append(frozenset(cur))
            return
        rec(i + 1, cur)
        if not any(j in adj[i] for j in cur):
            rec(i + 1, cur + [i])

    rec(0, [])
    return out


def product_k3(n, edges):
    idx = lambda v, c: 3 * v + c  # noqa: E731
    E = [(idx(v, a), idx(v, b)) for v in range(n) for a, b in ((0, 1), (1, 2), (0, 2))]
    E += [(idx(u, c), idx(v, c)) for u, v in edges for c in range(3)]
    return 3 * n, E


def three_colourable(n, edges):
    return any(all(col[u] != col[v] for u, v in edges)
               for col in itertools.product(range(3), repeat=n))


def third_in_stab(n, edges):
    N, E = product_k3(n, edges)
    lifted = [S | {N} for S in stable_sets(N, E)]  # (x, 1) in cone{(1_I, 1)}
    return in_cone(lifted, [1 / 3] * N + [1.0], N + 1)


random.seed(3)
named = {
    "K3": (3, [(0, 1), (1, 2), (0, 2)]),
    "K4": (4, list(itertools.combinations(range(4), 2))),
    "C5": (5, [(i, (i + 1) % 5) for i in range(5)]),
    "W5 (wheel, chi=4)": (6, [(i, (i + 1) % 5) for i in range(5)] + [(i, 5) for i in range(5)]),
}
for k in range(6):
    n = random.randint(4, 6)
    E = [e for e in itertools.combinations(range(n), 2) if random.random() < 0.5]
    named[f"random{k} n={n} m={len(E)}"] = (n, E)
bad = 0
for name, (n, E) in named.items():
    a, b = three_colourable(n, E), third_in_stab(n, E)
    bad += a != b
    print(f"{name:28s} 3-colourable={a!s:5s} (1/3)1 in STAB(GxK3)={b}")
print("mismatches", bad)
