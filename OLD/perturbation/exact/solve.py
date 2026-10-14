"""Exact minimal perturbation rho_1(P, y) = min { pi_1(P, Q) : Q >= 0, y weakly solvable at Q }.

Scheme (one iteration):

1. lower master on the current partitions -> lower bound LB (its dual bound) and Q_lo
   (iteration 0: the compact dominance form). Witness constraints are imposed only for
   the tracked indices, the rest is dropped (still a relaxation);
2. the family of the lower solution is checked exactly at Q_lo: an untracked t without
   a weak witness becomes tracked, a tracked t whose cell has no witness flags the cell;
   if everything passes, Q_lo is weakly solvable and optimal;
3. the oracle (column generation) at Q_lo, and a repair of the lower family (max-margin
   witnesses, exact LP over Q) -> exactly verified certificates, upper bounds UB;
4. every `upper_every` iterations the upper master: vertex witnesses, exact LP over Q;
5. refinement: flagged cells and their neighbours are cut into 2^depth pieces; on
   iterations 2^j - 1 the coarsest cells of all partitions are bisected.

LB is nondecreasing (nested partitions) and tends to rho_1 because the cells used by the
lower master shrink; UB tends to rho_1 because the vertices become dense and y is
strictly solvable near every weakly solvable Q (closure theorem), where witnesses form
an open set.
"""

from __future__ import annotations

import argparse
import json
import time
from fractions import Fraction

import numpy as np

from . import certify as C
from .grid import SimplexGrid
from .models import Solution, oracle, solve_master


def constant_start(P, y):
    """Certificate at a constant price set (all spectra weakly reachable there)."""
    T, d = len(P), len(P[0])
    c = []
    for i in range(d):
        col = [Fraction(P[t][i]) for t in range(T)]
        c.append(min(col, key=lambda v: sum(abs(v / p - 1) for p in col)))
    Q = [list(c) for _ in range(T)]
    levels = sorted({Fraction(v) for v in y})
    sets, m, prev = [], [], Fraction(0)
    for lv in levels:
        sets.append(frozenset(t for t in range(T) if Fraction(y[t]) >= lv))
        m.append(lv - prev)
        prev = lv
    xi = [Fraction(1, d)] * d
    wit = {(k, t): xi for k, S in enumerate(sets) for t in S}
    return Q, sets, m, wit


def _sets(Z, M=None):
    return [frozenset(np.flatnonzero(row).tolist()) for row in Z]


def _anchors(sets) -> list[int] | None:
    """Distinct anchors t_k in S_k (bipartite matching), or None."""
    owner: dict[int, int] = {}

    def augment(k, seen):
        for t in sorted(sets[k]):
            if t not in seen:
                seen.add(t)
                if t not in owner or augment(owner[t], seen):
                    owner[t] = k
                    return True
        return False

    if not all(augment(k, set()) for k in range(len(sets))):
        return None
    anchor = [0] * len(sets)
    for t, k in owner.items():
        anchor[k] = t
    return anchor


def _as_start(cert, grids, T) -> Solution | None:
    """Feed a certificate whose witnesses are grid vertices to the upper master."""
    Q, sets, m, wit = cert
    keep = [k for k in range(len(sets)) if m[k] > 0]
    anchor = _anchors([sets[k] for k in keep])
    if anchor is None:
        return None
    Z = np.ones((T, T), dtype=int)
    M = np.zeros(T)
    witness = {}
    for k, slot in zip(keep, anchor):
        Z[slot] = [int(t in sets[k]) for t in range(T)]
        M[slot] = float(m[k])
        for t in sets[k]:
            j = grids[t]._index.get(tuple(wit[k, t]))
            if j is None:
                return None
            witness[slot, t] = j
    for slot in range(T):
        for t in range(T):
            witness.setdefault((slot, t), grids[t].used_vertices()[0])
    Qf = np.array([[float(v) for v in row] for row in Q])
    return Solution("start", 0.0, 0.0, Qf, Z, M, witness=witness)


def _lower_start(cert, grids, tracked, T) -> Solution | None:
    """Feed a certificate to the lower master: true witnesses lie in some cell."""
    Q, sets, m, wit = cert
    keep = [k for k in range(len(sets)) if m[k] > 0]
    anchor = _anchors([sets[k] for k in keep])
    if anchor is None:
        return None
    Z = np.ones((T, T), dtype=int)
    M = np.zeros(T)
    cells = {}
    for k, slot in zip(keep, anchor):
        Z[slot] = [int(t in sets[k]) for t in range(T)]
        M[slot] = float(m[k])
        for t in sets[k]:
            if t in tracked:
                xi = tuple(C.F(v) for v in wit[k, t])
                cells[slot, t] = next(
                    c for c in range(len(grids[t].cells)) if grids[t].contains(c, xi)
                )
    Qf = np.array([[float(v) for v in row] for row in Q])
    return Solution("start", 0.0, 0.0, Qf, Z, M, cells=cells)


def best_witness(grid: SimplexGrid, cell: int, Q, S: frozenset, t: int):
    """max over xi in the cell of min_s <xi, q_s - q_t>, s outside S (exact LP).

    Returns (tau, xi). The cell contains a weak witness of t for S at Q iff tau >= 0.
    """
    ids = grid.cells[cell]
    d, T, n = grid.d, len(Q), len(ids)
    out = [s for s in range(T) if s not in S]
    V = [grid.vertices[j] for j in ids]
    # variables: lam_1..lam_n, tau; maximize tau
    A_ub = []
    for s in out:
        row = [-sum(v[i] * (C.F(Q[s][i]) - C.F(Q[t][i])) for i in range(d)) for v in V]
        A_ub.append(row + [Fraction(1)])
    A_ub += [[-Fraction(int(a == b)) for a in range(n)] + [Fraction(0)] for b in range(n)]
    if not out:
        A_ub.append([Fraction(0)] * n + [Fraction(1)])  # tau <= 1
    st, tau, x = C.lp(
        [Fraction(0)] * n + [Fraction(1)],
        A_ub,
        [Fraction(0)] * (len(A_ub) - (0 if out else 1)) + ([] if out else [Fraction(1)]),
        [[Fraction(1)] * n + [Fraction(0)]],
        [Fraction(1)],
        sense="max",
    )
    xi = tuple(sum(x[j] * V[j][i] for j in range(n)) for i in range(d))
    return tau, xi


def repair(P, y, Q, sets, rounds=3):
    """Upper bound from a family: max-margin witnesses at Q, exact LP over Q, repeat."""
    m = C.cone_masses(y, sets)
    if m is None:
        return None
    best = None
    for _ in range(rounds):
        wit = {
            (k, t): C.max_margin_witness(Q, S, t)[0] for k, S in enumerate(sets) for t in S
        }
        val, Qx = C.best_prices(P, y, sets, wit)
        C.verify(P, y, Qx, sets, m, wit)
        if best is not None and val >= best[0]:
            break
        best, Q = (val, (Qx, sets, m, wit)), Qx
    return best


def run(
    P, y, max_iter=50, time_limit=600.0, tol=1e-7, depth=2, upper_every=4, track_step=2,
    lazy=False, log=print,
):
    P = [[Fraction(v) for v in row] for row in P]
    y = [Fraction(v) for v in y]
    T, d = len(P), len(P[0])
    Pf = np.array([[float(v) for v in row] for row in P])
    yf = np.array([float(v) for v in y])
    grids = [SimplexGrid(d) for _ in range(T)]
    tracked: set[int] = set() if lazy else set(range(T))

    best = constant_start(P, y)
    UB = C.verify(P, y, *best)
    LB = 0.0
    history = []
    t0 = time.time()

    def offer(cand, tag):
        nonlocal UB, best, note
        if cand is not None and cand[0] < UB:
            UB, best = cand
            note += " " + tag

    for it in range(max_iter):
        tl = time.time()
        kind = "dominance" if it == 0 else "lower"
        lo = solve_master(
            Pf, yf, grids, float(UB) + 1e-9, kind, time_limit, tracked=tracked,
            start=_lower_start(best, grids, tracked, T) if kind == "lower" else None,
        )
        LB = max(LB, min(lo.bound, float(UB)))
        note = f"[lo {time.time() - tl:.1f}s"
        split, newly, sets = {}, set(), []
        if lo.Q is not None:
            Qlo = [[Fraction(float(v)) for v in row] for row in lo.Q]
            # 1. the family of the lower solution, checked exactly at Q_lo
            viol = {}
            if lo.z is None:
                sets, cells = [], {}  # iteration 0: no family, nothing to refine
            else:
                sets, cells = [], {}
                for k in range(len(lo.z)):
                    S = frozenset(np.flatnonzero(lo.z[k]).tolist())
                    if lo.m[k] > 1e-12 and S:
                        cells.update({(len(sets), t): lo.cells.get((k, t)) for t in S})
                        sets.append(S)
            for k, S in enumerate(sets):
                for t in S:
                    if t in tracked:
                        cell = cells[k, t]
                        tau, xi = best_witness(grids[t], cell, Qlo, S, t)
                        if tau < 0:
                            split.setdefault((t, cell), xi)
                    else:
                        tau = C.max_margin_witness(Qlo, S, t)[1]
                        if tau < 0:
                            viol[t] = min(tau, viol.get(t, tau))
            newly = set(sorted(viol, key=viol.get)[:track_step])
            if lo.z is not None and not split and not viol:
                found = C.weakly_solvable(Qlo, y, sets)
                if found is not None:
                    offer((C.verify(P, y, Qlo, *found), (Qlo, *found)), "FAMILY")
            # 2. the oracle at Q_lo
            if float(UB) - LB > tol:
                tl = time.time()
                ok, cand = oracle(lo.Q, yf, time_limit)
                note += f" or {time.time() - tl:.1f}s"
                if ok:
                    found = C.weakly_solvable(Qlo, y, cand)
                    if found is not None:
                        offer((C.verify(P, y, Qlo, *found), (Qlo, *found)), "ORACLE")
            # 3. repair of the lower family (iteration 0: the level sets of y)
            if float(UB) - LB > tol:
                offer(repair(P, y, Qlo, sets or constant_start(P, y)[1]), "REPAIR")
        # 4. the upper master (needed for the convergence of UB)
        if float(UB) - LB > tol and it > 0 and it % upper_every == 0:
            tl = time.time()
            up = solve_master(
                Pf, yf, grids, float(UB) + 1e-9, "upper", time_limit,
                start=_as_start(best, grids, T),
            )
            note += f" up {time.time() - tl:.1f}s"
            if up.Q is not None:
                usets = _sets(up.z)
                wit = {
                    (k, t): grids[t].vertices[up.witness[k, t]]
                    for k, S in enumerate(usets)
                    for t in S
                }
                m = C.cone_masses(y, usets)
                if m is not None:
                    val, Qx = C.best_prices(P, y, usets, wit)
                    C.verify(P, y, Qx, usets, m, wit)
                    offer((val, (Qx, usets, m, wit)), "UPPER")
        note += "]"
        gap = float(UB) - LB
        nv = sum(len(g.cells) for g in grids)
        history.append((it, LB, float(UB), nv, time.time() - t0))
        log(f"it {it:2d}  LB {LB:.9f}  UB {float(UB):.9f}  gap {gap:.2e}  "
            f"tracked {len(tracked):3d}  cells {nv:4d}  {time.time() - t0:7.1f}s {note}")
        if gap <= tol:
            break
        # refinement: new tracked indices, flagged cells with their neighbours
        tracked |= newly
        todo = set()
        for t, cell in split:
            ids = set(grids[t].cells[cell])
            todo |= {(t, c) for c, cs in enumerate(grids[t].cells) if ids & set(cs)}
        for t, cell in sorted(todo, key=lambda x: (x[0], -x[1])):
            grids[t].subdivide(cell, depth)
        # global refinement on iterations 7, 15, 31, ..., or when nothing else changed
        if (not todo and not newly and kind == "lower") or (
            it >= 7 and (it + 2) & (it + 1) == 0
        ):
            for g in grids:
                g.refine_coarsest()
    return LB, UB, best, history


def main():
    ap = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    ap.add_argument("instance", help="JSON file with keys P (T x d) and y (T)")
    ap.add_argument("--iters", type=int, default=50)
    ap.add_argument("--time", type=float, default=600.0)
    ap.add_argument("--out", help="write the certificate here (JSON, exact fractions)")
    a = ap.parse_args()
    data = json.load(open(a.instance))
    LB, UB, (Q, sets, m, wit), _ = run(data["P"], data["y"], a.iters, a.time)
    print(f"rho_1 in [{LB:.9f}, {float(UB):.9f}]  UB = {UB}")
    if a.out:
        json.dump(
            {
                "UB": str(UB),
                "LB": LB,
                "Q": [[str(v) for v in row] for row in Q],
                "sets": [sorted(S) for S in sets],
                "m": [str(v) for v in m],
                "witness": {f"{k},{t}": [str(v) for v in xi] for (k, t), xi in wit.items()},
            },
            open(a.out, "w"),
            indent=1,
        )


if __name__ == "__main__":
    main()
