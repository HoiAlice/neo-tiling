"""The perturbation problem (notes, def:model) as a SCIP model.

Variables, for t in [T], i in [d], k in [K]:
  a[t,i] in [1/(1+D), 1+D]          multipliers q = p * a
  g[t,i] in [0, D]                  perturbations: g >= a - 1, g >= 1/a - 1 (convex)
  z[k,t] binary                     spectra S_k = {t | z[k,t] = 1}
  m[k], w[k,t] in [0, Y]            masses and their products with the indicators
  xi[k,t,i] in [0, 1], sum_i = 1    witnesses in the simplex
Constraints: sum_k w[k,t] = y_t; linearized w = m z; witnesses for s != t
  sum_i xi[k,t,i] (p^i_s a[s,i] - p^i_t a[t,i]) >= -M_st (1 - z[k,t] + z[k,s]),
either with big-M or as indicator constraints on an auxiliary value r[k,t,s].
Objective: minimize sum g. The value is rho(P, y) (notes, thm:value) once D >= D(kappa).
"""

from __future__ import annotations

import time
from dataclasses import dataclass
from typing import TYPE_CHECKING

from pyscipopt import SCIP_PARAMSETTING, Model, quicksum

if TYPE_CHECKING:
    from .prep import Prepared

HALF = 0.5  # rounding threshold for binaries
MASS_EPS = 1e-9  # spectra with smaller mass are dropped from the report


@dataclass(frozen=True)
class Solution:
    status: str
    value: float
    bound: float  # global dual bound
    seconds: float
    a: tuple[tuple[float, ...], ...]  # multipliers, normalized coordinates (invariant)
    spectra: tuple[tuple[frozenset[int], float], ...]  # (S_k, m_k) with m_k > 0
    witnesses: dict[
        tuple[int, int], tuple[float, ...]
    ]  # (k, t) -> xi, normalized coordinates

    @property
    def gap(self) -> float:
        return abs(self.value - self.bound) / max(abs(self.value), 1e-9)


def build(  # noqa: PLR0912
    prep: Prepared,
    K: int | None = None,
    indicator: bool = False,
    symmetry: bool = True,
    D: float | None = None,
) -> tuple[Model, dict]:
    """`D` overrides the bound of `prep` (a known incumbent value tightens the box)."""
    T, d, P, y = prep.T, prep.d, prep.P, prep.y
    D = prep.D if D is None else D
    K = T if K is None else K
    Y = max(y) if y else 0.0
    lo, hi = 1 / (1 + D), 1 + D
    M = {
        (s, t): (1 + D) * sum(P[s][i] + P[t][i] for i in range(d))
        for s in range(T)
        for t in range(T)
        if s != t
    }
    model = Model("perturbation")
    a = {
        (t, i): model.addVar(f"a_{t}_{i}", lb=lo, ub=hi)
        for t in range(T)
        for i in range(d)
    }
    g = {
        (t, i): model.addVar(f"g_{t}_{i}", lb=0, ub=D)
        for t in range(T)
        for i in range(d)
    }
    z = {
        (k, t): model.addVar(f"z_{k}_{t}", vtype="B")
        for k in range(K)
        for t in range(T)
    }
    m = {k: model.addVar(f"m_{k}", lb=0, ub=Y) for k in range(K)}
    w = {
        (k, t): model.addVar(f"w_{k}_{t}", lb=0, ub=Y)
        for k in range(K)
        for t in range(T)
    }
    xi = {
        (k, t, i): model.addVar(f"xi_{k}_{t}_{i}", lb=0, ub=1)
        for k in range(K)
        for t in range(T)
        for i in range(d)
    }
    for t in range(T):
        for i in range(d):
            model.addCons(g[t, i] >= a[t, i] - 1)
            model.addCons(g[t, i] >= 1 / a[t, i] - 1)  # convex on a > 0
    for t in range(T):
        model.addCons(quicksum(w[k, t] for k in range(K)) == y[t])
        for k in range(K):
            model.addCons(w[k, t] <= Y * z[k, t])
            model.addCons(w[k, t] <= m[k])
            model.addCons(w[k, t] >= m[k] - Y * (1 - z[k, t]))
            if y[t] == 0:
                model.chgVarUb(z[k, t], 0)
    for k in range(K):
        for t in range(T):
            model.addCons(quicksum(xi[k, t, i] for i in range(d)) == 1)
            for s in range(T):
                if s == t:
                    continue
                lhs = quicksum(
                    xi[k, t, i] * (P[s][i] * a[s, i] - P[t][i] * a[t, i])
                    for i in range(d)
                )
                if indicator:
                    bound = (1 + D) * max(sum(P[s]), sum(P[t]))
                    r = model.addVar(f"r_{k}_{t}_{s}", lb=-bound, ub=bound)
                    u = model.addVar(f"u_{k}_{t}_{s}", vtype="B")
                    model.addCons(r == lhs)
                    model.addCons(u >= z[k, t] - z[k, s])
                    model.addConsIndicator(r >= 0, binvar=u)
                else:
                    model.addCons(lhs >= -M[s, t] * (1 - z[k, t] + z[k, s]))
    if symmetry:
        for k in range(K - 1):
            model.addCons(m[k] >= m[k + 1])
    model.setObjective(quicksum(g.values()), "minimize")
    return model, {"a": a, "g": g, "z": z, "m": m, "w": w, "xi": xi}


def start_family(y: tuple[float, ...], kind: str) -> list[tuple[frozenset[int], float]]:
    """Spectra and masses of the start point, ordered by decreasing mass.

    "singletons": S_t = {t} with mass y_t. "layers": the layer cake of y, nested spectra
    {t | y_t >= level} with the gaps between consecutive levels as masses. Both are
    weakly reachable at the hyperbola prices, where every t has a witness against all
    other indices, so both give feasible start points of the same cost D(kappa)."""
    T = len(y)
    if kind == "singletons":
        family = [(frozenset({t}), y[t]) for t in range(T) if y[t] > 0]
    elif kind == "layers":
        levels = sorted({v for v in y if v > 0})
        family = []
        prev = 0.0
        for level in levels:
            family.append(
                (frozenset(t for t in range(T) if y[t] >= level), level - prev)
            )
            prev = level
    else:
        raise ValueError(f"unknown start family {kind}")
    return sorted(family, key=lambda sm: -sm[1])


def add_start(
    model: Model, v: dict, prep: Prepared, K: int, kind: str = "singletons"
) -> bool:
    """The hyperbola start point with the family `kind` (see `start_family`)."""
    T, d, y = prep.T, prep.d, prep.y
    family = start_family(y, kind)[:K]
    sol = model.createSol()
    for t in range(T):
        for i in range(d):
            at = prep.start_a[t][i]
            model.setSolVal(sol, v["a"][t, i], at)
            model.setSolVal(sol, v["g"][t, i], max(at, 1 / at) - 1)
    for k in range(K):
        S, mass = family[k] if k < len(family) else (frozenset(), 0.0)
        model.setSolVal(sol, v["m"][k], mass)
        for t in range(T):
            on = float(t in S)
            model.setSolVal(sol, v["z"][k, t], on)
            model.setSolVal(sol, v["w"][k, t], mass * on)
            q = [prep.P[t][i] * prep.start_a[t][i] for i in range(d)]
            raw = [1 / q[0], 1 / q[1]] + [0.0] * (d - 2)
            total = sum(raw)
            for i in range(d):
                model.setSolVal(sol, v["xi"][k, t, i], raw[i] / total)
    return model.addSol(sol, free=True)


def solve(  # noqa: PLR0913, PLR0917
    prep: Prepared,
    K: int | None = None,
    indicator: bool = False,
    symmetry: bool = True,
    start: bool = True,
    start_kind: str = "singletons",
    time_limit: float | None = None,
    verbose: bool = False,
    D: float | None = None,
    params: dict | None = None,
    exact: bool = False,
    stall_nodes: int = 5000,
) -> Solution:
    """`D` tightens the box to a known upper bound on rho; `params`: SCIP settings.

    By default the heuristic mode: the hyperbola start point, aggressive heuristics, and
    the search stops after `stall_nodes` nodes without an improvement. No certificate:
    the dual bound is reported but is typically 0 on real data. `exact=True` runs the
    plain branch and bound to optimality (feasible for T <= 4 or so)."""
    T, d = prep.T, prep.d
    K = T if K is None else K
    model, v = build(prep, K, indicator, symmetry, D)
    if not exact:
        model.setHeuristics(SCIP_PARAMSETTING.AGGRESSIVE)
        model.setParam("limits/stallnodes", stall_nodes)
    for name, value in (params or {}).items():
        model.setParam(name, value)
    if not verbose:
        model.hideOutput()
    if time_limit is not None:
        model.setParam("limits/time", time_limit)
    if start:
        add_start(model, v, prep, K, start_kind)
    t0 = time.perf_counter()
    model.optimize()
    seconds = time.perf_counter() - t0
    status = model.getStatus()
    if model.getNSols() == 0:
        return Solution(status, float("inf"), model.getDualbound(), seconds, (), (), {})
    val = model.getVal
    a = tuple(tuple(val(v["a"][t, i]) for i in range(d)) for t in range(T))
    spectra = []
    witnesses = {}
    for k in range(K):
        mk = val(v["m"][k])
        S = frozenset(t for t in range(T) if val(v["z"][k, t]) > HALF)
        if mk > MASS_EPS and S:
            j = len(spectra)  # witnesses are keyed by the position in `spectra`
            spectra.append((S, mk))
            for t in S:
                witnesses[j, t] = tuple(val(v["xi"][k, t, i]) for i in range(d))
    return Solution(
        status=status,
        value=model.getObjVal(),
        bound=model.getDualbound(),
        seconds=seconds,
        a=a,
        spectra=tuple(spectra),
        witnesses=witnesses,
    )
