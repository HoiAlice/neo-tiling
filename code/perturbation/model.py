"""The perturbation problem (notes, def:model) as a SCIP model.

Variables, for t in [T], i in [d], k in [K]:
  a[t,i], b[t,i] in [1/(1+D), 1+D]  multipliers q = p * a and their inverses
  g[t,i] in [0, D]                  perturbations: g >= a - 1, g >= b - 1, a b >= 1
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

from pyscipopt import Model, quicksum

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
) -> tuple[Model, dict]:
    T, d, P, y, D = prep.T, prep.d, prep.P, prep.y, prep.D
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
    b = {
        (t, i): model.addVar(f"b_{t}_{i}", lb=lo, ub=hi)
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
            model.addCons(g[t, i] >= b[t, i] - 1)
            model.addCons(a[t, i] * b[t, i] >= 1)
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
    return model, {"a": a, "b": b, "g": g, "z": z, "m": m, "w": w, "xi": xi}


def add_start(model: Model, v: dict, prep: Prepared, K: int) -> bool:
    """The hyperbola start point: singleton spectra ordered by decreasing y."""
    T, d, y = prep.T, prep.d, prep.y
    order = sorted(range(T), key=lambda t: -y[t])[:K]
    sol = model.createSol()
    for t in range(T):
        for i in range(d):
            at = prep.start_a[t][i]
            model.setSolVal(sol, v["a"][t, i], at)
            model.setSolVal(sol, v["b"][t, i], 1 / at)
            model.setSolVal(sol, v["g"][t, i], max(at, 1 / at) - 1)
    for k in range(K):
        t0 = order[k] if k < len(order) else None
        model.setSolVal(sol, v["m"][k], y[t0] if t0 is not None else 0.0)
        for t in range(T):
            on = float(t == t0)
            model.setSolVal(sol, v["z"][k, t], on)
            model.setSolVal(sol, v["w"][k, t], y[t] * on)
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
    time_limit: float | None = None,
    verbose: bool = False,
) -> Solution:
    T, d = prep.T, prep.d
    K = T if K is None else K
    model, v = build(prep, K, indicator, symmetry)
    if not verbose:
        model.hideOutput()
    if time_limit is not None:
        model.setParam("limits/time", time_limit)
    if start:
        add_start(model, v, prep, K)
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
