# neotiling

Weak solvability of price data: exact box oracles, least perturbation radius, exact least l_p price
perturbation. Code collected from `price-perturbation/`, `l1-perturbation/`, `poly-hardness/`,
`np-hardness/` (those folders are unchanged).

Install: `pip install -e .` (extras: `.[plot]`, `.[tests]`). Needs setuptools >= 64 / a recent pip.

## Layout

- `neotiling/data/` loaders `us_d2, us_d3, bea, va_model, berndt_wood` -> `(P, y, years)`; csv files in `data/csv/`.
- `neotiling/geometry/planar.py` chain graph and flow LP for d = 2 (decision LP uses `highs-ipm`).
- `neotiling/geometry/reach.py` distance, exact simplex, weak reachability, breakpoints, Farkas check.
- `neotiling/oracle/` the oracle interface (`OracleAnswer`, `as_answer`, `CountingOracle`) and the oracles
  `brute` (tests), `flow_d2` (d = 2, polynomial), `exact` (any d, column generation with exact geometry).
- `neotiling/radius/` `least` (exact least radius, witness, refute), `weighted` (weighted/zonotope radius).
- `neotiling/lp/` exact least l_p perturbation (polyblock + MILP master + cover cuts).
- `tests/`, `experiments/` (not run by the tests), `tools/` (`build_bea.py`, `check_layout.py`).

## Tests

    python -m pytest -q -m "not slow" tests     # about 30 s
    python -m pytest -q -m slow tests           # brute-force grids and the l_p solver, several minutes

## Oracle

    from neotiling.geometry import reach
    from neotiling.oracle import as_answer
    from neotiling.oracle.exact import oracle_exact
    W = reach.corners(P, k)                      # 2T corners (P/k, P k)
    lo, hi = reach.box_bounds(len(P), y)
    ans = as_answer(oracle_exact(W, lo, hi))
    # ans.feasible; YES: ans.columns, ans.masses; NO: ans.lam (Farkas vector) and ans.covers (cover set C)

## Exact l_p perturbation

    from neotiling import data
    from neotiling.lp.problem import Problem
    from neotiling.lp.solve import solve
    P, y, years = data.us_d3()
    res = solve(Problem(P, y, p=1, metric="rel"), eps=1e-4, time_limit=600)
    # res["LB"] <= OPT <= res["UB"], res["Q"] exact rational prices, res["status"]

Command line: `python experiments/lp_runs.py us3 bea:15 va:US:M-N --p 1 --metric rel --eps 1e-4 --time-limit 600`.
Run only one solver process at a time.
