# hex-perturbation

Exact least hexagonal perturbation radius for weak solvability at d = 2.

## Problem

Prices `p_t` in R^2_{++} (t in [T]) are normalised 3D prices `(p1/p3, p2/p3)`.  The distance of
normalised points is the hexagonal norm in log space,
`dhat(a, b) = max(|u1|, |u2|, |u1 - u2|)`, `u_i = ln a_i - ln b_i`.
Given outputs `y >= 0`, find `rho* = min_Q max_t dhat(q_t, p_t)` over all `Q` at which `y` is weakly
solvable.

## Facts

1. The hexagon of radius `rho` around `ln p_t` lies in the square `[-rho, rho]^2` and contains its
   diagonal.  By the box theorem a solution can be put on the diagonals, so
   "feasible with hexagons of radius rho" <=> `BOX(p e^{-rho}, p e^{rho}, y)` (`box.py`).
   Hence `rho*_hex = rho*_box`, and `q_t = p_t e^{s_t}`, `|s_t| <= rho`.
2. The weakly reachable family is invariant under a common scaling of all points, so the corners
   can be `(p_t, z p_t)`, `z = e^{2 rho}`.  The code uses `z = k^2` with rational `k`, i.e. the
   box `(P/k, P k)`, so everything stays rational.
3. The chain graph of the corners depends only on the signs of coordinate differences and of cross
   products of corner triples.  Each is a polynomial in `z` of degree <= 2 with rational
   coefficients.  Between consecutive real roots (> 1) the combinatorics is constant, so BOX
   feasibility is constant on each open gap.  Feasibility is monotone in `z` and the feasible set
   is closed, so `rho* = 0` if `z = 1` is feasible, otherwise `rho* = (1/2) ln z_k`, where `z_k` is
   the left endpoint of the first feasible gap.

## Algorithm (`hex.py`)

* `breakpoints(P)`: all polynomials from fact 3 (O(T^2) pair differences, O(T^3) triples), their
  roots `z > 1`, deduplicated and sorted exactly.  A root is an `Alg` = `alpha + beta sqrt(D)` with
  rational parts.  Equality is exact through a canonical key (rational value, or the primitive
  irreducible quadratic plus the sign of the square root).  Order and equality are decided
  exactly by squaring (`sign_lin`, `sign3`); mpmath is used only to pre-sort.
* `gap_point`, `gap_points`: a rational `k` with `k^2` strictly inside each gap (checked exactly).
* `least_radius_exact(P, y)`: tests `z = 1`, then the last gap, then binary search over gaps by
  monotonicity with the float LP oracle `box.decide`.  Number of oracle calls
  O(log #breakpoints) = O(log T), since #breakpoints = O(T^3).
* `certify_result(P, y, res)`: NO certificate `box.refute` at the gap point below, YES certificate
  `box.witness` (+ `box.certify`) at the gap point above, and the exact check that the witness
  lies in the hexagons of radius `ln k_above` (`in_hex_exact`).

The only floating-point step is the LP oracle's yes/no answer, and both sides of the final answer
are certified exactly.

## Run

```
cd hex-perturbation
PYTHONDONTWRITEBYTECODE=1 ../.venv/bin/python example.py        # US data, T = 26, writes example.png
PYTHONDONTWRITEBYTECODE=1 ../.venv/bin/python -m pytest -p no:cacheprovider tests
```

## Lean

`lean/HexPerturbation/Hex.lean` (build: `lake build HexPerturbation` from the repository root; no
`sorry`, standard axioms only).  `Support.lean` and `Box.lean` are copies of
`OLD/box-perturbation/lean`.

* `hex_iff_scale`: some `Q` with `hexDist (q_t, p_t) <= rho` makes `y` weakly solvable iff some
  rescaling `c_t p_t`, `e^{-rho} <= c_t <= e^{rho}`, does (fact 1).
* `hex_iff_corners`: the same iff the corner cone condition on `(e^{-rho} P, e^{rho} P)`.

* `proj_iff_scale`, `proj_iff_corners` (`Proj.lean`): the same for every d >= 2 with `projDist`.
* `least_radius_breakpoint` (`Radius.lean`, linear algebra in `LocalConstancy.lean`): if some
  radius is feasible, the feasible radii are `[rho*, inf)`, and `rho* = 0` or some non-identically
  zero (d+1)-minor of the homogenized corners vanishes at `rho*` (facts 3 and closedness).

Not formalized: rationality of breakpoints, the algorithm and its complexity, certificates.

The text with all proofs: `hex-perturbation.tex` (Russian, self-contained modulo `latex/notes.tex`).

`box.py` is copied from `OLD/box-perturbation/box.py` (only the `sys.path` line differs).

## General d (`proj.py`)

Prices are normalised (d+1)-dimensional prices, `p_t in R^d_{++}`; `dist(a, b)` is the sum of absolute
deviations of `(u_1, .., u_d, 0)` from its median (`u = ln a - ln b`).  The ball of radius `rho` lies in
the cube `|u_i| <= rho` and contains the diagonal, so the problem is BOX at the corners `(P/k, P k)`,
`k^2 = z = e^{2 rho}`, for every d >= 2.

* `breakpoints(P)`: all `(d+1)`-subsets of the `2T + d` vectors `(p_t, 1)`, `(z p_t, 1)`, `(e_i, 0)`.
  Finding: each determinant is `z^{b-1} (D0 z + D1)` (the rows `(z x, 1)` differ from `(x, 1)` by a
  rank-one term), so all breakpoints are RATIONAL: no algebraic numbers, no factorisation.  For d = 2
  this reproduces `hex.py` exactly (US data: 8310 breakpoints).  US data, d = 3, T = 26: 341055
  determinants, 127160 breakpoints, 30 s.
* Oracle = black box `oracle(W, lo, hi) -> bool | OracleAnswer`: exists `w` in the cone of weakly
  reachable sets of `W` with `lo <= w <= hi`.  Reference oracles: `oracle_brute` (any d, exact),
  `oracle_flow` (d = 2, box form).  `least_radius_exact` uses only the booleans.
* `witness` (YES, needs columns + masses) and `refute` (NO, needs lambda; the global check
  `lambda(S) >= 0` is delegated to an optional column oracle) work when the oracle supplies them.
* `example_d3.py`: breakpoint statistics for the US data at d = 3.

## PLACEHOLDER MILP oracle (`milp_oracle.py`)

`oracle_milp(W, lo, hi)`: temporary stand-in for the real MILP oracle, to be replaced.  The
formulation of `OLD/code/perturbation/model.py` at fixed prices: K = |W| sets (Caratheodory),
binaries `z[k,r]`, masses `m[k] <= Y` (Y = max finite bound), McCormick `v = m z`, witnesses in the
simplex with big-M `M_st = max_i |W_s^i - W_t^i|`, bounds `lo <= sum_k v[k,r] <= hi`.  HiGHS via
`scipy.optimize.milp`; YES answers are certified exactly when the support allows it, NO answers
carry no Farkas vector.  `tests/test_milp_oracle.py` checks it against `oracle_brute` (d = 3,
T <= 4) and `oracle_flow` (d = 2).  On the US data at d = 3 (52 corners) it gives no decision
within 300 s.
