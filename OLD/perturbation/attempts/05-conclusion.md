# Attempt 5: synthesis and tentative polynomial-time conjecture

## Summary of the day's work

* **No NP-hardness reduction found.** Four reduction angles tried (SET COVER, NAE-3SAT
  via chain triangles, assignment-gadget CSP, star gadgets); each failed for a
  specific structural reason.
* **Several structural reasons point AWAY from NP-hardness** of `ρ_dom` at `d = 2`:
  - `y`-chain triangles are **ferromagnetic**: the pure-chain pool is cheapest, so
    chain gadgets cannot encode NAE.
  - Star gadgets with symmetric leaves are also ferromagnetic.
  - Anisotropic configurations produce "assignment gadgets" (force a single `σ`
    pattern) but not NAE gadgets. CSP by assignment gadgets is poly-solvable by
    unit propagation.
* **One structural reason points TOWARD NP-hardness**: the isotonic-regression
  cost `g_i(E)` is supermodular on constraint sets, and min-sum of two
  supermodular functions over coverings is a hard family in general.
* **Literature survey**: the `d = 2 / d ≥ 3` split holds for `GARP deletion`
  (Boodaghians–Vetta 2015), `POSET DIMENSION` (Yannakakis 1982), and our
  fixed-prices oracle. No source settles our `ρ` at `d = 2`.

## Tentative conjecture

`ρ_dom(P, y)` at `d = 2` is **polynomial-time computable**.

Supporting evidence:

* Gadgetability is weak (no NAE forcing, only assignment forcing); assignment
  CSPs are poly-solvable.
* Fixed-coordinate variant is poly (two isotonic regressions). The combinatorial
  layer is "assign each pair to one of 2 coords"; this feels tractable.
* The dominance conflict digraph is a transitive tournament (`y`-order), and
  the two orders on the coordinates have specific geometric structure.

A plausible algorithmic skeleton (not yet implemented):

1. Reorder the conflicts by `y`-rank: `(t_1, s_1), (t_2, s_2), ...` with each
   `t_i, s_i` taking `y`-ranks in a prefix of the total order.
2. Dynamic programming over the "state" `(current_coord_0_ordering,
   current_coord_1_ordering)`. Each new pair either extends an existing
   coord-order or merges partial orders. State grows polynomially in a special
   case (e.g., when each new pair touches only vertices already placed).
3. Alternatively: Lagrangian relaxation of the pair-selector `σ` with the
   isotonic cost; argue the LP relaxation is integral by a consecutive-ones
   argument on the pair-selector matrix.

Both skeletons are unverified; the DP state space is likely to blow up without a
nontrivial structural lemma. I did not reach a working algorithm this session.

## For `ρ` (not just `ρ_dom`)

`ρ = ρ_dom + extra pair-blocking constraints`. On the random `d = 2` instances
tested, `ρ = ρ_dom` almost always; the triangle example (`T = 3`) shows strict
inequality is possible. For a reduction from `ρ_dom` to `ρ` to transfer any
hardness result, the construction must avoid activating pair blockings; this is
non-trivial but seems achievable (large coordinate separation).

## State of this subproject

* `perturbation/lean/Perturbation/Decision.lean`: formal definition of the full
  `ρ`-decision problem. Builds; 0 `sorry`.
* `perturbation/experiments/`: `explore_d2.py` (SCIP-based `ρ_full`) and
  `fast_d2.py`, `iso_scipy.py` (scipy-based `ρ_dom` with fast enumeration).
* `perturbation/attempts/*.md`: this file plus `01`, `02`, `03`, `04`
  documenting the research path.
* `perturbation/perturbation.tex`: a stub.
* `scratchpad/`: literature and research files (`LITERATURE-D2.md`,
  `BV-TECHNIQUE.md`, `REDUCTION-SOURCES.md`, plus the Python exploration
  scripts).

## What a next session should do

1. **Prove a formal structural lemma** in Lean: isotonic-regression cost is
   supermodular, AND the specific gadget-ability bound: no 3-conflict configuration
   has a NAE-type cost function. If the latter is provable, it rules out a large
   class of reductions.
2. **Attempt the DP** sketched above on small `T` (say `T ≤ 10`) and see whether
   the state space blows up or stays polynomial.
3. **Consult experts in combinatorial optimization** (the problem has a
   scheduling / disjunctive-order flavour; there may be known results).
4. **If the DP works, formalize it in Lean** following the pattern of
   `poly-hardness/lean/PolyHardness/FlowLP.lean`.

The problem is genuinely open on the evidence I collected.
