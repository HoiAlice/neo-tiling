# Solvability in the plane in polynomial time, and the minimal price perturbation

Companion of `np-hardness/` (d = 3 is NP-hard). Here d = 2.

* `poly-hardness.tex` — the text (Russian), self-contained modulo the criteria of
  `latex/notes.tex` and the chain theorem of `complexity/complexity.tex`.
* `lean/PolyHardness/` — Lean 4, no `sorry`, standard axioms only. Not in the lakefile; check
  from the repository root:

  ```
  lake env lean poly-hardness/lean/PolyHardness/FlowLP.lean     # imports Complexity
  lake env lean poly-hardness/lean/PolyHardness/Blocking.lean   # imports Algorithms.Cuts
  ```

  (`Complexity` and `Algorithms` must be built: `lake build Complexity Algorithms`.)

## Part 1. (Weak) solvability at fixed prices, d = 2: one LP

The chain graph `G_P` has a node "the chain starts at b" for every index and a node "the last
edge is a b" for every pair; its source–sink paths are the strictly convex lower-left chains.
Every arc carries the indices of its vertical slab that are outside the region of the chain
(`Out`) or on its boundary (`Bnd`).

* `isReachableB_iff_path`: S is (weakly) reachable iff `Out(π) ⊆ S ⊆ Out(π) ∪ β Bnd(π)` for a
  path π (β = 1 weak, β = 0 strict).
* `mem_indicatorCone_iff_flow`: y is (weakly) solvable iff there are a flow f and a vector g with
  `y = Σ_e f_e 1_{Out e} + g`, `0 ≤ g ≤ β Σ_e f_e 1_{Bnd e}`. O(T³) variables, O(T²) rows.
  The proof includes the flow decomposition (`flow_decomposition`) and the cube lemma
  (`cube_mem_span`).
* Consequences (text): WS(2) is in P in both modes; the column problem is a longest path,
  O(T⁴); infeasibility gives a Farkas vector w with ⟨w, y⟩ < 0 and w(S) ≥ 0 on the family.

Code: `planar.py` (graph, LP, column problem, exact certificates `certify` /
`check_certificate`, brute-force `family` by the definition). Tests: `tests/test_planar.py`.

## Part 2. Minimal price perturbation, d = 2, any convex separable cost

`ρ_c(P, y) = min { Σ φ(r(p, q)) : y weakly solvable at Q }`, r = log(q/p) or q/p, φ convex.
Costs in the code: `log` = Σ|log(q/p)| (main), `pi` = Σ (max(q/p, p/q) − 1) (the notes),
`eps` = Σ|q/p − 1|.

Method (`perturb2d.py`): cutting planes.

* Separation is the LP of Part 1 (polynomial, exact). A Farkas vector gives a cut: a disjunction
  "t is blocked by R" over pairs (t, R), |R| ≤ 2. Pairs suffice in the plane (Helly on a
  segment).
* The master `min c(Q)` subject to the cuts is a lower bound. It is solved by branch and bound
  without any external nonlinear solver. Blocking by a pair has four explicit forms
  (`isBlocked_pair_iff`): two order constraints, and "q_t under a point of the segment q_r q_s"
  in two orientations. Nodes are LPs: isotonic regressions, plus McCormick / tangent / secant
  envelopes for the segment form, with spatial branching and an exact pruning test
  (`IsBlocked.mono`).
* The upper bound is certified exactly in rationals: the tilt of the notes, then `planar.certify`.

Lean (`Blocking.lean`): `isBlocked_two_iff`, `isBlocked_iff_pairs`, `isBlocked_pair_iff`,
`IsBlocked.mono`, `exists_pair_cover`, `exists_min_cost` (the minimum exists for every
continuous coercive φ of log(q/p)). Cut validity is `exists_isBlocked_of_cut` in
`Algorithms/Cuts.lean`.

Not formalized: the complexity-class statement, correctness of the branch and bound and
finiteness of the loop (on paper, text §4).

## Results

RESULTS

## Running

From this folder, with the project venv (`../.venv/bin/python`):

| script | what |
|---|---|
| `python -m pytest -q tests` | planar LP vs brute force (family, cone, column problem, certificates) |
| `run_bw.py [log pi eps]` | six planar Berndt–Wood series → `results/bw_<cost>.txt` |
| `run_klems.py <cost> [limit]` | 120 planar EU KLEMS slices → `results/klems_<cost>.txt` |
| `exp_random.py [n] [limit]` | random instances, three costs → `results/random.txt` |
| `exp_compare_scip.py [n]` | cost pi vs the SCIP cut method of `code/perturbation` |

`data.py` reads `../code/data` (Berndt–Wood file, EU KLEMS via `code/perturbation/datasets.py`)
without copying it.
