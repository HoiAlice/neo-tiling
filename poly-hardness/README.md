# Solvability in the plane in polynomial time

Companion of `np-hardness/` (d = 3 is NP-hard). Here d = 2: (weak) solvability at fixed prices
is one linear program.

* `poly-hardness.tex` — the text (Russian), self-contained modulo the criteria of
  `latex/notes.tex`.
* `lean/PolyHardness/` — Lean 4, no `sorry`, standard axioms only, depends only on
  `NeoTiling`. Build: `lake build PolyHardness` from the repository root.
  * `Chain.lean` — (weakly) reachable sets in the plane are cut out by strictly convex chains
    (`isReachableB_iff_chain`), locality of the slabs (`inHull_iff_of_piece`, `_left`, `_right`).
  * `FlowLP.lean` — the chain graph and the flow LP.

## Result

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

Not formalized: the complexity-class statement (Mathlib has no complexity classes), the column
problem and the Farkas corollary (direct consequences of the two theorems and LP duality).

## Code

`planar.py`: graph, LP, column problem, exact certificates (`certify`, `check_certificate`),
brute-force `family` by the definition. Tests, from this folder:

```
../.venv/bin/python -m pytest -q tests
```
