# Complexity of solvability and weak solvability at fixed prices

Question: given prices `P` (T points of R^d_{++}) and outputs `y`, is `y` in the cone of the
indicators of reachable sets (= neoclassical solvability) or of weakly reachable sets (= weak
solvability)? See `latex/notes.tex`. Both modes are treated by one proof: the only difference
is `>= 0` versus `> 0` for the witnesses ("mode" `b` in Lean, `\succ` in the text).

Results (text: `complexity.pdf`, source `complexity.tex`):

* **d = 2: polynomial.** In both modes the admissible sets are cut out by strictly convex
  lower-left chains (Theorem 2.2): points outside the region `C(V)` are in S, points of the
  forbidden region (interior for weak, closed region for strict) are not, boundary points are
  free only in the weak mode. The status of a point depends only on its vertical slab
  (Lemma 2.3). Hence solvability is one flow LP on a DAG with O(T^3) arcs, and the column problem
  is a longest path (Theorem 2.4). Code: `d2_flow.py` (`strict` flag).
* **d = 3: NP-hard.** A paraboloid gadget turns membership in the stable set polytope of a
  planar graph (Gabriel edges) into solvability in either mode (Theorem 3.1; heights
  `|a_u - a_v|^2 (1/4 + gamma/2)` work for both). The column problem is NP-complete (Karp, from
  planar max-degree-3 independent set). Solvability is in NP and NP-hard under polynomial-time
  Turing reductions (via Groetschel-Lovasz-Schrijver); Karp-hardness is open (remark after
  Corollary 3.5, `exp_stab_karp.py`). The same holds for every fixed d >= 3.
  Code: `d3_reduction.py` (`strict` flag).

Lean 4: `lean/Complexity.lean`, checked with `lake env lean complexity/lean/Complexity.lean` from
the repo root; no `sorry`, only standard axioms. `Ok b u` is `0 < u` (b = true) or `0 <= u`
(b = false); `IsReachableB b` is `IsReachable` / `IsWeakReachable`. Every theorem is proved once
for both modes; the single-mode statements are short corollaries.

* `isReachableB_iff_chain` (corollaries `isWeakReachable_iff_chain`, `isReachable_iff_chain`),
  `inHull_iff_of_piece`, `inHull_iff_of_left`, `inHull_iff_of_right`.
* `mem_indicatorCone_iff_inStabB`, `mem_indicatorCone_iff_inStabB_of_gabriel` (corollaries
  `mem_indicatorCone_iff_inStab_of_gabriel` for weak solvability and
  `neoSolvable_iff_inStab_of_gabriel` for neoclassical solvability itself).

Not formalized: flow decomposition (Theorem 2.4), the grid drawing lemma (3.2), NP-hardness of
planar independent set, the GLS equivalence theorems.

Experiments (`../.venv/bin/python <script>` from this folder):

| script | checks |
|---|---|
| `exp_d2_family.py`, `exp_d2_strict.py` | DAG family == brute-force family, longest path == brute force |
| `exp_d2_membership.py`, `exp_d2_strict.py` | flow LP == brute-force cone membership |
| `exp_covers_check.py`, `exp_covers_strict.py` | minimal covers of size <= d reproduce the family |
| `exp_d2_timing.py` | running time of the flow LP up to T = 80 |
| `exp_d3_reduction.py`, `exp_d3_strict.py` | gadget on K3, C5, a tree, the bowtie: covers, independent sets, STAB |
| `exp_d3_grid.py` | drawing lemma on K4: Gabriel margin, parity, alpha(G'') |
| `exp_stab_karp.py` | (1/3)1 in STAB(G x K3) iff G 3-colourable (Karp idea, non-planar) |

Helpers: `wsolv.py` (brute force), `covers.py` (exact minimal coverings).
