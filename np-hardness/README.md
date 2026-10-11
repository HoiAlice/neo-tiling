# NP-hardness of (weak) solvability in dimension 3

Graph 3-colouring reduces (Karp) to neoclassical solvability and to weak solvability at fixed
rational prices in `R^3_{++}`. Both problems are in NP, hence NP-complete.

* `np-hardness.tex` — the proof (Russian), self-contained modulo the two criteria of
  `latex/notes.tex` (solvability and weak solvability as cone membership).
* `lean/` — Lean 4 library `NPHardness` (depends only on `NeoTiling`), every statement of the
  text. Build: `lake build NPHardness` from the repository root.
  * `Gadget.lean` — paraboloid gadget; witnesses are disks that may depend on the independent set.
  * `Disks.lean` — lattice drawings with empty disks give valid gadgets.
  * `Layout.lean` — the lattice drawing of `G □ K3` (rows, columns, triangles); crossings need no
    gadget because rows and columns live on complementary parity classes.
  * `Coloring.lean` — `s ∈ STAB(H)` iff `G` is 3-colourable.
  * `Main.lean` — `neoSolvable_iff_colorable`, `weakSolvable_iff_colorable`, size and
    rationality of the instance.
* `check_layout.py` — numerical check of the drawing conditions and of the colouring lemma on
  small graphs (`.venv/bin/python np-hardness/check_layout.py`).

Not formalized: NP-completeness of 3-colouring and polynomial running time of the construction
(Mathlib has no complexity classes); the instance size and rationality are formalized.
