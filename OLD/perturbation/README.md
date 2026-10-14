# Minimal price perturbation

Companion of `poly-hardness/` (fixed-price (weak) solvability in the plane) and
`np-hardness/` (NP-hardness in dimension 3). Here we study the minimal perturbation of
the prices that makes a given output vector (weakly) solvable:

ρ(P, y) := inf { π(P, Q) : y is (weakly) solvable at Q }

where π is a separable convex cost on the per-coordinate price ratios (notes §5,
`latex/notes.tex`).

Layout (populated as the project grows).

* `perturbation.tex` — the text (Russian), self-contained modulo `latex/notes.tex` and
  the chain theorem of `poly-hardness/poly-hardness.tex`.
* `lean/Perturbation/` — Lean 4, no `sorry`, standard axioms only, depends on
  `NeoTiling` and `PolyHardness`. Build: `lake build Perturbation` from the repository
  root.
* Python experiments: numerical runs on the Berndt–Wood (US manufacturing, 1947–71) and
  EU KLEMS (2023) datasets, with exact rational certificates. Results and logs land in
  `results/`, tests in `tests/`.

Prior drafts and prototypes (SCIP master, C++ dominance branch and bound, set-cover
NP-hardness via a growing dimension, old chapter 6 of the notes, logs) live in
`OLD/` and are not maintained.
