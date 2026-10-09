# OLD — legacy, do not consult unless asked

Snapshot of the project before the 2026-10-07 rewrite, which removed general position from the
solvability theory.

- `latex/notes.tex`, `latex/notes.pdf` — previous notes (CES examples, finiteness of level-curve
  intersections, general position, regular solvability, the 2D algorithm with pair coverings).
- `NeoTiling/` — previous Lean library (profiles, transversality, level curves, general position,
  regular solvability, reachable spectra via pair coverings, degenerate prices). Not built: the
  lakefile only globs `NeoTiling/`.

- `Perturbation.lean` — the 2026-10-08 perturbation file (symmetric perturbation `pert`, box
  lemma, hyperbola bound `D(κ)`, witness bound `W_crit`), written for the perturbation problem
  with a witness bound `W`. Moved here on 2026-10-09 when that problem was replaced by the one
  through weak solvability. Not built.

The current theory lives in `latex/notes.tex` and `NeoTiling/`. Do not read, reuse or cite files
here unless the user explicitly asks.
