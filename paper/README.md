# paper/

Consolidated material for the journal article (target: Mathematics of Operations Research).
Created 2026-10-16 from `latex/notes.tex`, `poly-hardness/`, `np-hardness/`, `price-perturbation/`,
`l1-perturbation/`; those folders are the Russian sources and stay until the paper is complete.

```
tex/     main.tex (INFORMS class informs4, option moor),
         macros.tex, abstract.tex, chapters 01-09 as \input (01 introduction, 02 solvability, 03 weak, 04 planar, 05 hardness, 06 box oracle, 07 perturbation, 08 computations, 09 Lean), refs.bib, informs/ (template samples),
         figures/. informs4.cls, informs2014.bst, informs_Logo.* are the INFORMS files (keep in tex/).
         All chapters are in English; the introduction (01) and the computations (08) were written 2026-10-17.
lean/    independent Lake project, library NeoTiling (Core, Planar, Hardness, Perturbation, Lp).
         `lake build` from this folder; .lake/packages is a symlink to the repository's Mathlib checkout.
         No sorry, standard axioms. Not ported: PricePerturbation/Profile.lean (per-year profile, dropped).
code/    Python package `neotiling` (pyproject): data loaders, planar flow LP, exact box oracle with
         (lambda, covers) NO certificates, least radius (log metric, weighted), l_p solver; tests/,
         experiments/, tools/. See code/README.md.
```

Scope decisions (2026-10-16): one-sided and lexicographic profiles are out; theory in the log metric,
algorithm and computations in the relative metric with a log comparison; aggregation study stays;
planned experiment: lengths of maximal solvable year-intervals by d with a placebo control.
