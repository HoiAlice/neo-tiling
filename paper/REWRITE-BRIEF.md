# Brief: from a formalization transcript to a readable paper

Written 2026-10-17 for the next session. Goal of that session: rewrite `paper/tex` so that the main text
reads as a mathematical-economics paper (definitions, main theorems, ideas, meaning) and the technical
lemmas move to an appendix. The journal is not decided; the informs4 class is only the current format.
Do not use МФТИ or ФИЦ ИУ РАН as affiliation. Do not cite `references/lavrin2027.pdf` (accepted, no DOI).

## 1. What to read first (all in `references/`, index in `references/README.md`)

In this order; the first three are the frame of the paper.

1. `shananin1997a_mm1462.pdf`, Sect. 3–4 (pp. 120–126): the generalized pure-industry model. Micro production
   function F_0 neoclassical, unit cost q_0 = Young transform (Lemma 4.1), loading rule (Thm 4.1): a unit with
   technology x runs at full capacity iff p_0 > q_0(p∘x). This is where our h, A_t and y_t = μ(A_t) come from.
2. `shananin1999_mm1165.pdf` (7 pages): the moment problem (2.3) for finite data and fixed h; Prop. 3.1 is our
   Lemma "signature" (cone of cell codes; the code of a cell lists the periods in which it is profitable, same
   orientation as our S). Sect. 5: CES elasticity for two inputs by tracking triple intersections.
3. `agaltsov_molchanov_shananin2018.pdf`, Sect. 2 (pp. 730–733), 4 (pp. 741–746), 5 (pp. 746–748), 6 (pp. 749–755):
   the survey. Thm 2.2 = Henkin–Shananin complete-monotonicity criterion (linear h); Thm 4.3 and Prop. 4.1 =
   the same for homogeneous and CES h; Prop. 5.1–5.4 = cone criterion, 0/±1 necessary conditions, integer
   facet normals, discrete convexity; Sect. 6 = CES, braid moves, rhombic tilings (one sentence for us).
4. `agaltsov2015.pdf` (4 pages): range of the profit-function operator for arbitrary homogeneous q via Mellin
   division by ρ_q and complete monotonicity. `agaltsov2016.pdf`, Sect. 1–2 (pp. 1–9): uniqueness iff the
   Mellin transform of e^{−q} has a meagre zero set; proof idea = Wiener's Tauberian theorem.
5. `molchanov2013a_cones.pdf`: dual embeddability in {−1,0,1}^T fails at T = 6 (19 regions); stretchability of
   pseudolines is NP-hard (Shor 1991). `molchanov2013b_tilings.pdf`: ≤ C(T,3)+2 flips over ρ. One sentence each.
6. Western side: `kuosmanen2007.pdf` Sect. 1–3 (errors-in-variables tests, L∞ for computability, Varian's
   footnote that price errors make the problem nonlinear), `apesteguia2010.pdf` (NP-completeness of
   rationalization in JME, the precedent for our genre). Still missing as PDFs: Hildenbrand 1981 Econometrica
   49(5) 1095–1125, Varian 1984 Econometrica 52(3) 579–597, Kitamura–Stoye 2018 Econometrica 86(6) 1883–1909,
   Smeulders–Cherchye–De Rock 2021 Econometrica 89(1) 437–455 (bib entries already in refs.bib).

The user's own account of the model (the introduction of `lavrin2027.pdf`, pp. 1–4) is the best model for tone
and terminology: technologies, capacities, unit cost, profitable periods, cells and spectra. Use the framing,
not the affiliation, and do not cite the paper.

## 2. What the school's papers have that our text lacks

- **A story before the mathematics.** Every paper of the school opens with the economic problem (globalization,
  substitution of inputs, what statistics are available) and the model in words, then the formulas. Our chapter 2
  starts with "Throughout, d ≥ 2". The introduction written today (`01-introduction.tex`) has the facts but is a
  list of citations; it needs to become an exposition with one worked picture.
- **The model stated as a model.** Units, capacities μ, technology x as input requirements per unit of output,
  the loading rule, y as output at full loading, prices normalized by the output price. State it once, with the
  formulas Π(p_0,p) = ∫(p_0 − h(p∘x))_+ μ(dx), y = ∂_{p_0}Π, and the sampled Radon transform y_t = (R_h μ)(p_t).
- **Interpretation after each theorem.** They say what a condition means (Prop. 5.2 "Ω_+ profitable more often
  than Ω_− in every cell, hence more output"). Our theorems have no such sentences.
- **The three regimes** (complete data / finite data with fixed h / finite data with free h) and the parallels:
  cone duality, 0/±1 inequalities as finite complete monotonicity, no finite Bernstein theorem (NP-hardness,
  Cor. "extended" added today), stability instead of uniqueness, prices as the free variable. These are written
  today as bullet points in the introduction and as remarks in ch. 2, 5, 6, 7; keep them, write them out.
- **Pictures.** The survey and the user's paper draw the partition of R^2_+ by level curves, wiring diagrams and
  tilings. We have no figure of a partition, a chamber, a chain, or the paraboloid gadget.

## 3. Proposed structure of the main text (≈ 20 pages) and appendix (≈ 20–25 pages)

Main text keeps definitions, main theorems, a "proof idea" paragraph, and interpretation; everything else goes
to one appendix with sections A.1–A.6 mirroring the chapters ("proof in Appendix A.3"). For MOR the appendix
is the e-companion; for other journals an online appendix; decide with the journal.

| Chapter | Stays | Moves to appendix |
|---|---|---|
| 1 Intro | model in words + formulas, one figure (d = 2, three or four prices, cells, spectra, an unsolvable y), the three regimes written out, results with meaning, related work, outline | — |
| 2 Solvability | def neoclassical/unit cost, def solvability, def spectrum, def reachable, Thm solvability + idea (necessity via separation, sufficiency via the piecewise-linear h of Lemma patch), Cor open, remarks Radon / stability | prop null, lem signature (state in text as Shananin's criterion, prove in appendix), lem stability, necessity, separation, patch |
| 3 Weak | def weak, Thm closure + idea (limit of witnesses; tilt by δ Σ e^{−p}; why coinciding prices need uncrossing, with the 6-point example) | lem limit, rematch, uncross, monotone, tilt |
| 4 Planar | def chain + figure, Thm chain, Thm lp (flow LP) + idea (paths of the chain graph = chains, Out/Bnd sets), Cor poly/col/farkas | lem hull, def graph details, Thm family, lem cube, proofs |
| 5 Hardness | Thm main, Cor hard-np, Cor extended, idea of the gadget with a figure (paraboloid lift, disks = witnesses, STAB) and the role of crossings | gadget theorem, disks, lattice drawing, coloring lemma, cost count (Thm hard-karp) |
| 6 Box oracle | Thm corners + idea (path argument), Lemma cover as a theorem + remark cover/Bernstein, description of the exact oracle | proofs, Prop rational-Q |
| 7 Perturbation | problem, Thm reduction, Thm algo + the method described in words, cuts, remark on open questions | onesigned, certificate, closed, proofs, implementation refinements |
| 8 Computations | as planned (tables of OPT_1 / [LB,UB], aggregation, moved coordinates) | — |
| 9 Lean | as is, shorter | correspondence table |

Writing rules for the new text: one idea per sentence; after each theorem one or two sentences of meaning in the
model's terms (technologies, capacities, profitable periods), never consumers or demand; standard facts cited to
textbooks (Rockafellar, Schrijver, AMO, Garey–Johnson), Lean names only in the e-companion table; the user
proofreads chapters, so keep statements verbatim when moving them.

## 4. How to do it

1. Read the files in §1 (about an hour of reading), then `tex/01-introduction.tex` and chapters 02–07 (files are numbered as the sections: 02 solvability … 09 Lean).
2. Write the new introduction first (model exposition, figure, three regimes, results, related work, outline).
   The figure: synthetic d = 2 example unless the user prefers a real slice (ask once).
3. Create `tex/appendix.tex` with sections A.1–A.6; move lemmas and proofs chapter by chapter with the Edit
   tool (never rewrite files via scripts), replacing each moved proof by "Proof in Appendix A.k" and leaving the
   statement in the text only if it is used by the reader; add the "idea" paragraphs and interpretation sentences.
4. Keep labels unchanged so that `ec-companion.tex` and the Lean correspondence stay valid; re-run the
   label/cite check (`grep` over `\cref`/`\cite` vs `\label`/`refs.bib`) after each chapter.
5. Do not compile (the user builds in VS Code; read `tex/build/main.log` if needed).
6. Open questions to settle with the user at the start: appendix vs e-companion naming; synthetic vs real figure;
   whether chapter 4's chain graph figure is drawn by TikZ or exported from Python.

## 5. State of the numerical part (finished in the session of 2026-10-17, do not redo)

- `code/experiments/aggregation_lp.py`: rows carry Q and `moves`; `table` prints OPT_1 or [LB, UB] per cell;
  `moves` prints the moved coordinates. Queues `aggregation_queue.sh` (1800 s reruns) and `aggregation_queue2.sh`
  (d = 7 control: types / pII) ran sequentially; results in `experiments/results/aggregation_lp.jsonl`.
- Finding for ch. 7: at d = 8 the optimal perturbation moves 2–7 of 320 prices, and in six of seven industries
  the intermediate-input price pII is among them (the only one in 24, 1, 27); at d = 3 pII carries most of the
  correction; aggregation inflates OPT_1 by 10–100× and localizes the remaining violation on the aggregate
  coordinate. The d = 7 control (normalize by pII) tests whether this is pII mismeasurement.
- Time-limited cells: UB is the trivial alignment bound; the placebo comparison rests on LB.
- The solvable-interval experiment (`intervals.py`) was judged uninformative without a null; no figure.
- TODO on the code (memory `feedback-solver-run-logs`): per-iteration logs and HiGHS output capture.
