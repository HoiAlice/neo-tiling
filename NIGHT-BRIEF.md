# Overnight brief: an exact, solver-friendly reformulation of the minimal price perturbation

You are working autonomously in `/Users/olegoleg/Code/neo-tiling` for several hours. The owner
is asleep. Read `CLAUDE.md` and the memory index first. Work until you either succeed or
exhaust the directions below; leave a written report. Do not ask questions; decide yourself.

## Goal

Find a formulation of the minimal perturbation problem that a free solver (SCIP, or Gurobi
under its 2000-variable / 200-quadratic-variable restricted license) solves **with a global
optimality certificate** at sizes well beyond what the current formulation reaches
(currently: certified only for T ≤ 4–5; target d = 2 with T = 10–25, then d = 3, 4).
The ideal outcome is an exact MILP (no bilinear terms) or an exact finite scheme whose
pieces are LPs / MILPs. A formulation that is exact up to an explicit, controllable
tolerance ε (e.g. a refinable grid with a proven error bound) is acceptable if the bound is
proved, not assumed. Heuristics without certificates are NOT the goal; we have those.

Every mathematical claim you rely on (an equivalence of feasible sets, a validity of a
cut, an error bound) must be either already in the notes/Lean, or proved by you in Lean
with `/prove` (workers `lean-prover`, consultant `lean-advisor`, lookups `mathlib-search`),
or clearly marked UNPROVED in the report and not used for certified numbers.

## What exists (read these, in this order)

1. `latex/notes.tex`, chapters «Слабая разрешимость» (§5) and «Минимальное возмущение
   цен» (§6): definitions of weak reachability (witness ξ ≥ 0, ξ ≠ 0, ⟨ξ, q_s − q_t⟩ ≥ 0
   for s ∉ S), the closure theorem, π(p,q) = max(q/p, p/q) − 1, ρ(P,y) = inf π over
   solvable Q = min over weakly solvable Q (attained), the bound D(κ) from the hyperbola,
   the MIP (def:model) with a single parameter D, and thm:value (its value is ρ).
2. Lean: `NeoTiling/Reachable.lean` (reachability by witnesses), `Closure.lean` (weak
   reachability, closure theorem), `Perturbation.lean` (pert, box lemma, hyperbola bound,
   attained minimum `exists_minPert`). All compile; `lake build`.
3. Code: `code/perturbation/` — `prep.py` (normalization, κ, D), `model.py` (def:model in
   SCIP via PySCIPOpt, convex form g ≥ 1/a − 1, heuristic mode default, `exact=True` for
   branch and bound, hyperbola start off by default with a NOTE), `exact.py` (certified
   test of ρ = 0 both ways: witnesses/masses or refutation λ + strict coverings),
   `verify.py` (exact rational check of an answer; keep it dumb — rounding to truly
   solvable prices is a separate task), `datasets.py` (Berndt–Wood 1947–71 d=4; EU KLEMS
   2023 d=3; `select` for coordinate slices, `window`), `report.py`. CLI `code/perturb.py`.
   Tests: `cd code && ../.venv/bin/python -m pytest -q` (fast), `-m slow` (heavy).
   Lint: `../.venv/bin/ruff check perturbation perturb.py tests` (py39, line 88).
   `.venv` has pyscipopt (SCIP 10), gurobipy (restricted license), scipy, sympy,
   matplotlib, pytest, ruff.
4. Memory file `perturbation-code.md` (in the memory directory) — the experiment log.

## Established facts and numbers (use as regression tests)

- Triangle (4,1),(3,3),(1,4), y=(1,5,3): ρ = 2/5 (certified; q_2 → (5/2,5/2)).
- Berndt–Wood, prices (capital, labour) = coordinates (0,1), gross output QY:
  - 1947–1950 (T=4): ρ = 0.0703 certified by SCIP exact mode in 5 s.
  - 1947–1952 (T=6): best known 0.3151 (Gurobi, 900 s), SCIP 0.3870; Gurobi dual bound
    0.0722 after 900 s, SCIP dual bound 0. NOT certified.
  - 1947–1956 (T=10): best known 0.6748 = the antitonic fit of PK along the (monotone
    increasing) PL order, certified weakly solvable by `exact.py`; SCIP's own heuristics
    give 0.681 from every seed (a local optimum) and do not improve from 0.6748.
- Berndt–Wood d=4 1947–1952: best known 0.1466 (several families give the same value),
  single-spectrum threshold lower bound 0.068. Not certified.
- All real windows with T ≥ 5 are certified NOT weakly solvable at P (refutations like
  y_1952+…+y_1956 ≤ y_1947+…+y_1951), so ρ > 0 strictly.

## What was tried and failed (do not repeat blindly)

1. Direct MIP (def:model) in SCIP: good incumbents in seconds, dual bound stays 0 on real
   windows with T ≥ 6 (fractional z void the big-M witness constraints; McCormick for ξ·a
   is weak). Indicator constraints and box tightening do not change this. Gurobi does
   raise the bound slowly but the free license caps T at 6 (d=2) / 5 (d=3,4).
2. Family decomposition (master MIP over spectra + continuous subproblems v(F)):
   correct, finite, but the lower bound is stuck at the single-spectrum threshold; the
   joint cost is high-order (cores of 5 of 6 spectra); pair cuts do not help. Shelved in
   this session's scratchpad (`families_shelved.py`) — reuse ideas, not the code.
3. Spatial branch and bound over price boxes with LP relaxations: hopeless (33k nodes on
   the triangle, gap 0.32–0.44 vs 0.4).
4. Convex reformulation g ≥ 1/a − 1 of the cost: correct and 17× faster on continuous
   subproblems; the nonconvexity that matters is ξ·a in the witness constraints.

## Directions to attack (ranked; pursue in order, but skip a dead one quickly)

A. **d = 2 geometry.** In the plane, "t does not strictly cover R" means q_t is not
   strictly above a convex combination of {q_s : s ∈ R}, i.e. q_t lies on or below the
   lower-left boundary of conv{q_s} + ℝ²₊. Witnesses are normals; for fixed Q the set of
   valid witness directions is an interval of angles. Ideas: (i) encode the pairwise order
   relations q_s^i ≤ q_t^i and the "which edge supports q_t" choice with binaries so that,
   given the pattern, every constraint is linear in q (check carefully: a line through
   two variable points is bilinear; but a *fixed direction* ξ makes ⟨ξ, q_s − q_t⟩ ≥ 0
   linear). (ii) Direction grids: choose ξ from a finite set of angles Θ via binaries →
   an exact MILP for the restricted problem ρ_Θ ≥ ρ; prove a bound ρ_Θ − ρ ≤ f(mesh) or
   an adaptive refinement with a stopping certificate (e.g. a dual argument showing no
   direction between grid points can do better by more than δ). (iii) The antitonic
   structure: when one price is monotone in t, weak solvability with "all but one"
   spectra reduces to isotonic regression under π (convex, unique). Characterize exactly
   which families are needed and whether a monotone/order structure makes the family
   choice polynomial. The old 2D theory (pair coverings, `OLD/`) may be consulted for
   this direction only.
B. **Direction (column) generation for general d.** With a finite candidate set of witness
   directions Ξ, the problem over (a, z, m, choice of ξ ∈ Ξ per (k,t)) is a MILP. Pricing:
   given a MILP solution, find a direction that would allow a cheaper Q (an LP/QP on the
   witness cone). Prove that the scheme terminates with a certificate, or give an ε-bound.
C. **Lower bounds of a different nature** (needed for any certificate): the dual
   hierarchy — refutations λ (Farkas) and k-tuples of spectra; a Lagrangian relaxation of
   the family choice; an LP relaxation in the space of "which pairs (s,t) are in strict
   dominance" with valid inequalities. Any valid lower bound that reaches the known
   incumbents on the T=6 and T=10 windows is a success in itself.
D. Only if A–C stall: a certified ε-approximation via a log-scale grid on the multipliers
   a with an explicit Lipschitz/monotonicity argument (prove it), solved as a MILP.

## Rigor and bookkeeping

- Before using a reformulation for certified numbers, write its statement as a theorem
  (equivalence of optimal values, or inequality with explicit ε) and send it to `/prove`
  with a self-contained brief (file, statement, proof idea, conventions, notes section);
  `/formulate` first if the Lean statement is unclear. Put new Lean in a new file under
  `NeoTiling/`, do not edit existing Lean files or `latex/notes.tex`. If a theorem does
  not go through, keep the result as UNPROVED and say so in the report.
- Numerical claims: every "optimal value" must come with the solver's status `optimal`
  and a `verify.py` certificate of the answer (rational witnesses/masses); every lower
  bound must come from a proved-valid relaxation.
- Code goes into `code/perturbation/<newname>.py` behind an explicit function/flag; keep
  `model.py` behavior unchanged; tests in `code/tests/`; ruff clean; fast tests green.
  Scratch scripts and plots go to your scratchpad, not the repo. Do not commit. Never
  rewrite project files with scripts; use the Edit tool.
- Keep a running log `REPORT.md` in your scratchpad (what you tried, numbers, times,
  dead ends, proofs done). At the end write the final report at
  `/Users/olegoleg/Code/neo-tiling/code/NIGHT-REPORT.md` (the owner will delete it):
  (1) the best formulation found and its exact status (proved / ε-exact / heuristic);
  (2) a table of certified values vs. the known incumbents on the regression windows;
  (3) Lean theorems added; (4) what remains open and why.
- Budget: this is an all-night job. Give each direction at most ~2 hours before moving on
  unless it is clearly converging. Kill background solver runs before leaving.

## Conventions from the owner (memory)

Code, docstrings and comments in English; chat to the owner in Russian. Short sentences.
No economic wording in the notes. The x-space is a space of technologies ({h(p∘x) < 1} =
technologies active at prices p), never "demand". Reuse existing lemmas; give `/prove` a
line budget; never weaken a stated theorem; escalate to `lean-advisor` when stuck.
