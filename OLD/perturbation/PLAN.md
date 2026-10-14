# Working plan: NP-hardness of ρ at d = 2

**Goal.** Prove that the optimization problem

`PERT-2`: given P ∈ Q^(2×T)_{++}, y ∈ Q^T_+, θ ∈ Q_+, decide whether ρ(P, y) ≤ θ,

is NP-hard. Every claim used in the reduction must be proved in Lean 4 in this
subproject (`perturbation/lean/Perturbation/`).

## Status of the question

Open. After the first exploration session (2026-10-11, `attempts/01` through `05`,
`scratchpad/BV-TECHNIQUE.md`, `REDUCTION-SOURCES.md`, `LITERATURE-D2.md`):

* No NP-hardness reduction found.
* Structural evidence (NAE-un-encodability of chain and star gadgets) tentatively
  leans **polynomial-time** for `ρ_dom`. See `attempts/05-conclusion.md`.
* `ρ` is `ρ_dom + pair blockings`; latter rarely active on random instances but
  provably sometimes nonzero (triangle example).
* Lean skeleton with the formal decision problem is in
  `lean/Perturbation/Decision.lean`.

Known facts (before the session):

* `PERT-d` is NP-hard for d ≥ 3 via a reduction from planar 3-colouring
  (`np-hardness/`). The reduction uses `d`-dimensional lifts that are unavailable at
  d = 2.
* At d = 2 the oracle "y is weakly solvable at fixed Q" is polynomial (`poly-hardness/`,
  one flow LP). So the hardness, if any, must come from the choice of Q.
* `PERT-d` is NP-hard when d is part of the input (reduction from SET COVER,
  `OLD/Algorithms/Hardness.lean`); this does not touch the d = 2 case.
* The dominance relaxation `ρ_dom` at d = 2 is also open.

The problem has the shape of a bilevel convex program:
`min_{Q} π(P, Q)  s.t.  y ∈ cone(weakly reachable sets at Q)`.
General bilevel LPs are NP-hard (Jeroslow 1985), but ours has strong structure.

## Attack order (easier first)

1. **Weak NP-hardness via SUBSET SUM.** Given positive integers `a_1, …, a_n` and
   target `S`, build an instance `(P, y, θ)` such that `ρ(P, y) ≤ θ` iff some subset
   sums to `S`. Allowed to be pseudo-polynomial in the `a_i`; this is "weak"
   NP-hardness in the Garey–Johnson sense but still means `PERT-2 ∈ NP-hard`.
   * Gadget to design: an either/or choice (point either stays, cost 0, blocking some
     chain; or moves far, cost `a_i`, unblocking that chain).
   * Threshold gadget: equality `∑ chosen a_i = S` enforced by a "balancing" point
     whose cost penalizes any deviation from `S`.

2. **Strong NP-hardness via PLANAR 3-SAT or PLANAR MAX-2-SAT.** Encode variables and
   clauses as geometric wires. Planar 3-SAT is NP-complete (Lichtenstein 1982) and
   two-dimensional, which matches d = 2. Harder than SUBSET SUM but gives strong
   hardness.

3. **Reduction from a convex-chain-partition problem** known to be hard, if any such
   result exists in the computational-geometry literature. Needs search.

4. **Negative result.** If nothing works and we find a polynomial-time algorithm,
   that itself is a publishable result (closes the open question in the other
   direction).

## Lean plan

* `Decision.lean`: formal statement of `PERT-2` as a predicate on rational data. Also
  the equivalent `(exists weakly solvable Q with π(P, Q) ≤ θ)` form.
* `SubsetSum.lean`: the subset-sum reduction. Builds `(P, y, θ)` from `(a, S)` and
  proves the forward and reverse directions.
* `Planar3SAT.lean` (later): the planar 3-SAT reduction.

A note on complexity classes: Mathlib has no complexity classes, so the final
"NP-hard" statement will be text, as in `np-hardness/`. The polynomial-time map and
the equivalence `yes-instance ↔ (ρ ≤ θ)` are the formal content.

## Honesty log

Attempts, successes and dead ends go into `attempts/` (plain Markdown).
