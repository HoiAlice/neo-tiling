# Attempt 1: SUBSET SUM → `PERT-2`

**Target:** build a polynomial map `(a_1, …, a_n, S) ↦ (P, y, θ)` such that

`ρ(P, y) ≤ θ   ⟺   ∃ I ⊂ [n] : ∑_{i ∈ I} a_i = S`.

If such a map exists, `PERT-2` is NP-hard in the weak sense (pseudo-polynomial).

## What a gadget has to do

Blocking in `d = 2` is combinatorial: dominance (one coordinate), pair covering
(point above a segment), or longer convex chains. The cost of moving one coordinate
of one point by log-ratio `r` is `|r|` (or similar). The subset-sum structure requires:

1. **Choice.** For each item `i`, a binary configuration: "in" (cost `0`, blocks
   something) or "out" (cost `a_i`, unblocks it).
2. **Counting.** A separate point whose cost grows with `∑_{i ∈ I} a_i`, with a
   minimum at `S`.
3. **Combination.** The total ρ equals `min(c · |∑ a_i − S|)` plus a constant, so
   that `ρ ≤ θ` iff `∑ = S`.

## What is unclear

* The chain structure in `d = 2` is global: moving one point affects which chains
  are available for all neighbours. A clean independent choice per item is hard to
  isolate.
* The cost is π on each coordinate; it is **not** a linear function of positions.
  Summing items into a target `S` requires linearity. We would need either to
  linearise locally (log coordinates), or to encode `S` via a "balancing" point whose
  cost in π is affine in the positions of the item points.
* `ρ` is a continuous optimum, not combinatorial. Subset-sum is combinatorial.
  Making the optimum reached only at integer configurations needs a sharp penalty.

## First concrete attempt

Try the configuration (sketch, not yet implemented in Lean):

* Base points `A = (1, 1)` and `B = (M, M)` for a large `M`. `y_A = 1`, `y_B = 1`.
* Item points `P_i` at coordinates close to `A` but slightly dominated by `A`.
  `y_{P_i} = 1`.
* Target point `T` at coordinates somewhere forcing a convex chain through chosen
  items.

Expected failure mode: the π cost is smooth in positions, so the optimum will be a
continuous mixture, not a 0/1 selection, unless the gadget forces discreteness. This
is the main obstacle I want to understand before writing Lean.

## Where I am

Nothing committed to Lean yet beyond the decision predicate. The paragraph above
is my current analysis of why a straight subset-sum reduction is nontrivial. Need
to think more about either:

* a **harder-but-cleaner** reduction (planar 3-SAT with chain wires), or
* a **sharpening** mechanism that forces the optimum to be reached at integer
  configurations (e.g. a non-smooth cost term that is zero only at an integer).

## Next step

Spend time on the chain geometry: enumerate what configurations `(q_1, …, q_T)` in
`d = 2` are weakly solvable for a very simple `y` (`y = (1, 2, 1)` for `T = 3`), and
see whether a two-point choice gadget can be isolated. If yes, scale up.
