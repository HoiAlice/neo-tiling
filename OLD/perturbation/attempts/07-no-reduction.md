# Attempt 7: NP-hardness route via wire crossing (gadget found, assembly pending)

Four parallel attacks on d=2. Three negatives, one breakthrough. Full write-ups
in `scratchpad/`.

## 0. BREAKTHROUGH: crossing gadget found

`scratchpad/CROSSING-GADGET.md`, scripts `scratchpad/gad/{cx2,cx3,final,neg,wk*}.py`,
outputs `final_4_5.out`, `neg.out`.

An antiferromagnetic wire U (NW-SE anti-diagonal, step a=3, box d=4) crosses a
ferromagnetic wire V (SW-NE diagonal, step k=1, box dv=5), centred at (2,2).
Decoupling is by EXACT SYMMETRY, not tuning:

* R = swap x↔y: flips σ of every switch; flips U-phase; fixes V (ferro).
* P = point reflection about (2,2) composed with y→const−y: flips U-phase;
  fixes V.
* Together: all four `(U_in, V_in)` ground states have equal cost
  `ρ_dom = 10.552302` with spread 0.

Numerics (4U × 5V instance, verified independently from `final_4_5.out`):

| Phase pattern | Excess over min |
|---|---|
| 4 valid combos (U_out=NOT U_in, V_out=V_in) | 0.0 each |
| V broken only | 0.09018 |
| U broken only | 0.14006 or 0.19959 |
| Both broken | 0.28956 or 0.31019 |

* Full ρ at margin-1e-6 optimum: `planar.flow_lp` returns feasible for all 4
  valid combos (ρ = ρ_dom + 1.5e-5 numerical slack). Weak solvability confirmed
  with exact-rational Farkas.
* Detuning control: shift V by 0.25 along the diagonal splits phases by 0.0303;
  by 0.5 splits by 0.0554. An off-centre crossing acts as a FIELD on the U-bit
  (same magnitude as a designated coupler). Exact symmetry is essential.

**New structural fact**: y-levels (numeric values, not only order) matter at
d=2. Reachable sets admit 4-point covering inequalities
`y_a + y_b ≤ y_c + y_d` beyond the pair-cover `y_t ≤ y_r + y_s`. Symmetric
y-staircase fails for one U phase. Fix: concave y-profile `y = 1 + ε·F(x+y)`
with `h2 ≥ h0 + 2g` locally at every crossing. Threshold found numerically.

## Reduction sketch (not fully assembled)

Source: MAX-CUT on cubic graphs, NP-hard (Yannakakis 1978, Berman-Karpinski).

1. Draw G on a 45°-rotated grid: edges are polylines of NW-SE (antiferro,
   link cost 0.21) and SW-NE (ferro, link cost ≈0.09) segments. Orthogonal
   drawings of degree-3 graphs have O(n) bends and O(n²) crossings. Every
   crossing is a U × V crossing → use the gadget above.
2. Designated edge coupler: antiferro pair at step a=3.75 gives kink cost
   0.0506, below every wire-break cost (≥0.09). ρ = base + J_e·(|E| − maxcut)
   up to O(1e-5) per gadget.

**Still open** (CROSSING agent continuing on these):

* (a) Corner gadget: U-wire meets V-wire at a bend.
* (b) Degree-3 vertex switch: node joining 3 wires with consistent-bit forcing.
* (c) Designated weak coupler inside the global y-profile.
* (d) Global concave y-profile `y = 1 + ε·F(x+y)` matching h2 ≥ h0 + 2g at
  every crossing, with max y < 2·min y to kill pair-covers.
* (e) Weak solvability of a FULL assembled instance (verified per-crossing,
  per-wire of length ≤ 5, not end-to-end).

If (a)-(e) close, we have NP-hardness of ρ at d=2.

## 1. Weak NP-hardness via SUBSET SUM / PARTITION

`scratchpad/SUBSET-SUM.md`. **Negative, with structural reason**.

Every channel for an arithmetic sum has the wrong sign:
* The x-vs-y disjunction cost per conflict is `min(c_x, c_y)` (concave).
* Strict-order chains propagate the MAX of required displacements, not sum.
* Pooling (isotonic ties): cost `-S_J²/(M+|J|)`, CONCAVE in subset sum,
  min picks clustering not balancing. Subset-sum equality needs a convex
  penalty `(S_J − T)²`.
* A heavy's required displacement is a max over others, not a sum: no linear
  functional of binary choices to penalize.

Not relevant for the main reduction (which uses geometric wires), but rules
out the "arithmetic encoding" family.

## 2. Mixed-sign planar Ising with field (Barahona-style)

`scratchpad/BIASED-ISING.md`. **Partly superseded by the crossing route**.

Confirmed building blocks: biased switch (asymmetric gap), AF chain with
alternating gaps (gauge image of ferro+field), all-AF triangle at symmetric
gaps (frustrated 3-cycle). Mixed ferro+AF triangles cannot be frustrated
(comparability transitive).

Composition barrier: 263 integer offsets scanned for a 4th switch next to an
exact mixed triple; only 2 fit exactly, both are J=0 (isolated). Every 4th
switch that actually couples produces 3-body residuals ≈1e-2.

This matters for the crossing route too: the CROSSING agent sidestepped it by
using single-coupling-type wires (U all-AF, V all-ferro) and a geometrically
isolated crossing, not a composite Ising.

## 3. K₄ close-packing numerics

`scratchpad/k4_v2.py`, run `b7sqc3zlw`. **No clean K₄ antiferro Ising**.

Four switches at antidiagonal centres with gap d=4: `ρ_dom = 4.054` vs
baseline 3.935. Minimum at 2:2 bit partitions, not matching pure Ising K₄.
Confirms (2): multi-body terms dominate close-packings.

## 4. Polynomial algorithm (nested-staircase DP)

`scratchpad/POLY-ALGO.md`, `polyalgo/`. **Inconclusive, now likely wrong
direction**.

ILP on grid: polynomial-size, matches brute force 100/100 on T up to 10.
LP relaxation NOT tight (42/70 random instances have gap). Direct DP breaks
on supermodular distance-to-set.

In-progress: rotated coordinates ξ=x−y, η=x+y, Lipschitz-fit LP. Secondary
to the crossing route; if the crossing reduction completes, this is moot.

## Status

* Crossing gadget verified numerically (independent spot-check of `final_4_5.out`,
  `neg.out`).
* NP-hardness subject to five open assembly items; CROSSING agent working on
  them.
* Three independent NP-hardness obstructions (SUBSET-SUM, mixed-sign Ising,
  K₄ close-pack) are consistent with the crossing route being the ONLY route
  — the gadget uses pure geometric cancellation, not Ising composition.
