# Attempt 6: breakthrough on gadget construction

Three parallel agents produced convergent findings. Full write-ups: `scratchpad/`.
Summary:

## Confirmed numerically (not yet proved formally)

* **Switch gadget**: 2 points at `(4,4)` and `(0,0)` with `y = (2, 1)`. Both `σ = 0`
  and `σ = 1` cost exactly the same `B_1 = 2(e^{d/2} − 1)` where `d` is the gap.
  Verified in `scratchpad/gad/`.
* **Antiferromagnetic coupler**: 4 points placed with the two switches at anti-
  diagonal offset. Different `σ` costs `2 B_1`, same `σ` costs `2 B_1 + J` with
  `J ≈ 0.21034`. Exhaustive scan: offsets `(ox, oy)` with `ox·oy < 0` and
  `|Δ|_∞ < d` give antiferro; `ox = oy` gives ferro.
* **PATH `P_n` as an exact Ising chain**: `n` switches along `NE` diagonal (ferro
  propagation) or along `NW` (antiferro, equivalent to ferro after re-labelling).
  Cost fits `n·B_1 + J·(n − 1 − cut)` exactly (fit error `< 3·10^{−13}` for
  `n = 3, 4, 5, 6`).
* **`K_3` NAE table**: 3 switches with tuned `d^* = 11.1664276`. All 6
  non-constant `σ` cost `13.56360`; both all-zero and all-one cost `15.41316`.
  Exact NAE pattern.
* **Pair-cover (angle) couplings are all ferromagnetic**: 27 of 28 random
  2-heavy instances tested; mixed-face solutions are cheaper than or tied with
  pure ones. Pair-cover angles do NOT give frustration.

## What's missing for NP-hardness

**Wire crossing gadget**. Without it, the coupling graph realised by our gadgets is
**planar** (switches interact only when geometrically close). Planar MAX-CUT and
planar NAE-3SAT are polynomial, so no NP-hardness follows from the current gadget
set.

A planar NAE-3SAT reduction with ferro-wire variable copies would still need wire
crossings. Pair-cover angles cannot provide the crossing (all couplings ferro).

## Where hardness, if any, lives

Agent findings pin the HARDNESS SOURCE in `ρ_dom`'s `x/y` disjunction with
multi-level `y` nesting, NOT in pair-cover angles. Specifically:
- `g_x(E), g_y(E)` isotonic costs are neither sub- nor supermodular (frustrated
  Ising at the per-conflict level).
- Nested staircases couple adjacent levels: dropping nesting is a strict lower
  bound (`LB < ρ_dom` in 5/6 random 3-level instances).
- Antiferro couplers exist locally (`K_{2,2}` sub-geometry) but at offset signs
  that are consistent with planarity.

**The missing crossing gadget is the single technical obstacle to a complete
NP-hardness reduction** from MAX-CUT on cubic non-planar graphs (NP-hard,
Yannakakis).

## If no crossing exists

Then our gadget's coupling graph is strictly planar, planar MAX-CUT = polynomial,
and we'd need to look elsewhere for hardness. The weight of evidence from the
parallel agents is: **the problem looks like a specific planar-only reduction
collapses to a polynomial problem**. This would be CONSISTENT with ρ at `d = 2`
being POLYNOMIAL.

## Follow-up (in progress)

A fourth agent is specifically pursuing the crossing gadget via:
* Y-level separation (wires at different y-strata, geometrically incomparable).
* Three-body NAE term as a crossing primitive.
* Barahona-style cancellation gadgets (Barahona 1982 Ising hardness).

If any of these succeed, we have NP-hardness. If all fail, strong evidence for
polynomial.
