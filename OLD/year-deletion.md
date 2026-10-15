# Year deletion and solvability intervals (closed direction, 2026-10-14)

Question: instead of correcting prices (`price-perturbation/`, the main line), remove the least
number of years so that the remaining data become solvable; also find the maximal intervals of
consecutive years on which the data are solvable. Which oracle: weak or plain solvability.

**Status: closed.** Both measures are driven almost entirely by pairwise dominance violations,
so they say little about the model; price perturbation is the informative measure. Not planned
for the paper. The code lived in a session scratchpad and was not kept; everything below is
enough to rebuild it (about 200 lines on top of `poly-hardness/planar.py` and
`price-perturbation/perturb/milp_oracle.py`).

## Facts (proved in discussion, checked numerically)

1. **Heredity.** If y is (weakly) solvable at P, then y_K is (weakly) solvable at P_K for every
   set of years K: a witness of t against [T] \ S also works against K \ S. So the kept sets form
   an independence system; minimum deletion = minimum hitting set of the minimal infeasible sets
   ("conflicts").
2. **Restriction.** Sp(P_K) = {S ∩ K : S ∈ Sp(P)}, in both modes. Given S' reachable at P_K, add
   to it the deleted years outside conv{p_s : s ∈ K \ S'} + R^d_+ (weak: outside its interior);
   the region does not change, so the new set is reachable at P. Consequence: deleting year t
   only drops the equation w_t = y_t in the FIXED cone cone{1_S : S ∈ Sp(P)} (the box interface
   with lo_t = 0, hi_t = ∞); at d = 2 the chain graph is built once. The support of a Farkas
   vector is itself a conflict. Checked by brute force on 47 376 subsets of random instances with
   ties.
3. **Pair conflicts (closed form).** {s, t} is infeasible iff, up to swapping,
   weak: p_s < p_t in every coordinate and y_s < y_t;
   plain: p_s ≤ p_t, p_s ≠ p_t, y_s < y_t, or p_s = p_t, y_s ≠ y_t.
   The relation is a strict partial order, so the pair-only bound is T minus the width of the
   order (Dilworth, bipartite matching), with no oracle calls. Chains of a minimum chain cover
   give valid cuts sum_{t ∈ Q} del_t ≥ |Q| - 1.
4. **Weak vs plain.** min_weak ≤ min_plain; equal for prices in general position (they differ
   only on ties: equal points, coordinate ties, collinearities). min_weak(P) = liminf_{Q→P}
   min_plain(Q). With prices fixed, weak solvability is NOT needed (the problem is finite);
   plain solvability is the honest notion. Plain reachability is exactly MILP-representable by
   homogeneity: <xi, p_s - p_t> ≥ 1 with xi ≥ 0 unbounded, via indicator constraints (no big-M,
   no eps); exact but about 15x slower than the weak CG oracle on Berndt–Wood d = 4.
5. **Complexity.** d ≥ 3: NP-hard already for zero deletions (`np-hardness/`). d = 2: open.
   For a general black-box hereditary oracle no algorithm with polynomially many calls exists
   (a hidden large independent set); whether our families realize this is not known.
6. **Intervals.** Maximal solvable intervals of consecutive years: by heredity the right end b(a)
   is nondecreasing, two pointers give all of them with at most 2T oracle calls.

## Algorithms tried (d = 2 unless stated)

| method | exact | cost on real data |
|---|---|---|
| IHS, geometry rebuilt per call, deletion filter | yes | up to 1541 oracle calls per series |
| IHS on fixed geometry (fact 2), Farkas support as conflict, pairs seeded | yes | 1–46 calls, ≤ 3 s at T = 70 on the series finished; one hard series (Machinery) ran long, not resolved |
| one MILP: flow LP of all T years + T binaries (big-M M = sum y) | yes | 40 s at T = 70; 1–10 s with pair and chain cuts |
| forward greedy | no | 8 years worse than optimum (median) — the family is not a matroid |
| intervals, two pointers, CG oracle (weak) | yes | ≤ 1.9 T calls, ≤ 12 s per series at d = 4 |

## Results (US EU KLEMS d = 2, 3; 63 BEA industries, full series; Berndt–Wood d = 4)

- **Minimum deletion, d = 2, 64 series:** 31–87% of the years (median 64%); US 17 of 26 years,
  Farms 52 of 70. Weak = plain on every series (no ties in the data). The pair-only bound is
  exact in 43 of 64. d = 3 (US) and d = 4 (Berndt–Wood): pairs only; BEA Machinery d = 4: 20
  years, pair bound 18, conflicts of 4–10 years.
- **Rounded prices** (ties appear): at 3 significant digits the two modes differ by at most one
  year; at 1 digit they diverge in opposite directions (BEA Forestry: weak 9, plain 60).
- **Maximal solvable intervals:** longest interval median 8 years at d = 2 (quartiles 6–10),
  14 at d = 4 on 1963–2016 (d = 4 longer in 48 of 54 industries; note d = 2 normalizes by the
  II price and d = 4 by the output price). Median maximal interval 2 years at d = 2, 4.5 at
  d = 4; singletons 32% and 11%. The longest interval equals the pair-only bound (longest window
  without a dominance violation) in 63 of 64 series at d = 2 (exception: Chemicals, 4 vs 5) and
  in 55 of 55 at d = 4. At d = 2, 30% of consecutive year pairs are conflicts (both relative
  prices and output go up), 11% at d = 4. d = 7 was not run.

## Why closed

Both measures reduce to the dominance order "all relative prices higher and output higher";
the geometry of the model hardly enters. Deleting two thirds of the years is a much harsher and
less informative statement than a 9% price correction (US, rho* = 0.0897).

If ever mentioned in the perturbation paper: fact 2 (deletion = a degenerate box) and one
sentence comparing deletion with the price correction on the same data.
