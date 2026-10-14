# SUBSET SUM -> rho(P,y), d=2: NO reduction found (obstruction documented)

Script: ss_pool.py (pooled-block model). No 3-element instance was built, because no gadget survives the analysis below.

## Where a number a_i could enter
Cost is a sum over points of pi = e^|d|-1 (convex, separable). Constraints are order/dominance disjunctions (x or y) plus the pair-cover angle.
1. Choice (x vs y) is genuinely binary and costs min(c_x,c_y): concave, so choices are independent per conflict. No coupling => nothing global to balance.
2. Sums cannot come from chains: a strict-order chain propagates a MAX of required displacements (d_k >= d_{k-1} - gap), never a sum. Weights by chain multiplicity are unary only (pseudo-poly DP kills hardness).
3. The only place where Sum a_i appears with binary-sized numbers is a POOLED block (isotonic-regression tie): block of points forced equal in one coordinate moves to the exp-mean, cost
   ~ sum a_i^2 - (sum_J a_i + M*D0)^2/(M+|J|)   (M = mass of an anchoring hub, D0 its offset).
   Membership J is chosen by the x/y disjunction (point pools in the x-block or the y-block). So the encodable cost is  -f(S_J) - g(S_K), f,g convex: CONCAVE in the subset sum. Subset sum equality needs a convex penalty (S_J-T)^2; the pooling optimum always gives minus a square. Min of a concave function of sums picks extremes / similar values (clustering), never "balanced".
   Numerical check (exact exp cost, free hubs, all 2^n assignments):
   - a=(.1,.2,.3,.4) (YES for partition? {.1,.4}|{.2,.3}: sums .5/.5): best cost 0.20508 at sums .3/.7 (contiguous split); balanced .5/.5 split costs 0.42621, which is the WORST. Extreme-only value 0.42621 too.
   - a=(.1,.2,.3,.6): best 0.21034 at {.6}|{.1,.2,.3} (balanced) only because it is also the contiguous clustering.
   - a=(.05,.1,.15,.2,.25,.35): best 0.25898 at sums .3/.8 (contiguous); balanced-ish .5/.6 gives 0.30894.
   So the optimum is the 1-D 2-means (contiguous) split, polynomial, uncorrelated with equal-sum. The cost does not cross a threshold iff a subset sums to S.
4. Pair-cover angle (the other nonconvexity): single-heavy landscape unimodal; couplings through shared lights are ferro/sub-additive (see PAIR-COVER-HARD.md: 0.744 vs 0.420; 27/28 ferro). Angle is a continuous interpolation, so a "fractional subset" is always feasible at no worse cost: LP-relaxation integrality fails to bite.
5. Balance gadget (global sink): a point's required displacement is a max, not a sum of others' moves, so there is no linear functional of the choices to penalize. The only bilinear terms (lambda*d0+(1-lambda)*d1>=0) are per blocker triple with its own lambda.

## Verdict
Subset Sum / Partition / 3-Partition cannot be encoded by the mechanisms present: costs are separable convex; couplings are monotone (ferro) or pooling (concave in subset sums => clustering, not balancing). Not a proof of polynomiality, just: every arithmetic channel has the wrong sign. Consistent with the earlier lean towards poly for the angle part; remaining hope for hardness is the multi-level rho_dom nesting (antiferro chain pooling, REDUCTION-SOURCES 0.5), which has no arithmetic channel either (pooling is still concave in sums).

## If one wanted to continue
Look for a convex-in-sum channel: a point whose cost is paid on the DEVIATION of a forced (non-free) block position, i.e. a pooled block whose representative is pinned by a heavy anchor (M large) -> cost separable again. Intermediate M gives -S^2/(M+|J|), still concave. A cardinality-weighted variant (denominator M+|J|) could make  knapsack-like trade-offs, worth one search, but not subset-sum equality.
