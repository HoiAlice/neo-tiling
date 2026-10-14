# Attempt 2: structural analysis of `ρ` and `ρ_dom` at `d = 2`

Pre-reduction thinking. Collects what we know about the problem, where the
obstacles are, and which reductions look plausible. See also
`scratchpad/BV-TECHNIQUE.md` and `scratchpad/REDUCTION-SOURCES.md`.

## 1. Precise formulation

Points `P ∈ Q^(2 × T)_{++}`, outputs `y ∈ Q^T_+`. Cost
`π(p, q) = max(q/p, p/q) − 1`, `totalPert(P, Q) = Σ_t Σ_i π(p^i_t, q^i_t)`,
convex, separable, proper.

* **`ρ(P, y)` (full):** `min totalPert(P, Q)` over positive `Q` such that `y` is
  weakly solvable at `Q`. By the lemma on the attained minimum (notes §5), the
  infimum is attained.
* **`ρ_dom(P, y)` (dominance relaxation):** `min totalPert(P, Q)` over positive `Q`
  such that for every pair `(t, s)` with `y_t > y_s` there is some `i ∈ {0, 1}`
  with `q^i_t ≤ q^i_s`.

`ρ_dom ≤ ρ` because every weakly solvable `Q` satisfies the dominance disjunctions
(corollary of `IsBlocked.isWeakReachable`). Strict inequality is possible: the
triangle `P = ((4,1), (3,3), (1,4))`, `y = (1, 5, 3)` has `ρ_dom = 0`
(no coordinate dominance) and `ρ = 2/5` (needs a mixed witness `(1/2, 1/2)`).

## 2. `ρ_dom` as a 2-cover with convex-isotonic costs

For every assignment `σ : conflicts → {0, 1}` of a coordinate to each conflict,

   `cost(σ) = g_0({(t, s) : σ(t, s) = 0}) + g_1({(t, s) : σ(t, s) = 1})`,

where `g_i(E)` is the minimum of `Σ_t π(p^i_t, q^i_t)` over positive `q^i` subject
to `q^i_t ≤ q^i_s` for every `(t, s) ∈ E`. `g_i` is a convex-cost isotonic
regression and polynomial by Hochbaum–Queyranne 2003.

`ρ_dom = min_σ cost(σ)`.

**Property of `g_i`.** It is monotone (adding constraints only raises the cost). It
is **not submodular**: on a toy example (3 points `a_1 = 3, a_2 = 2, a_3 = 1`,
cost `(u − a)^2`), the marginal cost of adding the constraint `u_2 ≤ u_3` to the
empty set is `0.5`, but its marginal when the set `{u_1 ≤ u_2}` is already present
is `1.5`. The marginal cost **grows** with more constraints, so `g_i` is
**supermodular**. (Checked numerically; expected to hold for `π` as well. Needs a
formal proof.)

Min-cost 2-cover with supermodular costs is a hard problem in general: supermodular
minimisation is NP-hard. This is a **structural reason to suspect `ρ_dom` is
NP-hard**, but it is not a proof: supermodularity is necessary, not sufficient, for
the hardness to transfer.

## 3. Attempted reduction angles

Nothing has worked yet. For each, what breaks and what might save it.

### (a) From `VERTEX COVER` on general graphs

`VC`: pick a minimum-weight set of vertices covering every edge. Try `σ`-choice
`↔` vertex selection: each conflict `(t, s)` covered by one of two endpoints.
**Breaks** because our `σ` is per-edge, not per-vertex: moving one coordinate of
one point affects many conflicts, with a cost that depends on their mutual
isotonic regression and is **not linear in the number of conflicts covered**. VC
and ours have different cost structures.

### (b) From `BETWEENNESS` (Opatrny 1979, NP-complete)

Given triples `(a, b, c)`, find a linear order with each `b_i` strictly between
`a_i` and `c_i`. The constraint "`b` between `a` and `c`" is a disjunction of two
**conjunctions**: `(a < b < c) ∨ (c < b < a)`. Our conflict is a disjunction of
two **atoms**. **Doesn't fit the per-pair format.**

### (c) From `POSET DIMENSION ≥ 3` (Yannakakis 1982)

Recognition of 2D posets is **polynomial** (Yannakakis). Our problem lives in
`R^2`, so if the underlying structure were "poset realisable in `R^2`" we'd be
polynomial. This leans FOR polynomial, AGAINST hardness.

### (d) From `MIN FEEDBACK VERTEX SET` on tournaments

Our conflict tournament is **transitive** (`y` is a total order), so FVS `= 0`.
Not useful.

### (e) From `3-COLORING`

Three colours, we have two coordinates. Doesn't fit.

### (f) From `MIN-COST 2-SAT` on literals that are difference constraints

Min-cost 2-SAT is NP-hard in general (equivalent to weighted VC), but under
specific cost structures becomes polynomial (project selection). Our cost is
**convex** on continuous variables, not weights on literals, so the standard
reductions don't transfer directly.

## 4. Reasons to lean POLYNOMIAL

* `d = 2` versus `d ≥ 3` gives the same split as several related problems
  (`POSET DIM`, `GARP deletion` [Boodaghians–Vetta]).
* At `d = 2` the chain structure of weakly reachable sets is strongly ordered
  (strictly convex lower-left chains), giving a `O(T^3)` DAG for the fixed-prices
  oracle.
* The dominance conflict graph is the comparability graph of a product poset,
  hence perfect for every `d`. Perfection gives polynomial algorithms for several
  deletion variants.

## 5. Reasons to lean NP-hard

* `g_i` is supermodular. Min-sum of two supermodular functions with coverage
  constraints is a hard combinatorial family.
* The problem has a "job-shop with disjunctive precedences" flavour, and
  2-machine job shops with disjunctive constraints are often NP-hard.
* No polynomial algorithm found in the literature.

## 6. The honest state

**Open.** Neither direction has yielded a proof. I lean slightly toward NP-hard
based on supermodularity, but Yannakakis' dimension result for `d = 2` is weight
for polynomial.

## 7. Concrete next steps I'd try with more time

1. Prove formally that `g_i` is supermodular for `π`.
2. Search for a reduction from a lesser-known hard problem whose structure matches
   "min-sum of 2 supermodular isotonic costs over coverings": perhaps PSEUDO-TREE
   PACKING, MIN COST FEEDBACK ARC SET ON DAGS WITH BUDGET, or two-stage
   scheduling.
3. Attempt an algorithm: `g_i(E)` is a Lovász-extended convex function. The
   problem `min g_0(E_0) + g_1(E_1)` subject to `E_0 ∪ E_1 ⊇ all` might admit a
   convex relaxation whose LP is integral under additional structure (e.g.,
   consecutive-ones in the pair-selector matrix, which may hold at `d = 2` due to
   the transitive-tournament structure).
4. Characterise optimal `σ` structurally on small examples (`T ≤ 6`): is `σ`
   always "rank-monotone" (if `σ(t, s) = 0`, then `σ(t, s') = 0` for all
   `t ≤ t' < s' ≤ s`)? If yes, `O(T^4)` dynamic programming.

Steps 1, 3 and 4 are the most tractable in a short time frame.
