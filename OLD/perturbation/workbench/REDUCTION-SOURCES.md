# Sources for NP-hardness of rho_dom, d = 2

Verification tags: V-full = full text read; V-abs = bibliographic data and abstract confirmed on a publisher, repository or RePEc page this session; V-snip = confirmed only from a search-engine snippet; S = from my memory, not checked this session. No source was read in full (the sandbox only gave abstracts and pages), so nothing is tagged V-full.

## 0. Reformulations (useful for every reduction)

1. **3D antichain form.** A pair (t,s) with y_t > y_s is a conflict iff q^0_t > q^0_s and q^1_t > q^1_s. So Q is feasible iff the 3D points (q^0_t, q^1_t, y_t) contain no pair in strict 3D dominance. Hence the violation graph G(P,y) = {(t,s): p_t > p_s strictly in both coordinates and y_t > y_s} is the comparability graph of a strict 3D dominance order. Ties in y delete edges. Pairs already satisfied in P are free but can be re-activated by moving points.
2. **Sequential form.** Sort by y and let U_k be the union of the open NE quadrants of the first k points. Point k+1 must avoid U_k. The allowed region is a down-set under a non-increasing staircase g_k(x) = min{ q^1_s : q^0_s < x }. The DP state is the staircase, which is exponential in general. This is the main obstacle to a polynomial DP.
3. **Zero-cost case = 2-dimensional posets.** For distinct y, S_0 and S_1 must cover all pairs of the total order L. If their transitive closures also partition the pairs, both are transitive orientations of complementary graphs, i.e. L is realized by a permutation (dimension 2). In general the cost is isotonic-regression cost of closure(S_0) plus that of closure(S_1). Feasibility is always trivial: q^1 reversed-y works.
4. **Triangle forcing.** If t > s > u in the dominance-with-y sense, then (t,s), (s,u), (t,u) are all conflicts. Two of the three share a colour. The colour classes are:
   - (t,s) and (s,u) together form a chain pool of 3 points.
   - (t,s) and (t,u) together give a top t pooled with two points.
   - (s,u) and (t,u) together give a bottom u pooled with two points.
5. **Pooling cost, scale-invariant.** Pooling two points with ratio a costs about 2*sqrt(a) - 2, and a 3-chain 1, r, r^2 pooled costs about 2r - 2. Chain pooling is superadditive and "different colours" is cheaper. Splitting conflicts across coordinates is therefore encouraged on chains (antiferromagnetic coupling). Two conflicts sharing a common bottom s with incomparable tops t, u are resolved by raising s to max(.,.) in one coordinate. That is cheaper than in two coordinates, so agreement is encouraged (ferromagnetic, submodular, min-cut-like). Hardness must come from the chain / antiferromagnetic couplings. This is a heuristic, not proved. The test is cheap: brute-force F(sigma) for small T and check (super/sub)modularity numerically.

## 1. Candidate assessments

### (A) Poset dimension (Yannakakis 1982) — LOW
- **Source problem.** Decide dim(poset) <= k. NP-complete for k >= 3 (Yannakakis also gives k >= 4 for height-2 orders). The height-2, k = 3 case was open until Felsner, Mustata and Pergel closed it.
- **Refs.**
  - M. Yannakakis, "The complexity of the partial order dimension problem", SIAM J. Algebraic Discrete Methods 3(3), 351-358, 1982. [V-abs: citation and statement confirmed via secondary sources; no DOI located]
  - S. Felsner, I. Mustata, M. Pergel, "The complexity of the partial order dimension problem: closing the gap", SIAM J. Discrete Math 31(1), 2017, DOI 10.1137/15M1007720; arXiv:1501.01147. [V-abs]
- **Fit.** The d = 2 structure in item 3 above is exactly the dimension-2 case, which is polynomial (permutation graph recognition). Hardness of dimension k >= 3 would correspond to d = k problems (or to y plus two coordinates being a 3D realizer), not to our d = 2 with free y. Using the 3D antichain form: with y free we encode dim-3-like structure, but the cost is a continuous perturbation, not a yes/no realizer test.
- **Obstacles.** The zero-cost question is poly. Using k = 3 hardness needs an extra coordinate we do not have. Unclear gadget translation; I would not start here.

### (B) Betweenness (Opatrny 1979) — MEDIUM-LOW
- **Source.** n elements, triples (a,b,c). Is there a linear order with b strictly between a and c? NP-complete (Garey-Johnson MS1).
- **Ref.** J. Opatrny, "Total ordering problem", SIAM J. Comput. 8(1), 111-114, 1979, DOI 10.1137/0208008. [V-abs: DOI, volume/issue, problem and reduction from hypergraph 2-colourability confirmed by AcaWiki and SIAM abstract page; pages 111-114 are from memory]
- **Sketch.** Our objects are two orders (the coordinate orders pi_0 and pi_1) whose inversion sets cover all y-pairs. That is, pi_1 must invert everything pi_0 does not invert. Take pi_0 as "the" linear order, with pi_1 forced to be roughly the complement. A triple needs "b between a and c" = the pair (a,c) is not nested wrongly. It is hard to enforce a three-body constraint with pairwise conflicts. Opatrny's own source is 2-colourability of 3-uniform hypergraphs, which is closer to our "colour each conflict 0 or 1" picture (see the recommendation below).
- **Obstacles.** The constraint is on three points; pooled costs are pairwise per colour class (additive over closure blocks). A gadget must create a "not all equal" penalty out of the superadditive chain pooling (item 5). That works only through triangles (item 4), which complicates each clause.

### (C) Cyclic ordering (Galil-Megiddo 1977) — LOW
- **Ref.** Z. Galil, N. Megiddo, "Cyclic ordering is NP-complete", Theoret. Comput. Sci. 5(2), 179-182, 1977. [V-abs: bibliographic data confirmed from several bibliographies; no DOI found. Related: N. Megiddo, "Partial and complete cyclic orders", Bull. AMS 82 (1976) 274-276, V-abs]
- **Fit.** Circular structure has no counterpart in a 2D product order with a linear y. Dismiss unless the geometry produces cyclic structure through the two crossed coordinates, which I do not see.

### (D) FAS / linear ordering / tournaments — MEDIUM (strongest alternative)
- **Source.** Min feedback arc set on tournaments is NP-hard (Alon 2006; Charbit-Thomasse-Yeo 2007, independent). Weighted versions (also with weights on a tournament) follow, and Max Acyclic Subgraph is NP-hard in general (Karp 1972 FAS; S).
- **Refs.**
  - N. Alon, "Ranking tournaments", SIAM J. Discrete Math 20(1), 137-142, 2006. [V-abs: venue, volume, pages confirmed via citing papers, abstract via Princeton page; DOI not retrieved]
  - P. Charbit, S. Thomasse, A. Yeo, "The minimum feedback arc set problem is NP-hard for tournaments", Combin. Probab. Comput. 16(1), 1-4, 2007, DOI 10.1017/S0963548306007887; full text at https://hal-lirmm.ccsd.cnrs.fr/lirmm-00140321. [V-abs]
  - Closest economics analogue: K. Shiozawa, "Note on goodness-of-fit measures for the revealed preference test: the computational complexity of the minimum cost index", Economics Bulletin 35(4), 2455-2461, 2015 (working paper: Osaka Univ. DP 15-18, "Note on the goodness-of-fit measure for GARP; NP-hardness of minimum cost index"). The NP-hardness of Dean-Martin's MCI is shown by reduction from Maximum Acyclic Subgraph. [V-abs via RePEc; no DOI listed]
- **Fit.** The choice sigma: conflicts -> {0,1} partitions the pairs of the total order L. FAS asks for a linear order minimizing reversed arcs; our problem asks for two orders (the coordinates), with cost on each closure and the covering requirement. If the instance gives one coordinate (say 1) a huge cost for any perturbation, then q^1 ~ p^1 and the pairs not covered by p^1 must be covered by coordinate 0 inversions. Then the problem is a single-order problem: min convex cost to invert (relative to y) all pairs where p^1 is "wrong", i.e. an isotonic regression over a poset determined by P. This is poly (one coordinate, a fixed poset), so FAS-type hardness needs both coordinates active. The tournament weights must come from conflict-pair pool costs, with cycle structure from the three coordinates.
- **Obstacle.** Weights of the arcs are not free: they are pool costs tied to geometry. Cycles need the crossed-pair structure; I do not see a direct encoding of an arbitrary tournament (G is a 3D-dominance comparability graph, a perfect graph).

### (E) 2D vector packing / 2D scheduling — LOW
- No structural match: our constraints are order disjunctions, not capacity sums. Not pursued.

### (F) "2-colour edges of a (transitive) tournament, objective = sum of two per-colour isotonic regressions"
- Search found no direct result. Nearest known results:
  1. **Goodness-of-fit for revealed preference** (same family of structure; reductions from independent set / MASP). B. Smeulders, L. Cherchye, B. De Rock, F. C. R. Spieksma and co-author(s), "Goodness-of-fit measures for revealed preference tests: complexity results and algorithms", ACM Trans. Econ. Comput. 2(1), 2014 [S for TEAC details and author list; V-abs only for the ULB working-paper version "Goodness of fit measures for revealed preference tests: Complexity results and algorithms", ULB Institutional Repository 2013/162939, RePEc ulb:ulbeco:2013/162939 (De Rock, Smeulders, Cherchye, Spieksma). Abstract: NP-hardness of Afriat's vector index (Varian's index) and the Houtman-Maks index via independent set; no O(n^(1-delta)) approximation unless P = NP; Afriat's index in P.]
  2. M. Dean, D. Martin, "Measuring rationality with the minimum cost of revealed preference violations", Rev. Econ. Statist. 98(3), 524-534, 2016. [S] (introduces the MCI shown NP-hard by Shiozawa above.)
  3. H. Varian, "Non-parametric analysis of optimizing behavior with measurement error", J. Econometrics 30, 445-458, 1985. [V-snip: volume and pages confirmed] (the perturbation-of-data formulation closest to our rho; hardness there is for the number of goods growing, not d = 2.)
  4. S. Houtman, J. Maks, "Determining all maximal data subsets consistent with revealed preference", Kwantitatieve Methoden 19, 89-104, 1985. [S]
  5. A. Pananjady, R. J. Samworth, "Isotonic regression with unknown permutations: statistics, computation and adaptation", arXiv:2009.02609, 2020 (Ann. Statist. 2022). [V-abs: title, authors and the bivariate-versus-multivariate computational contrast confirmed; the claim that the d = 2 least-squares estimator is NP-hard via max-clique came from a search snippet of a different result and I did NOT verify it in the paper, treat as V-snip.] Related in spirit: choose the permutation (the order) for a monotone fit.
  6. V. Chepoi, D. Cogneau, B. Fichet, "Polynomial algorithms for isotonic regression", in L1-Statistical Procedures and Related Topics, IMS Lecture Notes-Monograph Series 31, 1997. [V-snip: only the statement that no polynomial algorithm for general partial orders is known and the NP question is open appeared; unverified, check before citing.]
  7. Garey, Johnson, Stockmeyer, "Some simplified NP-complete graph problems", Theoret. Comput. Sci. 1(3), 237-267, 1976. [S] (Max-Cut; used in the recommendation.)
  8. For 2-colouring hypergraphs (Opatrny's source): Lovasz 1973, "Coverings and colorings of hypergraphs", Proc. 4th Southeastern Conf. Combinatorics, Graph Theory and Computing, 3-12. [S]
- No result found for "min-cost 2-colouring of the edges of a tournament to minimise the sum of per-colour global functionals". Nothing on "disjunctive isotonic regression" turned up in the search either.

## 2. Evidence for and against polynomial time (honest)

For poly:
- Zero-cost feasibility is trivially true, and the exact-cover case is dimension 2, which is polynomial.
- Hardness in the revealed-preference literature (above) uses dimension that grows with the instance. We have no d = 2 hardness citation.
- The staircase structure (item 2) is a monotone chain; if the optimal Q always keeps the frontier as a bounded-complexity object (for example optimal Q only merges adjacent y-levels, or the support of the frontier is determined by P), a DP or a convex-chain flow LP could work. The repo already has a d = 2 polynomial result for the fixed-price problem via such an LP, which shows the 2D geometry can be benign.
- If F(sigma) were submodular (all couplings "agree-favouring") it would be a min-cut. The chain superadditivity heuristic in item 5 suggests this is not the case, but it is untested.
- In continuous terms the feasible set is a union of polyhedra in log-coordinates, but the constraint is "no strict 3D dominance", which is far more structured than a general disjunction.

Against poly: G realizes arbitrary 3D-dominance graphs (with y free), so the per-conflict choice has genuine combinatorial freedom with superadditive pooling couplings.

## 3. Recommendation

**Pursue first: a direct reduction from NAE-3SAT / 3-uniform hypergraph 2-colourability (Opatrny's source, equivalently Max-Cut), exploiting antiferromagnetic chain pooling (item 5).**

Concrete gadgets (rough):
1. *Variable gadget.* A pair (t_v, s_v) with p_t = (a,a), p_s = (1,1) in strict dominance, y_t > y_s. The conflict is resolved by coordinate 0 or 1. By symmetry both cost the same (about 2*sqrt(a) - 2 if pooled). The colour sigma(v) in {0,1} is the Boolean value. A flipped copy of the coordinates encodes negation.
2. *Wires / copies.* To make a literal appear in several clauses, put clause points relative to s_v so that one of the options (raise s in coordinate 0 or lower t in coordinate 1) changes whether a clause conflict is already satisfied. Equality chains are ferromagnetic: use common-bottom pairs with incomparable tops, where agreement is cheaper (max-type).
3. *Clause (NAE) gadget.* A middle point m placed on a chain between a top t and a bottom u so that the triangle (t,m), (m,u), (t,u) is forced (item 4). The three pair-conflicts are tied to three literal gadgets by geometric scale separation (coordinates in different orders of magnitude, so only intended pairs interact). Make the cost of "all three conflicts in the same colour" strictly larger than any other pattern, by chain superadditivity (about 2r - 2 versus 4*sqrt(r) - 4). That penalty vanishes exactly when the three colours are not all equal, i.e. the clause is NAE-satisfied.
4. *Threshold.* theta = n_vars * base_cost + n_clauses * (NAE-satisfied clause cost). Use rational scales r_j with r_j >> r_{j-1}, with y-ties to delete unwanted conflicts. All data are rational and polynomial in size since scales need only polynomially many bits (r = 2^k, k = O(n)).
5. *Main difficulty.* Forced triangles (item 4) leave a colour pattern with two equal colours inside each clause, and need to be compensated by a global offset. Also isolation of gadgets via geometric scale separation is plausible but I did not verify it numerically.

**Cheap first experiment (before committing to the proof).** Write the brute-force sigma enumeration for T <= 8 random points and check: (i) whether F(sigma) is submodular on random instances (if yes in all cases, suspect polynomial, e.g. min-cut), (ii) the NAE-clause gadget cost table for the three-pair chain.

**Strongest alternative: weighted tournament FAS / Max Acyclic Subgraph, following Shiozawa's MCI reduction** (Charbit-Thomasse-Yeo for tournaments). Encode a vertex as a point and an arc as a conflict whose orientation is chosen via the coordinate; make one coordinate expensive to push; cycles come from the crossing of the two coordinate orders. The weights are geometry-determined pool costs, which is the obstacle (see D).

Not recommended: A (dimension 2 is polynomial and k >= 3 needs a third coordinate), C, E.
