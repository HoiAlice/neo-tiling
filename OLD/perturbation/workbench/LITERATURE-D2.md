# Literature search: d=2 complexity of rho(P,y) (min price perturbation for weak solvability)

Method: web search plus a few page fetches. NO full paper was read (no V-full). Items are V-abs (abstract or publisher page seen) or S (search snippet only). Details beyond the abstract are unverified. Several searches (isotonic with disjunctive constraints, hardness of computing Renegar's distance, 2-SAT with convex costs) returned nothing directly relevant. Those gaps are stated, not filled.

## Revealed preference: closest analogues

1. Boodaghians, S., Vetta, A. "Testing Consumer Rationality using Perfect Graphs and Oriented Discs." arXiv:1507.07581 (2015); a WINE 2016 version exists but I did not verify it. https://arxiv.org/abs/1507.07581 [V-abs, via ar5iv page]
   Degree of rationality (min number of observations to delete so GARP holds). It is polynomial for 2 commodities, because minimal GARP cycles are digons and the digon-hitting vertex-cover graph is perfect. It is NP-complete for 3 or more commodities (reduction from planar 3-SAT). This is the same d=2 poly versus d>=3 NP-hard dichotomy as ours, which makes it the strongest structural analogue. But the measure is the number of deleted observations, not continuous price perturbation. It gives no result for rho.

2. Cherchye, L., De Rock, B., Smeulders, B., Spieksma, F. "Goodness-of-fit measures for revealed preference tests: complexity results and algorithms." ULB working paper 2013/162939 (https://ideas.repec.org/p/ulb/ulbeco/2013-162939.html); COMSOC 2012 version https://comsoc-community.org/assets/proceedings/comsoc-2012/Cherchye.pdf. The journal venue is not confirmed. I believe it is Journal of Mathematical Economics 2014 but did NOT verify this. [V-abs / S]
   Afriat's index is polynomial. Varian's index and the Houtman-Maks index are NP-hard (reduction from independent set), with no O(n^(1-delta)) approximation unless P=NP. Q4: the abstract and snippets do not mention a restriction on the number of goods. The reductions appear to use many goods or abstract graph-realizable data. I could not check whether they embed in d=2. By item 1, Houtman-Maks (deletion) at d=2 is polynomial, so the independent-set reduction cannot go through at d=2 for that measure. Varian's index at d=2 is unresolved by what I found.

3. Shiozawa, K. "Note on the goodness-of-fit measure for GARP: NP-hardness of minimum cost index." Economics Bulletin 35(4), 2455-2461, 2015. https://www.accessecon.com/Pubs/EB/2015/Volume35/EB-15-V35-I4-P246.pdf ; Osaka DP 15-18 https://www2.econ.osaka-u.ac.jp/econ_society/dp/1518.pdf [V-abs]
   The Dean-Martin minimum cost index is NP-hard (reduction from feedback arc set, or max acyclic subgraph in the DP version). There is a polynomial approximation via weighted FAS. It is a cost-based (weighted deletion) measure. It says nothing specific about d=2.

4. Dean, M., Martin, D. "Measuring Rationality with the Minimum Cost of Revealed Preference Violations." Review of Economics and Statistics, 2016. [S]
   Origin of the minimum cost index in item 3. Not opened.

5. Echenique, F. et al., approximate-rationalizability appendix (minimal epsilon rationalizing a dataset). https://eml.berkeley.edu/~fechenique/published/approximate_eu_appendix.pdf [S]
   Authors and title not confirmed from the snippet. It is an analogue of "minimal perturbation parameter" (Afriat-type epsilon), not price perturbation at d=2.

## Geometry: convex position and convex chains

6. Arkin, E.M., Dieckmann, C., Knauer, C., Mitchell, J.S.B., Polishchuk, V., Schlipf, L., Yang, S. "Convex transversals." WADS 2011, LNCS 6844, pp. 49-60. DOI 10.1007/978-3-642-22300-6_5. https://researchconnect.suny.edu/en/publications/convex-transversals-2/ [V-abs]
   The abstract states a PTAS for the minimum shift of points into convex position in 2D and a 2-approximation in any dimension. It also shows that deciding existence of a convex stabber of planar segments is NP-hard. The minimum shift to convex position is the closest geometric relative of rho (point movement to enforce a convex structure). But it uses a Euclidean/shift norm and global convex position, not our separable ratio cost and cone-of-cut-indicators condition. The existence of a PTAS suggests the exact problem is not known to be polynomial. I did not confirm whether exact hardness is stated there.

7. Report TU Berlin 694-2000 (convex cover number and convex partition number of planar point sets: NP-complete, with log-approximation). https://page.math.tu-berlin.de/~combi/coga-old/publications/techreports/2000/Report-694-2000.html ; related Springer chapter https://unpaywall.org/10.1007%2F3-540-44634-6_18 and "On the Reflexivity of Point Sets" https://www.ibr.cs.tu-bs.de/users/fekete/hp/publications/PDF/2000-On_the_Reflexivity_of_Point_Sets.pdf [S; authors not verified]
   Covering a planar point set by the fewest convex chains is NP-complete. This is relevant to the covering side of our y = sum of 1_S structure (y is a nonnegative combination of chain-cut indicators). Caveat: the problem is fixed-point-set covering, so it is not the same as our cone-membership at fixed Q, which is polynomial.

8. "Some Geometric Applications of Anti-Chains." arXiv:1910.07586 (authors not captured). https://arxiv.org/pdf/1910.07586 [S]
   Covering points by monotone non-crossing curves in polynomial time via antichains/Dilworth. A possible tool for the DAG/flow structure. Not a perturbation result.

## LP sensitivity / distance to infeasibility

9. Renegar's distance to ill-posedness, and Freund-Vera, Peña-Roshchina, Peña-Vera-Zuluaga (Hoffman constant). See https://arxiv.org/pdf/1506.03295v1 , https://optimization-online.org/2019/05/7210/ [S]
   Only background found. NO NP-hardness result for computing the distance to infeasibility, and none for a 2D structured version, was found. These are continuous norm-ball perturbations of the whole data. They do not match our combinatorial family (cuts by convex chains) and give no usable hardness or algorithm for rho. A known classical hardness line (Rohn, Poljak-Rohn on distance to singularity) is from my memory and was NOT confirmed by search. Do not cite it without checking.

## 2-variable-per-inequality / monotone IP / isotonic

10. Hochbaum, D.S., Naor, J. "Simple and fast algorithms for linear and integer programs with two variables per inequality." SIAM J. Computing 23(6), 1994. https://hochbaum.ieor.berkeley.edu/html/pub/HNaorSICOMP94.pdf [V-abs]
    Feasibility of LI(2) in O(d^2 n log n). Monotone integer programs are solvable in pseudo-polynomial time. A relevant tool if rho's constraints (after fixing which chain structure) reduce to monotone two-variable inequalities.

11. Hochbaum, D.S., Shanthikumar, J.G. "Convex separable optimization is not much harder than linear optimization." J. ACM 37(4), 1990. https://hochbaum.ieor.berkeley.edu/html/pub/Hochbaum-Shanthi-JACM90.pdf [V-abs]
    Separable convex minimization over totally unimodular constraints is polynomial. Relevant: totalPert is convex separable. It applies once the combinatorial structure (which cut/chain is active) is fixed or totally unimodular.

12. Ahuja, R.K., Hochbaum, D.S., Orlin, J.B. "Solving the convex cost integer dual network flow problem." Management Science 2003 (the Algorithmica 2004 link found is "A cut-based algorithm for the nonlinear dual of the minimum cost network flow problem"). https://hochbaum.ieor.berkeley.edu/html/pub/AHO-cut-based-Algorithmica-2004.pdf ; Hochbaum, "Monotone IPs", EJOR https://hochbaum.ieor.berkeley.edu/html/pub/EJOR-3var.pdf ; Networks 2020 https://hochbaum.ieor.berkeley.edu/html/pub/IP2-IP3-Net-2020.pdf [S; titles and years for the AHO paper unverified]
    Convex cost on difference/monotone constraints reduces to min-cut. Standard isotonic regression with convex losses lives in this family. Disjunctive (either/or) order constraints break monotonicity. No search result addressed this variant.

13. Isotonic regression with unknown permutations (arXiv:2009.02609) [S]: NP-hard even for d=2 (from max-clique). Also Bach, NeurIPS 2018 (https://arxiv.org/pdf/1707.09157), on convex and some non-convex losses over a DAG order. Not disjunctive, only context. No paper on "isotonic regression with disjunctive order constraints" was found.

## Shananin and the d=2 question

14. Shananin et al. (inverse demand, homogeneous utilities): "Effective algorithms for homogeneous utility functions" (https://cdnjs.deepai.org/publication/effective-algorithms-for-homogeneous-utility-functions) [S, snippet only]. It states that the problems are "at least NP-hard" without homogeneity and polynomial algorithms are built under positive homogeneity. Also Shananin-Tarasov, arXiv:math/0206186 [S]. No explicit d=2 perturbation or complexity discussion was found. Kübler-Malhotra-Polemarchakis, "Recovering Preferences from Finite Data" (arXiv:1909.05457) [S] is a general finite-data revealed preference reference.

## Not found
- Q2 (isotonic with disjunctive order constraints) and Q5 (min-cost 2-SAT with convex costs / convex 2-SAT): no direct source. Only the Hochbaum monotone-IP family (items 10-12), where 2-variable monotone problems are s-t cuts and the non-monotone case is hard in general (standard fact, not verified here).
- Q6 (bilevel or parametric minimum perturbation to flip feasibility at d=2): nothing found.
- Q7: nothing found that discusses d=2 complexity or perturbation for Houthakker-Johansen/Shananin.

## Top 5
1. Boodaghians-Vetta, arXiv:1507.07581: the same d=2 poly versus d>=3 NP-complete dichotomy (for deletion measures).
2. Cherchye-De Rock-Smeulders-Spieksma (ULB 2013/162939): NP-hardness of Varian and HM indices. The d=2 applicability is unchecked; read the full paper.
3. Arkin et al., Convex transversals (WADS 2011): minimum shift to convex position, PTAS in 2D.
4. Hochbaum-Shanthikumar JACM 1990 and Hochbaum-Naor SICOMP 1994: the poly toolbox for convex separable costs on monotone/TU constraints.
5. TU Berlin Report 694-2000 on convex cover number (NP-complete): the covering-by-convex-chains side.

## Does the literature settle d=2?
No. I found no source that states or implies polynomial or NP-hard for rho at d=2. The nearest evidence is a 2-versus-3 commodity dichotomy for the discrete deletion measure (Boodaghians-Vetta), which makes polynomial plausible at d=2. In the other direction, geometric problems with convex-position constraints (convex cover, stabbing, minimum shift with PTAS only) are NP-hard or approximation-only. This is suggestive, not decisive. Search coverage was limited, and none of the claims above come from reading full papers.
