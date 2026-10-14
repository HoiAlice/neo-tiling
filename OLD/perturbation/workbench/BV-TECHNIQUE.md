# Boodaghians–Vetta (arXiv:1507.07581v2): the d = 2 technique, and what it says about rho

Source status. Part I: I read the full 16-page arXiv v2 text (pdftotext of the PDF), every lemma and proof. Page refs are paper pages. Part II: my own derivations (marked "mine") plus three short web searches whose results are only snippets (marked "unverified"). I did NOT read the follow-up literature (Boodaghians' McGill MSc thesis, the 2018 sign-rank paper, GLS) beyond search snippets.

---------------------------------------------------------------------

# Part I. The paper

## 1. The problem (pp. 1–4)

Data: (p^1,x^1),...,(p^m,x^m), p^i, x^i in R^n_{>=0}. Assumed (p. 2): bundles distinct, all preferences strict (no ties).
- Direct revealed preference: x^i ≻ x^j iff p^i·x^i >= p^i·x^j (j != i).
- GARP (p. 2): no cycle x^1 ≻ x^2 ≻ ... ≻ x^k with x^k strictly preferred... in their strict-no-ties convention: "if x^1≻x^2,...,x^{k-1}≻x^k then x^k ⊁ x^1" (i.e. no cycle). Afriat (p. 2): GARP iff exists utility rationalising the data iff the revealed-preference digraph D = (V,A), V = bundles, arc i->j iff x^i ≻ x^j, is acyclic.
- CONSUMER RATIONALITY (p. 3): given data and integer k, is there a subcollection of <= k data points whose removal leaves a GARP-satisfying set? This is the (unweighted, cardinality) "degree of rationality" (dual to Houtman–Maks). It is exactly Directed Feedback Vertex Set (DFVS) on D.
- n large: equivalent to DFVS (Lemma 2.1, Deb–Pai, p. 4: with n = m commodities any digraph is realisable; p^i = e_i, x^i_j = 1 / 0 / 2). So inherits DFVS approximability (O(log n loglog n) upper, Seymour; UGC-hardness).

Note what is NOT in the paper: no weights, no perturbation of prices, no Afriat efficiency index, no continuous cost. Only vertex deletion with unit cost.

## 2. The two-commodity algorithm (Section 3, pp. 4–9)

Step 1: only digons matter (Lemma 3.1, Rose 1958, proof p. 5–6). For n = 2, every vertex-minimal directed cycle of D is a 2-cycle (WARP = GARP in 2D). Proof sketch: take a chordless cycle of length k>=3, the leftmost bundle x_i; budget lines l_i (through x_i perpendicular to p_i, non-positive slope); show inductively that l_j is steeper than l_{j+1} and x_{j+1} lies in the "below-right" quadrant of x_j for all j around the cycle, contradicting that x_i is leftmost.
Consequence: a set hits all cycles iff it hits all digons.

Step 2: auxiliary undirected graph G (p. 6). V(G) = V(D); edge {x_i,x_j} iff x_i ≻ x_j and x_j ≻ x_i (a digon). A vertex cover of G = feedback vertex set of D. So the rationality problem = Minimum Vertex Cover on G. (Examples p. 6–7: bundles on a concave curve give a clique; left-chain vs bottom-chain give a complete bipartite graph.)

Step 3: G is perfect (Theorem 3.2, pp. 7–9). Via the Strong Perfect Graph Theorem (Thm 3.1: no odd hole, no odd antihole), proved from:
- Lemma 3.2 (p. 7): for an induced path x_i - x_j - x_k in G, if x_i lies in the "upper-left" quadrant of x_j (x_j^{NW-closed}: x_i in x_j^{↖}) then x_k lies in x_j^{↖} as well; same for the opposite quadrant. Reason: mutual adjacency of x_i,x_j forces x_i,x_j to be incomparable in the coordinate (NE/SW) sense, so x_j lies in x_i's NW or SE quadrant. If x_i,x_k were on opposite sides of x_j, then (case x_j below the segment x_i x_k) budget line l_j cannot separate in a way giving both x_j ≻ x_i and x_j ≻ x_k; (case x_j on or above the segment) x_i ≻ x_j implies x_i ≻ x_k and x_k ≻ x_j implies x_k ≻ x_i, giving an edge x_i x_k, contradicting inducedness.
- Lemma 3.3 (p. 8): no odd hole with >= 5 vertices. In a hole, each x_i gets a colour (both neighbours in its NW quadrant, or both in its SE quadrant); adjacent vertices must get different colours (else x_{i+1} in NW quadrant of x_i and x_i in NW quadrant of x_{i+1}, contradiction), i.e. a proper 2-colouring of an odd cycle, impossible. (Fig. 5: an even hole C6 does occur, so G is not bipartite/the parity is needed.)
- Lemma 3.4 (p. 9): no antihole on >= 5 vertices (C5 is self-complementary, handled by 3.3; for k >= 6 the neighbourhood Γ_i of x_i lies entirely in one of two quadrants of x_i, then x_0,x_2,x_4 (pairwise adjacent) produce a contradiction).

Step 4: vertex cover in perfect graphs is polynomial (Thm 3.3, GLS 1984/88, via ellipsoid; cited, not reproved, p. 9). Hence Theorem 3.4: the 2-commodity consumer rationality problem is polynomial. The paper states the problem unweighted; the GLS theorem is (to my knowledge, unverified here) also valid for vertex weights, so weighted deletion would also be polynomial, but the paper does not state it.

## 3. Why it fails at n >= 3 (Section 4, pp. 10–15)

Not a "loss of perfection" in an abstract sense; it is the failure of both steps:
- WARP != GARP for n >= 3 (longer minimal cycles exist, even via Lemma 2.1 type constructions), so digons no longer suffice.
- Lemma 4.1 (p. 10–11): every oriented-disc graph (points x_i with a disc B_i through x_i on its boundary, arc i->j iff x_j in B_i) is a preference graph of a 3-commodity market: embed the disc drawing on the sphere of radius 1 centred at (1,1,1) (stereographic inverse preserves circles); choose p_i as the normal of the plane cutting the sphere exactly along B_i. This gives a much richer class of digraphs (incl. 3-cycles of arcs without digons, Fig. 6).
- Lemma 4.2 (Wang–Kuo, pp. 12–13): planar 3-SAT -> Vertex Cover on gadget graph G_phi (clause triangles, even variable cycles, edges to opposite literals), satisfiable iff VC <= 2m + (1/2) sum r_i.
- Lemma 4.3 (pp. 13–15): build an oriented-disc graph D_phi that has a digon for each edge of G_phi plus extra non-digon arcs forming an acyclic subgraph; so all cycles go through digons, and min DFVS(D_phi) = min VC(G_phi).
- Theorem 4.1: NP-complete for n >= 3.
So the paper does not explicitly exhibit an odd hole/antihole at n = 3; it shows that the digon graph of 3-commodity data contains arbitrary gadget graphs G_phi (which contain odd cycles: clause triangles are odd holes? a triangle is a clique, but variable gadget cycles with chords/clause connections create odd holes in G_phi), so perfection fails. The mechanism: in Lemma 3.2 the "two-sided quadrant" structure (a half-plane orientation per vertex) is what 2D budget lines give; in 3D the sphere-disc structure gives no such consistent side.
(The paper itself does not say "G loses perfection"; that is my gloss.)

## 4. Main theorems, verbatim content

- Thm 3.1 (SPGT, Chudnovsky–Robertson–Seymour–Thomas): perfect iff no odd hole, no odd antihole.
- Thm 3.2: the 2D auxiliary revealed-preference graph G is perfect.
- Thm 3.3 (GLS): vertex cover is polynomial on perfect graphs.
- Thm 3.4: consumer rationality is polynomial for two commodities.
- Thm 4.1: consumer rationality is NP-complete for >= 3 commodities.
- Also: (Lemma 3.1) WARP=GARP at n=2; (Lemma 2.1) every digraph is a preference graph for n = m; consequence: as hard to approximate as DFVS, and (via VC) 1.36-inapproximable (Dinur–Safra) unless P=NP, UGC: no constant factor.

---------------------------------------------------------------------

# Part II. Transferability to rho(P,y) at d = 2 (my analysis; each claim tagged)

## 5. Setup in log coordinates (mine)

u_t = (u_t^1,u_t^2) = log q_t, a_t = log p_t. Cost sum_{t,i} f_{t,i}(u_t^i), f_{t,i}(u) = e^{|u - a_t^i|} - 1 (separable, convex, minimised at a, f(a)=0).
rho_dom constraints: for each pair with y_t > y_s: u_t^1 <= u_s^1 OR u_t^2 <= u_s^2. Equivalently, forbid u_t >> u_s (strict in both coordinates).

Reformulation 1 (mine): y is non-increasing along strict dominance of u: u_s << u_t implies y_s >= y_t... precisely, the y-order is a linear extension (reversed) of the strict product order on u. I.e. rho_dom = minimum separable-convex movement of the points u_t in the plane so that the labels y become monotone (decreasing) functions of the point. This is "isotonic regression with errors in the independent variables" (move the x's, not the y's), 2-dimensional.

Reformulation 2 (mine): the three orders (y, u^1, u^2 ascending) must have no pair strictly increasing in all three, i.e. the poset (product order of (y,u^1,u^2)) restricted to strict comparabilities is empty. Choose the two orders sigma_1, sigma_2 (the weak orders of u^1, u^2); every y-ordered pair must be reversed in sigma_1 or sigma_2.

Reformulation 3 (mine): for fixed assignment of each conflicting pair (t,s) to a coordinate i(t,s) in {1,2} (the "chosen disjunct"), the problem splits into two independent problems "min sum f(u^i_t) s.t. difference constraints u^i_t <= u^i_s for chosen pairs", each a convex-cost dual-network-flow / isotonic-regression problem, polynomial (Ahuja–Hochbaum–Orlin; Hochbaum–Queyranne convex closure; snippets only, unverified). So all hardness is in the discrete choice of the assignment i(·,·) (equivalently of the two weak orders sigma_1, sigma_2). Note the y-comparability graph is complete multipartite (levels of equal y), so pairs are plentiful, and the choice is one of "pair partitions" realisable by two orders (not arbitrary 2-colourings): if sigma_1 reverses (t,s) and (s,r) then by transitivity it reverses (t,r).

Sanity: if one coordinate is frozen (infinite cost to move u^2), rho_dom is a pure isotonic problem under the induced partial order: polynomial (mine).

## 6. Question A: does BV say anything about optimising a convex perturbation?

Short answer: nothing directly; there is a structural analogue and a gap.
1. BV is purely about unit-cost deletion of data points. There is no perturbation of p or x. Verified: pp. 1–9, no weights, no continuous costs. Deletion = infinite perturbation in our setting (to make t harmless you need the point (-inf,+inf) in u, mine), so their problem is the "step cost" extreme of ours, never a finite-cost move.
2. Structural analogue (mine): for FIXED Q, the dominance-conflict graph H(Q): vertices t, edge iff y_t > y_s and q_t >> q_s (or reversed), is the comparability graph of the strict product order on (y,q^1,q^2), hence PERFECT for all d (comparability graphs are perfect; in fact poset dimension <= d+1). So "min number (or weight) of observations to delete so that dominance constraints hold" is polynomial for every d (weighted vertex cover = total weight minus max-weight antichain, Dilworth/flow). That is exactly BV's mechanism, moved to our setting, and it is much cheaper than their proof (no hole/antihole analysis). This also shows perfection is not what separates d=2 from d>=3 in OUR problem's dominance part; the d=2 vs d>=3 gap in our problem comes from the chain/pair-covering constraints beyond dominance (and, in BV, from WARP != GARP). (Unverified w.r.t. the claim that our full weak-solvability d=2 criterion is not pairwise; see your notes.)
3. Gap: BV's reduction is VC(G); our problem has continuous variables whose values interact between different conflicts (one move of u_t in coordinate 1 resolves conflicts with every s having u_s^1 >= new u_t^1). That is a "convex cost with thresholds," not a hitting set. No weighting/cost scale in BV lets you represent exp(|log q/p|)-1.

So BV supplies a poly algorithm for the DELETION degree (including a weighted version via GLS, unverified), not for rho.

## 7. Question B: reduction of rho_dom to convex min-cut on a perfect graph / min-cost 2-SAT with perfect structure?

What I tried (mine):
- Discretise u^i_t over a common grid; introduce threshold booleans x_{t,c} = [u_t^1 >= c], z_{t,d} = [u_t^2 >= d]. Cost of u_t^i is a convex separable function of the threshold chain: encodable as a standard chain with convex edge costs (min-cut / Ishikawa construction for convex unary costs). The forbidden pattern u_i << u_j (i y-below j) is "exists c,d with u_i^1 < c <= u_j^1 and u_i^2 < d <= u_j^2", i.e. a FOUR-literal clause (not x_{i,c}) and x_{j,c} and (not z_{i,d}) and z_{j,d}. So rho_dom is NOT a min-cost 2-SAT over the threshold variables; the "2-SAT" is only at the level of the two inequalities per pair (each inequality itself an ordered-domain constraint), i.e. a min-cost CSP over ordered domains with the relation "NOT(a_t > a_s AND b_t > b_s)".
- Submodularity check (mine): u_t^1 <= u_s^1 alone is L♮-convex (submodular, flow-dual), and the same for coordinate 2, but their OR is not submodular for any single choice of flipped variables (same reason vertex cover's clause x ∨ y is submodular only on bipartite instances after flipping). The H(Q) graph above is not bipartite in general (it is a general comparability graph, contains arbitrary cliques: a chain of points increasing in y and in u). Hence no min-cut-on-flipped-variables reduction for general instances. Min-cut would only apply if the "conflict graph" at the optimum can be 2-coloured in a way compatible with the order, which is exactly the content of the combinatorial choice. Unresolved.
- Perfect-graph-LP angle (mine): for deletion, perfection gives a clique-constrained LP (chains of the 3-dim poset) that is integral. For perturbation, cliques of H(Q) are chains t_1,...,t_k with y increasing and q increasing in both coords; the natural convex relaxation constraint would be "for each chain-clique of the potential conflict structure at least k-1... " but H depends on Q (decision variable), so the clique structure is variable. I found no way to fix the graph in advance. Open; this is the main place a genuinely new idea is needed.

## 8. Question C: literature (largely negative)

- Minimum weight / min-ones 2-SAT is NP-hard, generalises vertex cover; 2-approx (Gusfield–Pitt), Nemhauser–Trotter kernel extends (Hochbaum et al.); inapproximability of Min-2SAT-Deletion relates to VC (snippets from search results, unverified; sources: researchportal.port.ac.uk "On approximation hardness of the minimum 2SAT deletion problem"; imsc.res.in/~vraman/pub/mfcs-minones.pdf).
- Perfect-graph connection in 2-SAT literature: only found "claw-free perfect graphs: clique cover and stable set via 2-SAT, O(n^3)" (famnit.upr.si seminar abstract, snippet). Says that for general perfect graphs no combinatorial polynomial algorithm is known (only ellipsoid/GLS). This reverses the direction I need (2-SAT solves perfect-graph problems, not the converse).
- Convex cost over order/difference constraints (conjunctive): Hochbaum–Queyranne (SIAM J. Discrete Math 2003, convex cost closure), Ahuja–Hochbaum–Orlin (Management Sci. 2003; Algorithmica 2004), Hochbaum–Lu (SIAM J. Optim. 2017; isotonic median regression): solves exactly my Reformulation 3 subproblem for a fixed pair assignment. Snippets only, unverified in detail. No result I found treats DISJUNCTIONS of such constraints with a perfect-graph structure.
- Valued CSP dichotomy (Kolmogorov–Krokhin–Rolinek; Thapper–Zivny) classifies finite-domain VCSPs: tractable iff a suitable fractional polymorphism exists; my disjunction relation is not submodular/ L♮ and has no obvious tractable polymorphism, but I did not check; unverified, not read.
- BV follow-ups: Boodaghians' MSc thesis (McGill 2016) covers the same results plus "additively approximate rationality" (snippet; unverified, possibly relevant to a perturbation measure; I did not open it). Boodaghians 2018 "Revealed Preference Dimension via Matrix Sign Rank" (arXiv:1807.10878) characterises which digraphs arise in d-commodity markets (snippet; unverified).

Nothing found on "convex minimisation over disjunctive constraints with perfect-graph structure".

## 9. Honest verdict

Genuinely open, with the following leanings. It is not settled by BV or by anything I found.

What the evidence says (I mark what is derived by me):
1. For the DELETION analogue, rho_dom is polynomial for every d (comparability graph perfect; mine). So "perfect-graph-ness" of the dominance part carries no complexity information by itself.
2. For the perturbation cost rho_dom, the problem is "choose two weak orders (sigma_1, sigma_2) with every y-ordered pair reversed in at least one, minimise isotonic costs g_1(sigma_1)+g_2(sigma_2)". Given sigma_1 the optimal sigma_2 is any linear extension of a poset derived from sigma_1, with isotonic cost; discrete part has factorial search space. Fixing either coordinate makes it polynomial.
3. A version with box constraints (cost = indicator of an interval, i.e. feasibility: choose points z_t in rectangles B_t such that y is monotone decreasing along strict dominance) is in the same family as scheduling-with-release-dates / simultaneous-ordering problems that are often NP-hard; I could not prove hardness, and could not find a polynomial algorithm. The sequence structure (process points in y order, state = a staircase) has an exponential state.
4. Given exp-type convex costs and the specifically 2-dimensional order structure, neither a poly nor an NP-hardness result is implied by what I read. Weak lean: NP-hard in general if costs are arbitrary convex (box-like) functions; polynomial plausibility for the specific costs e^{|u-a|}-1 cannot be argued from BV.

Plan if polynomial is attempted (mine, speculative):
(a) Work with the Reformulation 2 (three orders, no common strict increase). Characterise optimal solutions: show an optimal (u^1,u^2) can be taken with a "staircase-compatible" structure: the Pareto-minimal chain of points of U_j relative to y-order; test whether the DP state can be reduced to O(T) (e.g. the staircase is determined by two pointers if points sorted by a_t^1 + a_t^2 ... ). Try small T numerically with the existing SCIP model (code/perturbation/) to see whether an optimal assignment is always "monotone" (i.e. i(t,s) depends only on a comparison of ranks) which would give a DP.
(b) Alternatively a Lagrangian/flow formulation: for each pair, a single selector variable; prove the selector matrix (pairs -> coordinate) has the consecutive-ones/ interval structure of a permutation graph so that the LP over pair selectors is integral; analogous to chain constraints of 3D poset.
(c) Check small-cases: enumerate all realisable pair-assignments for T <= 6 to see how many (vs 2^{C(T,2)}) and whether the cost-minimising one always has a special form.

Obstacles if NP-hardness looks right:
(i) A reduction must use the interplay (u_t^1 single move resolves many pairs) and the two-order realisability; vertex cover has no such sharing, so a natural source problem is a linear-ordering/betweenness-type or "3-dimensional poset recognition" (Yannakakis) problem rather than VC.
(ii) The cost e^{|u-a|}-1 is a fixed, specific convex function, so hardness must be proved for exp-cost (or near-step via scaling a_t spacing), not arbitrary convex costs; scaling of the p_t values gives steep costs, so box-like hardness may transfer.
(iii) The full rho adds chain/pair-blocking constraints; hardness of rho_dom only transfers if the extra constraints are inactive on the constructed instance, while polynomiality of rho_dom does not give polynomiality of rho.

Bottom line: BV and the 2-SAT/perfect-graph literature do not suggest polynomiality of rho at d = 2; they only give a polynomial algorithm for the cardinality-deletion variant (and our own comparability observation gives the same for dominance deletion at every d). rho at d=2 remains open on current evidence; there is mild structural support for a polynomial algorithm (one frozen coordinate gives isotonic regression; the remaining combinatorics lives in two permutations with a very rigid "no common increase" relation) and mild support for hardness (ordering-with-windows flavour). Next step I would recommend: brute-force small instances with SCIP to test whether the optimal pair assignment is rank-monotone, before trying either proof.

---------------------------------------------------------------------

## Reading log
- Read in full: arXiv:1507.07581v2 text, all 16 pages (all lemmas, proofs, theorems). Figures not viewed (text extraction only), so figure-dependent geometric steps (Lemma 3.1 base cases, Lemma 4.3 gadget drawings) are described from the text, not visually verified.
- Skimmed (search snippets only, unverified): Hochbaum et al. papers, 2-SAT literature, Boodaghians thesis/sign-rank paper.
- Mine (not from any source): everything in Sections 5, 6 items 2–3, 7, 9 (comparability observation, reformulations, submodularity argument, verdict). Not machine-checked; the comparability claim is easy to verify, the non-submodularity claim is by analogy with vertex cover (not rigorously proved).
