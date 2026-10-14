# PERT-2 (full rho at d = 2): status after one working session

Outcome: NO reduction found, NO polynomial algorithm found. Below: (A) structural facts
(proved or numerically checked), (B) what exactly breaks in each hardness attempt,
(C) a judgement. Scripts: scratchpad/probe1.py, probe2.py, probe3.py, milp_dom.py.

## A. Structure (new reformulations)

A1 (blockers have size <= 2). For t in S, S is weakly reachable at t iff no convex
combination of points of S^c is strictly below q_t in both coordinates (Gordan/Motzkin on the
witness xi >= 0, xi != 0). The open quadrant {z < q_t} is convex and unbounded, so if conv(R)
meets it, then some single point or some segment [q_r,q_s], r,s in R, meets it (boundary of
conv(R) would otherwise miss a convex unbounded set that is not contained in a bounded polygon).
So: S weakly reachable  <=>  for every t in S every "blocker" B (|B| <= 2: single s with
q_s < q_t, or pair with [q_r,q_s] meeting {z < q_t}) intersects S.
Equivalently: S^c = P cap K for a convex up-set K (K = conv(S^c) + R^2_+), weak case =
interior excluded. Reachable sets are closed under union; NOT under intersection.

A2 (necessary pairwise conditions, almost sufficient). Necessary for weak solvability:
y_t <= sum_{s in B} y_s for every blocker B of t. Checked against the exact cone LP (all valid
sets, T = 4..7, 3000 random instances): 2 mismatches (condition holds, y not in cone), e.g.
T=6, Q=[[.7322,.8594],[.6566,.0667],[.3426,.4128],[.7121,.4390],[.2449,.3463],[.0945,.4330]],
y=(0,3,4,2,5,3). So the true condition is the flow LP, not pairwise sums.

A3 (two-valued y is a single convex set). If y in {a on H, b on L}, a > 2b > 0, then y is weakly
solvable iff H avoids int(conv(L)+R^2_+). So the 2-class full problem is
  min over convex up-sets K of  sum_{l not in K} dist(l,K) + sum_{h in int K} dist(h, R^2 \ int K),
with dist = the separable cost pi. For a fixed K every point is independent; heavy h has a
private witness angle xi_h (one real parameter), lights are shared. This is a bilinear
(angle x position) program with ONE scalar nonconvex parameter per heavy point.

A4 (rho_dom as 3D antichain). rho_dom(P,y) = min pi-cost to move the first two coordinates so that
{(q_t^1,q_t^2,y_t)} has no pair strictly dominated in all three coordinates. The conflict
graph (pairs on which x-order, y-order, y-level order agree) is the comparability graph of a
poset of dimension <= 3, hence perfect.

A5 (rho_dom as nested staircases). Level sets of y give nested decreasing staircases
C_1 >= C_2 >= ... (C_k separates levels <=k from >k). Point of level j pays
dist(p, C_{j-1}) if above it, dist(p, C_j) if below it (only one can be active), so
rho_dom = min over nested chains sum_j f_j(C_j), f_j involving only levels j, j+1.
Each f_j is a sum of "distance to a set" terms, hence SUPERmodular on the lattice of
down-sets. Dropping nesting gives a lower bound LB = sum_j rho_dom(levels j,j+1 only).
Numerically LB < rho_dom strictly in 5/6 random 3-level instances (probe3.py,
sizes [2,2,2]: e.g. 0.9566 vs 0.8991, 3.653 vs 1.615), so nesting genuinely couples levels
(uncrossing argument fails because adjacent-level terms have opposite monotonicity).

A6 (sigma-cost function F is neither sub- nor supermodular). F(sigma) = g_x(E_x)+g_y(E_y),
sigma in {0,1}^{conflicts}; random T=4 instances, 4000 random pairs each: about 25-50%
of tested pairs violate submodularity, 3-8% violate supermodularity (probe2.py). The earlier
"supermodular, hence hard" heuristic is not valid as stated (sharing a point is
submodular: lowering t below two lights costs max, not sum).

## B. Where the hardness attempts break

B1 Vertex-cover style (pair (u,v) "covered" by moving u or v). With a single pair-cover or
orientation constraint per edge the constraint is LINEAR in displacements
((1-lam)Delta_u + lam Delta_v >= h_e), so the problem is the LP relaxation of fractional
vertex cover (half-integral, polynomial). Integrality needs a genuine disjunction. The only
disjunctions available are x-vs-y per conflict (dominance) and the choice of chord/witness
angle. Also: for one heavy t the blocker graph H_t is BIPARTITE (upper-left vs lower-right
points), whose cover polytope is integral, so one-t covering is pairwise sums y_u+y_w >= y_t.

B2 Antiferromagnetic coupler via x/y states (the most promising one). Variable v with a frozen
anchor (weight K copies) at gap (1,1): v must move by 1 in x (state X) or in y (state Y), equal
cost. Edge (j high, i low) at exact offset (1,1): satisfied iff S_j not subset of S_i, where
S_v subset of {x,y} is the set of coordinates v moved in. Then 2-states X,Y give a proper
2-coloring coupler (monochromatic edge costs extra), but:
 (i) a vertex can also take state XY (cost 2) and satisfies ALL edges where it is the high
     endpoint, so edge penalties are not additive: the core problem is "min |Z| such that
     G - Z is 2-colourable, Z only vertices with no higher neighbour, Z independent",
     not Max-Cut.
 (ii) The conflict graph is perfect (A4). A perfect graph minus Z is bipartite iff triangle-free,
     so the idealized model collapses to Greene-Kleitman (max 2-family of a poset), a
     min-cost-flow problem: polynomial. Odd cycles of length >= 5 never occur.
 (iii) Geometry: all pairs of variable points must be robustly non-conflicting (far in some
     coordinate) unless an edge. With a scale hierarchy this forces the near-graph in each
     coordinate to be interval-like (earlier neighbours form a contiguous block ending at j-1);
     the embeddable graphs are intersections of two such, a very restricted class.
 (iv) Numerically (milp_dom.py, L1 log cost, SCIP with big-M disjunctions) the naive gadget
     has unwanted cross conflicts: v_j (higher level) is NE of anchor a_i for i != j, so
     rho of the 2-vertex edge gadget is 3, not 2. Anchors cannot be made conflict-free with
     all other variables without destroying the offsets.
B3 NAE/ferromagnetism. Already in attempts/03-04: chain triples are ferromagnetic; shared
point (star) is submodular (max, not sum); the only supermodular source is the strict convexity
of pi (second order). I confirm these.
B4 Subset-sum / numbers. y enters only through the flow LP (convex), so numbers cannot
encode subset-sum unless they select combinatorial structure; the pairwise-sum selection
y_t > y_r+y_s defines a family of forbidden triples, but fixing one triple is a single
linear covering inequality (B1).
B5 Planar/graph gadgets. Unit-offset local gadgets give planar-like conflict graphs (Max-Cut
polynomial on planar).

## C. Judgement

I could not decide the complexity. Evidence for POLYNOMIAL (ordered by strength):
 1. conflict graph is perfect / 3-dim poset comparability graph, and the idealized unit-gap
    model equals Greene-Kleitman (flow);
 2. fixed-coordinate-assignment is convex; the only nonconvexity is one binary per conflict in
    rho_dom and one real angle per heavy point in rho;
 3. the 2-class problem is a single convex-set / staircase fit, plausibly solvable by DP over
    chains with local (Voronoi-cell) point costs (not written);
 4. all attempted couplers are ferromagnetic or collapse to perfect-graph problems.
Evidence for HARD: nesting couples the f_j (A5, LB gap), F is neither sub- nor supermodular
(A6), and the angle variables make the full problem a bilinear program (A3).
Most useful next experiment: test whether rho_dom (L1 regime) equals the value of a convex-cost
flow / Greene-Kleitman type dual; if yes, rho_dom is polynomial and the problem moves to the
single real angle per heavy point in the full rho.
The triangle example (rho_dom = 0, rho = 2/5) is the only structural difference found between
rho and rho_dom; it is the "chord" constraint (linear covering, B1), not an extra source of
disjunction. I do not see how it adds hardness.
