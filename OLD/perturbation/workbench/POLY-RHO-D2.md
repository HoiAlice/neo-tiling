# rho at d = 2: polynomial algorithm attempt (no algorithm found; verdict: lean NP-hard)

Status: no polynomial algorithm found, no hardness proof either. Everything below is either a proved
reformulation (marked PROVED), a numerical observation (marked NUM, scripts in scratchpad/d2/), or
heuristic (marked HEUR).

## 1. Clean reformulations of rho_dom (PROVED, elementary)

Let y_1 > ... > y_T (distinct; ties only delete pairs), L = this total order.

(R1) 3D antichain / errors-in-variables isotonic regression.
Q is dominance-feasible iff y is a non-increasing function of Q for the strict dominance order, i.e. the
3D points (q^1_t, q^2_t, -y_t) form a strict antichain. So rho_dom = "isotonic regression where the
COVARIATES are noisy": move the design points p_t to q_t (cost sum f(log-shift)) so that the fixed
responses y_t become a monotone (non-increasing) function of the design. Equivalent to a nested family of
monotone staircases gamma_1 >= gamma_2 >= ... (one per y-level) with point t forced into the band between
gamma_{k-1} and gamma_k (k = rank of y_t); cost of t = distance to its band.

(R2) Two-order form. rho_dom = min over pairs of linear (pre)orders (pi, sigma) such that every L-pair
(i above j in y) satisfies i <=_pi j or i <=_sigma j, of Iso_1(pi) + Iso_2(sigma), where Iso_i is the
isotonic-regression cost of the coordinate-i log values along the order. Equivalently min over
2-colourings sigma of the c conflicts (all pairs with y_t > y_s, not only P-comparable ones) of
F(sigma) = IsoCost_1(edges coloured 1) + IsoCost_2(edges coloured 2). Each F(sigma) is a convex program
(isotonic regression on a DAG). This is exactly what perturbation/experiments/fast_d2.py enumerates.

(R3) Sequential form. Process points by decreasing y. Point k+1 may not lie in the open SW quadrant of any
earlier placed point, so the future depends on the placed set only through its Pareto frontier (an
antichain = a monotone staircase). DP state = frontier; number of frontiers is 2^{Theta(T)} on a T x T grid
(even in the L1/grid regime where optimal coordinates can be taken from the original coordinate values).

## 2. Why each candidate stalls

(i) DP by y-rank. State = staircase, exponential. The three coordinates (x, y, -L) are symmetric in (R1), so
sweeping by x or by v instead gives the same obstruction (state = monotone profile over the other two).
HEUR Myhill-Nerode: take m independent "switch" pairs (a conflict that can be resolved in x or in y at equal
cost) in the prefix; the frontier after the prefix records the bit string s in {0,1}^m; a suffix of m probe
points, probe j costing delta iff s_j = 1, separates all 2^m frontiers with equal prefix cost. So no
compression of the frontier is possible by an equivalence of futures; any polynomial algorithm must not be
a left-to-right DP on frontier states. (Not a lower bound for all algorithms.)

(ii) Parametrise Q + chain LP. Chain LP at fixed Q is a flow LP; the dependence on Q enters through
chi(a,b,c) signs (which chains exist) so the feasible set in Q is a union of exponentially many semialgebraic
cells. At the dominance level it is the union of the 2^c convex pieces of (R2). No single convex program.

(iv) Convex relaxation / min-cut over sigma. NUM: F(sigma) is NOT submodular and NOT supermodular.
Script d2/submod.py: random T = 5 instances with 3..9 conflicts, 2nd differences
F(1,0)+F(0,1)-F(0,0)-F(1,1) in all contexts of the other conflicts: about 20 percent of the 5100 tested
(pair, context) combinations are negative (antiferromagnetic), the rest nonnegative (ferromagnetic), e.g.
magnitudes up to -0.84. Ferro couplings come from shared max-structure (a common top lowered below two
incomparable bottoms costs max, not sum). Antiferro couplings come from chain pooling (pooling a 3-chain is
superadditive). Both signs present means the "colour the conflicts" problem is a genuine Ising-type problem
with frustration, not a min-cut. (Collinear 3-chain d2/chain3.py gives purely ferro pattern: F(000)=F(111)=1.5
cheapest, mixed 2.3..2.96; so the sign depends on geometry, as needed for a gadget.)
Also, the continuous relaxation "relax the disjunction min(Delta_u^+, Delta_v^+) = 0 to a convex
inequality" is not tight: the triangle (rho_dom = 0, rho = 2/5) shows even the dominance level misses the
pair-cover layer, and for the dominance layer the minimum of a supermodular-type "distance to nearest chosen
cell" (facility location structure, D -> min_{c in D} d(p,c) on the lattice of down-sets) is a
cost-minimising supermodular function, which is NP-hard in general.

(v) Known polynomial problems. Poly cases I could prove or reduce:
  - one coordinate frozen: ordinary DAG isotonic regression (poly);
  - deletion version (remove points instead of moving): Boodaghians-Vetta, perfect-graph structure, poly,
    but see BV-TECHNIQUE.md: does not transfer to perturbation;
  - zero cost: always feasible (q^2 := reversed y order), so the question is only about cost;
  - fixed Q: weak solvability poly by the flow LP (known).
  I found no reduction of rho to min-cost flow / isotonic regression: the disjunction "x or y" per conflict
  is the obstruction, and (R2) shows rho_dom is a disjunctive isotonic regression.

## 3. Structure that may matter for hardness (not duplicating HARD-RHO-D2)

- Gadget alphabet: "switch" = isolated conflict pair with equal gaps in x and y (binary choice, symmetric);
  ferro wire = two bottoms under one top (shared max); antiferro = chain pooling. These give an Ising-type
  system with both signs on a 3D-dominance conflict graph; frustration is available. What is missing for a
  proof is isolation of gadgets (geometric scale separation) and a controllable coupling graph.
- Full rho vs rho_dom: a reduction must produce instances with rho = rho_dom (e.g. y within a narrow band so
  that no pair-cover obstruction y_t > y_r + y_s can occur, but note near-constant y does not trivialise the
  cone: y - c*1 must itself be handled). Pair-cover layer adds genuinely new geometry (triangle).

## 4. Verdict

Lean NP-hard (about 75 percent), genuinely open as far as I can prove. Reasons: (1) the problem is a
disjunctive isotonic regression = errors-in-variables isotonic regression on a 3D antichain structure;
(2) the per-conflict binary choice has couplings of both signs (NUM), so frustrated Ising instances can
be embedded locally; (3) every natural DP has a staircase/profile state of exponential size and the
Myhill-Nerode style argument shows no compression of that state; (4) the polynomial results that do exist
(fixed Q flow LP, BV deletion on perfect graphs) rely on discrete structure (perfection, convex-chain
DAG) that is destroyed once Q is a free continuous variable with convex cost. The most promising hardness
route: max-cut / NAE-3SAT with scale-separated switch gadgets (see REDUCTION-SOURCES.md section 3), proving
first rho_dom hard, then padding y to force rho = rho_dom.
Not found: any candidate polynomial algorithm, so none was tested on the 5 instances / triangle
(triangle rho = 2/5 is reproduced by scratchpad/rho_exact.py; rho_dom = 0 there).
