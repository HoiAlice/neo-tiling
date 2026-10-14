# POLY-ALGO: result = NO polynomial algorithm found (inconclusive, not a hardness proof)

Code: scratchpad/polyalgo/{lib.py,t1.py,t3.py,t4.py,t2.py,t2.out}. Note: iso_scipy.py does not exist in scratchpad
(it is in perturbation/experiments); I used a big-M MILP (HiGHS) as the exact brute force instead.

## What was verified
1. Staircase/assignment formulation of rho_dom (L1 cost in log coords, grid = original coordinate values) is EXACT:
   K levels, K-1 down-sets w^k on the grid (monotone), each point assigned one cell; level-j point needs
   w^k_c=1 (k<j) and w^k_{c+(1,1)}=0 (k>=j). No nesting constraint is needed (pair constraints are exactly these thresholds).
   Agrees with exact big-M MILP brute force: K=2,3 (T=4..7) 70/70 instances; K=2,3,4 (T=7..10) 30/30. (t1.py, t4.py)
2. But its LP relaxation is NOT tight: LP != ILP on 42/70 random instances (t1.py). Smallest gap example (T=3, L1):
   U=[[3,2],[4,0],[1,0]], levels [2,2,1]: ILP = brute = 2, LP = 1.5. So "LP = poly algorithm" fails for this
   formulation (assignment a<=w, a+w'<=1). A different/stronger LP is not excluded.
3. Why a DP over staircases does not directly work: cost of a point is the (grid-recurrence) distance to the staircase,
   D(i,j)=0 on W else min(D(i-1,j)+dx, D(i,j-1)+dy). It is nonlocal along the path (needs the whole column of D, or range-max
   over path vertices); corner (XY) moves are essential (W = a rectangle, p NE of its corner), so "X-only/Y-only" local costs
   are wrong. Facility-location on a path with 2D clients: no monotone assignment order found. So I did NOT get an
   O(T^3) DP for K=2; nothing claimed. Same obstruction as A5 in HARD-RHO-D2 (supermodular dist-to-set).
4. Pair-cover layer (task 2): 14 random T=3 instances (t2.out), rho_exact (SCIP families) vs rho_dom (SCIP, same cost
   max(q/p,p/q)-1): diff = 0 in all 14 (pair cover inactive on random instances). Only known active case remains the triangle
   P=[[4,1],[3,3],[1,4]], y=[1,5,3]: rho_dom=0, rho=0.4. The claim "rho_full-rho_dom = LP of pair-cover penalties" was NOT
   tested in a meaningful way (no instance with active pair cover except the triangle; no LP candidate defined). T=4 runs
   of rho_exact took >10 min each batch, abandoned.
5. Tasks 3 (poly algorithm, 50 instances to T=15) not done: no algorithm to verify.

## Usable tools produced
- lib.brute_L1(U,lev): exact rho_dom (L1) by MILP, fast to T~10.
- lib.grid_model(U,lev,costfun=, relax=): exact ILP for rho_dom on grid (polynomial size T^3 vars); with a convex costfun on a
  refined grid it approximates the true cost (not validated against rho_exact).
Open leads: (a) find a stronger/extended LP for this ILP and test integrality (any integral one => poly); (b) true-cost
pooling means grid exactness only holds in L1; (c) test K=2 DP using rotated coords xi=x-y, eta=x+y (staircase = 1-Lipschitz
graph eta=phi(xi); L1 dist to path = min_r box meets graph) - promising but unfinished.

## Addendum: rotated-coordinate (xi=x-y, eta=x+y) lead -- RESULT: NO algorithm
Code: polyalgo/rot.py, rot3.py, rot4.py.
- Verified: L1 in (x,y) = Linf in (xi,eta) exactly (|a|+|b| = max(|a+b|,|a-b|), no sqrt2); staircase = 1-Lipschitz graph eta=phi(xi).
- Lipschitz feasibility (Kirszbraun) for moved points: exists phi with eta'_h<=phi(xi'_h), eta'_l>=phi(xi'_l) iff for all H-L pairs
  eta'_h-eta'_l <= |xi'_h-xi'_l|. The cost max(|dxi|,|deta|) is convex, but the constraint has |.| on the right (reverse-convex): it is the
  same disjunction x-or-y as before. Given the xi'-ORDER of H-L pairs it is an LP. Not a single LP; the combinatorial object is the order.
- Test A (rot.py): LP with cross-pair signs fixed by the ORIGINAL xi order: upper bound only, strictly above brute force on 22/68 random
  instances (K=2,3, T<=10, gaps up to 2.75). Smallest: L=(0,0),(0,1), H=(1,2): brute 1 (move H to x=0, which flips xi order), LP 2.
- Test B (rot3.py): keep xi-order within H and within L (so only the interleaving of two sorted sequences, an O(T^2)-state lattice path, is
  free), LP per interleaving, min over all C(T,nH) interleavings: still != brute on 3/55 (T=7: brute 0.7211, interleaving 0.9527).
  Min over ALL T! total orders of xi' recovers brute 0.7211 (consistent, so the formulation is right; the order is what matters).
  So even the DP-friendly structure (class-wise sorted order, lattice-path DP) is false in general.
- Conclusion: rotation does not give a polynomial algorithm; it re-derives R2 (sigma-enumeration). Not a hardness proof either.
- Pair-cover T=4: rho_exact on triangle+4th point exceeded 10 min per instance (family enumeration); not obtained. Triangle alone: dom=0, full=0.4 reproduced.
