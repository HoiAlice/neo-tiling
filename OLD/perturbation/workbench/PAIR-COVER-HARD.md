# Pair-cover angle nonconvexity at d=2: no hardness found (verdict: leaning polynomial for the angle part)

Scripts: scratchpad/pc/{a2,land,e1,e3..e8}.py (run with /Users/olegoleg/Code/neo-tiling/.venv/bin/python).

## 0. Tool
pc/a2.py: global SCIP model of rho using the blocker characterisation (A1/A2 of HARD-RHO-D2): for every t and every pair {r,s}
(r=s allowed) with y_r+y_s<y_t, a separate angle xi_{t,r,s} with xi.(q_r-q_t)>=0 and xi.(q_s-q_t)>=0. For two-valued y this is exact
(A3). Validated against rho_exact.py (family enumeration): triangle 0.4 = 0.4; shared-light 5-point instance 0.4198352 = 0.4198352.

## 1. Numerical findings (exact rho, SCIP)
- Single triangle, y=(3,7,3): rho = 0.4; fixed-angle cost landscape lambda -> cost is UNIMODAL (1.46,1.35,1.21,0.81,0.50,0.40,0.50,...).
  Reason: for one heavy, the two light endpoints have deficits 2-3a and 3a-1 in the angle a; both costs are convex in a, so the angle
  settles at a balanced interior point, never at an "either endpoint" extreme. Angle is NOT binary.
- Two triangles far apart (anti-diagonal scaling): rho = 0.8000 = 2 x 0.4. Independent gadgets add up (so scale separation works).
  (Shifting the 2nd triangle NE creates cross pair-covers 5 > 1+3; must separate anti-diagonally.)
- Two heavies sharing a light (P=[[6,1],[3,3.2],[1,6],[4.8,2.9],[2.1,4.9]], y=(3,3,3,7,7)): rho = 0.41984.
  Individually 0.37222 (one heavy). Sum 0.744 vs joint 0.420: strongly SUBADDITIVE. The shared light L2 is raised 3.2 -> 3.909.
- Chain of 4 lights + 3 heavies over the 3 faces (pc/e8.py): individual 0.2294, 0.0967, 0.1528 (sum 0.479); pairs h1,h2: 0.3015
  (sum 0.326); all three 0.4509. Resolution of one heavy depends on the others only through how much the shared light is lifted
  (L2 up by 0.38 in the pair solution, partly L2/L3 in the triple). Dependence is monotone: lifting a light never hurts any other heavy.
- Angle landscape of ONE heavy against 3-6 lights (random, pc/e4.py): 23/300 random instances have two local minima in the angle
  (different faces of the lower-left convex chain of the lights), gaps up to 1.0 in cost. So the angle IS multimodal ("face choice"),
  but the modes are faces of one convex chain.
- Coupling sign test (pc/e5.py): two heavies each with 2 angle modes; F(a,b)=min cost with heavy1 in class a, heavy2 in class b
  (classes = angle ranges split at the barrier). d = F00+F11-F01-F10: 27 of 28 bimodal-bimodal instances have d<0 (ferromagnetic:
  same-face choices favoured, sharing a face means sharing the lift). One instance has d=+0.012..+0.024 (weak antiferro), but class
  boundaries are arbitrary there and F(0,0)=F(0,1), so I do not count it as a controllable frustrated coupler.

## 2. Why the angle alone should not give hardness (structure, partly proved)
(a) Monotonicity. If lights move into K = conv(lights)+R^2_+ then K only shrinks; heavy moves affect nobody. So any move of a light
    helps every heavy weakly. All couplings through shared lights are benefit-sharing => submodular/ferro. No source of
    antiferromagnetic interaction (needed for NAE/Max-Cut gadgets).
(b) Two-class form: rho = min over convex up-sets K' of sum_l dist(l,K') + sum_h dist(h, K'^c) (A3). Given the lights' final positions every
    heavy chooses independently its nearest exit face: sum_h min_f e_{h,f}(D), a k-median-like assignment, but the "centres" are the faces
    of ONE convex monotone chain (a PATH of faces sharing vertices). Faces form a path, vertices carry 2-D displacements: a DP over the
    chain (like Eppstein et al. optimal convex separation, O(n^3) for counts) is the natural polynomial algorithm. Not written.
(c) Per triple (t;r,s) the constraint is AND over the two endpoints with a common angle: "t moves, or r AND s move (consistently)".
    It is (t v r)(t v s): vertex-cover style on a graph, but with continuous partial moves allowed and increase-moves costing linearly
    (pi = q/p-1), so it is the fractional (LP) relaxation, which is a legitimate geometric solution. Integrality (needed for hardness)
    is never forced because mixed solutions are feasible and cost at most the same. Pure x or y choice only arises for single blockers
    (r=s), where xi collapses to {0,1}: that is the dominance disjunction of rho_dom, not a pair-cover feature.
(d) For a fixed xi vector the problem is convex; there is exactly one real xi per blocker triple. Both numerical probes (unimodal single
    triangle, ferro-only coupling) agree with "this nonconvexity is mild".
(e) With y multi-level the blocker pairs are the pairs with y_r+y_s<y_t (a threshold-type relation, nested in t); this gives different
    angles for different pairs of the same heavy, still covering constraints with the same monotone structure. Complex combinatorics
    could live here (nested chains, A5), but that is the rho_dom-type nesting, not the angle.

## 3. How each candidate reduction fails
(1) Angle-switching gadget (binary lambda): fails, lambda* is the interior balance point of two convex costs; switching to the ends is
    always dominated by the mixed solution (triangle landscape). To force binary behaviour one needs a concave cost; pi is convex/linear.
(2) NAE-3SAT via angles: needs antiferro couplers; shared-light coupling is ferro (27/28 samples, plus monotonicity argument (a)).
    Variables with a 2-mode angle exist (face choice), but a clause = 3 heavies pairwise coupled ferromagnetically cannot encode NAE.
(3) MAX-3-SAT via chained pair covers: chains only share lifts; sharing is sub-additive (0.744 -> 0.420, 0.479 -> 0.451),
    which is the wrong sign for a gap-producing gadget (everything "wants to agree"); the face graph is a path.
Reduction attempts therefore collapse to (i) fractional covering LPs, or (ii) path-structured (convex chain) DP, or (iii) the rho_dom
nesting problem that was already open.

## 4. Verdict
The angle variables alone do not look sufficient for NP-hardness: single-angle landscape unimodal, multimodality only as face choice on a
convex chain (path structure), interactions monotone/ferro, gadgets additive when scale-separated. I do not have a proof of polynomiality
(no DP written; multi-level y may still hide a nested-chain problem). If rho is NP-hard at d=2, the hardness has to come from the
dominance-type x/y disjunction with multi-level nesting (rho_dom, 3-D antichain / nested staircases), not from pair covers.
Confidence: about 65 percent that the pair-cover part is poly-friendly; the overall problem remains open.
