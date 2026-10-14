# Antiferromagnetic switch gadgets for full rho at d = 2 (numerical)

Scripts: scratchpad/gad/ (core.py = MILP rho_dom + exact polish + flow-LP weak-solvability check;
chain3.py, k22.py, k3root.py, enum_k3.py, pn.py, ctrl.py, k4.py). All numbers below are reproduced by these.

## Conventions
Points p_t = exp(0.2 * (integer grid point)), cost per coordinate e^{|log q/p|} - 1 (= max(q/p,p/q)-1).
y takes only two values: tops y = 2, bottoms y = 1 (so every pair-cover inequality y_t > y_r + y_s is impossible).
Conflicts = pairs (t,s) with y_t > y_s. sigma(t,s) in {0,1} = coordinate in which q_t <= q_s.

## Why rho = rho_dom here (the "full rho" requirement)
rho >= rho_dom always (dominance is necessary). Upper bound: take the rho_dom-optimal sigma, re-solve the convex program
with strict margin q_t <= q_s*(1-1e-7) on the chosen coordinate, and feed Q to planar.flow_lp (weak=True, exact rationals).
Result: weakly solvable = True for P3 and K3 gadgets (margins 1e-7, 1e-5, 1e-4; cost moves by <= margin).
So rho = rho_dom to within the margin. Negative controls: the gadget's original P (violated) and the triangle example
at its own P are reported NOT weakly solvable by the same checker. (Pair-cover obstructions are real in general but are
avoided by the two-level y; I did NOT prove rho = rho_dom for all instances of this family, only checked every
instance tested.)

## STEP 1. Switch (T = 2)
top (4,4), bottom (0,0) grid steps, y = (2,1). Gap delta = 0.8 in log in both coords.
sigma=0 cost 0.98365, sigma=1 cost 0.98365, formula 2(e^{delta/2}-1) = 0.98365. Both equal (checked). Optimal move is
split half/half between the two points (convexity), so a switch costs B1 = 0.98365.

## STEP 2. Antiferromagnetic coupler (T = 4, K_{2,2} of conflicts)
U = top (4,4), bottom (0,0); V = top (1,7), bottom (-3,3) (V is displaced by (-3,+3): NORTH-WEST of U, anti-diagonal).
y = (2,1,2,1). Table of min cost with the two designated conflicts' sigma fixed (other two cross conflicts free):
  (0,0) 2.17764   (0,1) 1.96730   (1,0) 1.96730   (1,1) 2.17764
Off-diagonal = 2 * B1 = 1.96730 (couplings satisfied, no extra cost), diagonal = +J, J = 0.21034. Symmetric.
Mechanism: cross conflicts (tU,sV) and (tV,sU) have small gap (1 step) in ONE coordinate and large (7) in the other.
Different sigma: each switch's own move also closes the small gap of the cross conflict for free. Same sigma: one cross
conflict is left to be resolved in its small coordinate, extra cost J.
Sign rule seen in an exhaustive offset scan (k22.py): offset (ox,oy) with ox*oy<0 and |Delta|_inf < d -> antiferro;
ox=oy (diagonal) -> ferro (T(00)=T(11) < T(01)=T(10), strength up to 1.40 for offset (-5,-5)).

## STEP 3/4a. Path P_n: exact Ising antiferromagnet
Switches at (-3i, +3i), i=0..n-1, gap d=4 (tops (c+4,c+4), bottoms c), all tops y=2, bottoms y=1.
Only consecutive switches interact (|Delta|_inf = 6 > d for next neighbours). Exact fit (all 2^n tables):
  T(sigma) = n*B1 + J * #{i : sigma_i = sigma_{i+1}},  J = 0.21034, max fit error < 3e-13 for n = 3,4,5,6.
Exact enumeration of all 2^9 sigma on P3 confirms: rho(P3) = 2.95095 = 3*B1 (all couplings satisfied, sigma alternating),
patterns 000/111 = 3.37163, one agreement = 3.16129.

## STEP 4b. Triangle K3: exact NAE table
Switches at (0,0),(-4,4),(-8,8), d tuned by bisection to d* = 11.1664276 (so that the three "one-agreement" classes
coincide). Exact enumeration of all 2^9 sigma (not only MILP):
  000, 111 : 15.41316        all six non-constant patterns : 13.56360 (spread 3e-6)
  rho(K3 gadget) = 13.5636 (rho_dom, global min); Delta = 15.41316 - 13.56360 = 1.8496.
Non-constant = cut value 2 of the 3 edges, constant = cut 0. Margin-1e-7 Q has cost 13.5636 and is weakly solvable.
So the K3 gadget realises  rho = E0 + (Delta/2)(2 - cut(sigma)) , maxcut(K3)=2 recovered, as opposed to the
bipartite chain where rho = B (no frustration, J*#agree = 0 attainable). Caveat: the K3 energy is NOT pairwise
(three-body term: with the next-nearest switch interacting, E depends on the pattern as base + pair terms + K*[all equal]);
what is verified is only the NAE-type table, which is what a K3 / NAE-clause needs.

## STEP 5. What is and is not established
Established numerically (exact enumeration / exact linear fit, full weak solvability checked):
 - switch with equal-cost sigma in {0,1};
 - antiferro coupler with symmetric 2x2 table and clean J (J = 0.21034 vs B1 = 0.98365, ratio 0.21);
 - arbitrary-length antiferro PATH as an exact Ising chain (rho = n*B1 + J*(n-1-cut)); polynomial size trivially;
 - a K3 gadget with exact NAE table (needs one real-valued tuning parameter d*).
NOT established, so NO NP-hardness proof:
 1. Coupling graph is geometric. Two switches interact only if |Delta|_inf < d (or via long-range comparable pairs
    with equal y-levels). Antiferro needs the anti-diagonal (NW/SE) relation, ferro the diagonal. Pairs of switches
    that are comparable in the product order and have close y-levels also interact at ANY distance unless y-levels
    separate them (y of the SW group above y of the NE group). So the family realises chains, odd cycles inside a
    mutually-interacting anti-chain cluster, and degree-4 stars (2 antiferro + 2 ferro neighbours at (+-3,-+3), (+-5,+-5))
    in the plane.  Planar Ising / planar MAX-CUT is polynomial, so hardness needs a CROSSING gadget (or non-planar
    many-body terms). I did not find one. Obstruction: crossing wires put switches of both wires within |Delta|_inf<d
    of each other; comparable close switches interact whichever way y is ordered (checked by hand: tU NE of sV violated if
    y_U > y_V, tV NE of sU violated otherwise). Candidate fix not yet tested: separate wires by y-levels
    (y decreasing along NE) with spacing >= d between comparable switches, and put the crossing in an anti-chain
    region where only one wire is anti-diagonal; or use the three-body term (K [all equal]) as a clause gadget (NAE-3SAT,
    which has no planarity obstruction when variables are copied by ferro wires -- wire crossing is still needed).
 2. K4/K5 not realised: in the 1-parameter anti-diagonal chain family with all pairs interacting, T is not symmetric in
    permutations (k4.py: for n=4,5 the same number of ones gives spread 1-6 in cost), so equal pair strengths
    need extra freedom (2-D offsets, y-levels). Not searched.
 3. rho = rho_dom was verified instance by instance only.

## Reduction statement (conditional)
IF an embedding of a graph G (all degrees <= 4) into such switches with every edge antiferro of equal strength J and
no spurious interactions exists with polynomially many points and polynomial bit-size coordinates, THEN
rho(P_G, y) = |V|*B1 + J*(|E| - maxcut(G)) and MAX-CUT is recovered; size O(|V|+|E|) points. Verified instance
classes: paths (all n <= 6) and the triangle (NAE). The conditional embedding for non-planar G is the open step.
