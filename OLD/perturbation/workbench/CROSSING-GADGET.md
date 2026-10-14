# Wire crossing gadget for full rho at d = 2 (found, numerically verified)

Scripts: scratchpad/gad/{cx2,cx3,term,yv,yv2,final,neg,wk*.py}; outputs scratchpad/gad/final_4_5.out, neg.out.
Run with /Users/olegoleg/Code/neo-tiling/.venv/bin/python. Conventions as in GADGET-D2.md
(points exp(0.2 * grid), cost e^{|log q/p|} - 1, a switch = box [b, b+d]^2 with top (b+d,b+d) above bottom b).

## 0. Verdict
A crossing exists. Antiferro wire U (anti-diagonal) crosses a ferro wire V (diagonal) with
 - exact degeneracy of all 4 (U bit, V bit) ground states (spread 0.00000, MILP-exact to ~1e-5),
 - every violation of "U_out = NOT U_in" or "V_out = V_in" costs >= 0.0902,
 - all 4 ground states are WEAKLY SOLVABLE at the margin-1e-6 optimum (flow LP, exact rationals), so rho = rho_dom there.
It is not a cancellation by tuning. It is exact by symmetry (section 2). Two further facts are needed and are new:
the numeric y-levels (not only their order) must be asymmetric (section 3), and "planar coupling graph" is avoided
because only ONE crossing type (U x V) is needed (section 5).

## 1. Why the naive approaches fail (obstruction analysis)
* Boxes. Two switches interact iff their boxes [b, b+d]^2 overlap (equivalently: some top is NE of some other bottom while
  the y-order says violated; with y decreasing along NE and boxes disjoint there is a consistent y with NO violation).
  A wire is a chain of overlapping boxes, so two crossing wires always contain overlapping boxes. Pure "separate by y-levels"
  (approach C) cannot decouple crossing wires: overlapping boxes force a cross conflict for EVERY y-order (the cycle
  t_S' >= b_S, t_S >= b_S' ). So decoupling must come from cancellation, not from separation.
* Two antiferro wires of different negative slopes (Barahona style) still overlap at the crossing; no symmetry kills them.
* Detuned crossing (control). Same gadget with the V wire shifted by delta along the diagonal (neg.py):
  delta = 0 : the 4 ground energies 10.55230 x4 (spread 0)
  delta = 0.25 : 10.58197, 10.58197, 10.55163, 10.55163 (spread 0.0303)
  delta = 0.5 : 10.61821, 10.61821, 10.56278, 10.56278 (spread 0.0554)
  i.e. an uncancelled crossing acts as a FIELD on the U-bit (0.03-0.055, same size as a designated coupler J_e).

## 2. The gadget and why it decouples (exact symmetry)
Place everything symmetric about the point C = (2,2) (grid units):
 U (antiferro, anti-diagonal, step a = 3, box size 4, nU switches, EVEN count): bottoms
   b_t = (3t, -3t) for t = -(nU-1)/2, ..., (nU-1)/2 (half-integers), y-levels (top, bottom) = (1+g, 1).
 V (ferro, diagonal, step k = 1, box size dv = 5, nV switches, odd count), centred switch at C:
   bottoms (s - 0.5, s - 0.5) + ... precisely bottom = (k s - dv/2 + 2) in both coordinates, s = -(nV-1)/2..(nV-1)/2,
   levels (1+g+shift(s), 1+shift(s)),  shift(s) = -h0 s (s<0), -h2 s (s>0).
 Parameters used: g = 0.05, h0 = g, h2 = 0.2 (see section 3).
Explicit 4x5 instance (bx, by, d, ytop, ybot):
  U: (-4.5,4.5,4,1.05,1.0) (-1.5,1.5,4,1.05,1.0) (1.5,-1.5,4,1.05,1.0) (4.5,-4.5,4,1.05,1.0)
  V: (-2.5,-2.5,5,1.15,1.1) (-1.5,-1.5,5,1.10,1.05) (-0.5,-0.5,5,1.05,1.00) (0.5,0.5,5,0.85,0.80) (1.5,1.5,5,0.65,0.60)
Symmetries of rho_dom (it only uses the y-ORDER): R = swap x<->y (fixes the diagonal pointwise, maps u_i -> u_{1-i} ...) which
exchanges sigma 0 <-> 1 of every switch, and P = point reflection about C combined with y -> const - y, which maps u_i <-> u_{-i}
and v_j <-> v_{-j} and PRESERVES sigma. In the antiferro ground state of U (bits alternate, phase s) R preserves s and flips V:
E(s, v) = E(s, -v). P flips the phase and keeps V (V ferro uniform): E(s, v) = E(-s, v). Together all four energies are equal.
Needs: V centred exactly at the midpoint of the two middle U switches (the control above shows what a 0.25 error does).
Note P is a symmetry of rho_dom but NOT of the weak-solvability test (it reverses y), which is why section 3 is needed.

## 3. Full rho vs rho_dom: the numeric y-levels matter
Reachable sets are complements of convex up-sets, so besides dominance and the pair-covers y_t > y_r + y_s (impossible here: all y
in [0.6, 1.15], max < 2 min) there are 4-point covering inequalities  y_a + y_b <= y_c + y_d  (Farkas certificates from
planar.flow_lp, scripts wk9-wk11). With the "symmetric staircase" y (V levels step by +-h) the polished optimum was NOT weakly
solvable for one of the two U phases (4U x 3V), although rho_dom is identical: a bias in rho vs rho_dom. The certificate was
 y(V_SWmost top) + y(V_NEmost top) <= y(U bottom) + y(V_centre bottom)  violated by 2g.
Fix (verified, scale invariant, threshold found): keep the ORDER pattern, but with h0 >= g (SW rise per step) require
 h2 >= h0 + 2g   (NE drop per step).
Tests (4U x 3V, both phases, both V values, weak solvable True): (g,h0,h2) = (0.002,0.002,0.008), (0.01,0.01,0.03), (0.01,0.02,0.04),
(0.01,0.02,0.05); h2 = 2.5g with h0 = g gives False for one phase. So the y-profile along the NE direction must be concave
(slope increasing by >= 2g across each crossing). Globally: y = 1 + eps * F(x+y) with F decreasing and concave is plausible
(range polynomial; keep max < 2 min). NOT verified for a full layout.

## 4. Verification (final_4_5.out; MILP rho_dom with free interior sigma, terminals' sigma fixed)
Terminal table, excess over min = 10.552302 (U_in, U_out, V_in, V_out):
  valid (U_out = NOT U_in, V_out = V_in): (0,1,0,0) (0,1,1,1) (1,0,0,0) (1,0,1,1) -> 0.00000 each
  V broken only: (0,1,0,1) (0,1,1,0) (1,0,0,1) (1,0,1,0) -> 0.09018
  U broken only: (0,0,1,1) (1,1,0,0) -> 0.14006 ; (0,0,0,0) (1,1,1,1) -> 0.19959
  both broken : (0,0,0,1) (0,0,1,0) (1,1,0,1) (1,1,1,0) -> 0.28956, 0.31019
Full rho: for each of the 4 valid combos, strict-margin 1e-6 optimum has cost 10.552317/10.552319 (rho_dom + 1.5e-5) and
planar.flow_lp (weak, exact rationals) answers feasible: True x4. (Original unperturbed P: False, as it must.)
Smaller instances (2U x 3V, 2U x 5V, 4U x 3V) behave the same; 2U x 3V isolated-switch table at centre c = 0 shows
E(01,x) = E(10,x) = 3.03314 for both V bits while the excited states (00, 11) already see V (0.03).
Wire-break costs near the crossing depend on parameters: dv = 6, k = 1 gives U-break 0.0315 / V-break 0.143; dv = 5, k = 1
gives U 0.140 / V 0.090 (chosen). Isolated wire links: U link 0.2103 (a = 3), V ferro link at dv = 5, k = 1 about 0.09.
Not run: 6U x 5V (MILP too slow on a loaded machine).

## 5. Reduction (what it gives, and what is still open)
Source: MAX-CUT on graphs of maximum degree 3 (NP-hard, Yannakakis 1978; Berman-Karpinski), equivalently any Ising with equal
antiferro couplings.
 1. Draw G on the 45-degree rotated grid: every edge is a polyline of NW-SE segments (antiferro chains U, link cost 0.21) and
    SW-NE segments (ferro chains V, link cost >= 0.09); orthogonal drawings of degree <= 4 graphs have O(n) bends and
    O(n^2) crossings. Every crossing is a U x V crossing (parallel segments never cross) -> the gadget above.
 2. Edge e = (x, y): a wire, whose last link before y is a designated weak coupler with kink cost J_e < 0.09:
    antiferro pair at step a = 3.75 (d = 4): kink cost 0.0506 (a = 3.5: 0.103, a = 3.25: 0.156, a = 3: 0.21, from the 2-switch table).
 3. rho = base + J_e * (|E| - maxcut(G)) + O(1e-5 per gadget). A broken wire costs >= 0.09 > J_e and can save at most one
    J_e, so it never helps; all other configurations pay at least J_e per frustrated edge.
This is NOT yet a complete proof. Open items, none checked:
 (a) corner gadgets U <-> V (ferro/antiferro link between last and first switch) and the degree-3 vertex switch with three wires;
 (b) designated coupler inside the global y-profile and its weak solvability;
 (c) a global y(x+y) profile satisfying concavity at every crossing and keeping max y < 2 min y; equalities of levels at the crossing
     (V centre level = U level, V_{-1} bottom = U top) must be matched exactly;
 (d) weak solvability of a full instance (checked only per crossing, and per wire P_n up to n = 5): rho = rho_dom was verified
     instance by instance, never proved;
 (e) additivity of gadget energies for far-apart gadgets (assumed, same as in GADGET-D2.md);
 (f) real-valued coordinates are rational here (half-integers, 5, 4, 3) apart from y-levels, which are rational too; the exp(0.2 .)
     map is only a numerical convention, p_t must be rational for a Turing reduction (replace by rational p with the same
     log-grid up to tolerance; the symmetry argument is exact for any p symmetric under x<->y and the point reflection, so
     choose p symmetric: the symmetries R and P act on p, not on the logs, so rational symmetric p exist; note P is an
     inversion in log coordinates, p -> c/p, which preserves rationality).

## 6. Other approaches
* B (NAE / XOR): not needed. D (pair-cover angle variables): not used; PAIR-COVER-HARD.md shows the angle gives only unimodal/ferro
  couplings, and here pair covers are excluded by y in (0.6, 1.15).
* C (y-level separation): impossible as such (section 1). y-levels only enter as (i) order (conflicts), (ii) numeric values (the
  4-point covers of section 3).

# UPDATE 2 (open items; scripts gad/{corner,star,weakc,attach,asm,asm2-5,ysolve}.py, outputs asm.out asm2.out)
Status: NOT a complete reduction. (a), (b), (c) done; (d), (e) blocked by a weak-solvability obstruction; (f)-(h) not done.

(a) Corner U->V: DONE. U bottoms (-6,6),(-3,3),(0,0) d=4 levels (1.05,1.0); V bottoms (0,0),(1,1),(2,2) d=5 levels
 (1.0,0.95),(0.95,0.90),(0.90,0.85). Exactly 2 ground states (U=010,V=000 and U=101,V=111) at equal cost; every other
 state >= 0.1258. (other corner orientations assumed by reflection, not run.)
(b) Degree-4/3 vertex: DONE. Centre V-type switch (d=5), NW and SE antiferro attachments (d=4, centre offset a=3), SW and NE ferro
 neighbours (k=1, levels h0=0.05 / h2=0.2). Ground states exactly 01100 and 10011 (centre,NW,SE,SW,NE): centre=SW=NE=v, NW=SE=not v.
 Next state 0.1644 (a=3), 0.1495 (a=2.5, 3.5). Degree 3 = drop one wire.
(c) Weak coupler: DONE for a pure U wire. 6 switches, links 3,3,3.75,3,3: alternating states excess 0, kink at weak link 0.05063,
 kinks at strong links 0.21034; both polished optima weakly solvable (flow LP True). For an attachment to a d=5 V switch the same
 kink cost needs centre offset a=4.25 (0.05063; a=3.75 gives 0.156, 4.0 gives 0.103, >=4.5 gives 0).
(e') Assembled test (two independent edges, crossing in the middle): U wire A..B (5 strong switches, weak link to B), V wire of 9 switches
 with C attached by a weak link (a=4.25), 16 switches. rho_dom(A,B,C,D) = base + J_e * #unsat within errors:
 satisfied combos 0, 0, 0, 0.00093; one unsat 0.05063 (x6), 0.05065, 0.05128, 0.0597; two unsat 0.10126-0.10128.
 Max deviation from base + 0.05063*#unsat is 0.0091 (< J_e/2 = 0.025): the crossing + corner-free wires + weak coupler behave, but the
 residual is not zero and would accumulate over many crossings (item g): unquantified.
(d/e) Weak solvability of the assembled instance: FAILS (all 4 satisfied combos False at the margin optimum). LP over free numeric y with
 the same strict order/ties (ysolve.py): feasible for the combos with V bit D=1... precisely 2 of the 4 (A,B,C,D)=(0,1,0,1),(1,0,0,1),
 infeasible for (0,1,1,0),(1,0,1,0) for ANY y with that order. Minimal infeasible switch set (greedy): {V_-1, V_0, C}, i.e. the
 attachment switch C (NW of the SW end of V) together with two middle V switches. Moving C's y-levels (x = 0.0 ... 0.2 above V_-4's):
 x = 0 (C level = U level) changes the order pattern and cost (19.64 / 20.19, wrong); every x >= 0.02 stays infeasible. So the
 obstruction is a genuine convexity/cover obstruction (rho > rho_dom for those terminal states), not a y-tuning issue. In the crossing
 alone (4U x 5V) all four combos were solvable, so it is caused by the extra attachment C geometry. Remaining work: re-place C (e.g.
 attach at the NE end by an SE switch, or attach with different levels/orientation) and rerun asm2.py; estimate: several hours, unknown success.
(f) gap-pair constraints at 3 crossings: NOT run. (g) full MAX-CUT instance: NOT run (only the 2-edge test above). (h) per the audit, the
 symmetry argument P is a numerical, not exact, statement; the only quantitative evidence is the table above (residual <= 0.0091 per
 crossing+wires, 0.00093 on the exact-degeneracy combos). The reduction therefore stays conditional.
Also: the global y-profile F(x+y) (d) was not constructed; note y-ordering constraints plus the 4-point covers are the binding ones.
REDUCTION-COMPLETE.md was NOT written because the conditions for it were not met.

# UPDATE 3 (attachment scan; scripts gad/scanC*.py, asm6.py)
Isolated test (V chain s=-2..2 + attachment C, d_C=4, free y LP with same order, both V bits): 640 candidates (end SW/NE, offsets -6..6 step 1.5,
4 level shifts). Feasible AND exactly 2 ground states with C = NOT V exist only for C displaced purely vertically or horizontally from
the SW end centre ((0,dy) or (dx,0), dy in [4,7]) with C's levels BELOW the V end's by 0.02-0.08; coupling 0.11-0.15 (too strong:
> V-wire break 0.09). Diagonal/NW/SE attachments (the earlier a=4.25 choice) are y-infeasible. Weak (0.05) attachments (dy=8.25, level
shift <= -0.12) get a third ground state (1,1) via long-range level effects. Ferro-type attachments (ground [(0,0),(1,1)]) are feasible at many
diagonal offsets (e.g. (+-1.5k, +-1.5k)), coupling 0.5-1.0 (too strong). NE end: nothing clean found.
Assembled with the feasible vertical attachment (offset (0,4.5), shift -0.04, U coupler a=3.4): rho_dom table is destroyed (excess 0..1.3, no
base + J_e*#unsat structure): C sits near the U wire / crossing and interacts at range through the y-levels; y-LP infeasible for 3 of 4 combos.
Verdict: no attachment works in the assembled instance. Obstruction pattern: (i) cover obstruction kills diagonal weak attachments
(y_a+y_b<=y_c+y_d type); (ii) the attachments that avoid it need C's level below the wire's, which makes C comparable to distant switches
(long-range conflicts). Not tried: buffer switch, U-type extra switch, placing C far from other wires (needs longer wire first), systematic 3-switch scans.

# UPDATE 4 (edge design without attachment switch C; scripts gad/edge.py edge2.py edge3.py cprime.py solvc2.py cert*.py; time limit 500 s matters)
Design: vertex gadget (b) at both ends (strong links), weak link (a=3.75, kink 0.05063) in the middle of a U segment, parity by U length.
Warning: MILP time_limit=120 s gives suboptimal sigma on 25-switch instances and scrambled tables / false infeasibility; use >= 500 s.
(a') vertex - U(6 links, weak in middle) - vertex: table (v1,v2): (0,1),(1,0) = 0; (0,0),(1,1) = 0.05063. Weakly solvable at the given y: True x2.
(b') vertex - V(5) - corner - U(weak) - vertex, g=0.01: V level step 0.01 (=gap) => corner phase (0,1) y-INFEASIBLE (minimal set {u1, V3, V4});
 V step 0.02, 0.04, 0.08 (> gap): table exact (0, 0.0506), y-feasible and weakly solvable at given y for both combos. Profile: U (1.01,1.00),
 V_j levels (1.01-sv(j+1), 1.00-sv(j+1)), sv >= 2g.
(c') two edges crossing (25 switches): E1 = V(s=-4..4, vertex1 = s=4) - corner at s=-4 - U arm NW with weak 3.75 - vertex2; E2 = vertex A - U (t=-4.75, weak 1.25 step, t=-3.5..2.5) - vertex B crossing E1's V at the centre (h0=0.02, h2=0.04, g=0.01; E1 U-arm levels (1.10,1.09), E2 (1.01,1.0)).
 rho_dom (all 16 terminal states, 500 s): excess = 0.05063 * #unsat EXACTLY (5 digits) for every state; 4 satisfied states cost 28.48724.
 Weak solvability: at my hand-set y: False x4. LP over free y with identical strict order/ties: JOINT y exists, ratio max/min = 1.28 (<2),
 all 4 satisfied states weakly solvable at it (flow LP True x4), cost at margin 1e-6: 28.48728-9 (rho_dom + 4e-5). Levels found:
 1.0, 1.00197, 1.00394, 1.00535, 1.00677, 1.00789/1.0079, 1.00902, 1.01663, 1.28026/1.28027 (saved gad/cprime_yfound.npz).
 (A first y-LP run showed a cover obstruction {switch 10, 20, 21} but it used suboptimal sigma; with exact optima it disappears.)
Not done: K_3 and a full MAX-CUT instance (a triangle drawing needs the mirrored corner V-SW/U-NW and a U segment in every edge, plus a
 vertex with two arms; untested), gap-pair slack check (f), global y-profile (y is found by LP per instance, not by a formula), mirrored corners.
So the earlier "attachment" blocker is removed by putting the weak link inside a U segment; remaining risk is assembly (global y LP, bounded range) and the K_3 end-to-end.

# UPDATE 5 : K_3 end to end (gad/k3.py, k3run.py, k3y.py; time_limit 500)
Layout (bottoms, grid units, g=0.01, V step sv=0.02, base 1.0): corners use only the verified corner (U on one side, V NE) and its coordinate-swap mirror
(x<->y is an exact symmetry of rho and of weak solvability, levels unchanged).
 K1=(0,0): V chain j=0..5 (d=5) at (j,j) levels (1.01-sv(j+1), 1.00-sv(j+1)); vertex Y = V_6 at (6,6) levels (0.87,0.86); U arm from K1 along (+1,-1),
 steps (3, 3.75, 3) (3 links, weak in the middle), levels (1.01,1.00), ending at vertex X.
 K2=(19.5,-19.5): V chain NE j=0..5, vertex Z=(25.5,-13.5) (0.87,0.86); U arm along (-1,+1), same steps, ends at the same vertex X at (9.25,-10.25) (1.01,1.00).
 Pure U edge Y-Z: 6 switches (d=4, levels 0.87/0.86), steps (s,s,s,3.75,s,s,s), s=2.625 (7 links, weak in the middle). 27 switches, 54 points.
 Parity: every edge has 3 or 7 antiferro links, V copies, so every edge penalises equal endpoint bits.
 Triangle needs: the corner arms of X on opposite sides (NW and SE) and Y, Z reached by their SW arms; consistency forces the YZ length 2P (=19.5), met by s=2.625 strong links.
rho_dom (vertex bits fixed, everything else free): 000 and 111: +0.10126 (= 2 J_e); the six other patterns: 0.00000 (one at 1e-5). I.e. rho_dom = base + J_e*(#monochromatic edges - 1)...
 equivalently base' + J_e*#mono: 1 mono edge on non-constant, 3 on constant. maxcut(K3)=2 recovered exactly.
Weak solvability: at my hand-set y 4/6 patterns solvable; LP over free y with the same strict order and ties gives a JOINT y (cap max/min <= 1.9 feasible,
 found max/min = 1.462; cap 1.3 also feasible, see below), flow LP True x6; MILP optimum 31.31611 for all 6 (spread <= 1e-5), margin cost within ~1e-5.
Not done yet: K_{3,3} / K_4 with a crossing in the generated layout, a general layout generator (layout.py), mirrored corner with reversed levels (not needed so far:
 the R-mirror covers the arm sides; the V-going-SW corner is not needed for K_3).
 (k3y.out: cap 1.3 -> max/min exactly 1.3, flow LP True x6; y saved gad/k3_yfound_1.3.npz, k3_yfound_1.9.npz.)

# UPDATE 6 : order/tie constraints of every gadget, and K_4 (scripts gad/wedge.py, refl.py, refl2.py, layout_search.py)
Notation: s = x+y of a switch centre (levels are strictly decreasing functions of s in all gadgets), g = top-bottom gap of a switch.
## Level (order/tie) relations imposed by each gadget
* switch: top = bottom + g (strict).
* U wire (arm, pure edge, any number of links, weak link included): all its switches have the SAME (top, bottom) levels (ties); U switches of one wire lie on one anti-diagonal, so s is constant.
  Consequently both endpoint vertices of a pure U edge have equal level (tie) and the A-vertex of a corner edge has the level of its arm.
* V wire (ferro chain, step 1, d=5): levels strictly decrease toward NE, by >= 2g per step at corners (sv = 0.02 and 0.04 with g = 0.01 verified; sv = g FAILS weak solvability at the corner),
  at a crossing only the ORDER pattern matters (see below); the V-end vertex B of a corner edge has the level of the last V switch.
* corner (V NE of K, arm NW or SE; verified): u0 at K has the arm level; V_0 top < U bottom (strict, sv > g); V_j below V_{j-1} (strict).
  Point-reflected corner (V SW of K, arm SE or NW; verified in refl2.py: rho_dom exact 0/0.05063, weakly solvable at given y and LP y): same with the order reversed, V levels strictly INCREASE toward SW.
  (Verified only WITHOUT dangling vertex stubs; with the reflected vertex stubs one phase is y-infeasible: minimal set {last U switch, vertex SW stub, vertex NE stub}.)
* vertex (b): centre switch d=5; its levels equal the arm levels of the attached U wires (ties); SW stub above, NE stub below (strict) -- stubs are NOT needed for degree <= 3 layouts
  (omit them, as in K_3).
* crossing (V centre switch c with U wire W): ties V_c = W levels (top = top, bottom = bottom); V_{-1} (SW neighbour) strictly above W; V_{+1} strictly below W (V_{-1} bottom > W top, V_{+1} top < W bottom);
  V_{-2}, V_{+2} continue monotone. The numeric rule h0 >= g, h2 >= h0 + 2g is NOT needed once y is found by the LP over free y with the same order (c').
## Global consequence
Take y(switch) = F(s of centre) with F strictly decreasing (+ gap g on top). Then every tie above is automatic (U wires have constant s, a V centre crossing a U wire has the same s, vertices of a pure edge have equal s),
every strict relation holds when F decreases by more than g per V step, and the level conditions are EQUIVALENT to the geometric conditions below: no extra order constraint appears.
## The real constraint is geometric, in terms of s = x+y and t = y-x (displacements B - A)
 pure U edge (P uses SE arm, Q uses NW arm):  ds = 0,           dt = -2m
 corner (A arm, B arm):  (NW,SW) ds>0,dt>0 ; (SE,SW) ds>0,dt<0 ; (NW,NE) ds<0,dt>0 ; (SE,NE) ds<0,dt<0   (|ds| = 2n, |dt| = 2P)
 (SW arm of B <-> V chain lies SW of B, K SW of B; the NE-arm corners are the point-reflected corner).
Each vertex has one NW, SE, SW, NE arm; an arm serves one edge.
 K_3: solutions exist with verified corners only (6 found, e.g. the layout of UPDATE 5).
 K_4, VERIFIED CORNERS ONLY (SW arms): NO layout. Reason: pure edges have ds = 0 and SW-corners have ds > 0 from A to B; each vertex needs a third arm, and the only third arms are SW (B end of a corner, needs a neighbour with SMALLER s)
 or NE; a vertex of minimal s cannot have an SW arm, so it has degree <= 2. Exhaustive check over all edge-type/arm assignments (wedge.py): 0 solutions. This is not a level cycle but the s-order: acyclicity fails exactly at the s-minimal vertex.
 K_4 WITH THE POINT-REFLECTED CORNER (NE arms): 96 type assignments are feasible (strict wedge LP).

## UPDATE 6, K_4 layout result (gad/wedge.py, ls2-ls4.py, layout_search.py)
* The point-reflected corner (V going SW, U going SE/NW, levels increasing toward SW) is VERIFIED without vertex stubs: rho_dom 0 / 0.05063, weakly solvable at the given y and at the LP y (refl2.py).
  With the reflected vertex stubs one phase is y-infeasible, so stubs must be omitted (degree <= 3 never needs them).
* The type-assignment LP finds 96 feasible K_4 assignments with NE arms allowed, but ALL 96 use only corner edges (no pure U edge). Parity obstruction: for a corner edge ds = +-(2n+1) (n = integer number of V steps, step 1),
  so every triangle of corner edges needs three odd integers with signs summing to 0: impossible. A layout with integer V lengths needs every triangle to contain a pure edge (even number of corner edges), but the strict wedge LP
  admits no K_4 assignment with pure edges. Exhaustive integer search (n in 3..14, arm lengths in the verified intervals): 0 layouts.
* Way out (NOT verified): make the V length continuous, e.g. let the last one or two V links have step in [0.5,1] (stronger ferro link; k=0.5 had kink 0.135 vs 0.09 at k=1 in the V-pair test),
  or let the vertex attach at an offset to the last V switch. Then the 96 assignments are solvable as a linear system (positions, arm lengths); the corner/vertex gadget with such a V link must be re-verified.
* Therefore K_4 (with or without a crossing) and K_{3,3} are NOT built. K_3 only used 2 corner edges and 1 pure edge, which is why integers worked.
* Weak-solvability remark (from the coordinator): use margin 1e-8 + snapping of coordinates that agree within 1e-5 (WEAK-SOLV.md section 9); earlier failures at 1011/0011 of cprime were artefacts.

# UPDATE 7 : relays, layout generator, K_4 (gad/relay.py, snapw.py, milp_layout.py, layout.py, lay_k4*.py, k4run.py, k4fix.py, k4ub.py, k3snap.py)
## Relay verified
vertex gadget used with 2 arms, all strong links. Test: V chain (n=4) - corner - U arm of 4 strong links - RELAY - pure U wire (3 links, weak in the middle) - vertex (13 switches):
 terminal table (u,v): (0,1),(1,0) = 0 ; (0,0),(1,1) = 0.05063. Weak solvability with snapping (margin 1e-8, snap 1e-5, snapw.py): joint y exists (cap 100, found max/min 1.5), flow LP True x2, cost 14.983994 both.
 A relay passes the bit and counts its arm links in the parity; ds parity of a chain of two corner edges is even, which removes the K_4 parity obstruction.
## K_3 recheck with snapping (k3snap.py): all six optimal patterns y-jointly feasible, max/min 1.449, flow LP True x6 (costs 31.31606 for three patterns, the others not converged under machine load).
## Layout generator (layout.py + milp_layout.py)
MILP (scipy/HiGHS) over: segment type per segment (pure U, 4 corner types: (NW,SW),(SE,SW),(SE,NE),(NW,NE)), arm uniqueness at every vertex, integer V lengths n_j, continuous arm/pure lengths L_j,
exactly one weak-link holder per original edge with L in the allowed union (3.75 + (l-1)*[2.65,3.45], l=3,5,7,9), potentials (s,t) of vertices; the optional relay set per edge.
Then build_instance: link counts per segment chosen so the total number of antiferro links per original edge is odd, arm steps in [2.6,3.5], weak link in the middle of the weak segment; levels y = L0 - 0.02*(centre s), top = bottom + 0.01
(rule of UPDATE 6; no gadget relation violated in any verified gadget, K_3 and the 25-switch instance order patterns are reproduced).
collisions() rejects layouts whose non-incident gadgets overlap. No crossing is produced by the MILP (a crossing needs an explicit alignment; not generated yet).
## K_4 with one relay
 relay on edge (0,1) (all other edges single segments), 7 segments, 77 switches (154 points), s range [-16,5], y range 4.9..5.33, only 1 of 51 random MILP solutions was collision free.
 vertex bottoms: (0,0),(-48.95,34.95),(-34.85,27.85),(-25.8,18.8), relay (-1.45,-19.55). Segments: e0 = (0,relay) CE n=10 L=9.05 weak seg, (relay,1) CE n=3 L=51 (16 links); e1 CE L=31.35; e2 CE 22.3; e3 CE 10.6; e4 CE 19.65; e5 pure 9.05.
 (instance saved gad/lay_k4_best.pkl)
 Direct rho_dom MILP does NOT converge at 154 points in 1500 s (conflicts 1141): bounds (lb / best exact): 0011: 88.40 / 88.63; 0101: 87.80 / 87.82; 0110: 90.51 / 104.99; 0001: 87.43 / 208.1.
 With conflicts of margin >= 0.5 fixed (514 free conflicts, 600 s): 0011: 88.146 / 88.2014; 0001: 87.12 / 94.65. The balanced patterns' best values differ by 0.38 between 0011 and 0101: NOT converged, no conclusion.
 A heuristic upper bound from the intended bit pattern (k4ub.py, max-margin routing of non-own conflicts) is useless (costs 98 - 243).
 Therefore the K_4 16-pattern table and its weak solvability are NOT established. What is needed: solve rho_dom block-wise (LOCALITY.md blocks) or a tighter MILP (warm start / stronger cuts), then snapped y-LP.

# UPDATE 8 : K_4 upper bound by gluing (gad/k4glue.py, k4ub.py, k4weak.py, rulecheck.py)
CORRECTION to UPDATE 7: the numbers called "milp lb" there are `res.fun` of the tangent-cut MILP = best INCUMBENT of the model, not a lower bound (no dual bound was recorded). The MILP incumbents (87.8-208) were far above the true optimum, see below.
## Upper bound by gluing, all 16 patterns of the K_4 instance (77 switches, 154 points, 1141 conflicts, layout gad/lay_k4_best.pkl)
Construction (no MILP): intended bits sigma(vertex bits): relay bit chosen to place kinks on weak links; propagate along each edge chain (AF links flip, weak link flips unless kinked, V/corner links copy).
Q(sigma) = optimum of the convex program with constraints only on the own-pair conflicts (bits fixed) plus an active-set loop: any conflict violated at the current optimum is added with the cheaper coordinate, until NO conflict is violated.
Exact check at the end: violations over all 1141 conflicts (tolerance 1e-7) = 0 for every pattern (3-4 iterations, 1 s each). So Q(sigma) is feasible and cost(Q(sigma)) is a valid upper bound.
 uncut = number of monochromatic K_4 edges; cost:
   uncut 2 (6 balanced patterns)  85.25606 (all six identical)
   uncut 3 (8 patterns)           85.30669  = 85.25606 + 0.05063 = S0 + J_e*(uncut-2)
   uncut 6 (0000, 1111)           85.45858  = 85.25606 + 0.20252 = S0 + 4*J_e
 i.e. cost(Q(sigma)) = S0 + J_e*(uncut - 2) with S0 = 85.25606 exactly (5 digits, J_e = 0.050630), as required by the reduction; no cross-gadget conflict is violated (no spacing-rule failure of the generator at these Q).
Not done: (2) lower bound by tilings (the block certificates of LOCALITY.md are hand-built per layout; the K_4 layout needs relay, mirrored-corner and 3-star blocks not in the library; blocks not generated), so rho_dom = S0 + J_e*(uncut-2) is only an UPPER bound for K_4 here.
Rule R (6.5 steps) was not checked: setup() prunes conflicts of margin >= 1.2, so a check on the pruned conflict list is vacuous; the glue test (zero violations of all 1141 conflicts) is the direct statement for this instance.
## K_4 weak solvability at the glued Q (gad/k4weak1.py, k4weak2.py; one flow LP on 154 points = 372765 arcs, build 5 min + LP 3 min)
Q(sigma) snapped (tolerance 1e-5, no margin polish: glued Q from the active-set solve). y = generator rule (y = 5 - 0.02*s, gap 0.01): pattern 0011: NOT weakly solvable.
y-LP over free y with the same strict order/ties, pattern 0011 alone: feasible, max/min = 1.1945 (cap 100). At that y the flow LP gives: 0011 True, 1010 True, 0110 True, 0101 False, 1001 False
(1100: see below if present). A joint y for all six patterns (find_y on six graphs) did not finish (hours); so at one common y at least 3 of the 6 maximum cuts are weakly solvable, which is all the reduction needs
(rho <= cost of a weakly solvable Q; one max cut suffices). The two False patterns are not known to be unsolvable (they were tested only at the y fitted to 0011).
Not done in UPDATE 8: lower bound by tilings; generator crossings and K_{3,3}. A crossing in the generator needs two lattice conditions on the layout potentials: (i) s_U - s_K(V chain start) = odd integer so that a V switch centre lies on the U wire's anti-diagonal (tie of levels);
(ii) the t-coordinate of that V switch equals the midpoint of two consecutive strong U switches (U steps exactly 3 for the four switches around it, V steps exactly 1 for s = -2..2). These can be added to milp_layout as integer/continuous constraints; not done.
(Final: 1100 False as well, so True for 0011, 1010, 0110; False for 0101, 1001, 1100 at that y.)

# UPDATE 9 : tiling conditions, rule-built y on K_4, quantised generator (gad/milp_layout2.py, layout2.py, lay2_k4*.py, k4rule.py)
## 1. Lower bound for K_4 via Lemma T/C: structural conditions NOT met by the UPDATE 7 instance, generator fixed to meet them
Lemma C (NP-HARDNESS.md) is a theorem given L1-L5 and the library certificates; so the lower bound for a layout is the verification of L1-L5, not a new MILP.
Findings on the UPDATE 7 K_4 instance (gad/lay_k4_best.pkl): (a) its grid is h = 0.2 and steps such as 2.625, 9.05 (not in (1/4)Z), whereas the library is certified at h = 4 ln(21/20) with all coordinates in (1/4)Z: L1 FAILS;
(b) its weak links lie in 3-link arms next to a star core, so the weak link is adjacent to a core (j < 2): L4/Lemma T hypothesis FAILS. No tiling listing is meaningful for that instance.
Fix implemented in the generator (milp_layout2.py): s,t potentials in (1/2)Z, arm/pure lengths L in (1/4)Z, integer V lengths; weak holder with link count l in {7,9,11,13,15} and strong steps in {2.75,3,3.25,3.5}, i.e. L in 3.75 + (l-1)[2.75,3.5];
strong segments l in 3..20 (pure strong segments l >= 5 so the plain stretch has r >= 2); total number of antiferro links per original edge odd (integer m_e); builder (layout2.py) emits quarter-multiple steps and verifies Lemma T per stretch with np_tiling.construct/verify:
cores = stars/relays (vertex + first arm switch), plain stretch = remaining chain switches, weak link index 2 <= j <= r-2, r >= 2. Over 618 random MILP layouts (relay sets of size 1-3, seeds 1-18) the tiling check passed in all 618.
Collisions: the same generator found NO collision-free K_4 layout in 618 tries (minimum 2 colliding gadget pairs; the unquantised short-arm layout had 1 in 51). With the new spacing frontier (WEAK-SOLV §13/14: non-adjacent gadgets must differ by >= 24 in s_c or be separated in t by >= the U-wire length) the layout will be larger still;
a K_4 layout meeting L1-L5, collision-freeness AND the frontier was not obtained, so the K_4 tiling table and the max over the two tilings were not computed.
## 2. Weak solvability on K_4 with rule-built y (glued Q, pattern 0011, snapped, one flow LP graph of 372765 arcs reused)
y = F(s_centre), top = bottom + 0.01, rules: linear c = 0.02 (max/min 1.43), 0.05 (2.06), 0.2 (5.21); concave (c1,c2) = (0.02,0.07) with kink at s* = -12, -8, -4, 0, 4 (max/min 2.28, 2.08, 1.88, 1.68, 1.48): weakly solvable = False for ALL eight rules.
(The final rule of WEAK-SOLV §13 - slope 0.02 plus 0.6 at crossing kinks, g = 0.002, eta normalised - was not run; this K_4 has no crossing.)
A free-y LP for the same Q (same strict order/ties) IS feasible (max/min 1.1945) and gives weak solvability for 3 of the 6 maximum cuts (UPDATE 8), so the obstruction is the y-profile, not the geometry of Q. This UPDATE 7 instance has s_c range 21 (< 24) so it violates the spacing frontier by construction; no deletion filter was run.
## 3. Crossings in the generator, K_{3,3}: NOT implemented. Design notes
In (s,t) potentials a corner segment is an L: U leg at s = s_K (t from t_K to t_A), V leg at t = t_B (s from s_K to s_B). A crossing of the U leg of segment a with the V leg of segment b needs
 (i) s_{K,a} - s_{K,b} = 2j+1 odd (tie of centre levels with V switch index j), 3 <= j <= n_b - 4 (K^+ needs one plain V switch beyond the core on both sides);
 (ii) |t_{V,b} - t_{K,a}| = 2q with q = (position of the crossing along the arm) = (sum of the steps before the aligned block) + 4.5, the arm containing a block of three steps equal to 3 around the V switch, with >= 1 plain switch on each side;
 (iii) all other pairs of legs separated by the spacing rule (6.5 steps in dominance, 24 in s_c or t-separation for weak solvability).
Not coded: it needs per-pair disjunction (cross / four separations) in the MILP on top of the type/arm variables; K_{3,3} (6 vertices, 9 edges, >= 1 crossing, >= 12 segments, several hundred switches) is far beyond the sizes at which the present checks run:
 glued UB per pattern takes ~1 s at 154 points but one flow LP is already ~5 min build + 3 min solve at 154 points (arcs ~ T^3: ~1.6e6 arcs at 250 points), and 64 patterns would be needed. So K_{3,3} numerics are out of reach without a lighter weak-solvability test; for K_{3,3} the argument has to rest on the theorems (Lemma C/G/R + WS rule), with the numerics limited to the library blocks.

# UPDATE 10 : explicit bus/track scheme: local tests, a lattice-parity obstruction and its fix (gad/gluelib.py, cross2.py, bus.py, bus2.py, halfv.py, vpair.py)
All numbers at the library step h = 4 ln(21/20) (cx2.EPS = H), y by the final rule of WEAK-SOLV 13: F concave piecewise linear, slope c1 = 0.02 below the first kink and +Delta = 0.6 at each kink level, g = 0.002, y = 1 + 0.3 (F + g[top])/max
(gluelib.rule_levels). Dominance conflicts of this rule coincide with the earlier orders (every F step between distinct s_c is >= 0.02 > g). Glued Q = active-set optimum (own-pair bits fixed, add violated conflicts until none; exact check of ALL conflicts, tol 1e-7), snapped 1e-5, flow LP exact rationals.
## 1. ONE U wire crossing TWO parallel V tracks (cross2.py): U wire of 4 + 2*... switches (steps 3), V tracks t = 0 and t = T (9 V switches each), both crossing cores centred on the U wire, kink at the common level s_c = 4.
 T = 36 (33 switches), T = 24 (31), T = 18 (30): glued cost - sum B = 0.245929 = 2 X_K (X_K = 0.1229644) for every one of the 8 satisfied terminal patterns, 0 violated conflicts, weakly solvable (final rule) True for the patterns printed
 (T=36: all 8; T=24, 18: first three patterns printed, rest not inspected). So two crossings on one U wire at the same s level are additive and solvable down to track separation 18.
## 2. Degree-3 bus (bus.py, bus2.py): V chain on t = 0 (bottoms (k-0.5, k-0.5)), three stars at k = 0, 12, 24 each with a NW U arm of 6 switches (first arm switch bottom = star bottom + (-2.5, +3.5), then steps (-3,+3)); 53 switches.
 Glued cost - sum B = 9e-14 (zero excess), 0 violations, both bus bits. Weak solvability: kinks at NO level: bit 0 False, bit 1 True; kinks at all three arm levels (s_c = 4, 28, 52): True/True; kink only at the first or only the last arm level: False/True.
 So in the rule every arm (U wire) level is a kink level, crossing or not.
## 3. Parity obstruction in the scheme (found while computing lattice conditions; verified on cprime: crossing core U bottoms s = 0, V bottoms odd; corner V_0 and arm bottoms both s = -9)
Let s_b = bx + by of a bottom. Library facts: (i) crossing core: U switches have s_b = V centre s_b + 1 (U bottoms (+-1.5,-+1.5),(+-4.5,-+4.5), V bottoms (k-0.5,k-0.5)); (ii) star: NW/SE arm first switch has s_b = centre s_b + 1;
(iii) corner (all four types, point reflection preserves parity): u0 and V_0 share the bottom K, so arm and V chain have the SAME parity; V steps are 1, U steps preserve s, so each wire has a constant parity.
Scheme: bus parity p, star arms p+1, corner V track = its arm parity p+1; the relay joining the two corner segments of an edge has the same parity, so the arm at the other bus has parity p+1 too, hence all buses have the same parity (graph connected).
A crossing needs (track parity) = (crossed arm parity) + 1 mod 2 by (i); but every track has the parity p+1 of every arm. => NO crossing can be aligned in the scheme as stated. (For cprime this does not occur because E1 and E2 are different components.)
Fix verified locally: a V link of step 0.5 flips the parity of the rest of the chain. V pair table (d = 5): step 1: break 0.14059; step 0.5: break 0.24106 (>= 2 J_e = 0.0988: stronger, credit 2J_e holds). In the relay edge (corner - V chain with link V1->V2 of step 0.5 - relay - weak U wire) glued cost - sum B = 0, 0 violations, weakly solvable (final rule, kinks none), both bits (halfv.py; unshifted chain identical). Library certificates for a V chain / corner window containing a 0.5 link are NOT done.
So each V track gets one 0.5-link (right after the corner) so that its bottoms have the parity opposite to the arms it crosses.
## 4. The scheme (specification; K_4 not generated)
Coordinates: bottoms (x,y), s = x+y, t = y-x, grid units, all multiples of 1/4. V switch d = 5 chains (a+j, b+j); U switch d = 4 wires (x - i p, y + i p).
* Bus of vertex v: V switches at (k - 0.5, k - 0.5), k = K_v - 5, ..., K_v + 12 (deg_v - 1) + 5, K_{v+1} - K_v >= 12 (deg-1) + 34 + 12 (24-in-s_c frontier between buses).
* Relay r_i (i = 0..deg-1): the bus switch k = K_v + 12 i is a star centre with a NW arm: arm switches a_1 = (k-3, k+3) (= star bottom + (-2.5,+3.5)), a_{i+1} = a_i + (-step, +step), steps in {2.75,3,3.25,3.5}, weak 3.75 in one arm per edge. Arm s_b = 2k (parity 0), t(a_i) = 6 + 2 p_i, p_1 = 0.
* Edge e = (i<j) gets track level T_e = T0 + W e with T_e = 3 (mod 6) (so crossing midpoints of all-3-step arms, t = 9 + 6m, coincide with tracks) and W >= 54 (tail >= 20 so that link-count parity is free); arm at bus i reaches K_1 with t(K_1) = T_e: p_K = (T_e - 6)/2.
  Arm steps: all 3 up to the topmost crossed track + 9 (t units), then a tail of >= 20 with link count chosen for the parity of the edge (sum of arm link counts odd), steps in {2.75,...,3.5}; weak 3.75 in the middle of the tail of ONE arm (j >= 2 from the core, r >= 4).
* Track: corner T1 at K_1 (A SE of K_1: V chain NE), V chain bottoms K_1 + (m,m), one 0.5-link right after the corner (parity), relay (V-type star, V arms SW and NE) in the middle, corner T4 (reflected, V chain SW) at K_2 above bus j.
* Crossings: the arm f at bus u crosses track e iff T_e < T_f and s_arm in the s-span of track e; centring: V centre bottom s = arm s_b - 1 (parity fixed by the 0.5-link), U switches of f at t = T_e +- 3, +- 9 with 3-steps (guaranteed by T_e = 3 mod 6 and all-3 steps below the tail).
* Levels: y by the final rule, kinks at the s_c of every arm. Number of switches for K_4 (rough count from the formulas: 4 buses of ~35, 12 arms of ~15-40, 6 tracks of ~60-100 V switches): about 700 switches = 1400 points.
## 5. What was not done (precise)
K_4 by the scheme was not generated and so no glued UB over its 16 patterns, no tiling LB and no weak-solvability run exist: (a) the half-link needs library certificates (V pair break 0.241 only); (b) generating 700 switches is routine but the glued UB by the SLSQP active-set (1400 variables) and the flow LP (arcs ~ T^3 = 3e9) do not run;
the glued UB would have to use the analytic Q* of Theorem U (isolated optima + stored crossing-core and kink displacements) and the weak-solvability check has to be done on sub-clusters (two parallel tracks, bus, relay-edge: done above) rather than on the whole K_4.

# UPDATE 11 : generator `gad/scheme.py`, analytic glued Q*, K_3 / K_4 / K_{3,3}, 0.5-link certificates, cluster list
Files (gad/): scheme.py (generator), qstar.py (library + analytic Q* + exact conflict check), schemerun.py (K3/K4/K33), schemetile.py (tiling conditions), np_half.py/np_half.out (0.5-link certificates),
clusters.py, clusters2.py (cluster weak-solvability), gluelib.py. Everything at h = 4 ln(21/20), all coordinates in (1/4)Z (exact Fractions in scheme.py).
## 1. Corrections to UPDATE 10 found while implementing
(a) The second corner of a track is the REFLECTED corner (V chain SW of the corner, arm SE): V'_0 shares the TOP corner of u0' (V'_0 bottom = K' - (1,1)), not the bottom. With the first draft (V'_0 at K') the cluster `edge` was not weakly solvable (minimal failing set: u1', V_{N-1}, V_N, V'_0 = {arm switch next to K', the last two V switches, V'_0}); with the correct geometry all 4 patterns pass (section 5).
    Track of edge e: V_0 = K, V_m = K + (m - 1/2)(1,1) for m = 1..N-1, V'_0 = K + (N-1)(1,1) (K' = K + N(1,1), N = k_j - k_i); links V_0-V_1 and V_{N-1}-V'_0 have step 1/2 (parity flips).
(b) No relay is needed in a track (the V chain is continuous from corner to corner); parity: arms with n_i, n_j switches, n_i + n_j odd, weak link in the tail of one arm.
## 2. Generator (scheme.py, build(n, edges)): exact specification
Buses: V switches (d=5) bottoms (k - 1/2, k - 1/2); bus v at K_v = 5 + 46 v, star centres at k = K_v + 12 r (r-th incident edge), bus switches k in [min-5, max+5].
Tracks: edge e (index e) at t = T_e = 3 + 6 (12 + 9 e) (W = 54 in t). Arm of e at star (u, k): a_1 = (k-3, k+3), a_{i+1} = a_i + step*(-1,+1); the arm ends (a_n = K, d=4) at t(K) = T_e, i.e. p_K = (T_e - 6)/2; K = (k_i - 3 - p_K, k_i + 3 + p_K).
Arm steps: 3 up to p = 3 (c_top + 2) where c_top is the level index of the topmost crossed track (6 if none), then a tail of n_tail steps in {2.75, 3, 3.25, 3.5} summing to p_K - p_start (>= 20); the weak step 3.75 sits in the middle of the tail of ONE arm of the edge;
n_tail chosen so that n_i + n_j is odd. Crossings: arm f crosses track e iff T_e < T_f and k_i(e) < k_f < k_j(e); the V centre is V_m, m = k_f - k_i(e); the four U switches at V_m + (2,-1) + mm(-3,3), mm = -1..2 exist by construction (assertion in build: lattice conditions hold automatically).
Levels: final rule (kinks at the s_c of every arm). Sizes: K_3 367 switches, 2 crossings; K_4 958 switches (1916 points), 11 crossings; K_{3,3} 2304 switches (4608 points), 45 crossings.
## 3. Analytic glued Q* and exact checks (qstar.py, schemerun.py; no solver for Q*, numpy over ALL conflict pairs)
Library (local glue runs, `qstar_lib.pkl`): crossing core (4U x 5V, all four terminal states): X_K = 0.1229644, neighbours at isolated optima to 1.7e-11; weak kink pair (a = 3.75): J_e = 0.0493902, neighbours isolated to 1.8e-9.
Q*(sigma): every switch at its isolated optimum (top -dH/2, bottom +dH/2 in its bit coordinate), crossing cores by the stored displacements (key: bit of the mm=0 U switch, V bit), unsat edges: kink pair by the stored pooled displacement; bits propagated by Lemma P (arm alternation, kink at the weak link of unsatisfied edges).
Result (all conflicts y_a > y_b, tolerance 1e-7):
| graph | patterns | conflicts per pattern | violations | min slack (tight pairs, float) | cost - (sum B + n_x X_K + J_e uncut) |
| K_3 | 8 | 269,940 | 0 | -3.6e-15 | <= 2.3e-12 |
| K_4 | 16 | 1,815,664 | 0 | -7.1e-15 | <= 1.9e-11 |
| K_{3,3} | 64 | 10,549,716 | 0 | -1.4e-14 | <= 1.9e-11 |
Conflict classes (K_4 0011 / K_{3,3} 000111): own pairs 958 / 2304 (slack 0 by design), different-switch pairs with slack < 1e-6 (tight, inside gadgets): 57 / 225; every other conflict has slack >= 0.0417 (= 0.214 grid steps).
Negative controls (K_4 0011): zero displacement: 4193 violations; one crossing core at isolated optima: 4; unsat edges without pooled kinks: 6; so the checker is sensitive.
So Q*(sigma) is rho_dom-feasible with cost exactly S0 + J_e * #uncut (S0 = sum B + n_x X_K) for every pattern; no spacing-rule failure at these layouts. (Float evaluation; tight pairs are ties.)
## 4. Certificates for the 0.5 link (np_half.py, interval B&B of np_dual, all 2^n bit patterns per window, credits 2 J_e per relation)
T1 (V NE of the corner: V_0 = u0 bottom, V_1 = V_0 + (.5,.5), ...) and T4 (V SW: V_0' bottom = u0' bottom - (1,1), V_1' = V_0' - (.5,.5), ...): V pair V0-V1 (0.5 link) margin 0.1423; V pair V1-V2 0.0418; V triple, V 4-chain 0.0418; corner pair 0.0418; corner triple V1,V0,u0 0.0801 (T1) / 0.0801 (T4);
corner 4: (V1,V0,u0,u1) 0.0335; (V2,V1,V0,u0) 0.0418; (V0,u0,u1,u2) 0.0335. In all 18 windows S - sum B <= 2.3e-9 (zero excess) and the minimum margin (lo - S - J_e * credit) over every pattern is 0.0335 > 0 (J_e = 0.04939).
(Lower bounds from interval arithmetic as in np_chain/np_corner; levels bottom = 1 - 0.02 (s_c - 4), gap 0.01, which has the order of the final rule.)
## 5. Tiling conditions (Lemma T hypotheses) on the generated layouts (schemetile.py)
Cores = first arm switch of every star + every crossing core (4U + 5V); stretches = maximal plain runs along the edge chain (arm, corner, track, arm), K_3: 7 stretches, K_4: 28, K_{3,3}: 99; minimum plain run r = 5 (K_4, K_{3,3}), 9 (K_3);
every weak link lies in a stretch with 2 <= j <= r-2 (j = 4 or 6, r = 17..218); np_tiling.verify passes on every stretch: no failures. So L1-L5 of NP-HARDNESS 3.1 hold for these layouts; Lemma C then gives rho_dom >= S0 + J_e #uncut for them (the library blocks used by the lower bound are those of NP-HARDNESS 4 plus the 0.5-link windows of section 4; stars with the bus neighbours were certified there).
## 6. Weak solvability by clusters (final rule, kinks at every arm level; Q* analytic, snapped 1e-5, exact-rational flow LP)
| cluster | switches | patterns | result |
| C1 degree-3 bus (V chain + 3 stars with 6-switch NW arms) | 53 | 2 (bus bit) | True/True with kinks at the 3 arm levels (False/True without kinks) |
| C2 one edge: bus - arm (weak link in the tail) - corner T1 - half-link track - corner T4 - arm - bus, no crossing (scheme.build(2,[(0,1)]) with BUS_GAP = 24) | 72 | 4: sat 01, 10; unsat (kinked) 00, 11 | True x4 (after the T4 correction of section 1; before it: True only for 11) |
| C3 single crossing (4U x 9V with neighbours), kink at the U level | 17 | 4 | True x4 |
| C4 U wire crossing TWO parallel V tracks (t = 0 and T) | 30-33 | 8 sat | True (T = 36; T = 24, 18: first three patterns inspected) |
| C5 V track crossed by two U wires, levels 24 apart (V centres 12 apart) | 37 | 8 | True x8 |
| C6 same, levels 12 apart | 31 | 8 | True x8 |
Cost agreement with the closed form in every cluster run: <= 5e-8 (kink library has J_e to 1e-9). Not run: clusters mixing a crossing with arms, corners and buses (an edge crossed by another arm), the whole K_3/K_4 (flow LP too large: 734 / 1916 points);
unsat patterns of the crossing clusters; exact (non-snapped) certificates. For clusters C2 (before the T4 fix) the free-y LP was feasible for every failing pattern, i.e. the failures were geometry, not the y rule; four rule variants (c1, Delta, g, kinks at arms+corners) did not rescue the wrong geometry.

# UPDATE 12 : lower-bound audit, cluster enumeration by radius, y-rule correction, Layout theorem
Files (gad/): audit.py (tilings, relation credits, Lemma C numerics), auditcert.py/auditcert2.py (plain block types + interval certificates, output auditcert2.out), auditcores.py/auditstar.py (core blocks),
auditclus*.py (window enumeration + weak solvability), rulecheck2.py (rule R statistics), plus UPDATE 11 files.
## 1. Lower-bound audit (K_3, K_4, K_{3,3} from scheme.py)
Tilings (audit.py): cores = star core {centre, a_1, SW bus neighbour, NE bus neighbour} and crossing core K (4U+5V); P2 = unenlarged cores + P2 blocks of np_tiling.construct on every plain stretch; P1 = star^+ (+ a_2, SW', NE'), K^+ (+ one plain neighbour on each of the 4 arms) + P1 blocks of np_tiling.construct.
Stretches (plain runs between cores, along arm/corner/track/arm and along bus segments): K_3 13, K_4 40, K_{3,3} 117; plain blocks P1/P2: K_3 136/152, K_4 337/383, K_{3,3} 723/849; star cores 6/12/18; crossing cores 2/11/45.
Block types that occur (24): (a) 20 plain types (sizes 2,3,4; 2580 occurrences): V pair (5,5) [2 level patterns], corner pairs (5,4),(4,5), U pairs with step 2.75, 3, 3.25, 3.5 (strong, credit 2) and 3.75 (weak, credit 1) with several level patterns, U triples (3,3),(3,3.25),(3.25,3),(3.5,3.25),
V triple, U 4-blocks (3,3.75,3.25),(3.25,3.75,3); (b) star core (4), star^+ (7), K (9), K^+ (13).
Certificates: each of the 20 plain types was certified DIRECTLY by the interval dual B&B of np_dual (all 2^n bit patterns, credits 2 J_e strong / J_e weak): S - sum B <= 1.2e-9 and min margin (lo - S - J_e*credits): 0.0000 (weak pairs and the two 4-blocks with the weak link: tight equality, -8e-15),
0.0012 (strong pair step 3.5 and triple (3.5,3.25): small but positive), 0.0531 (step 3.25), 0.1062 (step 3), 0.1153 (step 2.75), 0.0418 (V pair, corner pair), 0.1423 (V pair with the 0.5 link). Overall minimum -8.4e-15 (the tight weak equality, same as in the library).
Core blocks: scheme blocks are EQUAL (geometry up to translation + level order) to the library blocks in all 6+12+18 stars and 2+11+45 crossings (auditcores.py). Certificates: star core (NW,SW,NE) margin 0.0912, star^+ margin 0.0418 (np_star, rerun), K and K^+ from np_cross_table/np_kplus (K^+ margin 0.0364, X_K = 0.12296).
Corner windows incl. the 0.5 link and the corrected far-end corner T4: np_half.out (UPDATE 11), margin >= 0.0335.
NOTE: strong steps 3.25/3.5 pass the block certificates but Corollary M (E_S >= 4 J_e) only holds for step <= 3; for steps 3.25, 3.5 the credit 2 J_e is certified per block (above) instead. The 3.5-step margin is 0.0012: a generator with steps in {2.75, 3, 3.25} only has margin >= 0.0531.
Lemma C numerics (audit.lemmaC): relation weights = average of the two tiling credits (core-internal 1, core-adjacent link 2 in P1 only, plain strong 2 in one tiling, weak 1+1); bus links are charged to the edge of the star they lead to (representative star = middle star of the bus, so each bus link is charged once).
 result: every relation of every edge chain has weight >= 1 (J_e units), every edge has an odd number of ne relations, and min over all vertex patterns (8 / 16 / 64) of [sum_e DP_e(sigma_u,sigma_v)] - #uncut = 0 (never negative),
 where DP_e is the exact minimum over internal bits: so (LB_1 + LB_2)/2 >= S0 + J_e #uncut for every pattern, hence max_j LB_j >= S0 + J_e #uncut (Lemma C) for K_3, K_4, K_{3,3} given the certificates.
## 2. Cluster types by radius (auditclus*.py)
Definition: anchors = star centres, crossing V centres, corner switches (last arm switch = K), left switch of every weak link. Window(anchor, R) = all switches whose box centre is within L-infinity distance R + (d_a + d_b)/4 of the anchor's box centre; cluster type = (anchor kind, canonical form of the window: geometry up to translation + order/ties of the levels).
 R = 8: star 3, crossing 2, corner 6, kink 2 types (K_3,K_4,K_{3,3}), 14-28 switches; R = 13: star 8, crossing 14, corner 13, kink 3 (38 types), 11-45 switches.
 NOT saturating over graphs: adding Q3, Petersen, Prism gives (R=13) star 9, crossing 21, corner 23, kink 12 types (65 with the rest): the free parameters are the tail steps and the offsets of kinks/corners inside the windows. A provably finite list needs the generator to be canonicalised
 (steps exactly 3 within R/3 + 1 switches of every gadget, irregular steps only in the middle of long tails, with a separate list for plain irregular wire windows); this is not done. So: the list below is complete for the six graphs tested, not for the scheme.
 Local patterns: for each type all bit patterns realised by the 2^n vertex patterns (sat and unsat edges); weak solvability at the analytic Q* restricted to the window (a sub-collection of a weakly solvable collection is weakly solvable: reachable sets restrict, so window failures are failures of the global Q* with the same local bits).
 Results with the y-rule of WEAK-SOLV 13 (slope 0.02 + 0.6 at every arm level, linear increments, g = 0.002): R = 8: 34/34 local patterns weakly solvable; R = 13: 113/116, three failures: star window of K_4 (anchor 122, bits of pattern 0000), crossing windows of K_{3,3} (anchor 293).
 They are NOT confined to non-maximum cuts: the failing (type, bits) pairs occur in the K_4 maximum cuts 0110, 1010, 1100 (the cuts 0011, 0101, 1001 have no failing window) and in BOTH maximum cuts of K_{3,3} (000111 and 111000), i.e. this rule does not give a weakly solvable maximum cut for K_{3,3}.
 Diagnosis (auditclus6.py, minimal failing sets, free-y LP feasible): the failing windows lie above 3 kinks, where the local slope is c1 + 3 Delta = 1.82 while the local curvature is Delta = 0.6: relative curvature Delta/slope = 1/3 instead of 30. With local slope 0.02 (or with Delta = 30 * local slope) the same window passes.
 Corrected rule (geometric): the slope is multiplied by rho at every kink (slope_k = c1 rho^k, Delta_k = (rho - 1) slope_k), top-bottom gap g_k = 0.1 slope_k (any smaller gap is also fine), y = 1 + eps eta with eta normalised per window (scale-free).
 With rho = 3, 11, 31: 0 failures of 116 windows (R=13, K_3,K_4,K_{3,3}); rho = 11 on all six graphs: 65 window types, 208 local patterns, 0 failures. (rho = 1, no kinks: 68 failures.) Size: bits of the kinks grow like 2|E| log rho: polynomial.
 Earlier exact-cluster results (UPDATE 11 section 6: bus, edge, crossing clusters) used the linear-increment rule with <= 2 kinks in range and are consistent with this.
 Not done: exact rational certificates of the LPs (all are floating LPs at snapped Q*), whole-layout flow LPs (734/1916/4608 points), windows for plain irregular wire stretches.
## 3. Layout theorem (statement, what is proved, what is checked)
**Theorem (layout).** For every graph G = (V,E) with maximum degree 3 and edges listed as (i<j), scheme.build(G) is computable in time polynomial in |V|,|E| (number of switches O(|E|^2) in the worst case: tracks of length O(|V| 46 + ...), arms of length O(|E|); 367 / 958 / 2304 switches for K_3 / K_4 / K_{3,3}), all coordinates are in (1/4)Z, and:
 (L1) every switch is a library switch (d = 4 or 5) at coordinates in (1/4)Z; (L2) every wire is a path of library links (U strong with steps in {2.75,3,3.25,3.5}, weak 3.75, V steps 1 or 1/2 (the two parity links), corner T1/T4, vertex stars of degree 3 on buses, crossing cores K) and every gadget is one of the 24 block types above;
 (L3) every edge has an odd number of antiferro relations (computed in audit.lemmaC: all edges odd); (L4) exactly one weak link per edge, inside a stretch with 2 <= j <= r - 2 (schemetile.py); (L5) all plain stretches have r >= 5; (L6) levels y = F(s_c) + g_k [top] with the geometric-slope F, all arm levels are kinks;
 (L7) spacing rule R: every conflict of original margin < 2D = 1.2544 (6.43 steps) joins switches whose box centres are within 11 grid units (rulecheck2.py: 7004 / 17933 / 48032 such conflicts, max distance 11.00 in all three layouts), so all other conflicts satisfy R; (L8) distinct arms have s_c differing by >= 24 (relay gap 12 -> 24 in s_c), buses are 28+ apart in s_c, tracks are 54 apart in t.
 Then (a) rho_dom(P,y) >= S0 + J_e #uncut(sigma) >= S0 + J_e (|E| - maxcut) for the vertex bits sigma (Lemma C with the 24 certified block types; numerics above for K_3,K_4,K_{3,3}); (b) the analytic point Q*(sigma) is rho_dom-feasible and has cost exactly S0 + J_e #uncut for every sigma (S0 = sum B + n_x X_K);
 so rho_dom = S0 + J_e (|E| - maxcut(G)) and rho_dom <= theta iff cut >= k.
Proof sketch: (a) Lemma B (drop inter-block conflicts) with the two tilings of Lemma T; each block's value is certified from below by interval B&B with credits; summing and averaging the two tilings gives S0 + J_e sum over relations of the average credit * violation, and the parity of every edge chain
 plus one representative star per bus (each bus link charged to one edge) gives [sigma_u = sigma_v] <= sum of violations along the edge: Lemma C. (b) Q*: every switch at its isolated optimum except crossing cores and kink pairs (stored displacements, X_K = 0.1229644, J_e = 0.0493902); conflicts between switches farther than 11 apart satisfy R, hence hold since each point moves <= D = 0.6272 (Lemma R);
 conflicts between switches within 11 lie in one window of radius 13: feasible by the exact check (all 1.8e6 / 1.05e7 conflict pairs, 0 violations on K_4 / K_{3,3}, min positive slack 0.0417 = 0.21 steps) and, for general G, by translation invariance of the windows (finitely many types once the generator is canonicalised - see section 2).
Confirmations: 8 + 16 + 64 patterns, 0 violations, cost - closed form <= 1.9e-11; lower bound combinatorics (all patterns) exact.
Status / open: (i) the finiteness of window types for ALL G (generator canonicalisation) is not implemented, so (b) for general G is verified only on six graphs for windows and on K_3/K_4/K_{3,3} globally; (ii) weak solvability: cluster-level (116 + 208 windows) with the geometric-slope rule, not a whole-layout certificate and not exact arithmetic; the global gluing of the local cones is the WS agent's task;
(iii) tail steps 3.25/3.5 work only with the per-block credit certificates (0.0012 margin at 3.5); (iv) the 0.5 link needed library certificates (done: np_half, margin >= 0.0335).

# UPDATE 13 : canonical generator, complete cluster-type lists with exact certificates, audits on canonical layouts
Files (gad/): scheme2.py (canonical generator), schemerun2.py (Q* checks), audit2.py + auditcert3.py (Lemma C audit and plain block certificates), enum2.py/enum24.py (window types), exactcert2.py (exact rational certificates), invar.py (invariance tests).
## 1. Canonical generator scheme2.build(n, edges, RE, G)
Differences to scheme.py: (i) strong U steps are exactly 3 within RE steps of every gadget (star, crossing core, corner, weak link); (ii) the only irregular strong steps are 2.75 or 3.25, in ONE run of 12 steps in the middle of the tail of each arm: holder arm (the arm at the smaller vertex, carries the weak step 3.75): d = +3 (three steps 3.25 then nine 3), other arm: d = -6 (six steps 2.75 then six 3);
(the integers follow from p_K = 3c - 3/2: with S steps and h = 1 if the arm holds the weak link, d = 12 (c - S) - 6 - 3h; S_holder = c-1, S_other = c, which also fixes the odd link parity of every edge); (iii) tail = [irregular run][exact pad >= RE]([weak step][RE exact steps] for the holder); (iv) steps alphabet {2.75, 3, 3.25} + weak 3.75;
(v) all spacings are parameters: relay gap G on a bus (arms are then G apart in L-infinity, 2G in s_c), track spacing in t 6 (3 RE + 18), first track at the same value, bus gap 2G + 34. (RE, G) = (6, 16) for windows of radius R = 13, (10, 26) for R = 24 (in both cases RE steps = 3 RE >= R + 5 and G > R).
Sizes (RE,G) = (6,16): K_3 767 switches, K_4 2292 (11 crossings), K_{3,3} 5298 (45), cube 7640 (36), Petersen 11846 (65); (10,26): K_3 1011, K_4 3036, K_{3,3} 7038. Polynomial: O(|E|^2 + |V||E|) switches, arms of length O(|E|).
## 2. Rule for y (corrected in UPDATE 12) and its invariances
Kinks at the s_c of every arm; the slope of F (decreasing toward NE) is multiplied by rho at each kink (rho = 11; 3 and 31 also pass), gap of a switch at s_c = s: g(s) = (1/10) * slope on (s-1, s); y = 1 + (3/10) (F + g [top]) / max.
Order: since F(s) - F(s') >= slope on (s'-1, s') > g(s') for all s < s', the conflict set of this y equals that of the surrogate bottom = -s_c, top = -s_c + 0.1 (used for all dominance computations; no huge numbers); ties are the equal-s_c ties.
Bit size: the slopes are integer powers rho^k, k <= number of arms = 2|E|; a level is a sum of at most (s-range) such terms: O(|E| log rho + log(size)) bits, i.e. about 3.5 * 2|E| + O(log) bits for rho = 11: polynomial.
Invariance (item 4). C(Q) is a convex cone containing the all-ones vector (the set of all points is weakly reachable). Hence (a) y in C => a y in C (a > 0), (b) y in C => y + b 1 in C (b >= 0), (c) if 1 + e0 eta in C then 1 + e eta in C for 0 <= e <= e0 (convex combination of 1 and 1 + e0 eta).
The global y restricted to a window is c0 (1 + e_w eta_loc) with c0 = 1 + e F_hi / F_max > 0 and e_w <= e: F_hi is the (huge) offset of F at the window's NE end and eta_loc = (F_loc + g tau)/max uses only the slopes inside the window, i.e. only the ratios rho and g/slope. So the local cone condition for the global y follows from the window certificate at e0 = 0.3 with eta_loc normalised to the window: this is what makes the type list finite despite the growing slopes.
It is NOT invariant under shifts down (y - b 1): numerical test on all 49 R = 13 type representatives (invar.py): eps = 0.3, 0.03, 0.003, 1e-4: 49/49 weakly solvable; scale 1e-3, 1e3: 49/49; y + 0.5, y + 5: 49/49; y - 0.99 min y: only 19/49.
## 3. Complete lists of window types and exact certificates (anchors: star centres, crossing V centres, corners (K), weak-link left switches, every arm switch from 2 before the end of the head to the corner ("tail"); window = box centres within L-infinity R + (d_a + d_b)/4)
Finiteness (structure): with RE >= (R + 5)/3 and G > R every window of radius R contains one anchor gadget and only wire pieces whose step sequences are fixed: exact 3-steps, the two fixed irregular runs, the pad, the weak step, bus/track V steps 1, the two 0.5 links at the ends of a track; other gadgets are at distance >= G or >= RE steps (crossings on one track are G apart, crossed arms and tracks are >= 6(RE) in t apart);
the remaining freedom is the combinatorial environment within the window (number of arms of the star: 1, 2 or 3, position of the star on the bus, whether a crossing core lies within R of a corner, bus ends), a finite set. Enumeration (enum2.py / enum24.py) over 13 graphs
(P3, K_{1,3}, C4, C5, K_3, K_4-e, theta, bull, K_4, prism, K_{3,3}, cube, Petersen; all vertex patterns up to 300 samples each): 
 R = 13 (RE=6,G=16): 49 types after the first two graphs, unchanged by the other eleven: star 4, corner 2, kink 1, tail 40, crossing 2; 120 (type, local bit pattern) pairs. 
 R = 24 (RE=10,G=26): 134 types (star 4, corner 3, kink 1, tail 124, crossing 2), saturated from K_4 on (prism, K_{3,3}, cube, Petersen add none); 306 (type, bits) pairs.
(The enumeration is by saturation plus the structural argument above, not by a mechanical enumeration of the descriptor space.)
Exact rational certificates (ws_exact2: exact simplex + planar.is_reachable, Q = exact value of the snapped doubles, y exact rational of the rule): R = 13: 120/120 EXACT for rho = 11 (also rho = 3 and 31), largest window 42 switches, <= 13 s each; R = 24: 306/306 EXACT for rho = 11, largest window 72 switches, <= 97 s each.
Each window is a sub-collection of the global layout, with its local bit pattern, taken from the analytic Q* of the layout (displacement of Q* is local).
## 4. Audits on the canonical layouts
Q* (all conflict pairs, tolerance 1e-7; surrogate levels): (RE,G) = (6,16): K_3 8 patterns (1.1e6 conflicts), K_4 16 (1.0e7), K_{3,3} 64 (5.5e7), cube 22 sampled patterns (1.15e8), Petersen 12 sampled (2.8e8): 0 violations in all, cost - closed form <= 3.3e-10, min slack -5.7e-14 (ties).
(10,26): K_3, K_4, K_{3,3} (all patterns; up to 9.8e7 conflicts): 0 violations, cost deviation <= 3.5e-10.
Lemma C audit (audit2.py, both parameter sets): K_3, K_4, K_{3,3}, cube (256 patterns), Petersen (1024 patterns): every edge odd, every edge-owned relation has average credit >= J_e (0 exceptions), min over all patterns of [sum_e DP_e - #uncut] = 0.0 (never negative); all star cores, star^+, K, K^+ blocks equal the library blocks (6+12+18+24+30 stars, 2+11+45+36+65 crossings).
Plain block types: only 13 distinct types occur (down from 20), sizes 2-4, all certified by direct interval B&B (auditcert3.py): U pairs with step 3 (margin 0.1062), 2.75 (0.1153), 3.25 (0.0531), weak 3.75 (tight, +7.8e-10), V pairs/triples/corner pairs 0.0418 and 0.1423, U triple (3,3) 0.1062, the 4-block (3,3.75,3) tight (+7.8e-10 overall minimum). The step 3.5 of UPDATE 12 no longer occurs.
## 5. Status
Done: canonical generator, complete (by saturation + structure) type lists at R = 13 and R = 24, exact rational certificates for every (type, bit pattern) with rho in {3, 11, 31} (R = 13) and rho = 11 (R = 24), Lemma C and Q* audits on five canonical graphs.
Open: (i) the finiteness of the type list is argued structurally and confirmed by saturation over 13 graphs, not enumerated mechanically over the descriptor space; (ii) the whole-layout weak solvability still needs the WS agent's lifting theorem (clusters = slabs, G1/G2 with context) - the windows here are the local certificates; the far-field (NW/SE) lemma is not proved;
(iii) windows are certified at the analytic Q* after snapping coordinates that agree within 1e-5 to exact ties (as in WEAK-SOLV 9); I did not check that snapping merged only intended ties, nor that the snapped Q is still rho_dom-optimal to 1e-9; (iv) radius R fixed by the WS agent is unknown to me: both 13 and 24 are provided.

# UPDATE 14 : window descriptor space of scheme2 (exhaustive by construction), exact certificates for every descriptor, snapping audit
Files (gad/): scheme2.py (now build(n, edges, RE, G, RW) with BUS_GAP = 2G + 2RW + 34), descW.py / descW_all.py (descriptor enumeration on a witness layout), descCheck.py (comparison with graph-derived types), exactcertW.py / exactcertW2.py (exact certificates), snapaudit.py / snapcost.py (snapping audit).
## 0. Parameter condition and a correction to UPDATE 13
UPDATE 13 used (RE,G) = (6,16), (10,26): with G only 3 and 2 above R the windows of radius R (box-centre distance <= R + (d_a+d_b)/4 <= R + 2.5) touched the next star/crossing/corner at the window boundary, which produced spurious extra types (2 crossing types, 134 types at R = 24). Condition (P): G >= R + 6, 3 RE >= R + 11, BUS_GAP = 2G + 2R + 34 (so every track has N >= 2R + 34 V steps), track spacing 3RE + 18 in c.
(RE,G) = (8,20) for R = 13, (12,32) for R = 24. All results below are for these parameters (K_3, K_4, K_{3,3} Q* and Lemma C audits were re-run: see section 5).
## 1. Descriptor space, with lemmas from the code paths of scheme2.build
Lemma B (bus). Bus v has V switches (d=5) at bottoms (k - 1/2, k - 1/2) for k in [min kr - 5, max kr + 5], stars (centres) at k = K_v + G r (r = rank of the incident edge, r < deg(v) <= 3); K_{v+1} - K_v = BUS_GAP. Hence two stars of one bus are G apart (L-infinity G > R + 2.5), the bus ends 5 switches beyond the first/last star, and buses are >= 2R + 24 apart.
Lemma A (arms). Arm of edge e at star (u,k): a_1 = (k-3, k+3), steps = [3]*head + tail; head = c_top + 1 + RE (c_top = level index of the topmost crossed track) or RE + 1 (no crossing); tail = [irregular run of 12] + [pad] (+ [weak 3.75] + [RE steps of 3] for the holder); irregular run = three 3.25 then nine 3 (holder, d = +3) or six 2.75 then six 3 (other arm, d = -6)
 (d = 12 (c - S) - 6 - 3h with S_holder = c - 1, S_other = c); pad_holder = (c - 1) - head - 12 - (1 + RE) and pad_other = c - head - 12, where c - head = WC a - RE - 1 (WC = 3RE + 18, a >= 1 integer: a = e + 1 without crossings, a = e - e_top with crossings); hence pad_min(holder) = WC - 2RE - 15 = RE + 3, pad_min(other) = WC - RE - 13 = 2RE + 5, and + WC per unit of a.
 All arm steps before the tail start are exactly 3; the first RE steps after the last crossing core are exactly 3; the weak step is >= 3 RE + 9 L-infinity from the irregular run and RE steps from K.
Lemma T (track). Track of e: V_0 = K (shares the bottom of u0), V_m = K + (m - 1/2)(1,1) for 1 <= m <= N-1, V'_0 = K + (N-1)(1,1) (shares the top corner of u0'); N = k_j - k_i >= 2R + 34; only the two links V_0-V_1 and V_{N-1}-V'_0 have step 1/2.
Lemma X (crossing). Arm f crosses track e iff T_e < T_f and k_i(e) < k_f < k_j(e); V centre = V_m, m = k_f - k_i(e) >= G (arms of one bus are G apart, other buses >= BUS_GAP - 2G); N - m >= G; arm f is in its head there (exact 3-steps, c_top >= c_e) and the arm switches at V_m + (2,-1) + mm(-3,3), mm = -1..2 exist (assertion in build). Two crossings on one track are >= G apart; two crossings on one arm are >= WC 6 / 2 > R apart in t.
Lemma W (window content). Under (P) a window of radius R around any switch of the layout contains (i) pieces of at most ONE wire direction per gadget it touches, the gadgets being: a star with its bus and arm (bus ends at distance 5 or the bus continues), a crossing core with the arm and the track, a corner (T1: V NE of K, T4: V SW of K') with arm and track start (half links), a weak step with its two exact neighbours, plain wire; (ii) no second gadget: stars/crossings/corners of the same wire are >= G, tracks of different edges >= 6 WC / 2 in t, parallel arms of different edges >= G in L-infinity.
 (iii) the plain-wire step sequence inside the window is a substring of: head (all 3) . I(role) . pad . [weak . 3^RE] . K (corner), with pad in {pad_min, pad_min + WC, ...}; pad >= pad_min + WC exceeds the window length (about 2 (R+3)/3 + 1 steps): windows see at most one boundary of a pad, so pad in {pad_min, 'large'} is exhaustive.
 So the descriptor space is: anchor position (every switch) in { star (deg d, rank r: bus ends (L,R) in {end,cont}^2: realised by (1,0),(d>=2,0),(d>=2,d-1),(3,1) }, arm head, crossing neighbourhood, I-run (2 roles), pad (2 classes), weak neighbourhood (holder), end of tail / corner (T1 or T4), track (start half-link, interior, end half-link, crossing neighbourhood), bus (end, interior) } x local bit pattern (one free phase bit per chain crossing the window, plus the kink bit of a weak step inside the window).
## 2. Exhaustive enumeration by construction (descW.py, descW_all.py)
Witness layout W = disjoint union (contiguous in the bus order, so no track spans another component's buses) of K_{1,3} (stars of degree 3 at ranks 0,1,2 and degree 1), P3 (degree 2 at ranks 0,1), X = {(a,c),(b,d)} with bus order a<b<c<d (a crossing; arms with a crossing before the head, pad minimum), D x 2 (disjoint edges after other edges: arms without crossings with edge index >= 1: pad 'large').
Every descriptor of Lemma W is realised in W (the roles holder/other and the two pad classes occur at e = 0 and e >= 1, the crossing in X, star ranks in K_{1,3} and P3). Local bit patterns: all vertex patterns of the component (each window lies in one component).
 Gadget anchors (stars, crossing V centres, corners, weak steps, tail switches): R = 13: 50 types (star 4, crossing 1, corner 2, kink 1, tail 42), 120 (type, bits) pairs; R = 24: 68 types (star 4, crossing 1, corner 2, kink 1, tail 60), 172 pairs.
 EVERY switch as anchor (covers windows centred anywhere): R = 13: 7355 windows, 199 types, 522 (type, bits) pairs; R = 24: 9663 windows, 338 types, 922 pairs.
Comparison with graph-derived windows (descCheck.py, gadget anchors, 13 graphs P3, K_{1,3}, C4, C5, K3, K4-e, theta, bull, K4, prism, K33, cube, Petersen, up to 300 vertex patterns each): types NOT in the witness set: 0 (R=13 and R=24), local bit patterns not in the witness set: 0, witness types not seen in the 13 graphs: 0.
So the witness set equals the saturated graph-derived set; the list of UPDATE 13 (49 / 134) is superseded.
## 3. Exact certificates
Exact simplex + exact planar.is_reachable, Q = exact value of the snapped doubles, y exact rational (rho = 11, g(s) = (1/10) slope(s-1,s), eps = 3/10, kinks = arm levels inside the window; local normalisation, see UPDATE 13 section 2): 
 gadget anchors: R = 13: 120/120 EXACT for rho = 3, 11, 31 (largest window 41 switches, <= 14 s); R = 24: 172/172 EXACT for rho = 11 (71 switches, <= 78 s);
 every-switch anchors: R = 13: 522/522 EXACT (rho = 11; 41 switches, <= 14 s); R = 24: 922/922 EXACT (rho = 11; 71 switches, <= 79 s).
## 4. Snapping audit (snapaudit.py, snapcost.py)
Unsnapped Q* = isolated optima + stored library displacements. For every coordinate, all pairs of points with |difference| < 1e-4 were listed (all patterns of K_3, K_4, K_{3,3} at (8,20), and all 68 component patterns of the witness layouts W at R = 13 and R = 24).
 Gap: the differences fall in [0, 1e-12): 29725 / 282672 / 4533256 (K_3, K_4, K_{3,3}), 2.8e6 / 3.2e6 (W), and [1e-12, 1e-9): 194 / 3208 / 74448 / 7330 / 6014; NO pair in [1e-9, 1e-4). So snapping at 1e-5 merges exactly the numerically equal pairs and nothing else; the maximal coordinate shift is 5.4e-10.
 Classes of the merged pairs: (a) top and bottom of one switch (equal split: structural, own pair) ; (b) pairs with a conflict (different levels) whose slack in that coordinate is < 1e-5: tight constraints of the optimum; (c) same-level pairs of different switches: ALL are two switches of one crossing core (11520 / 704 / 64 in K_{3,3} / K_4 / K_3, 1088 in W); there are no unclassified pairs,
 and no pooled-kink pairs coincide. The (c) ties come from the stored core optimum: e.g. the displacement of the middle U switch is +3.0 (bottom) in its bit coordinate, which makes it coincide with the unmoved bottom of the neighbouring core switch: displacements 3, 1, 2, 2.5 are integers (tight chains), the pooled pair carries the transcendental split (1.2136946, 2.7863054).
 Accidental merges: none found (every merged pair is in a structural class and, by the gap, the true separations are 0 to 1e-9, i.e. the optimum has ties or numerically indistinguishable values there). Consequence for the logic: the exact certificate concerns the rational point Q_snapped, which is a genuine candidate point; its cost differs from the unsnapped Q* by <= 2.7e-9 (K_3, K_4, K_{3,3}, 16 patterns each) and
 with tolerance 0 the float conflict check of Q_snapped has no violation for K_3 and K_4 and 12 rounding-level violations (min slack -5.6e-17) for K_{3,3}; exact feasibility of Q_snapped is what the exact weak-solvability certificates prove (Lemma 0).
 Not done: exact (non-snapped) certificates; a proof that the exact optimum has the integer displacements (3, 1, 2.5) listed above (they are tight-chain consequences; the numerical library has them to 1e-10).
## 5. Re-run of the layout audits at the new parameters (8,20)
Q* with all conflicts: K_3 8 patterns (1.9e6 conflicts), K_4 16 (1.6e7), K_{3,3} 64 (9.2e7): 0 violations, cost deviation <= 3.4e-10. Lemma C audit (audit2.py 8 20): K_3, K_4, K_{3,3}, cube (256 patterns), Petersen (1024): every edge odd, no relation below average credit J_e, min over all patterns of the Lemma C slack = 0.0; stars and crossings equal to the library blocks; 13 plain block types (as in UPDATE 13).
## 6. Status / open
Done: explicit descriptor space with code-path lemmas, exhaustive enumeration on a witness layout, equality with the saturated graph-derived set, exact certificates for every enumerated (type, bit pattern) at R = 13 and R = 24, snapping audit with a clean gap and a structural classification of every merged pair.
Open: Lemma W is argued from reading the code, not machine-checked; the 'local bit patterns' are those realised by intended Q* (every window with a kink inside is realised, windows at unsatisfied edges included); windows are certified at Q* with snapped ties; whole-layout weak solvability needs the WS agent's lifting theorem (G1/G2 with the far field); the radius required there is still unknown.
