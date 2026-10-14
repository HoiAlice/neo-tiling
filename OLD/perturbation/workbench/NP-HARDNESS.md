# NP-hardness of PERT-2 (additive perturbation, d = 2): assembled proof and status

Scripts: `gad/np_*.py` (this document), outputs `gad/np_*.out`. Python: project `.venv`.
Formal problem: `perturbation/lean/Perturbation/Decision.lean` (`Decide P y theta`), `NeoTiling/Closure.lean` (`WeakSolvable`, `IsWeakReachable`, `weakSolvable_iff`).
Other agents' notes cited: CROSSING-GADGET.md (CG, UPDATE 1-7), CROSSING-PROOF.md (CP), P-GAP.md, LOCALITY.md (LOC), WEAK-SOLV.md (WS), GADGET-D2.md.

## 0. Verdict (read this first)

**Theorem (target).** MAX-CUT on graphs of maximum degree 3 is polynomial-time many-one reducible to PERT-2; hence PERT-2 is NP-hard.

What this document establishes:

* The reduction is written down completely (Sec. 3), and its correctness is reduced, by proofs given here, to the following finite list of
  facts, each classified in Sec. 8: (L) a layout generator with properties L1-L8, (G) a finite library of block certificates, now **interval-certified at a
  rational price step** (Sec. 5), (R) a spacing rule, and (WS) one weak-solvability hypothesis.
* **The lower-bound direction (G has no cut of size >= k  =>  PERT-2 answers NO) is a proof modulo the library certificates (G) and the layout properties (L).**
  Weak solvability is not used there. (Sec. 6, Thm LB.)
* **The upper-bound direction (a cut of size >= k  =>  YES) is conditional on (WS) and on (L)+(R)+cluster gluing.** (Sec. 7, Thm UB.)
* **(WS) is NOT proved.** It is verified numerically on four instance families (25 switches, K_3, a relay chain, two far-apart copies of the 25-switch instance) and has a partial theory (WS Sec. 11-12), but there
  is no argument that covers an arbitrary layout. Also **(L) is not complete**: the generator (gad/layout.py) produces no crossings yet, and the K_4 layout it found
  (77 switches) has no verified rho_dom table. So **the NP-hardness claim is NOT yet a proof**; this document is the proof with the remaining gaps isolated and labelled.

Closed in this session (new, with scripts): (i) tiling existence for wire stretches of arbitrary length with an explicit construction (Lemma T); (ii) exact degeneracy of
the crossing by symmetry alone, with NO MILP certificate (Prop. X: for the layout's order pattern the conflict set is exactly P-symmetric, `gad/np_pgap.py`);
(iii) all block certificates redone with a rigorous interval-arithmetic branch-and-bound (`np_dual.py`) at a RATIONAL price step, replacing the tangent-cut grid; the grid error
issue disappears (Sec. 5.1); (iv) closed forms for the weak and strong link excess; (v) Lemma M (matching bound), which reduces all U-wire block certificates to two pair facts;
(vi) interface additivity of the crossing core with its neighbours with slack >= one grid step (`np_glue.py`).

## 1. Conventions

Points `t` have two coordinates; `pert(p,q) = max(q/p,p/q) - 1 = exp(|ln q - ln p|) - 1`. Work in log coordinates `x = ln Q`, `a = ln P`; the cost of a point is `f(x-a)` with `f(u) = e^{|u|} - 1` per coordinate.
A **switch** `s` has a bottom point `b_s` and a top point `t_s = b_s + (d_s, d_s)` in grid units, with levels `y(t_s) = y(b_s) + g`.
`h > 0` is the log-length of one grid step. **Rational prices:** fix `rho = 21/20` and `h = 4 ln rho = 0.1951606567`. All coordinates are in `(1/4) Z`; a point with grid coordinate `m/4` gets price `rho^m`
(rational, bit length `O(m)`). All numerics below are for this `h`. (CG used `h = 0.2`; the numbers move by ~2-5%, e.g. the crossing's V-break is 0.0858 instead of 0.0902.)
Closed forms (exact): `e^{h} = rho^4`, `e^{h/2} = rho^2`, `e^{h/8} = sqrt(rho)`.

A **conflict** is an ordered pair `(a,b)` with `y_a > y_b`. Feasible `Q` for **rho_dom**: for every conflict some coordinate `i` has `Q_{a,i} <= Q_{b,i}`. `rho_dom(P,y) = inf cost`.
For feasible `Q` the **bit** `sigma_s in {0,1}` of switch `s` is a coordinate with `Q_{t_s,sigma} <= Q_{b_s,sigma}` (fix one if both hold).

**Lemma 0 (domination).** If `WeakSolvable Q y`, `y >= 0`, `y_a > y_b`, then some `i` has `Q_{a,i} <= Q_{b,i}`. Hence `rho >= rho_dom`.
*Proof.* By `WeakSolvable.mem_indicatorCone` (d = 2), `y = sum_S m_S 1_S` with `m_S >= 0`, `S` weakly reachable. Suppose `Q_a > Q_b` strictly in both coordinates. If `S` is reachable and `a in S`, take `xi >= 0, xi != 0` with
`xi . (Q_s - Q_a) >= 0` for all `s notin S`; if `b notin S` then `xi . (Q_b - Q_a) < 0`, contradiction; so `b in S`. Thus `1_S(a) <= 1_S(b)` for every reachable `S`, hence `y_a <= y_b`. Contradiction. QED (by hand)

**Lemma 1 (own pair).** For a switch with box size `d` and `delta = d h`, any feasible `Q` has cost of `{t_s, b_s} >= B(d) := 2(e^{delta/2} - 1)`, with equality iff `t_s` moves by `-delta/2` and `b_s` by `+delta/2` in the coordinate `sigma_s` and nothing else moves.
*Proof.* Needed: `x_t <= x_b` in coordinate sigma where `a_t - a_b = delta`; with `u = a_t - x_t`, `v = x_b - a_b`: `u+v >= delta`, `f(u)+f(v) >= 2 f((u+v)/2) >= 2 f(delta/2)` (convexity, monotonicity of `f` on `[0,inf)`); the other coordinate costs >= 0. QED (by hand)
Numbers: `B(4) = 2(rho^8 - 1) = 0.9549109`, `B(5) = 2(rho^10 - 1) = 1.2577893`. `S0` below uses only these.
Both values of `sigma_s` have the same cost: this is the Ising spin.

## 2. The gadgets and the closed-form link excesses

All gadgets are from CG; I restate only what is used.
* **U wire** (antiferro): `d = 4` switches with bottoms on an anti-diagonal, consecutive centres offset `(a, -a)`, all with the same two levels (ties). **Strong link** `a = 3` (grid gap `4 - a = 1`); **weak link** `a = 3.75` (gap `1/4`).
* **V wire** (ferro): `d = 5`, consecutive bottoms offset `(1,1)`, levels strictly decreasing toward NE.
* **corner** (V-end next to the first U switch, `eq` relation), **vertex star** (centre `d = 5` switch with up to four arms: NW/SE antiferro U attachments `a = 3`, SW/NE ferro V neighbours; the *star core* is the centre plus the first switch of each arm, `star^+` adds the second switch of each arm; both `star` (`np_star_core.out`, margins >= 0.0912) and `star^+` (`np_star.out`, `np_star_deg2.out`, margins >= 0.0418) are certified for degrees 2, 3, 4; in the scripts `star^+` = centre + two switches per arm), **relay** (a degree-2 star), **crossing core K** (4 U + 5 V switches, V centred at the midpoint of the two middle U switches), see CG Sec. 2, UPDATE 2, 7.
* **Relations.** A relation `(i,j,eq|ne)` between consecutive switches of a wire says `sigma_i = sigma_j` (V link, corner) or `sigma_i != sigma_j` (U link, weak link, vertex-U link). Inside `K` two relations: V_in = V_out (`eq`), U_in != U_out (`ne`).
* **Levels** `y = F(s_c) + g [top]`, `s_c = x+y` of the switch centre, `F` strictly decreasing (CG UPDATE 6, WS Sec. 11-12). `rho_dom` depends only on the strict order and ties of the levels, so the conflict set of any block is determined by the geometry once the order types of CG UPDATE 6 hold.

**Prop. P (pair facts, exact).** For two U switches at step `a` (all four conflicts `(t_i, b_j)`), with both bits equal the pair costs `2B + J(a)`, `J(a) = 2(e^{(4-a)h/2} - 1)`; with different bits it costs `2B`. In particular
`J_e := J(3.75) = 2(e^{h/8} - 1) = 2(sqrt(rho) - 1) = 0.0493901532` and `E_S := J(3) = 2(e^{h/2} - 1) = 2(rho^2 - 1) = 0.2050000000`, and `E_S >= 4 J_e` (`e^{4x} - 1 = (e^x - 1)(1 + e^x + e^{2x} + e^{3x}) >= 4(e^x - 1)`, `x = h/8`).
*Proof.* Routings: each of the four conflicts is routed through x or y. *Natural class:* own pairs through their bit coordinates, `(t_0,b_1)` through x (gap `-(4-a)h` closed by the own moves iff the bits make it so) and `(t_1,b_0)` through y. The x- and y-problems separate; for equal bits (x,x) the x-problem is two own pairs (cost `2B`, and `(t_0,b_1)` holds automatically), and the y-problem is a single constraint `y_{t_1} <= y_{b_0}` with gap `gamma = (4-a)h`, whose minimum is `2 f(gamma/2) = 2(e^{gamma/2}-1)` (same convexity argument as Lemma 1). For different bits both cross conflicts are closed by the own moves (`delta/2 = 2h >= gamma`), cost `2B`. *All other routing classes:* interval-certified lower bound, `gad/np_pair_classes.out`: every non-natural class has excess `>= 0.255` (`a = 3`) / `>= 0.400` (`a = 3.75`) over `2B`. QED
(Natural class: by hand. Other classes: finite computer certificate, interval arithmetic, Sec. 5.)

**Lemma M (matching bound).** For any block `B` (set of switches) and any bit pattern `tau`:
`m_B(tau) >= sum_{s in B} B_s + max_M sum_{(i,j) in M} e_{ij}(tau_i, tau_j)`, where `m_B(tau)` is the minimum cost of the points of `B` over all routings with own bits `tau` of the conflicts inside `B`, `M` ranges over sets of disjoint pairs of switches of `B`, and `e_{ij}` is the excess of the isolated pair (`m_{ij}(tau_i,tau_j) - B_i - B_j >= 0`).
*Proof.* Drop all conflicts except the own pairs and the conflicts inside the pairs of `M`; the cost then splits over the pairs of `M` and the remaining switches (Lemma 1). Dropping constraints only lowers the minimum. QED (by hand)
**Corollary M.** In a U chain (strong `E_S >= 4 J_e`, weak `J_e`) with credits `2J_e` per strong and `J_e` per weak relation, `m_B(tau) >= sum B + sum credits * viol` for every block. *Proof.* Among the violated links of a run of `k` consecutive violated links pick every other one (avoiding the weak link when `k` is even); each picked strong link gives `>= 4J_e`, the weak `J_e`; a case check over `k` and the position of the weak link gives `>= 2J_e (#strong) + J_e [weak]` (equality only for `k` odd with the weak link picked). QED
So **every U-wire block certificate (any chain length, weak link anywhere) follows from Prop. P.** V chains and corners have break `0.1406 < 4 J_e`, so they need the chain certificates of Sec. 5.

## 3. The construction

Input: a graph `G = (V_G, E)`, max degree 3, integer `k`. Output `(P, y, theta)`.

**3.1 Layout.** Rotated coordinates `(s, t) = (x+y, y-x)`: a U wire is a segment `s = const`, a V wire is a segment `t = const`, a corner is a bend, a crossing is a U wire meeting a V wire.
So a layout is an orthogonal drawing in the `(s,t)` plane. Every original edge `e = {u,v}` becomes **two corner segments joined by a relay**: `u` -- (U arm, corner, V chain) -- relay `r_e` -- (U arm, corner, V chain) -- `v`.
Orient edges so each vertex has out-degree (number of U ports used) `<= 2` and in-degree `<= 2` (exists for max degree 3); an edge `u -> v` uses a U port at `u`, a V port at `v`, and at the relay a V port toward `u` and a U port toward `v`.
Reason for relays: a corner edge has `|ds| = 2n+1` odd (n integer number of V steps), so triangles of corner edges are parity-obstructed (CG UPDATE 6); two corner edges per original edge give even total `ds`, so one parity class of `s` for all original vertices (CG UPDATE 7, relay verified).
Placement: original vertices on a diagonal at spacing `D`, edge `e` gets private horizontal and vertical tracks (distinct values), all coordinates multiples of the module `M` (large integer) up to the fixed gadget offsets. Crossings are then transversal U x V crossings, each realised by the crossing core K aligned as in CG Sec. 2.
Exactly one weak link per edge, in the middle of a U segment of that edge; link counts per U segment chosen with total number of antiferro relations per edge odd (steps in `[2.6, 3.5]`, weak `3.75`; any `L >= 20` admits two consecutive link counts).
Size: `O(|V|)` vertices and relays, `O(|E|^2)` crossings, `O(|V|)` wire length in modules; polynomially many switches, coordinates `O(poly)`.
**Status of Sec. 3.1: (L), pending numerics: `gad/layout.py` (it currently emits no crossings; K_4 with one relay is generated, 77 switches, rho_dom NOT verified; CG UPDATE 7).** The explicit scheme above is a plan, not a verified generator.

**Layout properties used by the proofs.**
* L1 (grid, library): all bottoms in `(1/4)Z^2`, all switch types and neighbourhoods are in the library of Sec. 5.
* L2 (relation graph): every wire is a path of switches; each relation is one of the library relations; vertex stars have `<= 3` arms; cores are crossings and stars.
* L3 (parity): along each edge the number of `ne` relations (counting the U passage of a crossing as one) is odd.
* L4 (weak): exactly one weak link per edge, with at least one plain switch on each side and not adjacent to a core.
* L5 (stretches): every maximal run of plain switches between two cores has `r >= 2` switches.
* L6 (levels): `y = F(s_c) + g[top]`, `F` as in WS Sec. 12 (concave piecewise linear, slope `>= 2g` everywhere, increase of the slope `>= 5g` at every crossing level, corner slope `> g`).
* L7 (spacing R): Sec. 7.2.
* L8 (WS spacing): copies of crossings far apart in `s` (WS Sec. 12.3: `2D >= 48` works, `<= 40` fails for two copies).

**3.2 Prices and levels.** Price of a point with log-coordinate `m/4` grid units: `rho^m`. Level of a switch centre `s_c`: `L0 - F(s_c)`-type rational, top `= +g`, with `g = 0.01 * (unit)`; `y = 1 + eps*eta` normalised (`eps` small, WS Prop 2: ratio `max/min < 2` is automatic, only order, ties and relative gaps matter).

**3.3 Threshold.** `S0 := N_4 B(4) + N_5 B(5) + n_x X_K`, where `N_d` = number of switches of size `d`, `n_x` the number of crossing cores, `X_K := m_K(sat) - sum_{s in K} B_s = 0.1229644` (Sec. 5.2). Stars, corners and wires have zero excess (Sec. 5).
`theta := S0~ + J~ (|E| - k) + J~/2`, with `S0~, J~` rational approximations of `S0`, `J_e` within `2^{-poly}` (computable from `rho` by series for `exp`; `J_e = 2(sqrt(rho)-1)`, `B(d) = 2(rho^{2d} - 1)` are algebraic; only `X_K` is a computed constant, it is a fixed number, known to 1e-8).
The additive slack `J_e/2 = 0.0247` dwarfs the approximation error.

**3.4 Parity and link counts (Lemma P) and how it combines with Lemma T.**
Along the wire of an original edge `e = {u,v}` (through its relay) the relations are: `ne` for every U-type link (strong, weak, vertex/relay-to-U-arm link, and each of the 3 links inside a crossing core on the U wire; the core relation `U_in != U_out` is their composition and has the same parity), `eq` for every V-type link (V chain, vertex/relay-to-V-arm link, V passage of a crossing) and for every corner link. A relay is an ordinary switch with two arms: its two incident relations are of the types of its arms, so a relay copies the bit across a V arm and inverts it across a U arm; nothing else is needed.
**Lemma P.** If all relations on the wire of `e` are satisfied then `sigma_v = sigma_u + N_e (mod 2)`, `N_e` = number of U-type links on the wire (all U segments of the edge, crossings included, weak link included). Conversely if `N_e` is odd and all relations are satisfied then `sigma_u != sigma_v`, and if `sigma_u = sigma_v` at least one relation is violated. (Induction along the path.) QED
**Generator rule (parity).** Choose, for every U segment of length `len` (in units of one strong step), a link count `l` with `2.6 l <= len <= 3.5 l`; for the segment holding the weak link `len = 3.75 + (l-1) step`, `step in [2.6, 3.5]`; crossing aligned links are exactly 3 strong steps inside the 4 core switches, so the remaining `len - 9` is split into `l - 3` free links. For `len >= 20` (resp. `len - 9 >= 20`) the admissible set of `l` contains two consecutive integers (its width `len (1/2.6 - 1/3.5) >= 2`), so the parity of `l` is free; the generator fixes the parity of the last U segment of each edge so that `N_e` is odd. All segment lengths are multiples of the module `M >= 20`, so this is always possible. (For the corner offsets: a corner segment has `ds = +-(2n+1)` odd, two per edge through a relay give an even total, which is what makes all original vertices lie in one `s`-parity class, CG UPDATE 6-7.)
**Combination with Lemma T.** Lemma T is about the *blocking* of the relation path, not about its parity: it needs only `r >= 2` plain switches between consecutive cores (a core = crossing core, star core, relay star) and, for the segment with the weak link, `2 <= j <= r-2`. Since the weak segment has `l >= 3` links on a stretch of `r = l - 1 + (\text{other links})` plain switches, choose the weak link in the middle of its stretch and require `len >= 20`; then `r >= 6` and `j` is in range, whatever the parity of `l`. Hence parity (fixed by the last segment) and tiling (needs only lengths) do not interact: all three conditions are "lengths `>= 20 M`-scaled" conditions on the generator.

## 4. Library (finite block types) and what each fact needs

| Block | Relation credits (units of `J_e`) | Source of the certificate |
|---|---|---|
| U pair strong / weak, any U chain, weak anywhere | 2 / 1 | Prop. P + Corollary M (hand) |
| V pair, V chain of 3 or 4 | 2 each | `np_chain.out` (interval B&B) |
| corner windows (V1,V0,u0,u1 etc.) | 2 each | `np_corner.out` |
| vertex-U pair | 2 | `np_lib.out` |
| crossing core K (9) | V `eq` 1, U `ne` 1 | `np_cross_table.out` |
| K^+ (13) | K: 1, neighbour links 2 | `np_kplus.out` |
| stars, degree 2 / 3 / 4, with outward neighbours | star links 1, outward 2 | `np_star.out` |

## 5. Certificates (finite computer facts)

### 5.1 Method and why the grid error is gone
`gad/np_dual.py`. For a fixed routing the problem is a separable convex program over a DAG order. Weak duality: for any `lam >= 0` on the routed conflicts,
`cost >= D(lam) = sum_v [ g_v a_v + phi(g_v) ]`, `g_v` = net multiplier at `v`, `phi(g) = |g| - 1 - |g| ln|g|` for `|g| > 1`, else 0 (no conservation constraint needed; the primal point is `x_v = a_v - sign(g)ln|g|`).
`D` is evaluated in **interval arithmetic** (mpmath `iv`, 60 digits) at rationalised `lam`, so every number below is a rigorous lower bound (trusting mpmath's interval `log`/`exp`).
A branch and bound over unassigned conflicts (relaxation = drop them; branch on the most violated conflict, both coordinates) gives `lo` = rigorous lower bound of the minimum over ALL routings consistent with the fixed bits, and `hi` = cost of the best feasible leaf (float, feasible to 1e-9).
Sanity: at `h = 0.2` the code reproduces CG: crossing 10.552302, V-break 0.09018.
**Consequence for the grid error.** The old tangent-cut MILP certificates compared two LOWER approximations and lost 2.6e-5 on tight cases, which would accumulate with size. Now: (a) the only *tight* comparisons are closed forms (`S = sum B` for satisfied blocks, `J_e` for the weak kink), proved by hand (Lemma 1, Prop. P, Lemma M); (b) every other comparison is between a rigorous lower bound and `S` with margin `>= 0.0364` (Sec. 5.2-5.4), so a numerical error of 1e-9 is irrelevant for any instance size. No error accumulates, because no block value is ever computed to a precision that matters except through closed forms and `X_K`; and `X_K` enters `theta` and the upper bound identically (Sec. 6-7).

### 5.2 Crossing core K (4U x 5V) -- `gad/np_cross_table.out`
All 16 terminal patterns `(U_in, U_out, V_in, V_out)`, all interior bits and all 133 conflicts free; `sum B = 10.1085898`. Lower bounds (the `hi` values agree to 1e-9):
* the four satisfied patterns (0100), (0111), (1000), (1011): 10.231554233 each, `X_K = 0.1229644`;
* excess over the satisfied value: V broken only `0.085758` (patterns 0101, 0110, 1001, 1010); U broken only `0.132077` (0011, 1100) and `0.194939` (0000, 1111); both broken `0.272669` (0001, 0010, 1101, 1110).
Every excess is `>= 0.085758 = J_e + 0.0364`, and the doubly broken ones are `>= 2J_e`.
**Prop. X (exact degeneracy, by symmetry alone).** For the order pattern of CG UPDATE 6 (V_c ties with the U wire, V_{-1} strictly above, V_{+1} strictly below) the conflict set of K is exactly invariant under the point reflection `P` about the centre `(2,2)` (`tau`: top(U_j) <-> bot(U_{5-j}), top(V_s) <-> bot(V_{-s}), conflicts `(a,b) -> (tau b, tau a)`): `|C| = |C^P| = 133`, `C \ C^P = emptyset` (`gad/np_pgap.out`). Together with the swap `R` (levels preserved), CP Thm 1 gives `E(s) = E(R s) = E(P s)` for every bit pattern `s`, i.e. the four satisfied terminal states have exactly equal `m_K`.
This supersedes P-GAP.md (which used a tie pattern with 12 asymmetric pairs and a MILP margin 1.14): with the UPDATE 6 pattern **no certificate is needed**. (CP Thm 1 by hand; invariance of `C` finite check.)

### 5.3 K^+ (13 switches), additivity -- `np_kplus.out`, `np_glue.out`
All `2^8` patterns of the eight terminal bits, relations `eq/ne` with credits (K internal 1, neighbour links 2): satisfied value `S_{K+} = 14.656954430`, `S_{K+} - sum B = 0.1229643`, equal to `X_K` within the B&B tolerance 1e-7; **minimum margin `lo - S - J_e*credits` = 0.036368** (pattern: one V link broken).
Additivity `S_{K+} = S_K + sum_{4 neighbours} B` holds exactly: `>=` by Lemma B-type relaxation, `<=` because gluing the optimum of K with isolated neighbours is feasible for all conflicts of `K^+`; the slack of every neighbour-involving non-own conflict at the glued point is `>= 0.19516 = h` (`np_glue.out`), far above the 1e-4 radius in which the true optimum (strongly convex cost, modulus `>= 1`) lies from the computed one.

### 5.4 Other blocks (all patterns, rigorous lower bounds; `S - sum B ~ 1e-10` i.e. zero excess)
* `np_chain.out`: U pair/triples/4-chains (consistent with Corollary M, margins 0.106 strong, tight `0` on weak), V pair, V triple, V 4-chain: margin `0.041811` (= V break `0.140592` minus `2J_e`).
* `np_corner.out`: windows around the U->V corner (V1,V0,u0,u1; V0,u0,u1,u2; V2,V1,V0,u0; triples): margin `>= 0.033468`.
* `np_lib.out`: corner pair, vertex-U pairs (0.168708), 5-block with weak link, 4-block with weak link, V pairs.
* `np_star.out`: degree 3 stars (all four choices of the missing arm) and degree 4 star, each with outward neighbours (7 and 9 switches): margin `0.041811`, zero excess. Degree-2 stars (relays): `np_star_deg2.out`, same margins.
**Mirrored orientations (item 4).** Maps: `R`: `(bx,by,d,yt,yb) -> (by,bx,d,yt,yb)` (levels preserved; swaps NW<->SE, fixes SW and NE); `P`: `-> (-bx-d, -by-d, d, C-yb, C-yt)` (levels reversed, top of the image = image of the old bottom; swaps NW<->SE and SW<->NE, so a corner with V toward NE and arm NW becomes V toward SW and arm SE with levels increasing toward SW). For a block `B` and its image `B'` the map `Phi(Q)_{tau a} = g(Q_a)` of CP Thm 1 is a cost-preserving bijection between feasible sets of `B` and `B'` (same proof: it needs only (S1)-(S3) between the two conflict sets, not invariance of one set), preserving bits under `P` (`P s = s`) and flipping all bits under `R`, hence `eq/ne` relations, credits and block values `m(tau)` transfer exactly. The image order pattern is exactly the image of the original order pattern; the generator's rule `y = F(s_c)`, `F` decreasing, produces it (the reflected corner has V levels increasing toward SW, CG UPDATE 6).
Direct re-certification (`gad/np_mirror.py`, `np_mirror.out`): the corner 4-windows and the V triple under `R`, `P`, `RP`: identical margins (0.033468 / 0.041811, zero excess). Stars: all arm subsets (4 arm types, degrees 2, 3, 4) are certified directly (`np_star*.out`), so the star library is closed by construction. Glue test of the mirrored relay cluster under `id, R, P, RP` (`gad/np_relay_mirror.py`): identical to the unmirrored one (slack 0.0976, cost = closed form). So item 4 is closed for every library block: by exact transfer (hand) and by direct runs.

### 5.5 Exact rational certificate for the crossing core (new)
`gad/np_farkas_gen.py` dumps `gad/np_farkas_K.json`: for the five symmetry classes of terminal patterns of K (0100 satisfied; 0101 V broken; 0011 U broken; 0000 U broken; 0001 both broken; the other 11 patterns are R/P images, CP Thm 1 / Prop. X) a complete branch tree over the 133 conflicts whose leaves carry multipliers `lam >= 0` with denominator `2^20`.
`gad/np_farkas_check.py` re-verifies everything with **`fractions.Fraction` only** (run with `python -I`): tree completeness, `lam >= 0` on assigned conflicts, and the Lagrangian bound `D(lam) >= T` at every leaf, with `ln` enclosed by the atanh series with an explicit rational tail bound (no floats, no mpmath, no numpy; only the strict order of the level floats is read).
Result: `T = 10.231553` (71 leaves), `10.317311` (140), `10.363630` (135), `10.426492` (202), `10.504222` (204): exact rational lower bounds of the minimum over ALL routings. The leaf bounds are `>= T` by exact arithmetic; the slack `T` vs the true values is 1e-6. So the lower-bound half of the key gadget is now (b) with exact rational arithmetic; the matching upper bound (`S_K` = 10.231554233) is still a float primal point, but it only enters through the closed-form constant `X_K` used identically in `theta` and in Lemma G (and all margins exceed 0.0364).

## 6. Lower bound

**Lemma B (block relaxation).** Let the switches be partitioned into blocks `B_1..B_m`. For every `rho_dom`-feasible `Q` with bits `sigma`, `cost(Q) >= sum_k m_{B_k}(sigma|_{B_k})`. *Proof.* Drop the conflicts between blocks; the cost is a sum over points. QED (by hand)

**Lemma T (tilings of a stretch).** Let a wire stretch have plain switches `w_1..w_r`, `r >= 2`, between two cores, and optionally one weak link `(w_j, w_{j+1})` with `2 <= j <= r-2`. There are partitions of `w_1..w_r` into consecutive blocks `P2` and of `w_2..w_{r-1}` into blocks `P1` (with `w_1, w_r` absorbed in the enlarged cores `K^+`) such that every strong link lies inside a block of `P1` or `P2`, the weak link lies inside a block of both, and all blocks have at most 4 switches.
*Proof (explicit).* Let `split(n)` be `n/2` pairs if `n` is even and `(n-3)/2` pairs and one triple if `n` is odd (`n >= 2`; `split(0)` empty). *No weak link:* `P2 = split(r)`; `P1` = the pairs `{w_b, w_{b+1}}` bridging each boundary `b` between consecutive `P2` blocks. *Weak link at `j`:* `P2 = split(j-1), [w_j w_{j+1}], split(r-j-1)`, with the middle block enlarged to a triple if one side has exactly one switch (to `{w_1..w_4}` if both); `P1` = bridging pairs over all `P2` boundaries together with the weak pair, merged where they overlap (the weak pair overlaps at most its two neighbouring bridging pairs, giving one block of size 4, or 3 near the ends).
Checks: every `P2` block has size `>= 2`, so consecutive boundaries are at distance `>= 2` and bridging pairs are disjoint; the first boundary is after `w_2`, the last before `w_{r-1}`, so `P1` never touches `w_1, w_r`; every link is either inside a `P2` block or a boundary link covered by a bridging pair; the weak link is inside a `P2` block and in the `P1` block built from it. QED
Machine check of the construction and of all conditions for `r <= 60` and all weak positions (1712 cases): `gad/np_tiling.py`, `np_tiling.out`. (This closes LOC "Open 2": existence for arbitrary stretch length; the proof is the explicit construction, the script is an independent verifier.)
Periodicity is not needed: the construction is uniform in `r` and `j`.

**Lemma C (closure).** Assume L1-L5 and the library certificates (Sec. 5) with the credits of Sec. 4. Then every `rho_dom`-feasible `Q` has
`cost(Q) >= S0 + J_e * #{ edges {u,v} : sigma_u = sigma_v }`, where `sigma_u` is the bit of the original vertex switch `u`.
*Proof.* Two tilings: `P1` = every core enlarged by its first plain neighbour on each arm (`K^+`, star+outward) plus the `P1` blocks of Lemma T, singletons elsewhere; `P2` = cores unenlarged plus the `P2` blocks of Lemma T.
By Lemma B and the certificates, `cost >= S0^{(j)} + sum_l c_l^{(j)} viol_l(sigma)` for `j = 1, 2`, where `S0^{(j)} = sum_{blocks} S_B` and `c^{(j)}_l` is the credit of relation `l` if it lies inside a block of `P_j`, else 0.
**Additivity:** `S_B = sum_{s in B} B_s + X(B)` with `X(K) = X(K^+) = X_K`, `X = 0` for all other blocks (Sec. 5.2-5.4; for wires by Lemma 1 plus feasibility of the isolated optima). Hence `S0^{(1)} = S0^{(2)} = S0` exactly: no (T3) numerical coincidence is needed.
Credits: weak relations `J_e` in both tilings; every strong relation `2J_e` in at least one tiling, and relations inside cores `J_e` in both. Hence `(c^{(1)}_l + c^{(2)}_l)/2 >= J_e` for every relation `l`.
Along an edge wire from `u` to `v` the relations alternate according to L3 (odd number of `ne`): if all are satisfied then `sigma_u != sigma_v`. Therefore `[sigma_u = sigma_v] <= sum_{l in e} viol_l`, and
`max(LB_1, LB_2) >= (LB_1 + LB_2)/2 >= S0 + J_e sum_e sum_{l in e} viol_l >= S0 + J_e #{sigma_u = sigma_v}`. QED

**Theorem LB.** `rho_dom(P,y) >= S0 + J_e (|E| - maxcut(G))`, hence also `rho(P,y) >= rho_dom(P,y)` (Lemma 0) has this bound. *Proof.* Lemma C and `#{sigma_u = sigma_v} >= |E| - maxcut`. QED
Status: a proof **modulo** (L) and the library certificates.

## 7. Upper bound

### 7.1 Gluing
**Construction of `Q*(sigma)`** for a bit assignment `sigma` of the original vertices (relays free): propagate bits along each wire (V and corner links copy, U links invert, K passes V copy and U invert); for an edge with equal endpoint bits put the single mismatch at the weak link. Each plain switch sits at its isolated optimum (Lemma 1: top `-delta/2`, bottom `+delta/2` in coordinate `sigma_s`); at an unsatisfied weak link the free pair is pooled (`y_{t_1}` down by `gamma/2`, `y_{b_0}` up by `gamma/2`, cost `J_e`, Prop. P); crossing cores sit at the optimum of `K` for their terminal pattern, stars at their isolated optimum.
**Lemma G.** If every conflict of the layout is satisfied by `Q*(sigma)`, then `cost(Q*(sigma)) = S0 + J_e * #{uncut edges}` and `Q*` is `rho_dom`-feasible. *Proof.* Cost is a sum over variables, each moved by exactly one piece; the values are `B_s`, `X_K`, `J_e` (Lemma 1, Sec. 5.2, Prop. P). QED
It remains to show feasibility of all conflicts:
* *Inside a switch, a link, a window:* the zero-excess certificates of Sec. 5.4 and Prop. P show that the isolated optimum (resp. the K optimum with isolated neighbours, Sec. 5.3) is feasible for all conflicts of the corresponding block: a block value equal to `sum B` forces the isolated configuration (unique), so its feasibility is certified for every block of the library.
* *Within a U wire* (non-adjacent switches): conflicts `(t_i, b_j)`: the isolated moves are monotone (tops only decrease, bottoms only increase, in each coordinate), so a pair satisfied at `P` in some coordinate stays satisfied; U switches at distance `>= 2` links have `x`-gap `3k - 4 >= 2` grid steps. (by hand)
* *Within a V chain:* V-wire lemma of LOC Sec. 5 (by hand).
* *Between different gadgets:* rule R of Sec. 7.2.
Status: Lemma G is a theorem; feasibility of the glued `Q*` for **arbitrary layouts** is conditional on (L) and R (Sec. 7.2) and on cluster windows that are not all in the library (e.g. crossing core with the V and U wires beyond `K^+`, relay with both corners, mirrored vertex arms): **pending** (`gad/np_glue.py` covers `K^+` only; a generic cluster tester `glue(layout)` should be added to the generator).

### 7.2 Displacement bound D and spacing rule R (explicit)
**Displacement.** At `h = 4 ln(21/20) = 0.19516`: isolated switches move each point by `delta/2 = d h/2` in one coordinate: `0.3903` (d = 4) and `0.4879` (d = 5); the stored optimum of the crossing core has `max |x - a| = 0.6272` over all 18 points (`np_cluster.py`: `D` column; it is the same in all wire extents); a pooled weak pair adds `gamma/2 = h/8 = 0.0244` to two points in the *other* coordinate, so no coordinate of any point moves by more than `D := 0.6272`. In grid steps `D/h = 3.214`.
**Rule R.** A *cluster* is one of: a crossing core with the wires incident to it (all switches of its two wires), a vertex/relay star with its arms, a corner window, a wire. Let `a, b` be points of two switches that do not belong to a common cluster, with `y_a > y_b`. Rule R: `max_{c=1,2} (P_{b,c} - P_{a,c}) >= 2D`, i.e. **at least 6.43 grid steps, rounded up to 6.5**, measured in log-price grid units, in ONE coordinate, in the direction "b is above/right of a".
Equivalent sufficient condition for the generator: with `y = F(s_c)`, `F` strictly decreasing, `y_a > y_b` forces `s_c(a') < s_c(b')` for the switch centres; if the `s`-gap of centres of non-cluster switches is `>= 13 + d_a + d_b` then every pair of their points satisfies R (the larger coordinate of the difference is at least half the `s`-gap minus the box offsets); for switches of equal level (parallel U wires at the same `s`) require a `t`-gap `>= 13 + d_a + d_b`.
**Lemma R.** If the layout satisfies R, then every conflict between points of different clusters is satisfied by the glued point `Q*(sigma)` of Sec. 7.1.
*Proof.* Let `(a,b)` be such a conflict and `c` the coordinate of R. Every point moves by at most `D` in each coordinate, so `Q*_{b,c} - Q*_{a,c} >= (P_{b,c} - P_{a,c}) - 2D >= 0`; hence `Q*_{a,c} <= Q*_{b,c}`. QED (by hand)
**Inside clusters** the rule is not used; instead the glued point is tested directly (all conflicts, full set):
* crossing core + incident wires, `m` switches beyond the core on every one of the four arms, `m = 1, 3, 5, 8`, all 4 satisfied terminal states: cost minus `(sum B + X_K)` is `<= 1.3e-7` (float), min slack over every conflict not inside the core `= 0.19516 = h` (`gad/np_xwires.py`, `np_xwires.out`). The slack is attained at adjacent own-wire pairs and does not decrease with `m`; for `m > 8` the new conflicts are (U wire pair `(t_i, b_j)`, `|i-j| >= 2`: monotone moves, by hand; V wire: V-wire lemma LOC Sec. 5) and (U switch vs far V switch, which lie at larger `s`-gap and satisfy R).
* the 25-switch instance `cprime` (corner, vertex-U, two weak links, crossing, all 16 vertex patterns, kinks pooled): cost minus closed form `S0 + J_e*#unsat` `<= 1.3e-7`, min slack over every non-core, non-kink conflict `= 0.0976 = h/2`, kink-pair conflicts exactly tight (slack 0, by design), `D = 0.6272` (`gad/np_cprime_glue.py`). (This instance violates R by design and is still feasible.)
* relay cluster (corner - relay - pure U wire with weak link, 13 switches, gadget agent's `relay.build_relay_cp`, 4 terminal patterns incl. unsatisfied): cost minus closed form `<= 5e-15`, min slack `0.0976`, `D = 0.4879` (`gad/np_relay_glue.py`).
* corner - relay - corner is the same relay (a degree-2 star) with its two arms of V type; the star certificates for all arm pairs (`np_star_deg2.out`) cover the block, and the glue is the same local geometry; the full 2-corner cluster has not been built as a separate test (generator-dependent, pending).
**Status of R:** Lemma R is a theorem. What is pending is only that the generator emits layouts satisfying R (an `O(T^2)` assertion) and that clusters are as listed; both are generator tasks (item 1 of the coordinator's list).

### 7.3 Weak solvability (the open hypothesis)
**(WS).** For every bit assignment `sigma` of the original vertices, the glued optimum `Q*(sigma)` (with exact ties, i.e. the exact-tie optimum or a limit of strictly feasible points) satisfies `y in indicatorCone(weakReachableSpectra Q*)`.
By `weakSolvable_iff` this is exactly `WeakSolvable Q* y`.

*What is proved (WS.md, CP):*
1. Prop 1 (shape of reachable sets: `S` reachable iff no `t in S` has `Q_t in int Z(S^c)`), Prop 2 (scale-freedom: `y = 1 + eps eta`, only order/ties/relative gaps matter, ratio `<2` automatic), CP Thm 6 (4-point cover: crossing needs `Delta >= g`), WS Sec. 12.4 (concavity lemma for far covers with explicit hypotheses).
2. **Snapping/closure lemma** (WS Sec. 10.4): `WeakSolvable` is closed; so it suffices to prove `y in cone(Q*)` at the exact-tie point, or along any favourable tie-breaking sequence. Then `rho = rho_dom` (CP Remark; WS Sec. 10.4 d): `rho <= cost(Q*) = rho_dom`.
3. Lemma 0 above: `rho >= rho_dom` always.

*What is verified numerically (floating flow LP at snapped Q; NOT exact rational certificates):* one crossing + wires (4 phases), `cprime` (25 switches, all 16 vertex patterns, `eps` up to 0.6), K_3 (all 8 patterns), relay chain (13 switches, 2 patterns), two far copies of `cprime` (256 patterns, offset `2D >= 48`), with `F` concave piecewise linear (slope `2g`, `7g`, `12g` ...), kinks at each crossing level (WS Sec. 11-12).

*What remains (precisely):* (i) a proof (or a finite certificate) that, for the layouts of L1-L8, the cone condition holds for ALL `2^{|V|}` patterns; WS reports that the binding covers are non-local (15-point sets across three gadgets), that the minimal slope increase `Delta` is `3.0-4.5 g` (not `g`), and that interleaving of crossings closer than `2D = 40` in `s` breaks it; (ii) closed form of the spacing needed (observed `D >= 24` for two copies, no general rule); (iii) layouts with cycles through two crossings and layouts with many crossings are untested; (iv) all verification is floating-point; (v) the exact-tie convention requires the optima to be stored as rational tight-constraint systems.
**Everything in Sec. 7 therefore depends on (WS).** If (WS) fails for some layout family, the reduction can fall back only if a different `y` (or additional "padding" points) is found; there is no such argument yet.

### 7.4 Theorem UB (conditional)
**Theorem UB.** Assume (L), the library certificates, R, cluster feasibility (Lemma G) and (WS). Then for every cut `sigma` of `G`: `rho(P,y) <= S0 + J_e (|E| - cut(sigma))`.
*Proof.* `Q*(sigma)` is `rho_dom`-feasible with the stated cost (Lemma G) and `WeakSolvable Q* y` by (WS); so `Decide P y theta'` holds for `theta' = S0 + J_e(|E| - cut)`. QED

## 8. Correctness and itemised status

**Theorem (reduction).** Under (L), (G), R, (WS): `G` has a cut of size `>= k` iff `Decide P y theta` with `theta = S0 + J_e(|E| - k) + J_e/2`.
*Proof.* (=>) Thm UB with a cut of size `>= k`: `rho <= S0 + J_e(|E| - k) < theta`. (<=) If `Decide` holds, `rho <= theta`; by Thm LB `S0 + J_e(|E| - maxcut) <= rho <= S0 + J_e(|E| - k) + J_e/2`, so `maxcut >= k - 1/2`, hence `maxcut >= k` (integers). The approximation of `S0, J_e` in `theta` by rationals changes this by `2^{-poly} << J_e/2`. QED
MAX-CUT for max degree 3 is NP-hard (Yannakakis 1978; Berman-Karpinski 1999). Since the map is polynomial (sizes in Sec. 3), PERT-2 is NP-hard **if** the hypotheses hold.

### Itemised status

Legend: (a) proved by hand; (b) finite computer certificate (script, kind); (c) pending/open.

| # | Ingredient | Status |
|---|---|---|
| 1 | Lemma 0 (weakly solvable => not strictly dominated), `rho >= rho_dom` | (a) |
| 2 | Lemma 1 (own pair `B(d)`), Lemma B, Lemma M, Corollary M, Lemma C (closure), Thm LB (given certificates) | (a) |
| 3 | Lemma T (tilings of arbitrary stretch, blocks <= 4) | (a) explicit construction; (b) independent verifier `np_tiling.py` r <= 60, all weak positions |
| 4 | Prop. P natural classes (`2B`, `2B + J`, closed forms `J_e = 2(sqrt rho - 1)`, `E_S = 2(rho^2 - 1) >= 4 J_e`) | (a) |
| 5 | Prop. P other routing classes (excess >= 0.255 / 0.400) | (b) `np_pair_classes.py`, interval B&B/dual, exact enough (non-tight) |
| 6 | U-wire block certificates, any length and weak position | (a) via Corollary M from 4, 5 |
| 7 | V chains (pair, 3, 4), corner windows, vertex-U pair, 5- and 4-blocks with weak link | (b) `np_chain.py`, `np_corner.py`, `np_lib.py`, interval B&B, margins 0.033-0.17, rigorous modulo mpmath |
| 8 | Crossing core K: 16-pattern table, X_K = 0.1229644, margins >= 0.0364 vs `J_e` | (b) `np_cross.py`/`np_cross_table.out`, interval B&B; **exact rational Farkas dump** for the 5 symmetry classes, checked with Fractions only (`np_farkas_*.py`, Sec. 5.5) |
| 9 | Exact degeneracy of the 4 satisfied states of K | (a) CP Thm 1 + Prop X (finite invariance check `np_pgap.py`); no MILP margin needed any more |
| 10 | K^+ credits (256 patterns), additivity `S_{K+} = S_K + sum B`, interface slack >= h | (b) `np_kplus.py` (interval B&B, 282 s on 8 cores), `np_glue.py` |
| 11 | Stars of degree 2, 3, 4 with outward neighbours, zero excess, margins >= 0.0418 | (b) `np_star.py`, `np_star_deg2.out` |
| 12 | Rational prices `rho^m`, `m` integer, all numerics at `h = 4 ln 21/20`; R and P symmetric exactly for rational prices | (a)+(b): definitions; certificates rerun at this `h` |
| 13 | Tight comparisons (weak kink, `S = sum B`) exact, others margin >= 0.0364: no accumulating numerical error, no scaling of `J_e` needed | (a)+(b) Sec. 5.1 |
| 14 | Mirrored corners/stars/relays (R, P images) | (a) exact transfer via the CP Thm 1 bijection; (b) direct runs `np_mirror.py`, all star arm subsets, `np_relay_mirror.py`; closed |
| 15 | Layout existence: explicit orthogonal scheme with relays (Sec. 3.1), L1-L8 | **(c)** plan only; `gad/layout.py` produces no crossings; K_4 (77 switches, one relay) generated but its table unverified |
| 16 | Cluster feasibility of `Q*`: crossing + wires (m <= 8 per arm), `cprime` (16 patterns), relay cluster (4 patterns, 4 mirrorings); `D = 0.6272`; rule R explicit (>= 6.5 steps) and Lemma R | (a) Lemma R; (b) `np_xwires.py`, `np_cprime_glue.py`, `np_relay_glue.py`, `np_relay_mirror.py` (float glue tests, slack >= h/2, no tight conflict except kink pairs); **(c)** the generator must assert R and emit only listed clusters; full corner-relay-corner not run separately |
| 17 | (WS): weak solvability for all patterns of an arbitrary layout | **(c)** open; numerics on 5 instances; partial theory (WS Sec. 10-12) |
| 18 | Parity bookkeeping L3, link counts per segment | (a) Lemma P and the parity rule (Sec. 3.4), combination with Lemma T; (c) the generator must implement it (UPDATE 7 does it for its instances) |
| 19 | Polynomial size / bit size | (a) given 15 |

### What was tried and what would close the rest
* Making the library certificates exact rational objects (e.g. Farkas/KKT certificates with exact exponentials) is not needed any more: every comparison with margin `>= 0.0364` is robust to 1e-9, and the tight comparisons are closed forms (Sec. 5.1). A fully formal object would need exact interval `exp/log` certificates of the dual points; the code already uses interval arithmetic, rational `lam`, so a rational-`lam` dump per node is a mechanical extension (not done).
* The remaining mathematical gap is (WS). A proof would show that the balanced facets of the cone at `Q*(sigma)` are determined by the combinatorial hull type and that concavity of `F` with slope growth `>= 5g` at each crossing and `s`-separation of crossings kills them all; WS Sec. 12.4 gives the first lemma (far covers) but the hypotheses (A `s`-minimal, `s`-sum condition) are not shown to hold for all facets. Alternative: change the instance (add padding points that make a convex-up-set decomposition of `y` available) -- not attempted.
* The second gap is the layout (L). The orthogonal-drawing scheme of Sec. 3.1 reduces it to elementary arithmetic once the explicit placement is coded and checked against the generator's own asserts (`collisions`, R, parity, link counts); I have not done it.

### Degree-2 stars (relays)
`gad/np_star_deg2.out`: all six arm pairs (NW+SW, NW+NE, SE+SW, SE+NE, NW+SE, SW+NE), with outward neighbours (5 switches): zero excess, margins 0.041811 (V-type arm) and 0.106220 (NW+SE); so item 11 is closed for degrees 2, 3, 4.

## 9. Script index (all new, `gad/np_*.py`)
`np_dual.py` (interval dual + B&B library), `np_pair_exact.py`, `np_pair_classes.py` (pairs), `np_chain.py` (chains), `np_corner.py`, `np_lib.py` (corner/vertex blocks from `cprime2.out`),
`np_cross.py` (crossing table), `np_pgap.py` (symmetry invariance), `np_kplus.py` (K^+, 256 patterns), `np_glue.py` (interface slack), `np_cluster.py`, `np_xwires.py`, `np_cprime_glue.py`, `np_relay_glue.py`, `np_relay_mirror.py` (glue tests), `np_mirror.py` (R/P images), `np_farkas_gen.py`/`np_farkas_check.py` (exact rational dump), `np_star.py` (stars: `np_star.out`, `np_star_deg2.out`, `np_star_core.out`), `np_tiling.py` (Lemma T).
