# Locality / additivity of rho_dom for assembled gadget layouts (revised: shifted two-partition certificate)

Scripts in `gad/`: `loc7.py` (MILP with violation credits), `loc8.py` (instance builder, weak step parameter), `loc9.py` (all link pair tables), `loc10.py` (block certificates of the 25-switch instance, outputs `loc10_3.75.out`), `loc11.py` (star blocks, crossing 16 patterns), `loc12.py` (exhaustive closure check over 2^25 bit patterns), `loc13.py` (degree-3 stars), `loc14.py` (U-chain intervals), `loc15.py` (near conflicts across blocks), `loc1-6.py` (older: structure of optimum, dual flows). Python: project `.venv`.
Conventions: log coordinates, grid step 0.2, cost per variable `e^{|d|}-1`; a switch has a top and a bottom, its bit `sigma_s` is the coordinate of its own pair (top <= bottom). `J_e = 0.050630` (weak link a = 3.75), design parameter, any `J_e > 0` smaller than half the smallest strong break works.

## 0. Verdict

| Item | Status |
|---|---|
| Lower bound ρ_dom ≥ S0 + J_e·(#uncut edges) ≥ S0 + J_e(\|E\| − maxcut) by a pair of shifted tilings (P1, P2) of the layout into library blocks and max over the two. Needs only finite block certificates with violation credits. | **Proved** (Lemmas B, C), given the certificates |
| Certificates (min over ALL routings of the block, all bit patterns, credits included): all blocks of the 25-switch instance (12 blocks), degree-4 star with 4 neighbours, 4 degree-3 stars, 5 U-chain intervals, 16 crossing patterns, all link pairs | **PASS** (numerical MILP with tangent cuts, tolerance 2.6e-5, Sec. 4) |
| Wrong-route case (W) | **Closed**: it is part of every block certificate (the block MILP minimises over all routings, including routes of cross conflicts through own-pair variables). Isolated wrong-routed link costs 0.2705 above 2B (> J_e and > 2J_e/2). Sec. 4.4 |
| Closure over all bit patterns of the 25-switch instance | **PASS**: min over all 2^25 patterns of `max_j LB_j − S0 − J_e·uncut` = 0.0 (attained at satisfied patterns), `loc12.py` |
| Upper bound (gluing) | Proved under spacing rule R and wire lemmas (Sec. 5); V-wire lemma proved by hand; crossing/corner/star interface agreement numerical |
| Spacing rule | Stated, Sec. 6: separation 6.5 grid steps (δ_max = 0.6426 = 3.21 steps) between non-adjacent gadgets. The 25-switch instance itself does NOT satisfy it (pairs at 4 steps) and is validated by direct MILP instead |
| Weak solvability | left aside, as requested |
| Remaining finite work | interval families for V stretches, mirrored corners, stars with all neighbour types; exact (non-grid) certificates; error scaling in n (Sec. 7) |

Correction of the earlier version of this file: it claimed that "max over partitions fails". That analysis assumed that a strong break is only partially captured at a cost κ/p smaller than J. With two shifted tilings and every strong relation certified with credit ≥ 2J_e the max works (Lemma C). The factor loss of fractional weights (3.1724 vs 3.3716 on P3) is real but irrelevant for this scheme.

## 1. Setting

For a routing σ (a coordinate for every conflict) ρ_dom(σ) is a separable convex program over the real variables `u_{t,i}`; ρ_dom = min_σ. Bits `sigma_s ∈ {0,1}` are the routings of the own pair `(top_s, bottom_s)`.

**Lemma B (block relaxation).** Let the switches be partitioned into blocks `B_1..B_m`. For every feasible Q with bits σ,
cost(Q) ≥ Σ_k m_{B_k}(σ|_{B_k}),
where `m_B(τ)` = min over Q_B of cost of the points of B subject to the conflicts inside B (any routing of them) and with the own-pair bits of B equal to τ. Proof: drop all conflicts between blocks; cost is a sum over points. QED
No spacing rule is needed for this direction.

A **relation** is a pair of switches with a required bit relation (eq or ne) taken from the satisfied pattern (V link, corner: eq; U link, weak link, vertex–U link: ne; crossing: V_out = V_in, U_out ≠ U_in). `viol_l(σ) ∈ {0,1}`.

A **block certificate** for block B with relations `l ∈ R_B` and credits `c_l ≥ 0` is the finite statement
(Cert) min over all routings of B (all bit patterns) of [ cost − Σ_{l ∈ R_B} c_l·viol_l ] ≥ S_B,
with `S_B` the minimum over routings that satisfy all relations. Computed by one MILP (indicator variables for viol).

## 2. Tilings and closure

Two tilings P1, P2 of the switches into blocks such that
(T1) every core (crossing, star, corner) is a block in both; in P1 it is enlarged by the first wire switch of every outward arm (`K^+`);
(T2) every relation on a wire (link, core-internal relation) lies inside a block of P1 or of P2; each weak link lies inside a block of BOTH;
(T3) Σ_{B ∈ P1} S_B = Σ_{B ∈ P2} S_B =: S0 (both equal ΣB_s + Σ_cores X_g, closed form).
Credits: weak relation `J_e`; a relation lying in one tiling only: `c ≥ 2J_e`; a relation lying in both: `c^{(1)} + c^{(2)} ≥ 2J_e`.

**Lemma C (closure).** Under (T1)-(T3) and (Cert) for all blocks, for every feasible Q:
cost(Q) ≥ S0 + J_e·#{edges (x,y): σ_x = σ_y} ≥ S0 + J_e(|E| − maxcut(G)).
Proof. By Lemma B and (Cert), cost ≥ S0 + Σ_l c_l^{(j)} viol_l for j = 1,2, where c^{(j)}_l = 0 if l is cut in tiling j. Along a wire e = (x,y) all strong relations satisfied implies (parity propagation, wire odd) σ_x = σ_y iff the weak relation is violated. Hence [σ_x = σ_y] ≤ viol_weak(e) + Σ_{strong l ∈ e} viol_l. Weak: credit J_e in both tilings. Strong: c^{(1)}+c^{(2)} ≥ 2J_e. So (LB_1 + LB_2)/2 ≥ S0 + J_e Σ_e [σ_x = σ_y], and max_j ≥ average. The second inequality: uncut edges ≥ |E| − maxcut. QED
Upper bound: Theorem U (Sec. 5) with a maximum cut gives cost = S0 + J_e(|E| − maxcut) (stored optima, exact), so ρ_dom equals it; the error is only the numerical grid of the certificates (Sec. 7), not a sum of per-gadget errors of the construction.

## 3. Library (switch types and tilings in the 25-switch instance)

Instance `cprime` (g = 0.01, h0 = 0.02, h2 = 0.04, a = 3.75): V chain 0..8 (vertex1 = 8), corner pair (0, 9), U arm 9..13 + vertex2 = 14 with weak link (11,12); E2: vertex A = 15, U 16..23, vertex B = 24, weak link (16,17); crossing core K = {2..6, 19..22}.
P1 = {K^+ = {1..7, 18..23}}, {0,9}, {10}, {11,12}, {13,14}, {8}, {15}, {16,17}, {24}.
P2 = {K = {2..6,19..22}}, {0,1}, {9..13}, {14}, {7,8}, {15..18}, {23,24}.
Every link lies in a block of P1 or P2, weak links (11,12), (16,17) in both. Relations of the 5-block {9..13}: (9,10), (10,11) ne with credit 2J_e, (11,12) ne credit J_e, (12,13) ne credit 2J_e.

## 4. Certificates (all PASS)

MILP: tangent-cut lower approximation of the convex cost (grid error up to 1.2e-5 per switch, which is the origin of the -2.6e-5 margins below and of S0 = 28.48695 versus the exact polished 28.48724; see Sec. 7), time limit 900 s, status 0 (optimal) for every run. `S` = value with relations forced, `cert` = min over all routings with credits.

### 4.1 Blocks of the 25-switch instance (`loc10_3.75.out`)
| block | switches | S | cert | margin |
|---|---|---|---|---|
| P1 K^+ | 1-7, 18-23 (13) | 15.114193 | 15.114193 | 0 |
| P1 corner pair | 0,9 | 2.281092 | 2.281092 | 4e-14 |
| P1 weak | 11,12 | 1.967299 | 1.967273 | -2.6e-5 |
| P1 vertex–U | 13,14 | 2.281092 | 2.281092 | 3e-14 |
| P1 weak | 16,17 | 1.967299 | 1.967273 | -2.6e-5 |
| P2 K | 2-6,19-22 (9) | 10.552009 | 10.552009 | 0 |
| P2 V pair | 0,1 and 7,8 | 2.594885 | 2.594885 | 0 |
| P2 5-block | 9-13 | 4.918247 | 4.918221 | -2.6e-5 |
| P2 4-block | 15-18 | 4.248391 | 4.248365 | -2.6e-5 |
| P2 U–vertex pair | 23,24 | 2.281092 | 2.281092 | 0 |
Singletons: S = B(delta). Sums: S0(P1) = 28.486951350, S0(P2) = 28.486951464 (equal to 1e-7, (T3)); ΣB_s = 28.356753; total excess X = 0.130199 (the crossing). Credits used: K internal relations J_e each (V break 0.0902 ≥ J_e, certified), K^+ neighbour links 2J_e, pairs 2J_e (V link, corner: 0.14945 ≥ 0.1013; U: 0.21034; vertex–U 0.28309).

### 4.2 Link pair tables (`loc9.py`, a = 3.85 gives J_e = 0.0302, a = 3.75 gives 0.0506)
V–V (dv = 5, k = 1, levels of the instance) break 0.14945; corner (0,9) break 0.14945; U–U strong 0.21034; weak 0.0302 / 0.0506; vertex(d=5)–U break 0.28309. These are minima over all four bit patterns and all routings of the pair.

### 4.3 Gadgets requested (`loc11.py`, `loc13.py`, `loc14.py`)
* **Crossing, all 16 terminal patterns** (exact optimum, interior free; excess over min 10.552302): satisfied 4 patterns 0.00000; V broken only 0.09018 (x4); U broken only 0.14006 (x2) and 0.19959 (x2); both 0.28956 (x4). Identical to the g = 0.05 table of CROSSING-GADGET.md. Credit J_e per relation (cert margin 0 for K and K^+).
* **Degree-4 star** (centre d=5, NW/SE U attachments a = 3, SW/NE V neighbours with levels h0/h2) with relations centre=SW=NE, centre≠NW, centre≠SE (credit J_e each): S = cert = 5.859626 = ΣB (zero excess), margin 1e-14. Star + 4 outward neighbours (9 switches, outward credits 2J_e): S = cert = 10.421810, margin 0.
* **Degree-3 stars** (drop one arm, with outward neighbours): no-NW and no-SE S = cert = 8.454511; no-SW and no-NE S = cert = 7.826925; margins ≤ 1e-13.
* **Weak link** (a = 3.75): J_e = 0.050630 exactly = 2(e^{0.025}−1); weak in a chain (weak-strong, strong-weak, strong-weak-strong) and strong 4-chains: margins 0 or -2.6e-5 (same grid error).
* **Corner**: the U→V corner of the instance is the pair (0,9) (break 0.14945). The three-switch corner of `corner.py` (break ≥ 0.1258) is not used here. Mirrored corners (V-SW / U-NW) NOT run.

### 4.4 Wrong-route lemma (W)
**Lemma W.** For a link and its neighbouring switches (blocks of 2, 3, 4, 5 consecutive U switches in the library, all in the tables above), the minimum over ALL routings, including every route of the cross conflicts, of cost minus credits is ≥ S. In particular wrong routing never helps. Proof: it is the (Cert) statement for those blocks; the MILP decides all routings. Mechanism seen by hand: the cross conflict `(t_V,b_U)` routed through the own variables (y, gap 1.4) forces `v(t_V)+v(b_U)` ≥ 2(e^{0.7}−1) = 2.03; with the second cross edge the pooled four own variables cost 2.2379 = 2B + 0.2705 (checked: single link 2.23785 vs 2B + J_s = 2.1776). The single-flow dual bound for that edge alone is only 0.1486 < J_s (flows meet at the own variables), which is why the old matching/flow route was abandoned for the block route. Isolated wrong-routed chains: extra per link 0.2705, 0.7346, 1.2139, 1.8369, 2.3405 (n = 2..6, `loc3.py`) so merging only increases cost.

### 4.5 Exhaustive closure (`loc12.py`)
For the 25-switch instance, all 2^25 bit patterns σ, credits as in Sec. 3: `min_σ [max(LB_1(σ), LB_2(σ)) − S0 − J_e([σ_8=σ_14] + [σ_15=σ_24])] = 0.0`, attained exactly at satisfied patterns. So the inequality of Lemma C holds on the instance for every bit pattern.

## 5. Upper bound (gluing)

**Theorem U.** Let σ be a routing consistent on every wire except at the weak links (a maximum-cut assignment propagated along wires). Define Q: every switch at its isolated optimum (top −δ/2, bottom +δ/2 in the coordinate σ_s), core switches at the stored library optimum (crossing: centre V 0.643/0.357 and U switches 20, 21 differ), and at every unsat weak link the free pair pooled (cost 2(e^{γ/2}−1)). Then Q satisfies all conflicts under rule R (Sec. 6) and the wire lemma below, and cost(Q) = S0 + J_e·#uncut.
Proof. Cost is a sum over variables and each variable is moved by exactly one piece (own pair, free pair of a weak link, or core). Conflicts inside a switch or link: the link table (Sec. 2 of the old notes: satisfied for free in the satisfied relation, free pair pooled otherwise). Conflicts inside a V chain: **V-wire lemma.** Levels `top_j = 1+g+shift(s_j)`, `bot_k = 1+shift(s_k)` with shift strictly decreasing with step ≥ g; (t_j, b_k) is a conflict iff s_k ≥ s_j; there `t_j − b_k = (s_j − s_k + 5)·0.2 ≤ 1.0`, and the common move (top −0.5, bottom +0.5 in the common coordinate) closes it. Conflicts between different gadgets: rule R. Interface agreement: observed in `cprime_Q_1010`: 22 of 25 switches have eps = 0 (exactly isolated), the crossing excess 0.130537 sits on switches {4,20,21}; dual flows (`loc6.py`): support 29 edges, own flows of all other switches equal the isolated flow to 6e-8; so neighbouring blocks agree on shared switches. QED (interface agreement for star and non-sat patterns is numerical only; non-sat patterns are not needed for the upper bound).
The 25-switch instance validates Theorem U directly: table `cprime2.out`, excess = 0.05063·#unsat to 5 digits for all 16 terminal states.

## 6. Spacing rule R (for the layout generator)

Let `δ_pt` be the maximum displacement of a point over all library optima (log units): 0.5 for V points, 0.4 for U points, 0.6426 at the crossing centre (3.21 steps), 0.6 on the two crossing-adjacent U points. Rule R: for every conflict pair (a,b), `y_a > y_b`, that does not lie inside one library gadget or one wire chain (consecutive links, incl. the V-wire lemma),
`max_i (log P_{b,i} − log P_{a,i}) ≥ δ_a + δ_b`.
Uniform sufficient form: separation ≥ 2δ_max = 1.285 in log = **6.5 grid steps** in some coordinate. Then every such conflict has slack ≥ 0 at the glued Q (each point moves ≤ δ per coordinate). Equivalently: two gadgets (wire stretches, cores) whose points a, b have `y_a > y_b` must have b at least 6.5 steps NE of a in x or in y; in a layout with y decreasing in x+y this is a minimum gap of 6.5 steps between non-adjacent gadgets after accounting for box sizes.
Also (T): wire stretches between cores need ≥ 4 switches so that K^+ and the tiling exist (Sec. 2). The generator asserts R by an O(n^2) pass.
Status of the instance: pairs such as (V0, U19) have separation 0.8 (4 steps) < 1.285, so the instance does not satisfy R as stated; there the slack was verified by the MILP (min slack of the 737 pruned pairs at Q: 0.70, `loc1.py`). R is sufficient, not necessary.

## 7. Numerical status and error scaling

All certificates are MILP with tangent cuts, a LOWER approximation of the convex cost (so a lower bound; grid error ~1.2e-5 per switch: S0 = 28.486951 vs exact 28.487240 on 25 switches). For the closure what matters is `S0^{exact} − S0^{LB} ≤ ε n`, which must be < J_e/4 ≈ 0.0127: fine for n up to about 1000 with the present grid; for larger layouts refine the grid (error ∝ step²) or certify block values by exact rational arithmetic. This error is a property of the certificate, not of locality: block values are closed-form exponentials (B(δ) = 2(e^{δ/2}−1), J_e = 2(e^{γ/2}−1), X_g from a 4-edge dual flow). Margins `-2.6e-5` in Sec. 4 are the same grid error on tight equality cases, not violations; non-tight patterns have margins ≥ 0.05.

## 8. Dual flows (kept as explanation)
Lemma 2 of the first version (weak duality `cost ≥ Σ f_e w_e − Σ ψ(|g_v|)`) is still valid and gives the exact structure used above: on U chains `eps_s = (J/2)·#unsat links at s`, the unsat J is the pooled free pair; the crossing excess 0.13054 is certified by a flow on 4 cross edges among switches {4,19,20,21} (`loc6.py`, D = 28.487244 vs primal 28.487290). It is not needed for the closure.

## 9. Open
1. Interval families for V stretches (V–V chains with level steps), strong/weak mixes up to length 5 with all positions; mirrored corners (V-SW/U-NW); degree-4 stars attached to the actual crossing-free vertices of a layout (star9 passes in isolation).
2. A tiling generator proof for arbitrary stretch lengths (T1-T3), including m parity, and the check (T3) S0(P1) = S0(P2) (holds to 1e-7 here).
3. Exact (grid-free) certificates, error scaling for large n.
4. Interface agreement (IAC) for general layouts by computation, and rule R as an asserted property of the generator.
5. Weak solvability (separate task).
