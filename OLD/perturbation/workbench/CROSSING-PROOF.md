# Exact degeneracy of the crossing gadget: symmetry proof, its gap, and the weak-solvability fix

Notation follows `perturbation/lean/Perturbation/Decision.lean` (`pert`, `totalPert`, `Decide`) and `NeoTiling/Closure.lean` (`WeakSolvable`, `IsWeakReachable`, `weakSolvable_iff`, `WeakSolvable.mem_indicatorCone`). Gadget data: `CROSSING-GADGET.md` section 2 (4U x 5V instance), conventions `GADGET-D2.md`.

## 0. Summary of what is and is not proved

| Claim | Status |
|---|---|
| R (swap x<->y) is an exact symmetry of the instance, of rho_dom, of weak solvability, hence of full rho. It maps (U-phase, V-phase) -> (U-phase, V-phase + 1). | **Proved** (Thm 1, Prop 3). |
| P (point reflection + level reversal) is an exact symmetry of rho_dom *for the symmetrized conflict set* `C_sym`. It maps U-phase -> U-phase + 1, V-phase fixed. | **Proved** (Thm 1, Prop 3). |
| P is a symmetry of the actual conflict set `C(y)` of the explicit 4x5 instance. | **FALSE as stated.** Exactly 6 + 6 pairs break it (Prop 3(c)). The tie structure of the y-levels is not transported by P, and this cannot be repaired within the level family of the notes without destroying the weak-solvability fix (Rem. 4). |
| P preserves weak solvability. | **FALSE** (Prop 5): price space is linear, P acts as `q -> c/q`, which is not affine. |
| Weak-solvability fix `h2 >= h0 + 2g`: necessity from a 4-point cover inequality with Farkas certificate. | **Proved** conditionally on a geometric hypothesis on the perturbed prices (Thm 6). Sufficiency is numerical only. |
| Reduction MAX-CUT -> rho. | Sketch; open items in section 5. |

So the four ground energies are *exactly* equal for the V-bit (by R), and equal for the U-bit (by P) **iff** a finite list of 12 extra constraints is inactive at optimal solutions (Cor. 3(d)). That is a finite certificate on the optimum, not a symmetry.

## 1. Formal setting

Index set `I` (finite), prices `P : I -> R^2_{>0}`, levels `y : I -> R`. For `u, v in R^2_{>0}` put

    N(u, v)  :<=>  exists i in {1,2}: u_i <= v_i          ("u does not dominate v strictly")

Conflict set `C(y) = {(a,b) in I^2 : y_a > y_b}`. Feasible prices for rho_dom:

    F(y) = { Q : I -> R^2_{>0} | N(Q_a, Q_b) for all (a,b) in C(y) }.

`rho_dom(P,y) = inf { totalPert P Q : Q in F(y) }`. (Convention: it matches the sigma of GADGET-D2, "sigma(t,s) = coordinate in which q_t <= q_s", i.e. a higher point must not lie NE of a lower one. The strict variant `u_i < v_i`, or the opposite orientation, changes nothing below: only the two properties (N1), (N2) are used.)

* (N1) `N(swap u, swap v) <=> N(u, v)`.
* (N2) For `inv_c(u) := (c_1/u_1, c_2/u_2)`, `c in R^2_{>0}`: `N(inv_c u, inv_c v) <=> N(v, u)`. Indeed `c_i/u_i <= c_i/v_i <=> v_i <= u_i`.

Designated pairs and bits. Let `D subset C(y)` be a set of designated pairs (here: the internal pair (top, bottom) of every switch) and `sigma : D -> {1,2}`. Define

    E(sigma) = inf { totalPert P Q : Q > 0, Q_{a,sigma(a,b)} <= Q_{b,sigma(a,b)} for (a,b) in D,
                                      N(Q_a, Q_b) for (a,b) in C(y) \ D }.

The bit of a switch k is `s_k = sigma(top_k, bot_k) - 1`. The energy of a bit pattern `s` is `E(s) := E(sigma_s)`, all cross pairs free (this is the "MILP with free interior sigma" of the notes, with the switch bits prescribed).

Two elementary facts about the cost.

* (K1) `pert(p,q) = pert(q,p)`, and `pert(c/p, c/q) = max(p/q, q/p) - 1 = pert(p,q)` for `c > 0`.
* (K2) `totalPert P Q = sum_a sum_i pert(P_{a,i}, Q_{a,i})` is invariant under permuting the index `a` and under swapping the two coordinates i simultaneously for P and Q.

## 2. The symmetry theorem

A *symmetry datum* is `(tau, g, eps)` with `tau` a permutation of `I`, `g in {swap, inv_c}`, and `eps = +1` if `g = swap`, `eps = -1` if `g = inv_c`, such that

* (S1) `P_{tau a} = g(P_a)` for all a;
* (S2) `(a,b) in C <=> (tau a, tau b) in C` if eps = +1, and `(a,b) in C <=> (tau b, tau a) in C` if eps = -1;
* (S3) the same for D.

Action on `sigma`: for eps = +1, `(g.sigma)(tau a, tau b) = 3 - sigma(a,b)`; for eps = -1, `(g.sigma)(tau b, tau a) = sigma(a,b)`.

**Theorem 1.** Under (S1)-(S3) with `tau` an involution, `E(g.sigma) = E(sigma)` for every `sigma`; in particular `rho_dom` (sigma free) is the same.

*Proof.* Let `Phi(Q)_{tau a} := g(Q_a)`. It is a bijection of positive price systems, with inverse of the same form since `tau`, `g` are involutions. By (S1), K1, K2: `totalPert P Phi(Q) = sum_a sum_i pert(g(P_a)_i, g(Q_a)_i) = totalPert P Q` (for swap the coordinate sum is permuted, for inv_c K1 applies termwise).

Feasibility, case eps = +1 (g = swap). Let `(a,b) in D` with `Q_{a,s} <= Q_{b,s}` (s = sigma(a,b)). Then `Phi(Q)_{tau a, 3-s} = Q_{a,s} <= Q_{b,s} = Phi(Q)_{tau b, 3-s}`, and `(tau a, tau b) in D` by (S3); this is the constraint prescribed by `g.sigma`. For `(a,b) in C \ D`: `N(Phi(Q)_{tau a}, Phi(Q)_{tau b}) = N(swap Q_a, swap Q_b) <=> N(Q_a,Q_b)` by (N1).

Case eps = -1 (g = inv_c). Let `(a,b) in D`, `Q_{a,s} <= Q_{b,s}`. Then `Phi(Q)_{tau b, s} = c_s/Q_{b,s} <= c_s/Q_{a,s} = Phi(Q)_{tau a, s}`, with `(tau b, tau a) in D` by (S3): the constraint prescribed by `g.sigma` at the pair `(tau b, tau a)`. For `(a,b) in C \ D`: `N(Phi(Q)_{tau b}, Phi(Q)_{tau a}) = N(inv Q_b, inv Q_a) <=> N(Q_a, Q_b)` by (N2).

So `Phi` maps the feasible set for `sigma` onto the feasible set for `g.sigma` preserving the cost; the infima coincide. Applying the same argument to the pair `(g, g.sigma)` is unnecessary since `Phi` is a bijection. QED

**Corollary 2 (bits).** For a switch family with `tau` mapping switch k to switch `tau k`: under R, `top_k -> top_{tau k}`, so `(R s)_{tau k} = 1 - s_k`. Under P, `top_k -> bot_{tau k}`, `bot_k -> top_{tau k}`, so `(P s)_{tau k} = s_k` (the bit is preserved, since the constraint at the image pair is `Q'_{top', s} <= Q'_{bot', s}` with the same coordinate s). Hence `E(R s) = E(s)` and `E(P s) = E(s)` for *every* bit pattern of the gadget (not only the ground patterns), so also for every terminal table.

## 3. Application to the explicit 4U x 5V instance

Grid coordinates `(x,y)`, prices `p = (u^{x}, u^{y})` with fixed `u > 1` (the notes use `u = e^{0.2}`; for a rational reduction take `u = r^2`, `r` rational, so that half-integer grid points have rational prices, and `c = u^{4}` below is rational). Points (18):

* U_j, j = 1..4: bottoms `(-4.5,4.5), (-1.5,1.5), (1.5,-1.5), (4.5,-4.5)`, size 4, tops = bottom + (4,4); levels top 1.05, bottom 1.00.
* V_s, s = -2..2: bottom `(s-0.5, s-0.5)`, top = bottom + (5,5); levels (top, bottom) = (1.15,1.10), (1.10,1.05), (1.05,1.00), (0.85,0.80), (0.65,0.60) (g = 0.05, h0 = 0.05, h2 = 0.2).

C = (2,2); `c = (u^4, u^4)`.

**Proposition 3.**

(a) *R.* `tau_R`: `U_j <-> U_{5-j}` (top to top, bottom to bottom), V_s fixed pointwise. (S1) with `g = swap`: top of U_j is `(b_x+4, b_y+4)`, its swap is `(b_y+4, b_x+4)`, the top of the switch with bottom `(b_y,b_x)`, which is `U_{5-j}` (the bottom list is closed under swap). The V points lie on the diagonal. (S2), (S3) hold with eps = +1 because **levels are preserved exactly**: all U tops equal 1.05, all U bottoms 1.00, V levels fixed. So R is an exact symmetry of the whole instance.

(b) *P.* `tau_P`: `top(U_j) <-> bot(U_{5-j})`, `top(V_s) <-> bot(V_{-s})`. (S1) with `g = inv_c`: reflection of the point `(x,y)` is `(4-x, 4-y)` in grid units, i.e. `p -> c/p`. U: the box of U_j is `[b_x, b_x+4] x [b_y, b_y+4]`; its reflection `(x,y) -> (4-x,4-y)` is `[-b_x, 4-b_x] x [-b_y, 4-b_y]`, the box with bottom `(-b_x, -b_y)`. The U bottom list is closed under `b -> -b`: `(-4.5,4.5) <-> (4.5,-4.5)`, `(-1.5,1.5) <-> (1.5,-1.5)`. The top maps to the bottom of the image box. V: box `[s-0.5, s+4.5]`, image `[-s-0.5, -s+4.5]` = box of V_{-s}. So P preserves the *geometric* switch set, swapping tops and bottoms. (Section 2 of CROSSING-GADGET says the V switch is "centred" at C, i.e. `s = 0` is fixed: `[−0.5,4.5]` is symmetric about 2. Yes.)

(c) *Levels: order reversal fails.* (S2) with eps = -1 needs `y_a > y_b <=> y_{tau b} > y_{tau a}`. A necessary condition is that `tau` induces a strictly decreasing map `f` on level values: `y_{tau a} = f(y_a)`. Here it does not: level 1.05 contains `top(U_j)`, `top(V_0)`, `bot(V_{-1})` whose images have levels 1.00, 1.00, 0.85. Direct enumeration of the 153 pairs (checked by hand and by enumeration; it is combinatorics of the stated levels, not an experiment): `|C| = 127 = |C^P|` where `C^P := {(tau b, tau a): (a,b) in C}`, and

* `C \ C^P` (6 pairs, conflicts whose image is a tie): `(U_j-bot, V_1-top)` for j = 1..4, `(V_0-bot, V_1-top)`, `(V_1-bot, V_2-top)`.
* `C^P \ C` (6 pairs, images of tie pairs that become conflicts): `(V_{-1}-bot, U_j-top)` j = 1..4, `(V_{-1}-bot, V_0-top)`, `(V_{-2}-bot, V_{-1}-top)`.

In every pair of the first list the higher point lies strictly SW of the lower one at P (gaps between 1 and 10 grid steps, at least 4 in the larger coordinate), so the pair is satisfied by `Q = P`. All other conflicts, and all internal switch pairs `D`, are P-symmetric. Define `C_sym = C cap C^P` (121 pairs) and `rho_sym`, `E_sym` the corresponding energies; they satisfy (S2), (S3) for P.

(d) *Consequences.* Let `s = (phi, v)` with `phi` the U-phase `s_j = phi + j mod 2` (j = 1..4) and `v` the V-bit (`s` = v on all V_s).
* `R s = (phi, v+1)`: `(Rs)_{5-j} = 1 - phi - j = phi + (5-j) mod 2` (uses `n_U = 4` even), V flips.
* `P s = (phi+1, v)`: `(Ps)_{5-j} = phi + j = (phi+1) + (5-j)` mod 2, V is uniform hence fixed.
Hence by Thm 1 / Cor. 2: `E(phi,v) = E(phi,v+1)` **exactly** (R acts on the full conflict set, so also for `E` with all pairs), and `E_sym(phi,v) = E_sym(phi+1,v)`. All four `E_sym(phi,v)` are equal. For the actual energies, `E_sym <= E` and
> `E(phi,v) = E_sym(phi,v)` for all four phases **iff** for each phase some minimiser `Q*` of `E_sym(phi,v)` (infimum attained, the feasible set is closed) can be chosen satisfying the 12 pairs of `C Delta C^P` as `N`-constraints, in all four phases (by R the V-bit is free; so it is a check in two phases, `phi = 0, 1`).
This is a finite check on explicit optima; the notes report `spread 0.00000` of the MILP optima, which is consistent with it, but it is a computation and not a consequence of symmetry.

**Remark 4 (the gap cannot be closed by relabelling levels).** Exact P-symmetry of the order needs tie classes to be mapped to tie classes. The class `{top(U_j), top(V_0), bot(V_{-1})}` (level 1.05; the ties "V_0 top = U top" and "V_{-1} bot = U top" are items (c) of the open list in the notes) maps to `{bot(U_j), bot(V_0), top(V_1)}`, forcing `y(top V_1) = y(bot V_0)`, i.e. `1 + g - h2 = 1`, `h2 = g`. The weak-solvability fix of section 4 needs `h2 >= h0 + 2g >= 3g`. So within this level family exact order-reversal and the fix are incompatible. (Whether another family does both is open.)

**Proposition 5 (P is not a symmetry of weak solvability).** Weak reachability is defined with the linear pairing `xi . (p_s - p_t)` on price space. R is linear on price space and preserves levels, so `WeakSolvable(Q,y) <=> WeakSolvable(swap Q, y)` (use `swap xi` as witness, and `weakSolvable_iff` or directly `IsWeakReachable`). P acts as `q -> c/q` coordinatewise, which is not affine, and in addition reverses y. For a point reflection that *is* affine (`q -> 2C - q`) the up-sets `conv(T) + R^2_+` become down-sets, which are not the sets controlling weak reachability. So only the order part of the picture (rho_dom) survives. In particular `Q` weakly solvable for `y` does not make `Phi(Q)` weakly solvable for `y` or for `y' = const - y`. Therefore `rho = rho_dom` has to be verified separately in each phase `phi`; by R, in each phase `phi`, for one value of `v`.

## 4. Weak solvability: the 4-point cover inequality

Throughout `d = 2`, `y >= 0`. By `WeakSolvable.mem_indicatorCone`, `WeakSolvable Q y` implies `y in cone{1_S : S weakly reachable at Q}`; the converse is `weakSolvable_of_mem_indicatorCone`.

**Lemma W (shape of weakly reachable sets).** Let `S` be weakly reachable at `Q`, `T = S^c`, `Z(T) = conv{Q_s : s in T} + R^2_{>=0}`. Then every `t in S` satisfies `Q_t not in int Z(T)`. Equivalently: if `Q_t in int Z(T)` then `t in T`.

*Proof.* Take `xi >= 0`, `xi != 0` with `xi . Q_s >= xi . Q_t` for all `s in T`. The linear function `xi . (.)` is `>= xi . Q_t` on `conv{Q_s}` and `>= 0` on `R^2_{>=0}` shifts, so `xi . z >= xi . Q_t` on `Z(T)`. If `Q_t in int Z(T)`, then `Q_t - eps xi in Z(T)` for small `eps > 0`, giving `-eps |xi|^2 >= 0`, a contradiction. QED

**Theorem 6 (4-point cover).** Let `A,B,C,D in I` and let `Q` satisfy

* (H1) `Q_A, Q_B in int( conv{Q_C, Q_D} + R^2_{>=0} )`;
* (H2) for each `X in {C,D}` some `Y in {A,B}` has `Q_Y - Q_X in int R^2_{>0}` (strictly NE).

Then every weakly reachable `S` obeys `1_S(A) + 1_S(B) <= 1_S(C) + 1_S(D)`, and so does every `y in cone`, hence every weakly solvable `y`:

    y_A + y_B <= y_C + y_D.

*Proof.* `T = S^c`. If `C, D in T`: `conv{Q_C,Q_D} + R^2_+ subset Z(T)`, so by (H1) and Lemma W `A,B in T`: `0 <= 0`. If exactly one `X in {C,D}` is in `T`: by (H2) `Q_Y in Q_X + int R^2_+ subset int Z(T)`, so `Y in T`, hence `1_S(A)+1_S(B) <= 1 = 1_S(C)+1_S(D)`. If none: right side is 2. QED

**Farkas certificate.** Define `lambda = 1_C + 1_D - 1_A - 1_B`, a linear functional on `R^I`. The theorem says `lambda(1_S) >= 0` for all weakly reachable `S`, i.e. `lambda` lies in the dual of the cone. If `y_C + y_D - y_A - y_B = lambda(y) < 0`, then `lambda` separates `y` from the (finitely generated, hence closed) cone, so `y` is not weakly solvable. This is the certificate; its form in the planar flow-LP (`wk9`-`wk11`) is the same `lambda`.

**Application.** In the failing phase of the 4U x 3V instance the certificate tuple is (numerically found, not re-derived here): `A = top(V_{-1})` (SW-most V top), `B = top(V_1)` (NE-most V top), `C = bot(U)` (a middle U bottom), `D = bot(V_0)` (centre V bottom). Levels `y_A = 1 + g + h0`, `y_B = 1 + g - h2`, `y_C = y_D = 1`:

    y_A + y_B <= y_C + y_D   <=>   2g + h0 - h2 <= 0   <=>   h2 >= h0 + 2g.

For `h2 = h0 = g` the inequality is violated by exactly `2g` (as reported). The tests in the notes agree with the threshold: `(g,h0,h2) = (0.002,0.002,0.008), (0.01,0.01,0.03), (0.01,0.02,0.04), (0.01,0.02,0.05)` all satisfy `h2 >= h0 + 2g` (three with equality) and are weakly solvable; `(g,h0,h2) = (g,g,2.5g)` has `h2 < h0 + 2g` and is not. For 5V the same tuple with `s = +-1` gives the same condition; with `s = +-m` one gets `m (h2 - h0) >= 2g`, weaker for `m >= 2`, so the innermost pair is binding.

What the theorem assumes about the perturbed prices (H1), (H2) is consistent with the dominance constraints: `y_B < y_C, y_D` so `B` may lie NE of both, (H2) holds through `B`; (H1) needs `A` (higher than `C, D`, hence *not* NE of either) to sit strictly above the segment `[Q_C, Q_D]` but with `Q_{A,i} <= Q_{D,i}` for some i, i.e. in the triangle that the perturbation of `A` creates. (H1), (H2) are properties of the optimum `Q*` of the failing phase, taken from the scripts; I did not re-verify them.

What is **not** proved: sufficiency of `h2 >= h0 + 2g`, i.e. that all four phases are weakly solvable. By `weakSolvable_iff` it amounts to exhibiting `y = sum_S m_S 1_S` with `m_S >= 0`, `S` weakly reachable at `Q*`; the flow-LP found it in exact rationals for the tested cases. All other 4-point and pair covers must be excluded; pair covers `y_t > y_r + y_s` are excluded by `max y < 2 min y`.

**Remark (rho = rho_dom without a margin).** `Q -> [WeakSolvable Q y]` is a closed condition by definition (closure). If for each margin `m > 0` the optimum `Q_m` of rho_dom with `Q_{a,s} <= (1-m) Q_{b,s}` is weakly solvable, then cost(`Q_m`) -> rho_dom, `Q_m` stays in a compact subset of `R^2_{>0}` (cost bound), and any limit point is weakly solvable with cost `rho_dom`. So `rho = rho_dom` holds *exactly* (and `Decide P y theta` holds iff `theta >= rho_dom`), not only up to 1.5e-5.

## 5. Reduction correctness (sketch) and what is open

Source: MAX-CUT on graphs of maximum degree 3. Drawing: each vertex a bus switch chain, each edge a wire composed of U-segments (NOT) and V-segments (copy), crossings are always U x V (the gadget above), the last link of each edge wire is an antiferro coupler of strength `J_e` with `J_e < min(wire-break costs) = 0.09`.

**Claim.** `rho(P_G, y_G) = base + J_e (|E| - maxcut(G))` up to an additive error `delta`, with `base = sum` of the gadget ground energies; YES iff `rho <= base + J_e(|E| - k)` for MAX-CUT value `>= k`, provided `delta < J_e/2`.

*Sketch.* (i) *Locality/additivity*: `rho` splits into a sum over gadgets plus interactions between adjacent gadgets, terminal-dependent; for gadgets far apart in the sense of conflicts (no conflicting pairs across gadgets) the constraint system decouples and E is additive. (ii) *Gadget tables*: each crossing has terminal table `E(U_in,U_out,V_in,V_out)` with zero on the four valid patterns (R, P, Cor. 2: exact up to the gap of Prop. 3(d)) and `>= 0.0902` elsewhere (numerical). Wires have link cost `>= 0.09` per violation. (iii) *Gap*: a configuration with `r >= 1` broken links costs `>= 0.09 r`, while it can unfrustrate at most one designated coupler per broken wire, saving `<= r J_e < 0.09 r`; so a minimiser has no breaks, all vertex bits propagate, and the cost is `base + J_e * #{uncut edges}`, minimised by a max cut. (iv) full `rho` instead of `rho_dom`: Remark above.

Open, in order of risk:

1. **P-symmetry gap (Prop. 3(c),(d))**: the 12 extra pairs must be shown inactive, or the level profile changed. Without it the U-phase degeneracy is only numerical (1e-5), and a U-phase field of size `epsilon` per crossing can accumulate over `O(n^2)` crossings against `J_e ~ 0.05`.
2. **Corners (U <-> V links) and the degree-3 vertex switch**: terminal tables, parity of inversions along each edge wire (a U segment inverts, V copies; the designated coupler must come out antiferro in the vertex bits: needs a parity-adjusting element or a ferro coupler of strength `J_e`).
3. **Global level profile**: `y = 1 + eps F(x+y)` with `F` decreasing and concave at every crossing, `max y < 2 min y`, and the exact tie conditions of the crossing (centre V level = U level, `bot V_{-1}` = `top U`) simultaneously for all crossings; plus the weak solvability of the whole instance (now checked per gadget only, and weak solvability is not additive over gadgets).
4. **Additivity**: exact decoupling of far gadgets and of the cost, including that no cross-gadget conflicting pair can be violated at near-optimal cost (cf. the 12-pair issue: such pairs are exactly where a "far, hence inactive" argument is needed and not available from a-priori cost bounds, since the cost to violate a pair is about 3 while rho is about 10).
5. **Rational data**: prices `u^{x}` with `u = r^2`; R and P are exact for these. The y-levels are rational. The thresholds are then algebraic and not closed-form, so the YES/NO separation has to be argued by the gap `J_e/2` against the controlled error, which forces explicit error bounds (margin in the Remark, accumulated over `O(n^2)` gadgets).
