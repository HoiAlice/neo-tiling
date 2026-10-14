# PERT-2[phi]: how much of the NP-hardness construction survives for a class of costs phi

Scripts and outputs: this directory (`phi_dual.py`, `run_tables.py`, `kscan.py`, `kvar.py`, `l1.py`, `concave_pair.py`, `tight.py`, `t_pairs*.py`; `out_*.txt`, `kscan_out.txt`, `kvar*_out.txt`).
Source: `workbench/NP-HARDNESS.md` (NH), `gad/np_*.py` (builders reused through `sys.modules['np_dual'] = phi_dual`).
Python: project `.venv`. "Rigorous" below = interval-arithmetic weak-duality lower bound (mpmath `iv`, 60 digits, rational multipliers), exactly as `np_dual.py`, with the conjugate `phi*` in place of `|g| - 1 - |g| ln|g|`; the upper values `hi` are floats. The code reproduces every NH number for `phi_pi` (X_K = 0.1229644, V break 0.085758, margins, 256-pattern K^+ table).

## 0. Verdict (read this first)

1. **The claimed theorem "for every phi in C there is a grid step h such that the library works, hence PERT-2[phi] is NP-hard" is NOT established, and for the library as written it is false as stated.** The crossing core K (and only K) is calibrated to phi_pi. For phi(r) = r^2 (every h, by homogeneity), cosh r - 1 (h >= 0.2) and |r|^p with p >= 1.75 (h = 0.2) the gadget K violates the one thing Lemma C needs: a *non-satisfied* terminal pattern is **cheaper** than the satisfied ones (for r^2 exactly by E_S = h^2/2; exact rational numbers in Sec. 6.2). So Lemma C is false for the NH library with those phi.
2. **Everything else in the library is robust.** For phi in {phi_pi, r^2, cosh r - 1, |r|^1.5} at the NH step h = 4 ln(21/20), all blocks except K/K^+ (pairs, U chains with a weak link, V chains of 2/3/4, five corner windows, vertex-U pair, degree-3 star with outward neighbours) pass with margin (rho_B/J_e >= 1.17 everywhere, >= 8 for r^2/cosh), and for strictly convex phi this is *explained by a theorem* (Prop. Iso, Prop. eps): the zero-excess/positive-excess pattern of every block with S = sum B is phi-independent, and the weak link can be made arbitrarily weak by moving its offset a -> 4.
3. **What is proved for the class C_s = {even, strictly convex, phi(0)=0}** (Sec. 3, by hand): own pair `B = 2 phi(delta/2)`, pair/link closed forms `J(a) = 2 phi((4-a)h/2)`, `E_S >= 4 J_e` for every convex phi, Lemma M / Corollary M, phi-independence of the isolated configuration and of the zero-excess patterns, and the weak-link tuning. Consequence (Theorem A, Sec. 4): **the lower-bound direction of NH reduces, for every phi in C_s and every h > 0, to ONE phi-dependent finite certificate: the "K ordering" (the 12 non-satisfied terminal patterns of K, and the K^+ rows, cost strictly more than the satisfied ones).** The tuning of the weak offset a = 4 - eps removes all other phi-dependence of the lower bound.
4. **K ordering holds** (numerically, interval-certified): phi_pi for h in [0.02, 0.5] (tested 0.02, 0.05, 0.1, 0.15, 0.195, 0.3, 0.5); |r|^p for p in [1.02, 1.5] at h = 0.2; and, after re-tuning the geometry (strong step u, V box), for r^2 (u = 2.25, 2.5), cosh at h = 0.2 (u = 2.25, 2.5), phi_pi at h = 1 (u = 1.75, 2.0), |r|^3 (u = 1.75, V box 6). It fails with the NH geometry for r^2, cosh, p >= 1.75, phi_pi h >= 1. **A single geometry that works for the whole class does not exist in the family I scanned (u, V box, V step), and I have no proof that a retuned K exists for every strictly convex phi.** The retuned libraries (stars, corners, K^+) were not re-run (the NH builders hard-code u = 3).
5. **phi(r) = |r|** (L1 in logs): the construction degenerates completely. The U pair has excess **zero for all four bit patterns for every a <= 4** (explicit configuration, Sec. 5, by hand), and by LP every block of the library (K 16 patterns, V chains, star) has all patterns at exactly `sum B`: no coupling at all. phi_pi = |r| + r^2/2 + ... works at h = 0.195 only because the quadratic part is large enough (Sec. 5.3: the strong-link closed form needs h >= ~0.17; smaller h still works through a different class, with margins O(h^2)).
6. (WS) and (L) are **not** phi-independent in the sense of the task: the combinatorial *order type* is, but (WS) is about the exact tie structure of the glued optimum, and the tight-conflict set of K's optimum depends on phi (`tight.py`: symmetric difference 2 for pow 1.5/1.25 and phi_pi at h = 0.5, 9 for r^2, cosh, |r|^3, versus phi_pi at h = 0.195). So (WS) must be re-verified per phi; I did not.
7. Non-even phi, non-log costs, non-convex phi: Sec. 7-8. Concave `|r|^q` (q < 1): Lemma 1 fails, but the pair keeps exactly two ground states and a tunable gap; **open**.

## 1. What is phi-free (checked against NH)

* Lemma 0 (weak solvability => no strict domination), `rho >= rho_dom`: only uses the cone argument. phi-free.
* Conflict sets, order types, tilings (Lemma T), parity (Lemma P), layout (L), spacing rule R *as a combinatorial statement*: phi-free. Only the numerical constant D (max displacement) in R depends on phi.
* Symmetries: swap `R` (x <-> y; needs the **same** phi in both coordinates) and point reflection `P` (inversion q -> c/q, r -> -r; needs phi **even**). CP Thm 1 and Prop. X (exact equality of the four satisfied terminal states of K) use only these, hence hold for every even phi. The finite invariance check of the conflict set (`np_pgap.py`) is phi-free.
* The isolated configuration of a switch (top -delta/2, bottom +delta/2 in its bit coordinate) for strictly convex even phi (Prop. Iso).

## 2. Inventory of phi-dependence in NH (every inequality / identity used)

Notation: `f = phi`, `delta = d h`, `gamma = (4-a) h`, `B(d)`, `J(a)`, `E_S = J(3)`, `J_e = J(a_weak)`.

| # | Where in NH | Statement | phi-dependence | Status for convex even phi |
|---|---|---|---|---|
| I1 | Lemma 1 | own pair cost `>= B(d) = 2 f(delta/2)` | convexity (Jensen) + monotone on [0,inf) | proved, Sec. 3.1; equality set = one point iff f strictly convex |
| I2 | Prop. P natural class | equal bits `2B + J(a)`, `J(a) = 2 f(gamma/2)`; different bits `2B` | convexity (same Jensen) | proved for the natural class |
| I3 | Prop. P other classes | every non-natural class has excess `>= 0.255` (a=3) `/ 0.400` (a=3.75) | **genuinely phi,h dependent** (a convex program) | NOT automatic: fails for small h (Sec. 5.3); replaced by Prop. eps (true weak excess = natural for a close to 4) |
| I4 | Prop. P, Cor. M | `E_S >= 4 J_e` | `f(h/2) >= 4 f(h/8)`: convexity with f(0)=0 | proved for every convex f, equality iff f linear on [0,h/2] (Sec. 3.3) |
| I5 | Lemma M / Cor. M | matching bound with credits `2 J_e` strong, `J_e` weak | uses only I4 and pair excess | proved, phi-free given I4 |
| I6 | Sec. 5.4 | S = sum B for V chains, corners, stars, wires (zero excess) | iso configuration feasible: combinatorial | **phi-independent** for strictly convex f (Prop. Iso) |
| I7 | Sec. 5.4 | violated patterns of those blocks cost `>= S + credit * J_e` (margins 0.033-0.17) | positivity automatic (Prop. Iso); size needed is `<= rho_B`, J_e adjustable | automatic after tuning J_e (Prop. eps) |
| I8 | Sec. 5.2 | K: four satisfied patterns equal (CP + Prop. X) | symmetry only | phi-free for even f |
| I9 | Sec. 5.2 | K: 12 non-satisfied patterns cost `>= S_K + (credit) J_e`; `X_K` constant in theta | **genuinely phi,h,geometry dependent** | the single non-automatic ingredient; certified numerically per phi (Sec. 6) |
| I10 | Sec. 5.3 | K^+ rows, additivity `S_{K+} = S_K + sum B_nbr`, interface slack `>= h` | phi,h dependent (K's optimum positions) | LB needs only `S_{K+} >= S_K + sum B` (relaxation, free) plus the K^+ rows (numerical); UB needs the slack (numerical) |
| I11 | Lemma G / Sec. 7.1 | glued point cost `S0 + J_e*#uncut`, pooled weak pair at `+-gamma/2` in the other coordinate | closed forms of I2 | proved (positions phi-free) |
| I12 | Sec. 7.2 | displacement `D`, rule R | `D(phi,h)` = max displacement of K optimum | finite constant; R is "`2 D / h` grid steps", absorbed by the module M |
| I13 | Sec. 7.3 | (WS) | exact tie structure of the glued optimum | phi-dependent (Sec. 0.6), not re-verified |
| I14 | Sec. 3.3 theta | `theta = S0 + J_e(|E|-k) + J_e/2` needs `S0, J_e` to precision `<< J_e/2` | `X_K(phi,h)` must be a computable constant; prices `rho^m` rational needs `h = 4 ln rho` | h can be perturbed (all conditions open) except the tight closed forms I2, which are exact for any h |

## 3. Proved statements for phi in C (even, convex, phi(0)=0, phi>0 off 0)

Facts used: phi is continuous, nondecreasing on [0,inf) (convex, even, minimum at 0), `phi(l x) <= l phi(x)` for `l in [0,1]` (convex, phi(0)=0), strictly increasing and strictly sub-homogeneous if strictly convex.

**3.1 Lemma 1 (own pair).** Any feasible Q has `cost{t_s,b_s} >= B(d) := 2 phi(delta/2)`; the other coordinate costs >= 0. *Proof.* Need `u + v >= delta`, `u = a_t - x_t`, `v = x_b - a_b`; `phi(|u|)+phi(|v|) >= phi(u+)+phi(v+) >= 2 phi((u+ + v+)/2) >= 2 phi(delta/2)` (Jensen, monotone). If phi is strictly convex the minimiser is unique (`u = v = delta/2`, nothing else moves); if phi is affine on [0, delta/2] the minimiser set is the whole segment `u + v = delta, u, v >= 0`. QED. (For the exact Lean-style statement this is NH Lemma 1 with `e^|r| - 1` replaced by phi.)

**3.2 Pair closed forms (natural class).** For two U switches at step a, equal bits (x,x): the x-problem is two own pairs, the cross conflict `(t_0,b_1)` is satisfied at their optimum (slack `a h`); the y-problem is a single constraint with gap `gamma`, minimum `2 phi(gamma/2)` (3.1). Different bits: both cross conflicts are closed by the own moves iff `delta/2 >= gamma` i.e. `a >= 2`; cost `2B`. So `J(a) = 2 phi((4-a)h/2)`, `E_S = 2 phi(h/2)`. Verified numerically for phi_pi, r^2, cosh, |r|^1.5, |r|^3 (`t_pairs.py`: natural value = closed form to 1e-9).

**3.3 `E_S >= 4 J_e` for every convex phi.** `phi(h/8) = phi((1/4)(h/2)) <= (1/4) phi(h/2)`. Equality iff phi is linear on [0,h/2] (L1: equality). For strictly convex phi the inequality is strict; the ratio is huge when phi is flat at 0 (for |r|^p the ratio is exactly 4^p; numerics: r^2 16.000, cosh 16.012, pow1.5 8.000, phi_pi 4.151).

**3.4 Lemma M and Corollary M** hold verbatim for any phi for which `e_S >= 4 e_W` where `e_S, e_W` are the *true* equal-bit excesses of the strong/weak pair (they equal `E_S`, `J_e` when the natural class is the minimum). Proof unchanged (NH Sec. 2): it uses only the pair excesses.

**Prop. Iso (isolated configuration, strictly convex phi).** For a block B and bit pattern tau, let `iso(tau)` be the configuration with every switch at its isolated optimum (top `-delta/2`, bottom `+delta/2` in coordinate `tau_s`). Then (i) `iso(tau)` does not depend on phi; (ii) `m_B(tau) >= sum_s B_s`, with equality iff `iso(tau)` satisfies every conflict of B (the sum of own-pair costs has `iso(tau)` as its unique minimiser by 3.1). *Proof.* Lemma B/3.1 and strict convexity. QED.
*Consequences.* (a) `S_B = sum B` for a block with some bit pattern having feasible iso configuration; the set of such patterns is phi-independent. From the phi_pi tables (S - sum B = 1e-10 on satisfied patterns, `m - sum B > 0` on violated ones) this holds for **all** strictly convex phi for: U pair/chains with weak link (any a close to 4 too, `t_pairs`), V chains, corner windows, vertex-U pair, stars of degree 2-4 (the certified arm subsets). (b) For such a block every violated pattern has `m_B(tau) - S_B > 0` automatically; the constant `rho_B = min_tau (m_B(tau) - S_B)/credit(tau)` is therefore positive (finitely many patterns). Numerically confirmed for r^2, cosh, pow 1.5 (Sec. 6.1).

**Prop. eps (weak link tuning).** Let `a = 4 - eps`. The true weak equal-bit excess is `e_W(eps) = min(2 phi(eps h/2), c_other(eps))` where `c_other` is the minimum excess over the non-natural routing classes. Each class value is the minimum of a convex program depending continuously on a, and at `a = 4` every non-natural class has excess `> 0` for strictly convex phi (the unique 2B configuration for equal bits violates `(t_0,b_1)` in y and `(t_1,b_0)` in x, hence satisfies only the natural routing, with a tie). So there is `eps_0(phi,h) > 0` with `e_W(eps) = J_e := 2 phi(eps h/2) -> 0` for `eps < eps_0`. Numerics: phi_pi, h = 0.195: at a = 3.99, natural 0.00195, other classes 0.454 (ratio 232); phi_pi h = 1, a = 3.9: 0.1025 vs 76.4; r^2 a = 3.75: 0.00125 vs 0.5625 (`t_pairs*.py`). Since all non-weak relations of blocks with `S = sum B` have `rho_B > 0` and `rho_K` etc. are fixed, **choose eps so small that `J_e <= min_B rho_B / (max credit)` and `4 J_e <= e_S`**: the credit inequalities of the whole library (except the genuinely phi-dependent K, K^+ rows, which are constants independent of eps, and also made `>= J_e` by the same choice) hold.
*Caveat.* Moving the weak offset from 3.75 to 4-eps changes geometry only inside U pairs; I re-ran only the pair (and the weak-link chain blocks reduce to the pair by Cor. M). The weak link at a close to 4 uses grid `(1/q) Z` with q ~ 1/eps (prices `rho^m`, m up to q times the layout size, still polynomial bit size for eps = 1/const).

## 4. Theorems

Let C_s = {phi even, strictly convex, phi(0)=0} (strictly convex implies phi > 0 off 0). Fix the NH layout parameters (L), the library geometry (strong step u, V box 5, ...), a grid step h (prices `rho^m`, `h = 4 ln rho`, rho rational; all conditions below that are strict inequalities survive a small change of h; the closed forms are exact for any h), the weak offset `a = 4 - eps`.

**Certificate Cert-K(phi,h,geometry).** (K1) the four satisfied patterns of K have equal minimum `S_K = sum B + X_K` (automatic, Prop. X); (K2) every one of the 12 non-satisfied patterns tau has `m_K(tau) - S_K >= c_K * credit(tau)`, `c_K > 0` (credits: V-eq 1, U-ne 1; both broken 2); (K3) the 256 rows of K^+ (K internal credit 1, neighbour links 2) have `m_{K+}(tau) - (S_K + sum B_nbr) >= c_K credit(tau)`.

**Theorem A (lower bound, any phi in C_s, h > 0).** Assume Cert-K(phi,h,geometry), the combinatorial layout (L1-L5) and the other library facts that are phi-free or automatic by Prop. Iso. Then for all `eps < eps_0(phi,h,c_K)`: `rho_dom(P,y) >= S0 + J_e (|E| - maxcut(G))`, `S0 = sum B + n_x X_K(phi,h)`, `J_e = 2 phi(eps h/2)`; hence (Lemma 0) `rho >= ` the same, and "maxcut < k => NO".
*Proof.* NH Sec. 6 line by line, with: Lemma 1 = 3.1; Lemma M/Cor. M = 3.4 (using 3.3 and Prop. eps); the credit tables = Prop. Iso (b) + Prop. eps + Cert-K; Lemma T and Lemma B are phi-free; Lemma C's equality `S0^{(1)} = S0^{(2)}` is **replaced** by `S0^{(1)} >= S0^{(2)} = S0` (since `S_{K+} >= S_K + sum B_nbr` by dropping conflicts; in the numerics equality holds: S_{K+} - sum B = X_K to 1e-7 for phi_pi, r^2, cosh, pow 1.5), which is enough for the lower bound because K^+ rows are certified against `S_K + sum B_nbr` (K3). QED (modulo the cited NH ingredients).

**Theorem B (upper bound, conditional).** As Theorem A plus (WS) for the glued optima of phi, the interface slack of the clusters (numerical for each phi) and R with `D(phi,h)`: `rho <= S0 + J_e (|E| - cut)`. Same proof as NH Sec. 7 (positions of isolated switches and of the pooled weak pair are phi-free; only K's optimum, X_K and D depend on phi).

**Corollary (conditional hardness).** Under A, B (and (L), (WS), which remain open even for phi_pi), PERT-2[phi] is NP-hard for every phi in C_s, h > 0, geometry for which Cert-K holds and (WS)(phi) holds. By Sec. 6 this includes (numerically): phi_pi, h in [0.02, 0.5] with NH geometry; |r|^p, p in [1.02, 1.5], h = 0.2 with NH geometry; r^2, cosh (h = 0.2), phi_pi (h = 1), |r|^3 with retuned K (library otherwise not re-run).

**What is not true / not shown.**
* No uniform-in-phi h: for r^2, cosh r - 1, |r|^p (p >= 1.75) there is no h at all for the NH geometry (homogeneity for the pure powers; at the tested h for cosh, phi_pi h >= 1).
* "For every phi in C there is an h and a K": not proved. Convex phi that are exactly affine on large intervals reduce to L1 at every scale where the library lives (Sec. 5), and the degeneracy persists; so for non-strictly convex phi one must put the scale h where phi is already curved (e.g. a Huber-type phi at h comparable to the kink). I did not analyse piecewise-linear phi with kinks.

## 5. The boundary case phi(r) = |r|

**5.1 Exact degeneracy of the U pair (by hand).** Put `delta = 4h`, tops `t_0 = 4, t_1 = a + 4`, bottoms `b_0 = 0, b_1 = a` (x coordinates, units of h). For a <= 4 let c in [a,4] and move all four points to x = c: all four conflicts (all routed through x) hold, cost `(4-c) + (a+4-c) + c + (c-a) = 8 = 2B` (B(4) = 4h in L1). The same in y. Different bits: the natural configuration costs 2B. So **all four bit patterns cost exactly `2B`** (LP confirms, `l1.py`: excess 0.0 for a = 3, 3.75, 3.99): J = 0 at every a <= 4; the "pooling" configuration costs nothing because L1 is indifferent to how the move is split. (For phi_pi the same configuration costs 0.255 (a=3) / 0.400 (a=3.75): the non-natural classes, all-x being the minimum.)
**5.2 Whole library (LP, `l1.py`).** K: all 16 terminal patterns have excess 0 over `sum B` (X_K = 0); V chains of 2, 3, star of degree 3: all patterns at `sum B`. So the instance value is `sum B` for every bit pattern: **the reduction produces a constant**. Which inequality degenerates: every credit inequality `m(tau) >= S + credit J_e`, with `E_S = 4 J_e` also tied (3.3) and `J_e` effective = 0. A fix needs a different gadget (e.g. unequal arms so that no common threshold is available); none is known to me. Whether PERT-2[|r|] is even NP-hard is open to me (it is an LP over routings; the box problem, phi_infinity, is polynomial at d=2).
**5.3 phi_pi as a perturbation of L1 (`t_pairs3.py`).** ratio = (min non-natural class excess)/(natural `E_S`) at a = 3: h = 0.01: 0.046; 0.05: 0.246; 0.1: 0.537; **0.195: 1.244**; 0.5: 5.64. So NH's closed form `E_S = 2(rho^2 - 1)` holds only for h >~ 0.17; below it the true strong excess is the all-x class value (O(h^2)). The reduction still has positive margins (Prop. Iso + Prop. eps; K-scan OK down to h = 0.02, Sec. 6.3) but the closed form for `E_S` is replaced by a computed constant. At a = 3.99 the natural class wins for all tested h (ratio 8.1 at h = 0.01).

## 6. Numerics

All at the NH rational step `h = 4 ln(21/20) = 0.19516`, weak offset 3.75, unless stated. `rho_B` = min over violated patterns of `(lo - S_B)/credit` (largest admissible J_e for the block); column = `rho_B / J_e` (>= 1 required; the weak-link chains are tight at exactly 1.000 by Prop. P). "FAIL" = a violated pattern is cheaper than satisfied.

### 6.1 Library at h = 0.19516 (`out_*_h0195.txt`, `run_tables.py`)

| block | phi_pi | r^2 | cosh r - 1 | abs r ^1.5 |
|---|---|---|---|---|
| closed forms: B(4), B(5) | 0.954911, 1.257789 | 0.304701, 0.476096 | 0.154295, 0.242808 | 0.487712, 0.681598 |
| E_S = 2f(h/2), J_e = 2f(h/8) | 0.2050, 0.04939 | 0.019044, 0.001190 | 0.009529, 0.000595 | 0.060964, 0.007620 |
| E_S/J_e (>= 4 needed) | 4.151 | 16.000 | 16.012 | 8.000 |
| true e_S, e_W (B&B) = closed forms | yes | yes | yes | yes |
| V chain 2/3/4 | 1.423 | 24.0 | 24.96 | 4.70 |
| U chains (S,S / S,W / W,S / S,W,S) | 2.075 / 1.000 / 1.000 / 1.000 | 8 / 1 / 1 / 1 | 8.006 / 1 / 1 / 1 | 4.000 / 1 / 1 / 1 |
| corner windows (5) | 1.169 or 1.423 | 8 or 24 | 8.006 or 24.96 | 2.938 or 4.70 |
| vertex-U pair | 2.708 | 18.0 | 18.03 | 7.348 |
| star deg 3 + outward (7 sw.) | 1.423 | 8 | 8.006 | 4.000 |
| **crossing K** (16 patterns) | **1.736** | **-16 (FAIL)** | **-16.01 (FAIL)** | **3.977** |
| X_K | 0.1229644 | 0.0888713 (=7/3 h^2) | 0.0451007 | 0.0855956 |
| K^+ (256 patterns), S_{K+} - sum B | 1.423; 0.1229643 | -16 (FAIL); 0.0888713 | -16.01 (FAIL); 0.0451007 | 3.977; 0.0855956 |
| S - sum B on zero-excess blocks | <= 1e-9 | <= 1e-15 | <= 2e-9 | <= 6e-9 |

(For K: satisfied patterns equal to 1e-7 or better in all cases, Prop. X.) The V/U/corner/star/vertex rows for r^2 and cosh are not merely above 1: they are enormous, because at a = 3.75 `J_e` is tiny; the whole non-K library is "automatic" in the sense of Sec. 3.

### 6.2 The K failure, exactly (r^2, `kscan_out.txt`, units h^2, S_K = sum B + 7/3)

K excess over S for the 12 non-satisfied patterns: `(0101)` (V broken) 5/6; `(0011)` (U broken) 1/2 = E_S; `(0000)` (U broken) **-1/2 = -E_S**; `(0001)` (both) 1/3. So the pattern with U_in = U_out and V_in = V_out is cheaper than the satisfied ones by exactly `E_S`: K does not enforce `U_in != U_out`, and a "U chain through K" costs less when broken. Same for cosh (h = 0.2: -E_S exactly) and phi_pi at h >= 1 (-1.0 E_S), |r|^p, p >= 1.9 (-1.000 E_S).

### 6.3 K scan (NH geometry), excess/E_S, X_K/E_S, verdict (`kscan_out.txt`)

|r|^p, h = 0.2: p=1.02: X_K/E_S 0.022, min excess 0.012 E_S OK; 1.05 OK; 1.1 OK; 1.25 OK (0000: 0.996 E_S); 1.5 OK (V break 0.497 E_S, 0000: 0.80 E_S); **1.75 FAIL (0000: -0.072 E_S)**; 1.9, 2, 2.5 FAIL (-1.000 E_S).
phi_pi: h = 0.02 / 0.05 / 0.1 / 0.15 / 0.195 / 0.3 / 0.5: OK, X_K/E_S = 0.044 / 0.117 / 0.257 / 0.423 / 0.600 / 1.122 / 2.331 (0000: 0.143 / 0.381 / 0.845 / 0.968 / 0.951 / 0.891 / **0.268**); h = 1, 2: FAIL (-1.000 E_S).
Pattern: success iff X_K/E_S <~ 2.4-3 (threshold between 2.33 and 3.0 in this data).

### 6.4 Retuned geometry (`kvar_out.txt`, `kvar2_out.txt`; U step u, V box dV, V step 1; K only)

| phi | h | geometry | K min excess over S (credit 1) | verdict |
|---|---|---|---|---|
| r^2 | 0.2 | u=2.5, dV=5 | +0.0217 (V break), 4 satisfied equal (1e-8) | OK |
| r^2 | 0.2 | u=2.25, dV=5 | +0.0158 | OK |
| r^2 | 0.2 | u=2.75, 3, 3.25, 3.5 | -0.011 ... -0.020 | FAIL |
| cosh | 0.2 | u=2.25 / 2.5 | +0.0083 / +0.0091 | OK |
| cosh | 1.0 | u=2.5 | -0.589 | FAIL |
| phi_pi | 1.0 | u=2.0 / 1.75 / 2.25, 2.5 / 1.5 | +0.324 / +0.148 / -1.05, -2.23 / -1.37 | OK / OK / FAIL / FAIL |
| |r|^3 | 0.2 | u=1.75, dV=6 | +0.0056 | OK |
| |r|^3 | 0.2 | u=1.75 dV=5 | +0.00077 (thin); u=2.0, dV=6: +0.0069; u=2.0, dV=5: -0.016; dV=4: -0.016 | mixed |
| r^2 | 0.2 | u=3, dV=4 or 6, V step 1 or 1.5 | -0.010 ... -0.020 | FAIL |
Not run: stars/corners/K^+/pair classes at the retuned steps, except pair class tables (`t_pairs2.py`: natural class is the minimum with ratio 4.7-6.5 at the strong step, hundreds at the weak one). The tuned values are existence evidence, not a theorem.

### 6.5 Tie structure of K's optimum (`tight.py`, pattern 0100)
#tight conflicts: phi_pi h=.195: 14; phi_pi h=.5: 12 (sym. diff. 2); pow1.5, pow1.25: 12 (2); r^2, cosh, |r|^3 (h=.2): 15 (9). So (WS) at phi_pi does not transfer.

## 7. Non-even phi, non-log costs (what transfers)

*Asymmetric phi (phi(r) != phi(-r), same phi in both coordinates).* Transfers: Lemma 0, the swap symmetry R, conflict sets/order types, tilings, parity, the dual/B&B method (`phi*(-g)` replaces `phi*(|g|)`). Breaks: (i) the point reflection P (inversion q -> c/q maps r to -r), hence **Prop. X: the four satisfied terminal states of K are only R-equivalent in pairs** (E(s) = E(Rs) stays, E(s) = E(Ps) fails): two different energies for K's satisfied states, i.e. a bias (field) on every crossing that the construction must cancel (e.g. pair each crossing with its P-mirror, which the layout does not do). (ii) Lemma 1: `B = min_{u+v>=delta} phi(-u) + phi(v)` (top moves down by u, bottom up by v): the minimiser is no longer `u = v = delta/2`, so the isolated configuration, hence all slacks/D, depend on phi, and Prop. Iso (i) fails; combinatorics of iso(tau) must be rechecked. (iii) The glued weak pair `+-gamma/2` and `E_S >= 4 J_e` need re-derivation with the two branches (the latter still holds if phi is convex with phi(0)=0 on each branch, by the same sub-homogeneity). Not computed.
*Costs `phi(q - p)`, `|q-p|^2`, i.e. not functions of log q - log p.* In log coordinates the cost of a point is `p^s * g(e^r - 1)`, a position-dependent weight. Transfers: Lemma 0 only. Breaks: translation invariance (all copies of a gadget at different log-prices have different energies, with weights varying by `exp(O(poly))` over the layout), P (inversion `q -> c/q` is not an isometry of `|q-p|`), the relation between energies of different gadgets (sum B no longer a layout-independent constant; Max-Cut edge weights `J_e` become position-dependent, potentially exponentially, which changes the problem to weighted Max-Cut with possibly dominated weights). So NH does not transfer, even heuristically; a scale-invariant substitute is needed (e.g. relative costs). Open.

## 8. Non-convex and the dividing line

**8.1 Concave on [0,inf), phi = |r|^q, q < 1 (`concave_pair.py`, exact by vertex enumeration).** Lemma 1 fails: `B = phi(delta)` (one endpoint moves the whole distance; equal splitting is the worst, `2 phi(delta/2) = 2^{1-q} phi(delta)`), and the "bit" is no longer a coordinate but (which endpoint, which coordinate), 4 states per switch. U pair, q = 0.5, h = 1: the pair minimum is exactly `2B = 4.000` at a = 3, 3.75, 3.9, 3.99 with **exactly two optimal vertices** (b_1 moves +4 in x and b_0 moves +4 in y, or the mirror), the next level at +0.646 (a=3), +0.436 (3.75), +0.291 (3.9), **+0.0975 (3.99)** (= phi(gamma) up to 0.0025). At a = 4: 400 optimal vertices (uncoupled). So the antiferromagnetic link survives, with a tunable gap ~ phi(4-a), but the NH machinery (Lemma 1, equal splitting, E_S >= 4 J_e via Jensen, the isolated configuration, Cor. M) does not apply. q = 0.75: same structure. Status: **open**; neither a proof nor a counterexample; K, V chains, corners not analysed.
**8.2 Quasi-convex non-convex (e.g. capped phi = min(|r|, c), or convex then concave).** The B&B/dual certificates are invalid (nonconvex programs). Capped phi: at scale where all moves are below the cap it is L1 (degenerate, Sec. 5); where the cap bites, moves above c are free, which creates box-like freedom. Open.
**8.3 The dividing line (conjectural; proven pieces).** (a) phi in {0,inf} (box): polynomial at d = 2 (BOX-THEOREM). (b) phi = |r|: the NH library is degenerate (Sec. 5); status of the problem unknown to me. (c) strictly convex with moderate curvature: the construction works (Cert-K numerically). (d) very curved phi (r^2 at all h; cosh at h >= 0.2; p >= 1.75; phi_pi at h >= 1) needs a re-tuned K (exists numerically in several cases). So the "right" line is not "finite and strictly positive vs convex": the hardness proof needs (1) enough strict convexity at the working scale (excludes affine pieces, |r|) and (2) a crossing gadget compatible with the curvature (K calibration: X_K/E_S <~ 2.4-3 for the NH geometry). As p -> infinity the problem approaches the polynomial box problem; I have no argument whether PERT-2[|r|^p] stays NP-hard for large p (|r|^3 retuned K exists, with thin margins 0.0008-0.0056), nor a polynomial algorithm.

## 9. Files
`phi_dual.py` (interval dual B&B for phi in {pi, sq, cosh, pow p}); `run_tables.py NAME p h a` (block library, Pool(8)); `kscan.py`, `kvar.py` (K tables/variants); `l1.py` (LP B&B, L1); `concave_pair.py`; `tight.py`; `t_pairs.py`, `t_pairs2.py`, `t_pairs3.py` (pair classes); outputs `out_*_h0195.txt`, `kscan_out.txt`, `kvar_out.txt`, `kvar2_out.txt`.
Not done: (WS) re-verification per phi; retuned full library; exact rational (Farkas) dumps for the new phi; proof that a K exists for every strictly convex phi; any analysis of piecewise-linear phi with kinks.

---

# 10. UPDATE: theorem for phi = r^2 and the smooth class (coordinator plan, steps 1-4)

New scripts: `lib_u.py` (whole library with parametrised strong step u, star attach offset att, weak offset aw, any phi), `glue_u.py` (Lemma G / rule R tests), `uniq.py`, `ties.py`, `l1_big.py`. Outputs: `lib_sq_u25.txt`, `glue_sq_u25.txt`. Builders validated by reproducing every NH phi_pi number at u = 3 (corners 0.0578/0.0703, star 0.0703, K 0.085758, D = 3.2137 h, glue slack h, kink slack 0).

## 10.1 Retuned geometry G* for phi = r^2 and the whole library (interval certificates, `lib_sq_u25.txt`, `glue_sq_u25.txt`)

Geometry G*: U wires with strong step **u = 5/2**; weak link offset **a = 15/4** (weak gap 1/4); V chains as in NH (box 5, step 1, same levels); crossing core K = 4 U (bottoms `((j-1.5)u, -(j-1.5)u)`, j = 0..3) + 5 V (as NH); star attach offset **att = 3** (centre to first U switch, then steps u); corner = V end aligned with the first U switch, then U steps u. phi = r^2, h = 1 (homogeneous: units h^2; any h gives the same ratios). J_e = 2((4-a)h/2)^2 = h^2/32, E_S = 2((4-u)h/2)^2 = 9h^2/8, E_S/J_e = 36.

rho_B = min over violated patterns of (lo - S)/credit (credit 2 strong/V/corner/outward, 1 weak/K-internal/star-internal); required rho_B >= J_e = 0.03125.

| block | S - sum B | rho_B (h^2) | rho_B/J_e |
|---|---|---|---|
| U strong pair: true e_S = natural | 0 | 1.125 | 36 |
| U weak pair: true e_W = natural | 0 | 0.03125 | 1.00 (tight, closed form) |
| U chains (S,S / S,W / W,S / S,W,S / S,S,S) | <= 2e-14 | 0.5625 / 0.03125 / 0.03125 / 0.03125 / 0.5625 | 18 / 1 / 1 / 1 / 18 |
| V chains 2, 3, 4 | <= 5e-14 | 0.75 | 24 |
| corner windows V1U2, V2U1, V2U2, V3U1, V1U3, V2U3 | <= 9e-14 | 0.4219 or 0.75 | 13.5 or 24 |
| stars deg 2 (six arm pairs), 3 (four), 4, with outward neighbours | <= 1e-13 | 0.5625 or 0.75 | 18 or 24 |
| **K** (16 patterns): S_K - sum B = X_K = 157/60 = 2.616667; satisfied four equal (6e-8) | 2.6167 | 0.541667 (V broken) | 17.3 |
| K excess over S, the 12 patterns | | 0000/1111: 71/120; 0001,0010,1101,1110: 17/15; 0011/1100: 9/8; 0101,0110,1001,1010: 13/24 | all > 0 |
| **K^+** (13 sw., 256 patterns): S_{K+} - sum B = 2.616667 = X_K (additivity) | 2.6167 | 0.541667 | 17.3 |

Everything is strictly positive; the smallest non-tight margin `(rho_B - J_e) * credit` is 0.510 h^2 (K, V broken). The weak-link rows are tight and are closed forms (Prop. P / Cor. M, by hand, valid for every convex phi).

Glue (all conflicts of the layout, glued point = K optimum + isolated switches + pooled kinks), r^2, G*:
* crossing core + wires, m = (1,1), (3,3), (5,5), (8,8) switches beyond the core, all four satisfied patterns: cost - (sum B + X_K) <= 5e-8 (float); min slack of every conflict not inside K: **0.5 h**; D = max |x - a| = **3.15 h** (hence rule R: 2D = 6.3 h, take R = 7 grid steps).
* U wire, 6 switches, weak kink pooled (both bit phases): cost - (sum B + J_e) = 0 exactly; non-kink slack 0.5 h; kink-pair conflicts exactly tight (by design); D = 2 h.
* stars of degree 2-4 at isolated optimum, all satisfied patterns: cost = sum B; min slack **0.5 h** with att = 3 (with att = u = 2.5 the slack is 0: exact ties, still feasible but undesirable; hence att = 3).
Mirrored orientations: transfer by the exact bijection of CP Thm 1 (swap R, reflection P; both are cost-preserving for r^2, even phi); not re-run directly.
Not done for G*: the full corner-relay-corner cluster, and any wire step other than u (steps in [2.5, 3.5] are covered by pair closed forms + Cor. M + non-adjacent conflicts (x-gap 2s - 4 >= 1), by hand, but the K^+ / corner / star blocks were certified only at exactly u).
The numbers are rational (r^2 gives QPs): X_K = 157/60 h^2 etc.; an exact-rational Farkas dump was not produced (the interval certificates are rigorous only modulo mpmath).

Uniqueness / nondegeneracy of K's optimum for r^2 (`uniq.py`, `ties.py`): the satisfied patterns have a **unique** optimal point over all routings (second-best routing class is +17/15 h^2 above, so no routing tie), tight conflicts have positive multipliers (min 0.2), but there are **two additional conflicts, (2,13) and (12,5), that are exactly tied at the optimum without being routed** (zero multiplier; degenerate). They stay exactly tied at the optimum for cosh r - 1 at h = 0.05, 0.2, 0.4 (the whole tie set of 14 equals the r^2 tie set), and the tie set changes at h = 1 (21 ties). Presumably forced by the P/R symmetry; not proved.

## 10.2 Theorem for r^2 and the smooth class

**Class S.** phi: R -> R even, convex, C^2, phi(0) = phi'(0) = 0 < phi''(0) =: 2c (so phi > 0 off 0 and strictly increasing on [0,inf)). Let theta(s) = sup_{|t|<=s} |phi''(t)/phi''(0) - 1| (modulus; theta(0+) = 0). 

**Lemma Cont (continuity).** Put psi_h(r) = phi(h r)/(c h^2). (i) By Taylor, psi_h(r) = r^2 (1 + eps), |eps| <= theta(h|r|). Hence psi_h -> r^2 uniformly on compacts. (ii) Let C0 = 150 (a bound, in the r^2/h=1 units, for every block value used: the largest is K^+, sum B = 135.5, X_K = 2.62) and M = sqrt(5 C0) = 27.4. If theta(hM) <= 1/2, then every configuration of a block with psi_h-cost <= 2 C0 has all displacements |r_t| <= M (convexity: psi_h(r) >= psi_h(M)|r|/M beyond M, psi_h(M) >= M^2/2 = 2.5 C0). (iii) For every routing R of a block, the minimum m_h(R) of the psi_h-cost satisfies (1 - theta(hM)) m_0(R) <= m_h(R) <= (1 + theta(hM)) m_0(R), where m_0(R) is the r^2 minimum (for r^2-values <= C0). Hence for every block B and pattern tau: |m_{B,h}(tau) - m_{B,0}(tau)| <= theta(hM) C0 (finitely many routings, min of finitely many). (iv) The weak excess `2 phi(h/8 * 1)/(c h^2) = (1/32)(1 +- theta(h))`.
*Proof.* (i) Taylor with Lagrange remainder: phi(t) = phi''(xi) t^2/2. (ii) as written. (iii) For the lower bound take a psi_h-minimiser of cost <= m_0(R)(1+theta) <= 2 C0, it lies in the ball of radius M, where cost_h >= (1-theta) cost_0 >= (1-theta) m_0(R); the upper bound evaluates cost_h at the r^2-minimiser. QED

**Theorem S (lower bound, class S).** Let mu = 0.51 (the smallest r^2-margin of Sec. 10.1) and
`h_0(phi) := sup{ h > 0 : theta(h M) <= 1.6e-3 }`, M = 27.4 (so 2 C0 theta + 2 theta/16 <= mu/... : need 2 theta C0 + 2 credit-weighted weak perturbation <= mu, i.e. theta <= mu/(2 C0 + 1) = 1.69e-3).
Then for every h <= h_0(phi) (and every rational rho with 4 ln rho = h' close enough), with the geometry G* (strong step 5/2, weak 15/4, star attach 3, K as in 10.1) and the NH layout (L), levels and spacing:
(1) every credit inequality of the library holds with the exact J_e = 2 phi(h/8) *as a closed form* for the weak links (Lemma 1, Prop. P natural class, Cor. M: by hand, any convex phi, using E_S >= 4 J_e which holds with margin 36 in the limit) and with margin >= mu c h^2 / 2 for all others (Lemma Cont);
(2) all zero-excess equalities `S_B = sum B` hold exactly (Prop. Iso: strict convexity of phi on the ball |t| <= hM, guaranteed by phi'' >= c/2 there; local strict convexity suffices because the minimisers lie in the ball by Lemma Cont (ii));
(3) K: four satisfied patterns equal (Prop. X, even phi), X_K(phi, h) = c h^2 (157/60 +- theta C0);
(4) Lemma C and Theorem LB hold: `rho(P,y) >= rho_dom(P,y) >= S0 + J_e (|E| - maxcut(G))`, `S0 = sum B + n_x X_K`.
**Upper direction.** The glued point has the r^2 slacks 0.5 h (and D = 3.15 h): since the optimum of K for phi_h converges to the unique r^2 optimum (unique over routings with gap 17/15 h^2, strictly convex psi_h near the ball), all non-tie conflicts keep slack >= 0.4 h for h <= h_1(phi) (same style of bound, not computed explicitly), the tied conflicts stay tied if the tie set is stable (verified for cosh, not proved), and Lemma G (cost = S0 + J_e #uncut) follows.
**Corollary S (conditional).** For every phi in class S and h <= min(h_0, h_1): PERT-2[phi] is NP-hard provided (L) (layout generator) and (WS)(phi, h) hold.

**Status of (WS) for r^2 and the class.** (a) (WS) for phi_pi does not transfer to r^2 or to the class: weak solvability is a *closed*, not open, condition and the glued optimum has exact ties (kinks, K's degenerate ties), so it is not stable under small perturbation of Q*; the claim "WS depends only on order type and ties" is not available because reachability uses the convex-hull geometry of Q = exp(log P + r) (Prop. 1 of WS-notes), which depends on actual positions. (b) I have NOT run the WS flow LP for G* (new geometry: new instance family); so WS(r^2, G*) is open, as WS(phi_pi) is. (c) What does hold: the *position* of the glued point is a continuous function of phi_h -> r^2 and the tie set agrees (cosh); a proof of WS for r^2 would therefore transfer to the class only with an additional margin argument (strict feasibility of the cone representation), which is not known. So Corollary S is conditional on WS for each (phi, h), not just for r^2.

**Example.** phi = cosh r - 1: phi'' = cosh, c = 1/2, theta(s) = cosh s - 1, so h_0 = arccosh(1.0016)/27.4 = 2.1e-3 (provably covered); the numerically tested h = 0.05-0.4 are far outside this crude proven range (the bound M = 27.4 is very pessimistic). For phi = r^2, theta = 0 and h_0 = infinity.

## 10.3 Kink class phi'(0+) > 0 (phi_pi-like) -- what is proved

* **Proved (modulo the same (L), (WS))**: phi = phi_pi = e^{|r|} - 1 at h = 4 ln(21/20), geometry of NP-HARDNESS.md; the lower-bound direction fully (NH Thm LB), certificates re-run here at u = 3 with identical numbers.
* **Evidence, not theorem**: K ordering holds for phi_pi at h in {0.02, 0.05, 0.1, 0.15, 0.195, 0.3, 0.5} (NH geometry), fails at h >= 1; |r|^p, 1 < p <= 1.5 at h = 0.2 (no kink but p -> 1). Full library re-run only at h = 0.195 (phi_pi, |r|^1.5).
* **Why no class theorem**: for phi'(0+) > 0 the rescaled costs phi(hr)/(h phi'(0+)) -> |r| (L1) as h -> 0, and L1 degenerates (10.4); the margins of phi_pi scale like h^2 relative to B ~ h, the strong-link closed form needs h >= ~0.17 (Sec. 5.3), and K ordering needs X_K/E_S <~ 2.4-3, which fixes a window of h that depends on the whole function phi, not just on a modulus at 0. A class statement would need: for every phi with a kink, a window of h (existence) -- not proved, since for phi with phi'' = 0 on [0, s1] (affine pieces) and large curvature only beyond, h must be chosen at the scale where phi first curves, and no certificate for such a profile exists. I do **not** claim a theorem.

## 10.4 Proposition L1 (phi(r) = |r|, no hardness claim)

**Proposition.** For phi(r) = |r| the NH library has no coupling: (a) [proved by hand] for the U pair at any step a <= 4 (any gap), every bit pattern has minimum cost exactly 2B = 8h (configuration: all four points to one threshold c in [a,4]h in the common coordinate, Sec. 5.1; the unequal-bit patterns by the natural configuration); hence E_S = J_e = 0 and the weak/strong distinction disappears. (b) [LP, float, `l1.py`] for K (all 16 patterns), V chains 2, 3 and the degree-3 star, all patterns have minimum exactly sum B (X_K = 0, all excesses 0). Consequently Lemma C degenerates to `cost >= sum B` and the reduction outputs the same value sum B for every graph: it cannot distinguish cuts. (c) [not proved] that rho_dom(P,y) = sum B for the *whole* reduction instance: lower bound sum B holds (Lemma 1 + B), the upper bound is verified only block-wise (up to 13 switches); a global LP check of the 25-switch instance was started (`l1_big.py`, result not collected). **The complexity of PERT-2[|r|] (L1 in logs) is open; nothing here suggests either hardness or an algorithm.**

## 10.5 Honest status table

| phi | h | geometry | lower bound (LB) | upper bound / (WS), (L) | verdict |
|---|---|---|---|---|---|
| phi_pi = e^{|r|}-1 | 4 ln(21/20) | NH (u=3) | proof modulo certificates (interval B&B + exact Farkas for K) | (WS), (L) open | NH status |
| r^2 | any (homogeneous) | **G*** (u=5/2, a=15/4, att=3) | all library certificates pass (Sec. 10.1), margins >= 0.51 h^2 except tight closed forms | glue slack 0.5 h, D = 3.15 h; (WS) not run, (L) open | LB: proved modulo certificates; UB: conditional |
| class S (C^2, phi''(0) > 0, convex) | h <= h_0(phi) explicit via theta | G* | Theorem S (continuity + hand lemmas) | + tie stability (verified for cosh), (WS)(phi,h) open for each phi | conditional hardness |
| cosh r - 1 | 0.05, 0.2, 0.4 | G* (K scan done at 0.2 only) | member of class S; K at u=2.5, h=0.2 OK (0.0091 margin), full library not re-run | ties equal r^2 up to h = 0.4 | covered by Theorem S for h <= h_0 (h_0 not computed numerically) |
| cosh r - 1 | >= 1 | any tested | K fails (u = 2.5, h = 1: -0.589) | | no certificate |
| |r|^p, 1 < p <= 1.5 | 0.2 | NH (u=3) | K ordering OK; full library at p = 1.5 (h = 0.195) | not run | evidence (non-C^2 at 0: not in class S) |
| |r|^p, p >= 1.75; p = 3 | 0.2 | NH fails; retuned K exists (|r|^3: u=1.75, V box 6) | K only | | open |
| phi'(0+) > 0 family | | | no class theorem | | open (Sec. 10.3) |
| |r| (L1) | | | construction degenerates: constant (Prop. L1) | | complexity open |
| asymmetric / non-log / non-convex | | | Sec. 7-8 | | open |

---

# 11. UPDATE 2: (WS) numerics for r^2 at G*, and the upper-bound theorem S-UB

New scripts: `ws_g.py` (cprime layout rebuilt at G*, glued optima, snapping, y rule, flow-LP check), `ws_k3g.py` (K_3 at G*), `ws_eps.py` (scale-free rescaling of y, two values of h), `tiegraph.py`, `tieext.py`. Outputs: `ws_sq_g.txt`, `ws_eps_out.txt`. The pipeline was first run as a control with phi_pi at the NH geometry (u = 3): cprime 16/16 and K_3 8/8 weakly solvable at the rule (c1, c2, s*) = (0.02, 0.07, 4), exactly as in WEAK-SOLV.md.

## 11.1 (WS) for r^2 at G*: what was run

* **Instances.** cprime layout (V chain s = -4..4, corner, corner arm U steps (u, u, a_w, u, att), vertex 2, edge E2 with vertices A, B, two weak links, crossing core K at the centre, K's U wire at bottoms ((j-1.5)u)) rebuilt at G* (u = 5/2, a_w = 15/4, att = 3): 25 switches, 50 points. K_3 (`gad/k3.py` layout, no crossing) at G*: arms (2.75, 3.75, 3) and (2.5, 3.75, 3.25), pure-edge strong step 2.54 (the pure edge needs `s = (2P - a_w)/6`; with P = 9.5 it is 2.54 >= 2.5; the original arm (u, a_w, att) = (2.5, 3.75, 3) gives 2.458 < 2.5, which I did not use), 27 switches.
* **Glued optima.** For every vertex-bit pattern (16 for cprime, 8 for K_3): K at its r^2 optimum (`kopt`, dual solution, B&B), all other switches isolated, weak kinks pooled when the two endpoint bits are equal (mismatch placed at the weak link), coordinates within 1e-5 snapped to a common value (exact ties). Prices Q = exp(x), h = 0.2 (NH's EPS) and 0.1.
* **y.** `y_bottom = F(s_c)`, `y_top = y_bottom + g`, g = 0.01, F concave piecewise linear with slopes c1 (s <= s*) and c2 (s > s*), s* = 4 (the s_c of the crossing U wire), via `ws_rule4.y_pw`; **no hand-set levels, full conflict set with no distance filter**.
* **Checks per pattern.** (a) dominance: every conflict (y_a > y_b) has a coordinate with Q_a <= Q_b at the glued point (cost identity = Lemma G holds); (b) weak solvability by the flow LP (`core.weakly_solvable`, exact flow LP on rationalised data with strict = False, floating-point data, **not** an exact rational certificate).

Results (h = 0.2):

| instance | (c1, c2, s*) | ratio max/min | dominance violations | weakly solvable |
|---|---|---|---|---|
| cprime G* | (0.02, 0.07, 4) | 1.75 | 0 | 8/16 (all v1 = 0 patterns fail) |
| cprime G* | **(0.02, 0.08, 4)** | 1.83 | 0 | **16/16** |
| cprime G* | (0.03, 0.08, 4) | 1.92 | 0 | 8/16 (v1 = 0 fail) |
| cprime G* | (0.02, 0.12, 4) | 2.15 | 0 | 16/16 |
| cprime G* | (0.03, 0.12, 4) | 2.24 | 0 | 16/16 |
| cprime G* | (0.02, 0.05, 4) | 1.59 | 0 | 0/16 |
| K_3, arms (2.75, 3.75, 3) | (0.02, 0.07 / 0.08 / 0.12, 4), (0.03, 0.08, 4) | 1.92-2.57 | 0 | **8/8 each** |
| K_3, arms (2.5, 3.75, 3.25) | (0.02, 0.07), (0.02, 0.08), ... | 1.92-2.05 | 0 | 8/8 (rows (0.02,0.07,4) and (0.02,0.08,4) read; the remaining rows of that run were not read) |

Scale-freedom (`ws_eps.py`), cprime G*, y = 1 + eps*eta with eta from (0.02, 0.08, 4): eps = 0.01, 0.1, 0.5 at h = 0.2 and at h = 0.1: **16/16 weakly solvable in all six runs**. Per-pattern report: every one of the 16 (0000 ... 1111) passes in every passing row; in the failing rows exactly the eight patterns with v1 = 0 fail (as in WEAK-SOLV.md, Delta threshold depends on v1: "0.0451 for v1 = 0, 0.0304 for v1 = 1"); at G* the threshold for r^2 is between c2 - c1 = 0.05 and 0.06 above (slope c2 = 0.08 passes, 0.07 does not at c1 = 0.02), compared with 0.07 passing at NH. The kink sizes were found by the same small scan as in WEAK-SOLV.md, not derived from CROSSING-PROOF Thm 6 (the local necessary condition Delta >= g is far below the observed threshold ~ 5-6 g; I did not derive the G* threshold in closed form).
**Scope and caveats.** (i) Only these two instances, floating data, snapped at 1e-5; (ii) the glued Q is the r^2 optimum, not the phi_h optimum; (iii) nothing is proved for arbitrary layouts: the flow-LP check is a per-instance statement, as for phi_pi; the open item (WS) in full generality (all layouts L1-L8) is exactly as open as in NP-HARDNESS.md Sec. 7.3; (iv) the joint max-min-gap LP (`ws_gap.solve`) was not needed since the explicit rule passes. **So (WS) for r^2 at G* has the same status as (WS) for phi_pi: verified numerically on cprime (16 patterns) and K_3 (8 patterns), open in general.**

## 11.2 Stability of the glued optimum for phi in class S (explicit h_1)

Data of the r^2 optimum of K at G* (`uniq.py`, `tiegraph.py`; units h, r^2 cost; m_0 = 97.1167 = sum B(K) + X_K):
* unique optimal routing class R*; every other routing class costs >= 17/15 more; unique optimal point x_0;
* 12 routed tight conflicts with positive multipliers (min 0.2), the 12 x 18 active-constraint matrix M has full row rank, smallest singular value sigma >= 0.618 (four satisfied patterns: 0.618, 0.720, 0.720, 0.618);
* the K block has 19 coordinate coincidences x_a = x_b among its 18 points, **all 19 are implied by the 12 positive-multiplier tight constraints** (connected components of the equality graph, per coordinate; this includes the two unrouted ties (2,13), (12,5) seen earlier: they are consequences of the routed ties), so they are *structural*; the smallest positive slack of any other conflict inside K is 1/12;
* K points vs exterior switches (crossing + 3+3 wire switches, isolated): 5 exact coincidences of one coordinate (e.g. points (33,22), (35,24), (26,37), (28,39), (31,20) in the `xwires(u,3,3)` numbering) that are **not** forced (the corresponding conflicts, if any, have slack >= 0.5 h): a rational accident of r^2 numbers; the smallest non-coincident gap is h/6.

**Lemma Stab.** Let phi in class S, theta = theta(h M) with M = 27.4 as in Lemma Cont, and let x_h be the minimiser of the K block (pattern with the r^2 routing class R*). Set `delta := sqrt(2 theta m_0 / (1 - theta))` (m_0 = 97.12). Then
(a) routing: if theta < (17/15)/(2 m_0 + 17/15) = 5.8e-3 the optimal routing class of phi_h is R*;
(b) displacement: cost_0 is 2-strongly convex on the polyhedron of R*, so `cost_0(x) >= m_0 + |x - x_0|^2`; with (1 - theta) cost_0 <= cost_h <= (1 + theta) cost_0 on the ball: `|x_h - x_0|_2 <= delta` (so every coordinate moves by <= delta h);
(c) multipliers: stationarity `grad cost_h(x_h) = -M^T lambda_h` and `|psi_h'(r) - 2 r| <= 2 theta |r|` give `|lambda_h - lambda_0|_inf <= (2 delta + 2 theta sqrt(m_0/(1 - theta)))/0.618`; positive multipliers (>= 0.2) stay positive if this is < 0.2, which holds for `theta <= 1.9e-5`;
(d) slacks: every conflict slack changes by <= 2 delta h; the K-internal non-tight conflicts (slack >= 1/12) stay non-tight if `2 delta < 1/12`, i.e. `theta <= 8.9e-6`; exterior conflicts keep slack >= (0.5 - 2 delta) h.
Hence for `theta(h M) <= theta_1 := 8e-6` all of (a)-(d) hold (delta <= 0.0394, exterior slack >= 0.42 h, D <= 3.19 h). Consequently the **tie set internal to K at phi_h equals the r^2 one** (the 12 routed ties persist with positive multipliers; the 19 coincidences are implied by them; no other coincidence appears since the remaining conflicts keep positive slack; strict complementarity). Exterior coincidences (the 5 above) are NOT preserved: they split by O(delta) h in a phi-dependent direction.
*Proof.* (a) and (b): Lemma Cont comparisons with the numbers above; (c): `M M^T` invertible with smallest eigenvalue >= 0.618^2; (d): triangle inequality. QED (constants: by hand from the computed 17/15, 0.2, 0.618, 1/12, m_0.)
**Explicit h_1.** `h_1(phi) := sup { h > 0 : theta(h M) <= 8e-6 }`, M = 27.4, where theta(s) = sup_{|t| <= s} |phi''(t)/phi''(0) - 1|. (cosh r - 1: theta(s) = cosh s - 1, h_1 = arccosh(1 + 8e-6)/27.4 = 1.5e-4; r^2: h_1 = infinity.) The constants are pessimistic by orders of magnitude (the experiment shows the same K-internal tie set for cosh up to h = 0.4).

## 11.3 Theorem S-UB

**Theorem S-UB.** Let phi be in class S, h <= min(h_0(phi), h_1(phi)), the geometry G*, a layout satisfying (L1)-(L8) with the cluster list of NH Sec. 7.2 and rule R with 7 grid steps. For every bit assignment sigma of the original vertices let Q*(sigma) be the glued point: K at its phi_h optimum (in the r^2 routing class R*), every other switch at its isolated optimum (top -delta/2, bottom +delta/2, coordinate = bit; phi-independent by Prop. Iso), every violated weak link pooled (y_{t_1} down, y_{b_0} up by gamma/2 in the non-bit coordinate; phi-independent). Then:
(1) Q*(sigma) satisfies all conflicts of the layout (rho_dom-feasible), with slack >= 0.4 h at every conflict except the pooled-kink pairs (exactly tight by construction) and the structural ties inside K;
(2) `cost(Q*(sigma)) = S0 + J_e * #uncut edges` with `S0 = sum B + n_x X_K(phi, h)`, `J_e = 2 phi(h/8)`;
(3) the tie set of Q* inside every K equals the r^2 one (Lemma Stab); the exterior coincidences are not preserved;
(4) therefore: `rho(P, y) <= S0 + J_e(|E| - cut(sigma))` **if and only if** `WeakSolvable(Q*(sigma), y)`, i.e. conditional only on (WS)(phi, h) and on (L).
*Proof.* (1): r^2 slacks (0.5 h for crossing + wires up to 8 switches per arm, weak kink wire, stars of degrees 2-4; `glue_sq_u25.txt`) minus 2 delta h <= 0.08 h by Lemma Stab; D <= 3.19 h and rule R (2D = 6.4 h < 7 h) for conflicts between different clusters (Lemma R); (2): Lemma G (cost is a sum of the closed forms B, X_K, J_e); (3): Lemma Stab; (4): Thm UB with Lemma 0. QED (the finite parts are interval/float certificates at G* for r^2 transported by the continuity estimate; the cluster list is the tested one).
Combined with Theorem S (LB): **Corollary S-NP.** For phi in S and h <= min(h_0, h_1), PERT-2[phi] is NP-hard modulo exactly (L) and (WS)(phi, h). (WS) is verified numerically for r^2 at G* on cprime (16 patterns) and K_3 (8 patterns) but not for phi != r^2 (not transferable by continuity: closedness; the 5 exterior coincidences split) and not in general.

## 11.4 Updated status

| item | r^2 at G* | class S, h small |
|---|---|---|
| library certificates (pairs ... K^+) | interval, all pass, margins >= 0.51 h^2 | Theorem S, explicit h_0 |
| Lemma G / glue slack / D / R | float, 0.5 h, D = 3.15 h, R = 7 | Lemma Stab, explicit h_1, slack >= 0.4 h, D <= 3.19 h |
| K-internal tie set | unique optimum, 12 positive multipliers, 19 ties all implied | exactly preserved for h <= h_1 |
| exterior coincidences | 5, accidental | not preserved |
| (WS) | cprime 16/16 and K_3 8/8 at (0.02, 0.08, 4) (h = 0.2; cprime also eps in {0.01, 0.1, 0.5}, h = 0.1), floating flow LP | open, must be re-run per phi, h |
| (L) layout generator | open | open |
