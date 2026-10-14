# Closing the P-gap (route A): the 6 asymmetric pairs are inactive, with margin 1.14

Scripts: `pgap_slack.py` (optimal Q, slack of the asymmetric pairs), `pgap_viol.py` -> `pgap_viol.out` (violation-cost certificate). Python: project `.venv`.

## 0. Verdict
For the explicit 4U x 5V gadget (g = h0 = 0.05, h2 = 0.2) U-phase degeneracy E(0,v) = E(1,v) is now a **theorem modulo one MILP lower-bound certificate with margin 1.14** (not an exact-arithmetic proof, and not a statement for arbitrary numbers of switches). Route B was not attempted (see section 5). The "12 pairs" are really 6 that matter: only `C \ C^P` can obstruct (see 1).

## 1. Reduction to a finite check (rigorous)
Let C be the full conflict set (127 pairs), C^P its P-image, C_sym = C cap C^P. E = energy with C, E_sym = with C_sym (same designated bits). Then
* E_sym <= E (fewer constraints);
* E_sym(phi,v) = E_sym(phi+1,v) exactly (Thm 1 / Cor. 2 of CROSSING-PROOF.md);
* E(phi,v) = E(phi,v+1) exactly (R).

**Lemma.** Let phi in {0,1}. If every price system Q feasible for C_sym with cost < E_sym(phi) + delta (delta > 0) satisfies the 6 constraints N(Q_a,Q_b), (a,b) in C \ C^P, then E(phi,v) = E_sym(phi,v). Proof: a minimiser of E_sym (the feasible set is closed, cost coercive) has cost E_sym < E_sym + delta, so it is feasible for C, hence E <= E_sym. QED

So it suffices to lower-bound, for each of the 6 pairs p = (a,b) and each phi, the quantity
V_p(phi) = inf { cost(Q) : Q feasible for C_sym with the designated bits of phase phi, Q_a > Q_b in BOTH coordinates }
and check V_p(phi) > E_sym(phi). Then delta = min_p V_p - E_sym works.

## 2. Certificate (pgap_viol.py, MILP with tangent cuts = valid lower bound; log-box |u-a| <= 4 is harmless since a point outside costs e^4-1 = 53.6 > 11)
Pairs (a higher, b lower): (Ub_j, Vt_1) j = 1..4, (Vb_0, Vt_1), (Vb_1, Vt_2). Margin of violation 1e-6. Full conflict set (no pruning).

| | E_sym | Ub1,Vt1 | Ub2,Vt1 | Ub3,Vt1 | Ub4,Vt1 | Vb0,Vt1 | Vb1,Vt2 |
|---|---|---|---|---|---|---|---|
| phi=0, V=0 | 10.55201 | 12.2175 | 11.9353 | 12.1124 | 12.2175 | 12.1992 | 12.2293 |
| phi=1, V=0 | 10.55204 | 12.7805 | 11.6912 | 11.8157 | 12.7805 | 12.2919 | 12.2293 |

(MILP primal and dual bounds agree to <= 1e-6 in every run.) Minimum margin: V_p - E_sym = 11.6912 - 10.5520 = **1.139** (> 10% of E). The 3e-5 difference of E_sym between the phases is the tangent-cut grid (polished exact cost: 10.552302 in both phases, same as full E), as it must be since E_sym(0) = E_sym(1) exactly. V = 1 follows by R.

Conclusion: for both phases every Q feasible for C_sym with cost < E_sym + 1.13 satisfies all 6 asymmetric pairs, so E = E_sym in both phases (Lemma), hence
**E(0,v) = E_sym(0,v) = E_sym(1,v) = E(1,v) exactly** for the designated terminal patterns (U-ends (0,1) vs (1,0), V ends uniform).

## 3. Sanity (pgap_slack.py)
At the optimal Q of E for each phase (full and pruned conflict sets identical) the slack max_i (log Q_b,i - log Q_a,i) of the 6 pairs is >= 0.8 in log (= 4 grid steps; same as at the original prices) although the maximum single-point displacement is 0.64 (3.2 steps). Minimisers do not even approach the pairs. The pruned conflict set used in `cx2.setup` (drops pairs with a lower point >= 1.2 NE) gives the same optimum.

## 4. What this does and does not give
* Gives: exact U-phase degeneracy of rho_dom for the crossing gadget as used, robustly (a violation costs >= 1.14 extra, vs break costs 0.09 and J_e ~ 0.05). No per-crossing error accumulates in rho_dom: U-field = 0 exactly for each crossing in isolation.
* Not a general argument for any number of U/V switches: I found no a-priori displacement bound (single-point moves reach 0.64 > gap/2, so a crude "each point moves less than half the gap" argument fails; isotonic min-max bounds depend on the chosen sigma-chains). The geometry of the gadget is fixed (4x5, same levels) in the reduction, so a fixed finite certificate suffices for the gadget itself.
* Still open and unchanged: (i) the same certificate for the gadget embedded in the global instance (extra conflicts with other gadgets; if far gadgets only add constraints, V_p can only increase relative to E_sym only when E_sym is the same, so re-run per embedding, or argue far pairs are inactive); (ii) full rho vs rho_dom: weak solvability is checked per phase (P does not preserve it, Prop. 5), which is a separate numeric check; (iii) the certificate is floating-point MILP, a rational Farkas/dual certificate would make it fully formal.

## 5. Route B (not attempted; why)
Exact order reversal needs a decreasing involution f on levels with y(tau a) = f(y(a)), so tie classes must map to tie classes: {Ut_j, Vt0, Vb-1} (1.05) -> {Ub_j, Vb0, Vt1} forces y(Vt1) = y(Vb0), i.e. h2 = g (Remark 4), against h2 >= h0 + 2g. Changing the family means re-deriving the ties that make the crossing cancel (V centre level = U level) and rerunning the whole table; given the margin in route A this was not worth it.
