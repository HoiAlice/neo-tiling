# Referee report on BOX-FINAL.md

Verdict: CORRECT, with minor presentation fixes (no gap found in Theorems 1-4).

## 1. Cited Lean facts
- WeakSolvable (Closure.lean:36) is a closure; IsWeakReachable (l.46) as quoted; weakSolvable_iff (l.423) needs hd: 2<=d, P>=0, y>=0 (as used: Q>=L>0, y>=0).
- mem_indicatorCone_iff_flow (FlowLP.lean:645): hypotheses are only the section variable P : Fin T -> Fin 2 -> R, b, y. No positivity/injectivity. isReachableB_false_iff (Chain.lean:57) is Iff.rfl. cube_mem_span (FlowLP.lean:592): O,B disjoint, 0<=z<=1_B gives 1_O+z in the span of 1_{O u B'}. Stated as claimed. Use with O=R_min, B=R_max\R_min, z=v-1_Rmin is correct.

## 2. (=>)
Correct. K_k = conv Q(T_k)+R^2_{>=0}. S'_k is weakly reachable in W: for a_t=L_t not in int K_k, supporting xi exists (separation of a point from the open convex int K_k, xi>=0 by up-set property); every W-point outside S'_k is in K_k. For b_t=U_t not in K_k, strict separation. Inequalities w(a_t)>=y_t>=w(b_t) check (int K and K up-sets, L<=Q<=U). Empty S_k and empty K_k are fine.
Minor: Lemma 1 is stated for V_t in V, but in (=>) it is applied to the corner L_t which is not a point of the K_k generators. The proof (separation from int K) does not use v in V; say so.

## 3. (<=)
Checked all steps: Lemma 2 (closed up-interval / open up-interval complement) right; hi usc nonincreasing, lo lsc nonincreasing, lo<=hi; hi(0)>=y_t, lo(1)<=y_t (b_t not in K_k forces b_t in S_k, also with duplicates); s*=max{hi>=y_t} exists; lo(s*)<=y_t for s*=1 and s*<1 (lsc from the right); R_min,k/R_max,k; every R between them weakly reachable at Q (needs only Q_t not in int K_k, separation vs the fixed set K_k, and Q_r in K_k for r not in R); coordinatewise decomposition y_t=sum m_k v_k(t) with common fraction; cube_mem_span; weakSolvable_iff. Boundary points on dK_k, duplicates, zero-width (hi,lo constant), y_t=0 (s*=1, lo(1)<=0 holds), ties in y: no gap. (Only existence of Q on the diagonal segment is claimed; this is enough.)

## 4. Rational witness
Correct. {s: z(s) not in int K} = {s : exists j xi_j.z(s)<=c_j} = down-interval with right end max_j(...), terms with zero slope +-inf as stated; negative lambda (empty interval) excluded by lambda>=0. For y_t>0, s* is a breakpoint min(1,lambda_k) (hi is a right-constant step function; if s*=1 then some lambda_k>=1). y_t=0 gives s*=1 (special case listed). Q rational, in [L,U]. Minor: "O(b)-bit" is really O(b) with constant ~6 (c_j is cubic in input, ratio quadratic-ish): still polynomial. The nested splitting of the g-part is only sketched in the text; it is validated by the exact is_reachable filter + assert in construct_closed, so fine, but the sketch should cite planar.certify or give the argument (sets Out u B', B' in a chain of Bnd subsets, each weakly reachable by F2).

## 5. Polynomiality
Arcs <= 1+2n+2E+C(n,3), n=2T: O(T^3) variables, O(T^2) rows, coefficients in {0,+-1}, RHS 0 and y_t. Exact LP polynomial (Khachiyan/ellipsoid or any poly LP in rational arithmetic); the Bland simplex used in code is not polynomial in the worst case but the claim is about LP in general: say so explicitly.

## 6. Theorem 4 (dominance, any d)
Checked in full: necessity trivial; b_i(p,t)<=1 iff L_{p,i}<=U_{t,i} in all three cases; hypothesis gives beta<=1 so tau_t in [0,1] and tau_s>0 implies max beta in (0,1]; Claim 1 (zero-width forces +inf), Claim 2 (-inf for zero width, beta<=tau for positive width), final case split (tau_s=0 uses Claim 2 with p=s; tau_s>0 uses a heavier p, transitivity y_p>y_s>y_t). Correct.

## 7. Theorem 5 (not requested in detail)
Plausible: closed set of feasible kappa, LP truth is a function of sign pattern of coordinate differences and cross products, polynomial in kappa of degree <=4 after multiplying by kappa^2 (note count should include ordered pairs, still O(T^3)). Not independently tested.

## Independent numerical test (my own generator, exact Fractions)
Script: scratchpad rv.py / rv2.py. Random T in {2,3,4}, half-integer corners, ~half the widths zero, forced duplicates L_1=L_0, y in small integer ranges (second run up to 8). decide_closed from exactbox.py; for true instances construct_closed Q checked in the closed box and certify_Q; for false instances brute-force over a 3x3 grid per box (full box, up to 9^T points) with planar.flow_lp.
- Run 1 (200 instances): 176 true, all 176 witnesses valid; 24 false, 0 grid counterexamples.
- Run 2 (250 instances, harder): 181 true, 181 valid witnesses; 69 false, 0 grid counterexamples.
(An early run showed failures; they were a bug in my generator, which set L_1=L_0 without moving U_1, producing U<L. Fixed, then 0 failures.)
