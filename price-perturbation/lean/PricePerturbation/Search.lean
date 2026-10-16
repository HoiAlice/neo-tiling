import PricePerturbation.Shape
import NPHardness.Costed

/-!
# The exact least-radius search, with oracle calls counted

For rational prices `Pq` the least feasible radius `ρ*` satisfies `e^{2ρ*} = 1` or
`e^{2ρ*} = -B_I / A_I` for some choice `I` of `d + 1` homogenized corner vectors, where `A_I`,
`B_I` are two explicit rational determinants (`coefA`, `coefB`). So `e^{2ρ*}` lies in the finite
set `cands Pq`, and a binary search over the sorted candidates with a feasibility oracle finds it.

* `coefA`, `coefB`: the coefficients of `e^{ρ}` and `e^{-ρ}` in the corner determinant.
* `cands`: `1` and the roots `-B_I / A_I > 1`; at most `(2T + d)^(d+1) + 1` of them.
* `search`: binary search for the first `true` element of a list, one `tick` per oracle call.
* `leastRadius`: `search` over the sorted candidates.
* `leastRadius_spec`: it returns `e^{2ρ*}` (or `none` if no radius is feasible) after at most
  `(d + 1) ⌈log₂ (2T + d)⌉ + 2` oracle calls.

A `tick` here is one oracle call. Arithmetic (the determinants) is not counted.
-/

namespace NeoTiling.PricePerturbation

open NeoTiling Real NPHardness Costed

variable {d T : ℕ}

/-! ### The coefficients of the corner determinant -/

/-- Rational homogenized rows: last entry `bL` on the lower corners, `bU` on the upper corners,
and `0` on the directions `(e_i, 0)`. -/
def rowQ (Pq : Fin T → Fin d → ℚ) (bL bU : ℚ) : Fin T ⊕ Fin T ⊕ Fin d → Fin (d + 1) → ℚ :=
  Sum.elim (fun t => Fin.snoc (Pq t) bL)
    (Sum.elim (fun t => Fin.snoc (Pq t) bU) (fun i => Fin.snoc (Pi.single i 1) 0))

/-- The coefficient of `e^{ρ}`: the determinant with last entry `1` on the lower corners. -/
def coefA (Pq : Fin T → Fin d → ℚ) (I : Fin (d + 1) → Fin T ⊕ Fin T ⊕ Fin d) : ℚ :=
  (Matrix.of fun j => rowQ Pq 1 0 (I j)).det

/-- The coefficient of `e^{-ρ}`: the determinant with last entry `1` on the upper corners. -/
def coefB (Pq : Fin T → Fin d → ℚ) (I : Fin (d + 1) → Fin T ⊕ Fin T ⊕ Fin d) : ℚ :=
  (Matrix.of fun j => rowQ Pq 0 1 (I j)).det

/-- The corner determinant is a positive factor times `e^{ρ} coefA + e^{-ρ} coefB`
(the explicit form of `det_cornerVec_eq`, with the same proof). -/
theorem det_cornerVec_coef (Pq : Fin T → Fin d → ℚ) (P : Fin T → Fin d → ℝ)
    (hPP : ∀ t i, P t i = Pq t i) (I : Fin (d + 1) → Fin T ⊕ Fin T ⊕ Fin d) (ρ : ℝ) :
    ∃ c : ℝ, 0 < c ∧ (Matrix.of fun j => cornerVec P ρ (I j)).det =
      c * (exp ρ * coefA Pq I + exp (-ρ) * coefB Pq I) := by
  classical
  let R : Fin T ⊕ Fin T ⊕ Fin d → Fin (d + 1) → ℝ :=
    Sum.elim (fun t => Fin.snoc (P t) 0)
      (Sum.elim (fun t => Fin.snoc (P t) 0) (fun i => Fin.snoc (Pi.single i 1) 0))
  let L : Fin T ⊕ Fin T ⊕ Fin d → ℝ := Sum.elim (fun _ => 1) (fun _ => 0)
  let U : Fin T ⊕ Fin T ⊕ Fin d → ℝ := Sum.elim (fun _ => 0) (Sum.elim (fun _ => 1) (fun _ => 0))
  let α : Fin T ⊕ Fin T ⊕ Fin d → ℝ → ℝ :=
    Sum.elim (fun _ ρ => exp (-ρ)) (Sum.elim (fun _ ρ => exp ρ) (fun _ _ => 1))
  let M0 : Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ := Matrix.of fun j => R (I j)
  let Lv : Fin (d + 1) → ℝ := fun j => L (I j)
  let Uv : Fin (d + 1) → ℝ := fun j => U (I j)
  have hq : ∀ (bL bU : ℚ) (v : Fin (d + 1) → ℝ),
      (∀ j, v j = Sum.elim (fun _ => (bL : ℝ)) (Sum.elim (fun _ => (bU : ℝ)) (fun _ => 0)) (I j)) →
      (M0.updateCol (Fin.last d) v).det = (Matrix.of fun j => rowQ Pq bL bU (I j)).det := by
    intro bL bU v hv
    have : M0.updateCol (Fin.last d) v =
        (Matrix.of fun j => rowQ Pq bL bU (I j)).map (Rat.castHom ℝ) := by
      ext j k
      refine Fin.lastCases ?_ (fun i => ?_) k
      · simp only [Matrix.updateCol_self, Matrix.map_apply, Matrix.of_apply, hv j]
        rcases I j with t | t | i' <;> simp [rowQ]
      · simp only [Matrix.updateCol_ne (Fin.castSucc_lt_last i).ne, M0, R, Matrix.of_apply,
          Matrix.map_apply, rowQ]
        rcases I j with t | t | i' <;> simp [hPP]
        by_cases h : i = i' <;> simp [Pi.single_apply, h]
    rw [this]; exact (RingHom.map_det (Rat.castHom ℝ) _).symm
  have hA := hq 1 0 Lv (fun j => by rcases h : I j <;> simp [Lv, L, h])
  have hB := hq 0 1 Uv (fun j => by rcases h : I j with _ | _ | _ <;> simp [Uv, U, h])
  refine ⟨∏ j, α (I j) ρ, Finset.prod_pos fun j _ => ?_, ?_⟩
  · rcases I j with _ | _ | _ <;> simp [α, exp_pos]
  · have hM : (Matrix.of fun j => cornerVec P ρ (I j)) =
        Matrix.of fun j k => α (I j) ρ *
          (M0.updateCol (Fin.last d) (exp ρ • Lv + exp (-ρ) • Uv)) j k := by
      ext j k
      refine Fin.lastCases ?_ (fun i => ?_) k
      · rcases h : I j with t | t | i' <;>
          simp [M0, R, α, L, U, Lv, Uv, cornerVec, h, ← exp_add]
      · rcases h : I j with t | t | i' <;>
          simp [M0, R, α, cornerVec, h, Fin.snoc_castSucc]
    rw [hM, Matrix.det_mul_column, Matrix.det_updateCol_add, Matrix.det_updateCol_smul,
      Matrix.det_updateCol_smul, hA, hB]
    simp [coefA, coefB]

/-! ### The candidates -/

/-- The candidate values of `e^{2ρ*}`: `1` and the roots `-coefB / coefA` that exceed `1`. -/
def cands (Pq : Fin T → Fin d → ℚ) : Finset ℚ :=
  insert 1 (((Finset.univ.filter (fun I => coefA Pq I ≠ 0)).image
    (fun I => -coefB Pq I / coefA Pq I)).filter (1 < ·))

theorem card_cands_le (Pq : Fin T → Fin d → ℚ) : (cands Pq).card ≤ (2 * T + d) ^ (d + 1) + 1 := by
  unfold cands
  refine (Finset.card_insert_le _ _).trans ?_
  have h1 := Finset.card_filter_le
    ((Finset.univ.filter (fun I : Fin (d + 1) → Fin T ⊕ Fin T ⊕ Fin d => coefA Pq I ≠ 0)).image
      (fun I => -coefB Pq I / coefA Pq I)) (1 < ·)
  have h2 := Finset.card_image_le (s := Finset.univ.filter
    (fun I : Fin (d + 1) → Fin T ⊕ Fin T ⊕ Fin d => coefA Pq I ≠ 0))
    (f := fun I => -coefB Pq I / coefA Pq I)
  have h3 := Finset.card_filter_le (Finset.univ : Finset (Fin (d + 1) → Fin T ⊕ Fin T ⊕ Fin d))
    (fun I => coefA Pq I ≠ 0)
  have h4 : (Finset.univ : Finset (Fin (d + 1) → Fin T ⊕ Fin T ⊕ Fin d)).card
      = (T + (T + d)) ^ (d + 1) := by
    simp [Finset.card_univ, Fintype.card_sum]
  have h5 : T + (T + d) = 2 * T + d := by ring
  rw [h4, h5] at h3
  omega

theorem one_le_of_mem_cands {Pq : Fin T → Fin d → ℚ} {z : ℚ} (hz : z ∈ cands Pq) : 1 ≤ z := by
  unfold cands at hz
  rcases Finset.mem_insert.1 hz with h | h
  · exact h.ge
  · exact (Finset.mem_filter.1 h).2.le

/-- `e^{2ρ*}` is a candidate. Proof: `ρ* = 0` gives `1`. Otherwise some corner determinant
vanishes at `ρ*` but not identically, so `(coefA, coefB) ≠ (0, 0)` by `det_cornerVec_coef`, and
`e^{2ρ*} coefA + coefB = 0`; then `coefA ≠ 0` and `e^{2ρ*} = -coefB / coefA > 1`. -/
theorem exists_mem_cands (hd : 2 ≤ d) (Pq : Fin T → Fin d → ℚ) (P : Fin T → Fin d → ℝ)
    (hP : ∀ t, P t ∈ orthant d) (hPP : ∀ t i, P t i = Pq t i) (y : Fin T → ℝ)
    (hy : ∀ t, 0 ≤ y t) (hfeas : ∃ ρ, 0 ≤ ρ ∧ Feasible P y ρ) :
    ∃ ρs, 0 ≤ ρs ∧ (∀ ρ, 0 ≤ ρ → (Feasible P y ρ ↔ ρs ≤ ρ)) ∧
      ∃ z ∈ cands Pq, exp (2 * ρs) = z := by
  obtain ⟨ρs, h0, hiff, h | ⟨I, hdet0, ρ, hρ⟩⟩ :=
    least_radius_breakpoint hd P hP y hy hfeas
  · exact ⟨ρs, h0, hiff, 1, Finset.mem_insert_self _ _, by simp [h]⟩
  by_cases hz : ρs = 0
  · exact ⟨ρs, h0, hiff, 1, Finset.mem_insert_self _ _, by simp [hz]⟩
  obtain ⟨c, hc, hc'⟩ := det_cornerVec_coef Pq P hPP I ρs
  rw [hdet0] at hc'
  have h1 : exp ρs * (coefA Pq I : ℝ) + exp (-ρs) * (coefB Pq I : ℝ) = 0 := by
    rcases mul_eq_zero.1 hc'.symm with h | h
    · exact absurd h hc.ne'
    · exact h
  have h2 : exp (2 * ρs) * (coefA Pq I : ℝ) + coefB Pq I = 0 := by
    have e1 : exp ρs * exp (-ρs) = 1 := by rw [← exp_add]; simp
    have e2 : exp (2 * ρs) = exp ρs * exp ρs := by rw [two_mul, exp_add]
    rw [e2]
    calc exp ρs * exp ρs * (coefA Pq I : ℝ) + coefB Pq I
        = exp ρs * (exp ρs * coefA Pq I + exp (-ρs) * coefB Pq I) := by
          linear_combination (-(coefB Pq I : ℝ)) * e1
      _ = 0 := by rw [h1]; ring
  have hA : (coefA Pq I : ℝ) ≠ 0 := by
    intro hA0
    have hB : (coefB Pq I : ℝ) = 0 := by rw [hA0] at h2; simpa using h2
    obtain ⟨c2, _, hc2⟩ := det_cornerVec_coef Pq P hPP I ρ
    apply hρ
    rw [hc2, hA0, hB]; simp
  have hAq : coefA Pq I ≠ 0 := by exact_mod_cast hA
  have hval : exp (2 * ρs) = ((-coefB Pq I / coefA Pq I : ℚ) : ℝ) := by
    push_cast
    rw [eq_div_iff hA]
    linarith
  have hρpos : 0 < ρs := lt_of_le_of_ne h0 (Ne.symm hz)
  have hgt : (1 : ℝ) < ((-coefB Pq I / coefA Pq I : ℚ) : ℝ) := by
    rw [← hval]; exact Real.one_lt_exp_iff.2 (by linarith)
  have hgtq : (1 : ℚ) < -coefB Pq I / coefA Pq I := by exact_mod_cast hgt
  refine ⟨ρs, h0, hiff, -coefB Pq I / coefA Pq I, ?_, hval⟩
  exact Finset.mem_insert_of_mem (Finset.mem_filter.2
    ⟨Finset.mem_image.2 ⟨I, Finset.mem_filter.2 ⟨Finset.mem_univ _, hAq⟩, rfl⟩, hgtq⟩)

/-! ### Binary search -/

/-- Binary search for the first element of `l` on which the oracle `O` is `true`, assuming `O`
is monotone along `l`. Each call of `O` costs one tick: test the last element of the first half
and recurse into the half that holds the answer. -/
def search (O : ℚ → Bool) (l : List ℚ) : Costed (Option ℚ) :=
  if h : l.length ≤ 1 then
    match l with
    | [] => pure none
    | a :: _ => tick (if O a then some a else none)
  else do
    let b ← tick (O (l.getD (l.length / 2 - 1) 0))
    if b then search O (l.take (l.length / 2)) else search O (l.drop (l.length / 2))
termination_by l.length
decreasing_by all_goals simp; omega

/-- The search returns the first `true` element if `O` is monotone along `l`. -/
theorem val_search (O : ℚ → Bool) (l : List ℚ)
    (hl : l.Pairwise fun a b => O a = true → O b = true) :
    (search O l).val = l.find? (fun z => O z) := by
  induction' h : l.length using Nat.strong_induction_on with n ih generalizing l
  rw [search]
  split_ifs with h1
  · match l, h1 with
    | [], _ => simp
    | [a], _ => by_cases ha : O a <;> simp [tick, ha]
    | a :: b :: t, h2 => simp at h2
  · have hn : 2 ≤ n := by omega
    have hlt : n / 2 - 1 < l.length := by omega
    have hget : l.getD (n / 2 - 1) 0 = l[n / 2 - 1] := by
      simp [List.getD_eq_getElem?_getD, hlt]
    simp only [val_bind, tick, h, hget]
    have hsplit : l = l.take (n / 2) ++ l.drop (n / 2) := (List.take_append_drop _ _).symm
    have hmem : l[n / 2 - 1] ∈ l.take (n / 2) := by
      have : (l.take (n / 2))[n / 2 - 1]'(by simp; omega) ∈ l.take (n / 2) := List.getElem_mem _
      simpa using this
    have hP := List.pairwise_iff_getElem.mp hl
    by_cases hx : O l[n / 2 - 1] = true
    · simp only [hx, if_true]
      rw [ih (n / 2) (by omega) (l.take (n / 2)) (hl.sublist (List.take_sublist _ _))
        (by simp [h]; omega)]
      have hs : (l.take (n / 2)).find? (fun z => O z) ≠ none := by
        rw [Ne, List.find?_eq_none]
        simp only [not_forall]
        exact ⟨_, hmem, by simpa using hx⟩
      conv_rhs => rw [hsplit, List.find?_append]
      cases hf : (l.take (n / 2)).find? (fun z => O z) with
      | none => exact absurd hf hs
      | some v => simp
    · have hx' : O l[n / 2 - 1] = false := by simpa using hx
      simp only [hx', Bool.false_eq_true, if_false]
      have hnone : (l.take (n / 2)).find? (fun z => O z) = none := by
        rw [List.find?_eq_none]
        intro a ha
        obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem ha
        simp only [List.length_take] at hi
        simp only [List.getElem_take]
        intro hOa
        have hi' : i ≤ n / 2 - 1 := by omega
        rcases hi'.lt_or_eq with hlt' | heq
        · exact hx (hP i (n / 2 - 1) (by omega) hlt hlt' hOa)
        · subst heq; exact hx hOa
      rw [ih (n - n / 2) (by omega) (l.drop (n / 2)) (hl.sublist (List.drop_sublist _ _))
        (by simp [h])]
      conv_rhs => rw [hsplit, List.find?_append, hnone]
      simp

/-- The search makes at most `⌈log₂ |l|⌉ + 1` oracle calls. -/
theorem cost_search_le (O : ℚ → Bool) (l : List ℚ) :
    (search O l).cost ≤ Nat.clog 2 l.length + 1 := by
  induction' h : l.length using Nat.strong_induction_on with n ih generalizing l
  rw [search]
  split_ifs with h1
  · match l, h1 with
    | [], _ => simp
    | a :: t, _ => simp [tick]
  · have hn : 2 ≤ n := by omega
    have hc : Nat.clog 2 n = Nat.clog 2 ((n + 2 - 1) / 2) + 1 :=
      Nat.clog_of_two_le (by norm_num) hn
    simp only [cost_bind, tick, h]
    split
    · have := ih (n / 2) (by omega) (l.take (n / 2)) (by simp [h]; omega)
      have h2 := Nat.clog_mono_right 2 (show n / 2 ≤ (n + 2 - 1) / 2 by omega)
      omega
    · have := ih (n - n / 2) (by omega) (l.drop (n / 2)) (by simp [h])
      have h2 := Nat.clog_mono_right 2 (show n - n / 2 ≤ (n + 2 - 1) / 2 by omega)
      omega

/-! ### The least radius -/

/-- Binary search over the sorted candidates. -/
def leastRadius (O : ℚ → Bool) (Pq : Fin T → Fin d → ℚ) : Costed (Option ℚ) :=
  search O ((cands Pq).sort (· ≤ ·))

/-- `⌈log₂ (n^k + 1)⌉ ≤ k ⌈log₂ n⌉ + 1`. -/
theorem clog_pow_add_one_le (n k : ℕ) :
    Nat.clog 2 (n ^ k + 1) ≤ k * Nat.clog 2 n + 1 := by
  have h1 : n ≤ 2 ^ Nat.clog 2 n := Nat.le_pow_clog (by norm_num) n
  have h2 : n ^ k ≤ 2 ^ (k * Nat.clog 2 n) := by
    rw [pow_mul']; exact Nat.pow_le_pow_left h1 k
  have h3 : 1 ≤ 2 ^ (k * Nat.clog 2 n) := Nat.one_le_two_pow
  apply Nat.clog_le_of_le_pow
  rw [pow_succ]; omega

/-- **The exact least-radius search.** Let `O` answer, for `z ≥ 1`, whether the radius
`log z / 2` is feasible. Then `leastRadius O Pq` returns `e^{2ρ*}` for the least feasible radius
`ρ*` (so the feasible radii are `[log z / 2, ∞)`), or `none` if no radius is feasible, after at
most `(d + 1) ⌈log₂ (2T + d)⌉ + 2` oracle calls.

Proof. The candidates are `≥ 1`, so by `hO` and `Feasible.mono` the oracle is monotone along the
sorted candidates and `val_search` gives the first `true` candidate. If some radius is feasible,
`e^{2ρ*}` is a `true` candidate (`exists_mem_cands`); every `true` candidate `z` has
`log z / 2 ≥ ρ*`, so the first one is `e^{2ρ*}`. If none is feasible, no candidate is `true`.
The cost is `cost_search_le` with `card_cands_le` and `clog_pow_add_one_le`. -/
theorem leastRadius_spec (hd : 2 ≤ d) (Pq : Fin T → Fin d → ℚ) (P : Fin T → Fin d → ℝ)
    (hP : ∀ t, P t ∈ orthant d) (hPP : ∀ t i, P t i = Pq t i) (y : Fin T → ℝ)
    (hy : ∀ t, 0 ≤ y t) (O : ℚ → Bool)
    (hO : ∀ z : ℚ, 1 ≤ z → (O z = true ↔ Feasible P y (Real.log z / 2))) :
    ((∃ ρ, 0 ≤ ρ ∧ Feasible P y ρ) → ∃ z, (leastRadius O Pq).val = some z ∧
        ∀ ρ, 0 ≤ ρ → (Feasible P y ρ ↔ Real.log z / 2 ≤ ρ)) ∧
      ((¬ ∃ ρ, 0 ≤ ρ ∧ Feasible P y ρ) → (leastRadius O Pq).val = none) ∧
      (leastRadius O Pq).cost ≤ (d + 1) * Nat.clog 2 (2 * T + d) + 2 := by
  classical
  set l := (cands Pq).sort (· ≤ ·) with hl
  have hmem : ∀ z, z ∈ l ↔ z ∈ cands Pq := fun z => Finset.mem_sort _
  have hsorted : l.Pairwise (· ≤ ·) := Finset.pairwise_sort _ _
  have hmono : l.Pairwise (fun a b => O a = true → O b = true) := by
    refine List.Pairwise.imp_of_mem ?_ hsorted
    intro a b ha hb hab hOa
    have ha1 := one_le_of_mem_cands ((hmem a).1 ha)
    have ha0 : (0:ℝ) < a := by exact_mod_cast (zero_lt_one.trans_le ha1)
    have hb1 := one_le_of_mem_cands ((hmem b).1 hb)
    exact (hO b hb1).2 (((hO a ha1).1 hOa).mono
      (by have := Real.log_le_log ha0 (by exact_mod_cast hab : (a:ℝ) ≤ b); linarith))
  have hv : (leastRadius O Pq).val = l.find? (fun z => O z) := val_search O l hmono
  have hc : (leastRadius O Pq).cost ≤ Nat.clog 2 l.length + 1 := cost_search_le O l
  have hlen : l.length = (cands Pq).card := Finset.length_sort _
  refine ⟨?_, ?_, ?_⟩
  · intro hfeas
    obtain ⟨ρs, hρ0, hiff, zs, hzs, hez⟩ := exists_mem_cands hd Pq P hP hPP y hy hfeas
    have hzs1 := one_le_of_mem_cands hzs
    have hlogzs : Real.log zs / 2 = ρs := by
      rw [← hez, Real.log_exp]; ring
    have hOzs : O zs = true := by
      rw [hO zs hzs1, hlogzs]; exact (hiff ρs hρ0).2 le_rfl
    have hne : l.find? (fun z => O z) ≠ none := by
      rw [Ne, List.find?_eq_none]
      intro h; exact absurd (h zs ((hmem zs).2 hzs)) (by simp [hOzs])
    obtain ⟨z, hz⟩ := Option.ne_none_iff_exists'.1 hne
    obtain ⟨hOz, l1, l2, hsplit, hl1⟩ := List.find?_eq_some_iff_append.1 hz
    have hzmem : z ∈ l := List.mem_of_find?_eq_some hz
    have hz1 := one_le_of_mem_cands ((hmem z).1 hzmem)
    have hOz' : O z = true := by simpa using hOz
    have hfz := (hO z hz1).1 hOz'
    have hzz : z ≤ zs := by
      have hsp : (l1 ++ z :: l2).Pairwise (· ≤ ·) := by rw [← hsplit]; exact hsorted
      have hzsmem : zs ∈ l1 ++ z :: l2 := by rw [← hsplit]; exact (hmem zs).2 hzs
      rcases List.mem_append.1 hzsmem with h | h
      · have := hl1 zs h
        simp [hOzs] at this
      · rcases List.mem_cons.1 h with h | h
        · exact h ▸ le_rfl
        · exact (List.pairwise_append.1 hsp).2.1 |> fun hp => (List.pairwise_cons.1 hp).1 zs h
    have hz0 : (0:ℝ) < z := by exact_mod_cast (zero_lt_one.trans_le hz1)
    have hlog0 : 0 ≤ Real.log z := Real.log_nonneg (by exact_mod_cast hz1)
    have hge : ρs ≤ Real.log z / 2 := (hiff _ (by linarith)).1 hfz
    have hle : Real.log z / 2 ≤ ρs := by
      rw [← hlogzs]
      have := Real.log_le_log hz0 (by exact_mod_cast hzz : (z:ℝ) ≤ zs); linarith
    have heq : Real.log z / 2 = ρs := le_antisymm hle hge
    refine ⟨z, by rw [hv, hz], fun ρ hρ => ?_⟩
    rw [hiff ρ hρ, heq]
  · intro hnf
    rw [hv, List.find?_eq_none]
    intro z hzl
    have hz1 := one_le_of_mem_cands ((hmem z).1 hzl)
    have : ¬ O z = true := fun h =>
      hnf ⟨Real.log z / 2, by have := Real.log_nonneg (by exact_mod_cast hz1 : (1:ℝ) ≤ z); linarith,
        (hO z hz1).1 h⟩
    simpa using this
  · have h1 : Nat.clog 2 l.length ≤ Nat.clog 2 ((2 * T + d) ^ (d + 1) + 1) :=
      Nat.clog_mono_right 2 (hlen ▸ card_cands_le Pq)
    have h2 := clog_pow_add_one_le (2 * T + d) (d + 1)
    omega

end NeoTiling.PricePerturbation
