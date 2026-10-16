import NeoTiling.Perturbation.Radius

namespace NeoTiling.PricePerturbation

open NeoTiling Real
open scoped Pointwise

variable {d T : ℕ}

/-- The `2(d+1)` vertices of the unit ball of `projDist` in log coordinates: `± e_i` and
`± (1, …, 1)`. -/
def ballVertices (d : ℕ) : Set (Fin d → ℝ) :=
  Set.range (fun i => Pi.single i 1) ∪ Set.range (fun i => -Pi.single i 1) ∪ {1, -1}

/-- The vectors `v` with `∑ |vᵢ + s| + |s| ≤ 1` for some `s` form a convex set
(take the same convex combination of the shifts `s`). -/
theorem convex_setOf_exists_shift :
    Convex ℝ {v : Fin d → ℝ | ∃ s : ℝ, (∑ i, |v i + s|) + |s| ≤ 1} := by
  rintro v ⟨s, hs⟩ w ⟨t, ht⟩ a b ha hb hab
  refine ⟨a * s + b * t, ?_⟩
  have h1 : ∀ i, |(a • v + b • w) i + (a * s + b * t)| ≤ a * |v i + s| + b * |w i + t| := by
    intro i
    have : (a • v + b • w) i + (a * s + b * t) = a * (v i + s) + b * (w i + t) := by
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      ring
    rw [this]
    calc _ ≤ |a * (v i + s)| + |b * (w i + t)| := abs_add_le _ _
      _ = _ := by rw [abs_mul, abs_mul, abs_of_nonneg ha, abs_of_nonneg hb]
  have h2 : |a * s + b * t| ≤ a * |s| + b * |t| := by
    calc _ ≤ |a * s| + |b * t| := abs_add_le _ _
      _ = _ := by rw [abs_mul, abs_mul, abs_of_nonneg ha, abs_of_nonneg hb]
  have h3 : ∑ i, |(a • v + b • w) i + (a * s + b * t)|
      ≤ a * ∑ i, |v i + s| + b * ∑ i, |w i + t| := by
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    exact Finset.sum_le_sum fun i _ => h1 i
  nlinarith [mul_le_mul_of_nonneg_left hs ha, mul_le_mul_of_nonneg_left ht hb]

/-- The vertices satisfy the shift bound: `s = 0` for `± e_i`, `s = ∓ 1` for `± 1`. -/
theorem ballVertices_subset :
    ballVertices d ⊆ {v : Fin d → ℝ | ∃ s : ℝ, (∑ i, |v i + s|) + |s| ≤ 1} := by
  rintro v ((⟨i, rfl⟩ | ⟨i, rfl⟩) | hv)
  · exact ⟨0, by simp [Pi.single_apply, apply_ite abs]⟩
  · exact ⟨0, by simp [Pi.single_apply, apply_ite abs]⟩
  · rcases hv with rfl | hv
    · exact ⟨-1, by simp⟩
    · rw [Set.mem_singleton_iff] at hv
      subst hv
      exact ⟨1, by simp⟩

/-- A shift with value at most `r` puts `u` into `r • conv V`: `u = ∑ᵢ (uᵢ + s) eᵢ + (-s) 𝟙`,
a combination of `± eᵢ`, `± 𝟙` with total weight `≤ r`, padded by `0 = (𝟙 + (-𝟙)) / 2`. -/
theorem mem_smul_convexHull_of_shift (u : Fin d → ℝ) (s : ℝ) {r : ℝ} (hr : 0 ≤ r)
    (h : (∑ i, |u i + s|) + |s| ≤ r) : u ∈ r • convexHull ℝ (ballVertices d) := by
  set K := convexHull ℝ (ballVertices d) with hK
  have hKc : Convex ℝ K := convex_convexHull ℝ _
  have hV : ∀ v ∈ ballVertices d, v ∈ K := fun v hv => subset_convexHull ℝ _ hv
  have h0 : (0 : Fin d → ℝ) ∈ K := by
    have := hKc (hV 1 (by simp [ballVertices])) (hV (-1) (by simp [ballVertices]))
      (a := 1/2) (b := 1/2) (by norm_num) (by norm_num) (by norm_num)
    simpa [smul_neg] using this
  have hnn : 0 ≤ ∑ i, |u i + s| := Finset.sum_nonneg (fun i _ => abs_nonneg _)
  rcases hr.eq_or_lt with rfl | hpos
  · have hs : s = 0 := by
      have := abs_nonneg s; have : |s| = 0 := by linarith
      simpa using this
    have hu : ∀ i, u i = 0 := by
      intro i
      have h1 : |u i + s| ≤ ∑ i, |u i + s| :=
        Finset.single_le_sum (f := fun i => |u i + s|) (fun i _ => abs_nonneg _) (Finset.mem_univ i)
      have : |u i + s| = 0 := by linarith [abs_nonneg (u i + s), abs_nonneg s]
      rw [abs_eq_zero] at this; linarith
    have : u = 0 := funext hu
    subst this
    exact ⟨0, h0, by simp⟩
  · refine Set.mem_smul_set.2 ⟨r⁻¹ • u, ?_, by rw [smul_smul, mul_inv_cancel₀ hpos.ne', one_smul]⟩
    let e : ℝ → Fin d → (Fin d → ℝ) := fun c i => if 0 ≤ c then Pi.single i 1 else -Pi.single i 1
    let o : ℝ → (Fin d → ℝ) := fun c => if 0 ≤ c then 1 else -1
    let z : Option (Fin d ⊕ Unit) → (Fin d → ℝ)
      | none => 0
      | some (Sum.inl i) => e (u i + s) i
      | some (Sum.inr _) => o (-s)
    let w : Option (Fin d ⊕ Unit) → ℝ
      | none => 1 - ((∑ i, |u i + s|) + |s|) / r
      | some (Sum.inl i) => |u i + s| / r
      | some (Sum.inr _) => |s| / r
    have hw0 : ∀ k, 0 ≤ w k := by
      intro k
      rcases k with _ | k | k
      · simp only [w]; rw [sub_nonneg, div_le_one hpos]; exact h
      · exact div_nonneg (abs_nonneg _) hr
      · exact div_nonneg (abs_nonneg _) hr
    have hw1 : ∑ k, w k = 1 := by
      rw [Fintype.sum_option, Fintype.sum_sum_type]
      simp only [w, Finset.univ_unique, Finset.sum_singleton, ← Finset.sum_div]
      ring
    have hz : ∀ k, z k ∈ K := by
      intro k
      rcases k with _ | k | k
      · exact h0
      · apply hV; simp only [z, e]; split_ifs <;> simp [ballVertices]
      · apply hV; simp only [z, o]; split_ifs <;> simp [ballVertices]
    have key := hKc.sum_mem (t := Finset.univ) (w := w) (z := z) (fun k _ => hw0 k) hw1
      (fun k _ => hz k)
    convert key using 1
    funext j
    rw [Fintype.sum_option, Fintype.sum_sum_type]
    simp only [z, w, e, o, Finset.univ_unique, Finset.sum_singleton, Pi.smul_apply, Pi.add_apply,
      Finset.sum_apply, smul_eq_mul, Pi.zero_apply, mul_zero, zero_add]
    have : ∀ i, |u i + s| / r * (if 0 ≤ u i + s then (Pi.single i 1 : Fin d → ℝ) else
        -Pi.single i 1) j = (u i + s) / r * (Pi.single i 1 : Fin d → ℝ) j := by
      intro i
      by_cases hc : 0 ≤ u i + s
      · simp [hc, abs_of_nonneg hc]
      · simp [hc, abs_of_neg (not_le.1 hc)]; ring
    simp only [this]
    simp [Pi.single_apply]
    by_cases hs : s ≤ 0
    · simp [hs, abs_of_nonpos hs]; field_simp; ring
    · have hs' : 0 < s := not_le.1 hs
      simp [hs, abs_of_pos hs']; field_simp; ring

/-- The infimum over shifts is attained (the function is continuous and `≥ |s|`). -/
theorem exists_shift_le_iInf (u : Fin d → ℝ) :
    ∃ s : ℝ, (∑ i, |u i + s|) + |s| ≤ ⨅ t : ℝ, (∑ i, |u i + t|) + |t| := by
  set f : ℝ → ℝ := fun t => (∑ i, |u i + t|) + |t| with hfdef
  have hf : Continuous f := by rw [hfdef]; fun_prop
  have hge : ∀ t, |t| ≤ f t := fun t => by
    have : 0 ≤ ∑ i, |u i + t| := Finset.sum_nonneg (fun i _ => abs_nonneg _)
    simp only [hfdef]; linarith
  have hM : 0 ≤ f 0 := le_trans (abs_nonneg _) (hge 0)
  obtain ⟨s, hsK, hs⟩ := (isCompact_Icc (a := -f 0) (b := f 0)).exists_isMinOn
    ⟨0, by constructor <;> linarith⟩ hf.continuousOn
  have h0 : f s ≤ f 0 := hs (show (0:ℝ) ∈ Set.Icc (-f 0) (f 0) from ⟨by linarith, hM⟩)
  refine ⟨s, le_ciInf fun t => ?_⟩
  by_cases ht : t ∈ Set.Icc (-f 0) (f 0)
  · exact hs ht
  · have : f 0 < |t| := by
      by_contra h
      exact ht (abs_le.mp (not_lt.mp h))
    linarith [hge t]

/-- **Shape of the ball.** `projDist a b ≤ ρ` iff the log difference `log a - log b` lies in
`ρ • conv {± e_i, ± (1, …, 1)}` (for `d = 2` a hexagon).

Proof. `(→)`: take a minimizing shift (`exists_shift_le_iInf`) and apply
`mem_smul_convexHull_of_shift`. `(←)`: `u = ρ • v` with `v ∈ conv V`; the shift set is convex and
contains `V`, so some `s` gives value `≤ 1` at `v`, and `ρ s` gives value `≤ ρ` at `u`. -/
theorem projDist_le_iff_mem_convexHull (a b : Fin d → ℝ) {ρ : ℝ} (hρ : 0 ≤ ρ) :
    projDist a b ≤ ρ ↔
      (fun i => log (a i) - log (b i)) ∈ ρ • convexHull ℝ (ballVertices d) := by
  constructor
  · intro h
    obtain ⟨s, hs⟩ := exists_shift_le_iInf (fun i => log (a i) - log (b i))
    exact mem_smul_convexHull_of_shift _ s hρ (hs.trans h)
  · intro h
    obtain ⟨v, hv, hvu⟩ := Set.mem_smul_set.mp h
    obtain ⟨s, hs⟩ := convexHull_min ballVertices_subset convex_setOf_exists_shift hv
    refine (ciInf_le (projDist_bddBelow a b) (ρ * s)).trans ?_
    have e : ∀ i, |log (a i) - log (b i) + ρ * s| = ρ * |v i + s| := by
      intro i
      have := congrFun hvu i
      simp only [Pi.smul_apply, smul_eq_mul] at this
      rw [← this, ← mul_add, abs_mul, abs_of_nonneg hρ]
    calc _ = ρ * ((∑ i, |v i + s|) + |s|) := by
          simp only [e, ← Finset.mul_sum, abs_mul, abs_of_nonneg hρ, mul_add]
      _ ≤ ρ := mul_le_of_le_one_right hρ hs

/-- For `d = 2` the general distance is the hexagonal one. -/
theorem hexDist_eq_projDist (a b : Fin 2 → ℝ) : hexDist a b = projDist a b := by
  have hb := projDist_bddBelow a b
  unfold hexDist projDist
  simp only [Fin.sum_univ_two] at hb ⊢
  generalize Real.log (a 0) - Real.log (b 0) = x at hb ⊢
  generalize Real.log (a 1) - Real.log (b 1) = y at hb ⊢
  apply le_antisymm
  · refine le_ciInf fun s => max_le ?_ (max_le ?_ ?_) <;>
      rw [abs_le] <;> constructor <;>
      linarith [le_abs_self (x + s), neg_abs_le (x + s), le_abs_self (y + s),
        neg_abs_le (y + s), le_abs_self s, neg_abs_le s]
  · refine (ciInf_le hb (-(max (min x y) (min (max x y) 0)))).trans ?_
    rcases le_total x y with h1 | h1 <;> rcases le_total x 0 with h2 | h2 <;>
      rcases le_total y 0 with h3 | h3 <;>
      simp [h1, h2, h3, abs_of_nonneg, abs_of_nonpos]

/-- A determinant of a matrix with rational entries is rational. -/
theorem det_eq_ratCast {n : Type*} [Fintype n] [DecidableEq n] (M : Matrix n n ℝ)
    (h : ∀ i j, ∃ q : ℚ, M i j = q) : ∃ q : ℚ, M.det = q := by
  choose N hN using h
  refine ⟨(Matrix.of N).det, ?_⟩
  have : M = (Matrix.of N).map (Rat.castHom ℝ) := by ext i j; simp [hN]
  rw [this]
  exact (RingHom.map_det (Rat.castHom ℝ) _).symm

/-- The corner determinant as a function of `ρ`: a positive factor times
`e^{ρ} A + e^{-ρ} B` with rational `A, B`. Scale each corner row by `e^{±ρ}` so that its first
`d` entries become `P t`; the last column is then `e^{ρ} 𝟙_L + e^{-ρ} 𝟙_U`, and the determinant
is linear in it. -/
theorem det_cornerVec_eq (P : Fin T → Fin d → ℝ) (hPq : ∀ t i, ∃ q : ℚ, P t i = q)
    (I : Fin (d + 1) → Fin T ⊕ Fin T ⊕ Fin d) :
    ∃ A B : ℚ, ∀ ρ, ∃ c : ℝ, 0 < c ∧
      (Matrix.of fun j => cornerVec P ρ (I j)).det = c * (exp ρ * A + exp (-ρ) * B) := by
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
  have hq : ∀ (v : Fin (d + 1) → ℝ), (∀ j, v j = 0 ∨ v j = 1) →
      ∃ q : ℚ, (M0.updateCol (Fin.last d) v).det = q := by
    intro v hv
    apply det_eq_ratCast
    intro j k
    refine Fin.lastCases ?_ (fun i => ?_) k
    · rcases hv j with h | h
      · exact ⟨0, by simp [h]⟩
      · exact ⟨1, by simp [h]⟩
    · simp only [Matrix.updateCol_ne (Fin.castSucc_lt_last i).ne, M0, R, Matrix.of_apply]
      rcases I j with t | t | i'
      · obtain ⟨q, hq⟩ := hPq t i; exact ⟨q, by simpa using hq⟩
      · obtain ⟨q, hq⟩ := hPq t i; exact ⟨q, by simpa using hq⟩
      · by_cases h : i = i'
        · subst h; exact ⟨1, by simp⟩
        · exact ⟨0, by simp [Ne.symm h]⟩
  obtain ⟨A, hA⟩ := hq Lv (fun j => by rcases h : I j <;> simp [Lv, L, h])
  obtain ⟨B, hB⟩ := hq Uv (fun j => by rcases h : I j with _ | _ | _ <;> simp [Uv, U, h])
  refine ⟨A, B, fun ρ => ⟨∏ j, α (I j) ρ, Finset.prod_pos fun j _ => ?_, ?_⟩⟩
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

/-- **Rationality of the least radius.** For rational prices, the least feasible radius `ρ*`
exists (the feasible radii are `[ρ*, ∞)`), and `e^{2ρ*}` is rational.

Proof. `least_radius_breakpoint` gives `ρ*`; if `ρ* > 0` some corner determinant vanishes at
`ρ*` but not identically. By `det_cornerVec_eq` it is `c (e^{ρ} A + e^{-ρ} B)`, so
`e^{2ρ*} A + B = 0`; `A ≠ 0` (else `B = 0` and the determinant vanishes identically), hence
`e^{2ρ*} = -B / A`. -/
theorem least_radius_rational (hd : 2 ≤ d) (P : Fin T → Fin d → ℝ) (hP : ∀ t, P t ∈ orthant d)
    (hPq : ∀ t i, ∃ q : ℚ, P t i = q) (y : Fin T → ℝ) (hy : ∀ t, 0 ≤ y t)
    (hfeas : ∃ ρ, 0 ≤ ρ ∧ Feasible P y ρ) :
    ∃ ρs, 0 ≤ ρs ∧ (∀ ρ, 0 ≤ ρ → (Feasible P y ρ ↔ ρs ≤ ρ)) ∧
      ∃ q : ℚ, exp (2 * ρs) = q := by
  obtain ⟨ρs, h0, hiff, h | ⟨I, hdet0, ρ, hρ⟩⟩ :=
    least_radius_breakpoint hd P hP y hy hfeas
  · exact ⟨ρs, h0, hiff, 1, by simp [h]⟩
  obtain ⟨A, B, hAB⟩ := det_cornerVec_eq P hPq I
  obtain ⟨c, hc, hc'⟩ := hAB ρs
  rw [hdet0] at hc'
  have h1 : exp ρs * (A : ℝ) + exp (-ρs) * (B : ℝ) = 0 := by
    rcases mul_eq_zero.1 hc'.symm with h | h
    · exact absurd h hc.ne'
    · exact h
  have h2 : exp (2 * ρs) * (A : ℝ) + B = 0 := by
    have e1 : exp ρs * exp (-ρs) = 1 := by rw [← exp_add]; simp
    have e2 : exp (2 * ρs) = exp ρs * exp ρs := by rw [two_mul, exp_add]
    rw [e2]
    calc exp ρs * exp ρs * (A : ℝ) + B
        = exp ρs * (exp ρs * A + exp (-ρs) * B) := by linear_combination (-(B : ℝ)) * e1
      _ = 0 := by rw [h1]; ring
  have hA : (A : ℝ) ≠ 0 := by
    intro hA0
    have hB : (B : ℝ) = 0 := by rw [hA0] at h2; simpa using h2
    obtain ⟨c2, _, hc2⟩ := hAB ρ
    apply hρ
    rw [hc2, hA0, hB]; simp
  refine ⟨ρs, h0, hiff, -B / A, ?_⟩
  push_cast
  rw [eq_div_iff hA]
  linarith

end NeoTiling.PricePerturbation
