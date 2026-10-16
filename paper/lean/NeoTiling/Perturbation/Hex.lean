import NeoTiling.Perturbation.Box

namespace NeoTiling.PricePerturbation

open NeoTiling Real

variable {d T : ℕ}

/-- Distance between normalized prices `a = (x₁/x₃, x₂/x₃)`, `b = (y₁/y₃, y₂/y₃)` induced by the
log-`ℓ¹` distance of the triples after optimal rescaling:
`max (|u₀|, |u₁|, |u₀ - u₁|)` with `uᵢ = log aᵢ - log bᵢ`. -/
noncomputable def hexDist (a b : Fin 2 → ℝ) : ℝ :=
  max |log (a 0) - log (b 0)|
    (max |log (a 1) - log (b 1)| |(log (a 0) - log (b 0)) - (log (a 1) - log (b 1))|)

open BoxPerturbation
open scoped Classical

/-- `exists_point_between` with the point on a continuous path `z`, `s ∈ [0, 1]`. -/
theorem exists_path_between {N d n : ℕ} {P : Fin N → Fin d → ℝ} {S : Fin n → Finset (Fin N)}
    (m : Fin n → ℝ) (hm : ∀ k, 0 ≤ m k) {z : ℝ → Fin d → ℝ} (hz : Continuous z) {c : ℝ}
    (h0 : c ≤ ∑ k, if Supported P (S k) (z 0) then m k else 0)
    (h1 : (∑ k, if StrictlySupported P (S k) (z 1) then m k else 0) ≤ c) :
    ∃ s ∈ Set.Icc (0 : ℝ) 1,
      (∑ k, if StrictlySupported P (S k) (z s) then m k else 0) ≤ c ∧
        c ≤ ∑ k, if Supported P (S k) (z s) then m k else 0 := by
  have hsum : ∀ (p : Finset (Fin N) → (Fin d → ℝ) → Prop) (s : ℝ),
      (∑ k, if p (S k) (z s) then m k else 0) =
        ∑ k, Set.indicator {s | p (S k) (z s)} (fun _ => m k) s := by
    intro p s; simp [Set.indicator]
  have hup : UpperSemicontinuous fun s => ∑ k, if Supported P (S k) (z s) then m k else 0 := by
    simp_rw [hsum]
    exact upperSemicontinuous_sum fun k _ =>
      (isClosed_setOf_supported.preimage hz).upperSemicontinuous_indicator (hm k)
  have hlow : LowerSemicontinuous fun s =>
      ∑ k, if StrictlySupported P (S k) (z s) then m k else 0 := by
    simp_rw [hsum]
    exact lowerSemicontinuous_sum fun k _ =>
      (isOpen_setOf_strictlySupported.preimage hz).lowerSemicontinuous_indicator (hm k)
  obtain ⟨s, hs, h1', h2'⟩ := exists_mem_Icc_between hup hlow
    (fun s _ => Finset.sum_le_sum fun k _ => by
      by_cases h : StrictlySupported P (S k) (z s)
      · simp [h, h.supported]
      · simp only [h, if_false]; split_ifs <;> simp [hm k])
    h0 h1
  exact ⟨s, hs, h1', h2'⟩

/-- `exists_point_between` with the point on the segment `l + s • (u - l)`, `s ∈ [0, 1]`. -/
theorem exists_segment_between {N d n : ℕ} {P : Fin N → Fin d → ℝ} {S : Fin n → Finset (Fin N)}
    (m : Fin n → ℝ) (hm : ∀ k, 0 ≤ m k) {l u : Fin d → ℝ} {c : ℝ}
    (h0 : c ≤ ∑ k, if Supported P (S k) l then m k else 0)
    (h1 : (∑ k, if StrictlySupported P (S k) u then m k else 0) ≤ c) :
    ∃ s ∈ Set.Icc (0 : ℝ) 1,
      (∑ k, if StrictlySupported P (S k) (l + s • (u - l)) then m k else 0) ≤ c ∧
        c ≤ ∑ k, if Supported P (S k) (l + s • (u - l)) then m k else 0 :=
  exists_path_between m hm (z := fun s => l + s • (u - l)) (by fun_prop) (by simpa using h0)
    (by simpa using h1)

/-- The `←` half of `box_iff` with every `Q t` on a continuous path `z t` from the lower corner
`z t 0 = L t` to the upper corner `z t 1 = U t` through nonnegative prices. -/
theorem path_of_corners (hd : 2 ≤ d) (L U : Fin T → Fin d → ℝ) (z : Fin T → ℝ → Fin d → ℝ)
    (hz : ∀ t, Continuous (z t)) (hz0 : ∀ t, z t 0 = L t) (hz1 : ∀ t, z t 1 = U t)
    (hpos : ∀ t, ∀ s ∈ Set.Icc (0 : ℝ) 1, 0 ≤ z t s) (y : Fin T → ℝ) (hy : ∀ t, 0 ≤ y t)
    (h : ∃ w ∈ indicatorCone (weakReachableSpectra (Fin.append L U)),
      (∀ t, y t ≤ w (Fin.castAdd T t)) ∧ (∀ t, w (Fin.natAdd T t) ≤ y t)) :
    ∃ s : Fin T → ℝ, (∀ t, s t ∈ Set.Icc (0 : ℝ) 1) ∧
      WeakSolvable (fun t => z t (s t)) y := by
  obtain ⟨w, hw, hlow, hupp⟩ := h
  set W := Fin.append L U with hW
  obtain ⟨n, f, g, hfg⟩ := Submodule.mem_span_set'.1 hw
  choose S hS hSg using fun k => (g k).2
  let m : Fin n → ℝ := fun k => f k
  have hwS : ∀ u, w u = ∑ k, if u ∈ S k then m k else 0 := by
    intro u
    simp only [← hfg, Finset.sum_apply, ← hSg, Pi.smul_apply, Set.indicator_apply,
      Finset.mem_coe, Pi.one_apply, smul_ite, smul_zero]
    exact Finset.sum_congr rfl fun k _ => by
      split_ifs
      · exact mul_one _
      · rfl
  have hpt : ∀ t, ∃ s ∈ Set.Icc (0 : ℝ) 1,
      (∑ k, if StrictlySupported W (S k) (z t s) then m k else 0) ≤ y t ∧
        y t ≤ ∑ k, if Supported W (S k) (z t s) then m k else 0 := by
    intro t
    refine exists_path_between m (fun k => (f k).2) (hz t) ?_ ?_
    · refine (hlow t).trans ((hwS _).trans_le (Finset.sum_le_sum fun k _ => ?_))
      have := IsWeakReachable.supported (hS k) (t := Fin.castAdd T t)
      rw [hW, Fin.append_left, ← hz0 t] at this
      split_ifs with h1 h2 <;> first | exact absurd (this h1) h2 | simp [m]
    · refine (Finset.sum_le_sum fun k _ => ?_).trans ((hwS _).symm.trans_le (hupp t))
      have := StrictlySupported.mem (P := W) (S := S k) (r := Fin.natAdd T t)
      rw [hW, Fin.append_right, ← hz1 t] at this
      split_ifs with h1 h2 <;> first | exact absurd (this h1) h2 | simp [m]
  choose s hs hQlo hQhi using hpt
  refine ⟨s, hs, (weakSolvable_iff hd (fun t => hpos t (s t) (hs t)) hy).2 ?_⟩
  refine mem_indicatorCone_of_between m (fun k => (f k).2)
    (fun k => Finset.univ.filter fun t => StrictlySupported W (S k) (z t (s t)))
    (fun k => Finset.univ.filter fun t => Supported W (S k) (z t (s t)))
    (fun k t ht => by simpa using (by simpa using ht : StrictlySupported W (S k) _).supported)
    (fun k R h1 h2 => isWeakReachable_of_supported (fun t ht => by simpa using h2 ht)
      fun t ht hst => ht (h1 (by simpa using hst)))
    y (fun t => by simpa using hQlo t) (fun t => by simpa using hQhi t)

/-- The `←` half of `box_iff` with every `Q t` on the diagonal `L t + s t • (U t - L t)`. -/
theorem diag_of_corners (hd : 2 ≤ d) (L U : Fin T → Fin d → ℝ) (y : Fin T → ℝ)
    (hL : ∀ t, L t ∈ orthant d) (hLU : ∀ t i, L t i ≤ U t i) (hy : ∀ t, 0 ≤ y t)
    (h : ∃ w ∈ indicatorCone (weakReachableSpectra (Fin.append L U)),
      (∀ t, y t ≤ w (Fin.castAdd T t)) ∧ (∀ t, w (Fin.natAdd T t) ≤ y t)) :
    ∃ s : Fin T → ℝ, (∀ t, s t ∈ Set.Icc (0 : ℝ) 1) ∧
      WeakSolvable (fun t => L t + s t • (U t - L t)) y := by
  refine path_of_corners hd L U (fun t s => L t + s • (U t - L t)) (fun t => by fun_prop)
    (fun t => by simp) (fun t => by simp) (fun t s hs i => ?_) y hy h
  have := mul_nonneg hs.1 (sub_nonneg.2 (hLU t i))
  simp only [Pi.add_apply, Pi.smul_apply, Pi.sub_apply, smul_eq_mul, Pi.zero_apply]
  linarith [hL t i]

/-- Pure rescaling: `hexDist (c • p) p = |log c|`. -/
theorem hexDist_smul {c : ℝ} (hc : 0 < c) {p : Fin 2 → ℝ} (hp : p ∈ orthant 2) :
    hexDist (c • p) p = |log c| := by
  have h : ∀ i, log (c * p i) - log (p i) = log c := fun i => by
    rw [Real.log_mul hc.ne' (hp i).ne']; ring
  simp [hexDist, h]

/-- The hexagon lies in the box: `hexDist q p ≤ ρ` gives `e^{-ρ} p ≤ q ≤ e^{ρ} p`. -/
theorem mem_box_of_hexDist {q p : Fin 2 → ℝ} (hq : q ∈ orthant 2) (hp : p ∈ orthant 2) {ρ : ℝ}
    (h : hexDist q p ≤ ρ) (i : Fin 2) : exp (-ρ) * p i ≤ q i ∧ q i ≤ exp ρ * p i := by
  have hi : |log (q i) - log (p i)| ≤ ρ := by
    fin_cases i
    · exact (le_max_left _ _).trans h
    · exact ((le_max_left _ _).trans (le_max_right _ _)).trans h
  obtain ⟨h1, h2⟩ := abs_le.1 hi
  have hp' := hp i
  have hqp := div_pos (hq i) hp'
  have hlog := Real.log_div (hq i).ne' hp'.ne'
  constructor
  · rw [← le_div_iff₀ hp', ← Real.le_log_iff_exp_le hqp, hlog]; exact h1
  · rw [← div_le_iff₀ hp', ← Real.log_le_iff_le_exp hqp, hlog]; exact h2

/-- `(A) → (C)`: a hexagon solution lies in the box `[e^{-ρ} P, e^{ρ} P]`; apply `box_iff`. -/
theorem corners_of_hex (P : Fin T → Fin 2 → ℝ) (hP : ∀ t, P t ∈ orthant 2) (y : Fin T → ℝ)
    (hy : ∀ t, 0 ≤ y t) {ρ : ℝ} (hρ : 0 ≤ ρ)
    (h : ∃ Q : Fin T → Fin 2 → ℝ, (∀ t, Q t ∈ orthant 2) ∧ (∀ t, hexDist (Q t) (P t) ≤ ρ) ∧
        WeakSolvable Q y) :
    ∃ w ∈ indicatorCone (weakReachableSpectra
          (Fin.append (fun t => exp (-ρ) • P t) (fun t => exp ρ • P t))),
        (∀ t, y t ≤ w (Fin.castAdd T t)) ∧ (∀ t, w (Fin.natAdd T t) ≤ y t) := by
  obtain ⟨Q, hQ, hd, hws⟩ := h
  refine (box_iff le_rfl _ _ y (fun t i => mul_pos (exp_pos _) (hP t i))
    (fun t i => mul_le_mul_of_nonneg_right (exp_le_exp.2 (by linarith)) (hP t i).le) hy).1
    ⟨Q, fun t i => ?_, hws⟩
  simpa using mem_box_of_hexDist (hQ t) (hP t) (hd t) i

/-- `(C) → (B)`: the diagonal of the box `[e^{-ρ} P t, e^{ρ} P t]` consists of the rescalings
`c • P t`, `c ∈ [e^{-ρ}, e^{ρ}]`; apply `diag_of_corners`. -/
theorem scale_of_corners (hd : 2 ≤ d) (P : Fin T → Fin d → ℝ) (hP : ∀ t, P t ∈ orthant d)
    (y : Fin T → ℝ)
    (hy : ∀ t, 0 ≤ y t) {ρ : ℝ} (hρ : 0 ≤ ρ)
    (h : ∃ w ∈ indicatorCone (weakReachableSpectra
          (Fin.append (fun t => exp (-ρ) • P t) (fun t => exp ρ • P t))),
        (∀ t, y t ≤ w (Fin.castAdd T t)) ∧ (∀ t, w (Fin.natAdd T t) ≤ y t)) :
    ∃ c : Fin T → ℝ, (∀ t, exp (-ρ) ≤ c t ∧ c t ≤ exp ρ) ∧
        WeakSolvable (fun t => c t • P t) y := by
  have hle : exp (-ρ) ≤ exp ρ := exp_le_exp.2 (by linarith)
  obtain ⟨s, hs, hws⟩ := diag_of_corners hd _ _ y (fun t i => mul_pos (exp_pos _) (hP t i))
    (fun t i => mul_le_mul_of_nonneg_right hle (hP t i).le) hy h
  refine ⟨fun t => exp (-ρ) + s t * (exp ρ - exp (-ρ)), fun t => ⟨?_, ?_⟩, ?_⟩
  · nlinarith [(hs t).1]
  · nlinarith [(hs t).2]
  · convert hws using 2 with t
    ext i; simp; ring

/-- `(B) → (A)`: a rescaling `c • P t` with `c ∈ [e^{-ρ}, e^{ρ}]` is within distance `ρ`. -/
theorem hex_of_scale (P : Fin T → Fin 2 → ℝ) (hP : ∀ t, P t ∈ orthant 2) (y : Fin T → ℝ) {ρ : ℝ}
    (h : ∃ c : Fin T → ℝ, (∀ t, exp (-ρ) ≤ c t ∧ c t ≤ exp ρ) ∧
        WeakSolvable (fun t => c t • P t) y) :
    ∃ Q : Fin T → Fin 2 → ℝ, (∀ t, Q t ∈ orthant 2) ∧ (∀ t, hexDist (Q t) (P t) ≤ ρ) ∧
        WeakSolvable Q y := by
  obtain ⟨c, hc, hws⟩ := h
  have hc0 : ∀ t, 0 < c t := fun t => (exp_pos _).trans_le (hc t).1
  refine ⟨fun t => c t • P t, fun t i => by simpa using mul_pos (hc0 t) (hP t i), fun t => ?_,
    hws⟩
  rw [hexDist_smul (hc0 t) (hP t), abs_le]
  exact ⟨(Real.le_log_iff_exp_le (hc0 t)).2 (hc t).1,
    (Real.log_le_iff_le_exp (hc0 t)).2 (hc t).2⟩

/-- Some prices within hexagonal distance `ρ` of `P` make `y` weakly solvable iff some
rescalings `c t • P t` with `e^{-ρ} ≤ c t ≤ e^{ρ}` do. -/
theorem hex_iff_scale (P : Fin T → Fin 2 → ℝ) (hP : ∀ t, P t ∈ orthant 2) (y : Fin T → ℝ)
    (hy : ∀ t, 0 ≤ y t) {ρ : ℝ} (hρ : 0 ≤ ρ) :
    (∃ Q : Fin T → Fin 2 → ℝ, (∀ t, Q t ∈ orthant 2) ∧ (∀ t, hexDist (Q t) (P t) ≤ ρ) ∧
        WeakSolvable Q y) ↔
      ∃ c : Fin T → ℝ, (∀ t, exp (-ρ) ≤ c t ∧ c t ≤ exp ρ) ∧
        WeakSolvable (fun t => c t • P t) y :=
  ⟨fun h => scale_of_corners le_rfl P hP y hy hρ (corners_of_hex P hP y hy hρ h), hex_of_scale P hP y⟩

/-- Some prices within hexagonal distance `ρ` of `P` make `y` weakly solvable iff the `2T`
corners `e^{-ρ} P t`, `e^{ρ} P t` carry a vector `w` of the cone of weakly reachable spectra with
`w (lower corner of t) ≥ y t ≥ w (upper corner of t)`. -/
theorem hex_iff_corners (P : Fin T → Fin 2 → ℝ) (hP : ∀ t, P t ∈ orthant 2) (y : Fin T → ℝ)
    (hy : ∀ t, 0 ≤ y t) {ρ : ℝ} (hρ : 0 ≤ ρ) :
    (∃ Q : Fin T → Fin 2 → ℝ, (∀ t, Q t ∈ orthant 2) ∧ (∀ t, hexDist (Q t) (P t) ≤ ρ) ∧
        WeakSolvable Q y) ↔
      ∃ w ∈ indicatorCone (weakReachableSpectra
          (Fin.append (fun t => exp (-ρ) • P t) (fun t => exp ρ • P t))),
        (∀ t, y t ≤ w (Fin.castAdd T t)) ∧ (∀ t, w (Fin.natAdd T t) ≤ y t) :=
  ⟨corners_of_hex P hP y hy hρ,
    fun h => hex_of_scale P hP y (scale_of_corners le_rfl P hP y hy hρ h)⟩

end NeoTiling.PricePerturbation
