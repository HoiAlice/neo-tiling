import NeoTiling.Solvability

/-!
# Weakly reachable spectra and the closure of the solvable prices

An index `t` *strictly covers* `R` (`StrictCovers`) if `p_t` strictly dominates, in every
coordinate, a convex combination of the prices `p_r`, `r ∈ R`. A set `S` is *weakly reachable*
(`IsWeakReachable`) if every `t ∈ S` has a witness `ζ ≥ 0`, `∑ ζ = 1`, with `⟨ζ, p_s - p_t⟩ ≥ 0`
for all `s ∉ S`; equivalently no `t ∈ S` strictly covers `Sᶜ` (`isWeakReachable_iff`, by
separation in `exists_weak_witness_of_not_strictCovers`).

Main result: `y ≥ 0` lies in the cone of the weakly reachable spectra of `P` iff `P` is a limit of
prices at which `y` is solvable (`mem_closure_of_weakReachable`, `weakReachable_of_mem_closure`).

The hard direction combines two ideas.

* **(A) Monotone representation** (`mem_indicatorCone_monotone`). The *cluster* of `b`
  (`cluster`) is the set of indices with price `p_b`. An *upper set* of `y` on `C` is a set
  `{x ∈ C | y x > θ}`; `UpperOn y C S` says that `S ∩ C` is one. Cluster by cluster, the spectra
  of a representation `y = ∑ m_S 1_S` are rematched inside the cluster `C` (`rematches`: weakly
  reachable, unchanged off `C`, meeting `C` in an upper set of `y`): write the mass of the spectra
  splitting `C` as a layer cake (`layer_cake`) and glue its layers to the parts of these spectra
  outside `C` (`isWeakReachable_rematch`, `add_mem_indicatorCone_glue`,
  `add_mem_indicatorCone_cluster`, `mem_indicatorCone_rematch`).
* **(B) One tilt** (`isReachable_tilt`). Moving every price along `-1` by
  `δ ∑ᵢ log (p_t)ᵢ + δ² y_t` makes every weakly reachable spectrum meeting every cluster in an
  upper set of `y` reachable for small `δ > 0`: strict concavity of `log` separates distinct
  prices at order `δ`, and the term `δ² y_t` separates equal prices at order `δ²`.
-/

open Set Filter Topology

namespace NeoTiling

variable {d T : ℕ} {P : Fin T → Fin d → ℝ} {y : Fin T → ℝ}

/-! ### Definitions -/

/-- `t` strictly covers `R`: `∑_r w_r p_r < p_t` in every coordinate for convex weights `w`
supported on `R`. -/
def StrictCovers (P : Fin T → Fin d → ℝ) (t : Fin T) (R : Finset (Fin T)) : Prop :=
  ∃ w : Fin T → ℝ, (∀ r, 0 ≤ w r) ∧ (∀ r ∉ R, w r = 0) ∧ ∑ r, w r = 1 ∧
    ∀ i, (∑ r, w r • P r) i < P t i

/-- `S` is weakly reachable: every `t ∈ S` has a normalized witness `ζ ≥ 0`, `∑ ζ = 1`, with
`⟨ζ, p_s - p_t⟩ ≥ 0` for all `s ∉ S`. -/
def IsWeakReachable (P : Fin T → Fin d → ℝ) (S : Finset (Fin T)) : Prop :=
  ∀ t ∈ S, ∃ ζ : Fin d → ℝ, (∀ i, 0 ≤ ζ i) ∧ ∑ i, ζ i = 1 ∧ ∀ s ∉ S, 0 ≤ ζ ⬝ᵥ (P s - P t)

/-- The weakly reachable spectra. -/
def weakReachableSpectra (P : Fin T → Fin d → ℝ) : Set (Finset (Fin T)) :=
  {S | IsWeakReachable P S}

/-- A strict covering is a covering. The same weights work, with `<` weakened to `≤`. -/
theorem StrictCovers.covers {t : Fin T} {R : Finset (Fin T)} (h : StrictCovers P t R) :
    Covers P t R :=
  let ⟨w, hw0, hwR, hw1, hlt⟩ := h
  ⟨w, hw0, hwR, hw1, fun i => (hlt i).le⟩

/-! ### Weak witnesses -/

/-- A convex combination with a positive value at every point of its support is positive. -/
theorem pos_sum_mul {ι : Type*} [Fintype ι] {w f : ι → ℝ} (hw0 : ∀ r, 0 ≤ w r)
    (hw1 : ∑ r, w r = 1) (hf : ∀ r, w r ≠ 0 → 0 < f r) : 0 < ∑ r, w r * f r := by
  obtain ⟨r, hr⟩ : ∃ r, w r ≠ 0 := by
    by_contra h; push_neg at h; simp [h] at hw1
  refine Finset.sum_pos' (fun s _ => ?_)
    ⟨r, Finset.mem_univ _, mul_pos ((hw0 r).lt_of_ne' hr) (hf r hr)⟩
  by_cases h : w s = 0
  · simp [h]
  · exact (mul_pos ((hw0 s).lt_of_ne' h) (hf s h)).le

/-- Averaging against weights of total mass `1`:
`∑ w_r ⟨ξ, q_r - q_t⟩ = ⟨ξ, ∑ w_r q_r - q_t⟩`. -/
theorem sum_dotProduct_sub {Q : Fin T → Fin d → ℝ} {w : Fin T → ℝ} (hw1 : ∑ r, w r = 1)
    (ξ : Fin d → ℝ) (t : Fin T) :
    ∑ r, w r * (ξ ⬝ᵥ (Q r - Q t)) = ξ ⬝ᵥ ((∑ r, w r • Q r) - Q t) := by
  simp only [dotProduct_sub, dotProduct_sum, dotProduct_smul, smul_eq_mul, mul_sub,
    Finset.sum_sub_distrib, ← Finset.sum_mul, hw1, one_mul]

/-- A weak witness excludes strict covering: `0 ≤ ∑_s w_s ⟨ζ, p_s - p_t⟩ = ⟨ζ, ∑ w p - p_t⟩ < 0`. -/
theorem not_strictCovers_of_isWeakReachable {S : Finset (Fin T)} (hS : IsWeakReachable P S)
    {t : Fin T} (ht : t ∈ S) : ¬ StrictCovers P t Sᶜ := by
  rintro ⟨w, hw0, hwS, hw1, hlt⟩
  obtain ⟨ζ, hζ0, hζ1, hζ⟩ := hS t ht
  have ha : 0 ≤ ∑ r, w r * (ζ ⬝ᵥ (P r - P t)) := Finset.sum_nonneg fun r _ => by
    by_cases hr : r ∈ S
    · simp [hwS r (by simpa using hr)]
    · exact mul_nonneg (hw0 r) (hζ r hr)
  have hc := pos_sum_mul hζ0 hζ1 (f := fun i => P t i - (∑ r, w r • P r) i)
    fun i _ => sub_pos.2 (hlt i)
  rw [sum_dotProduct_sub hw1] at ha
  simp only [dotProduct, Pi.sub_apply, mul_sub, Finset.sum_sub_distrib] at ha hc
  linarith

/-- A nonnegative `ξ` with `⟨ξ, q_s - q_t⟩ > 0` for all `s ∉ S` excludes covering. -/
theorem not_covers_of_pos {Q : Fin T → Fin d → ℝ} {S : Finset (Fin T)} {t : Fin T}
    {ξ : Fin d → ℝ} (hξ : 0 ≤ ξ) (h : ∀ s ∉ S, 0 < ξ ⬝ᵥ (Q s - Q t)) : ¬ Covers Q t Sᶜ := by
  rintro ⟨w, hw0, hwS, hw1, hle⟩
  have hpos := pos_sum_mul hw0 hw1 (f := fun r => ξ ⬝ᵥ (Q r - Q t)) fun r hr =>
    h r fun hrS => hr (hwS r (by simpa using hrS))
  rw [sum_dotProduct_sub hw1] at hpos
  have := dotProduct_le_dotProduct_of_nonneg_left (sub_nonpos.2 hle) hξ
  simp only [dotProduct_zero] at this
  linarith

open Pointwise in
/-- **Separation.** If `t` does not strictly cover `R`, some `ζ ≥ 0` with `∑ ζ = 1` has
`⟨ζ, p_s - p_t⟩ ≥ 0` for all `s ∈ R`. A functional `f` separates `p_t` from the open convex set
`O` of points strictly above a convex combination of `p_s`, `s ∈ R`; testing `f` on
`p_s + ε 1 + λ eᵢ ∈ O` shows that `ζ ∝ -f` is a nonnegative nonzero witness. The case `R = ∅` is
the witness `e₀`. -/
theorem exists_weak_witness_of_not_strictCovers (hd : 1 ≤ d) {R : Finset (Fin T)} {t : Fin T}
    (h : ¬ StrictCovers P t R) :
    ∃ ζ : Fin d → ℝ, (∀ i, 0 ≤ ζ i) ∧ ∑ i, ζ i = 1 ∧ ∀ s ∈ R, 0 ≤ ζ ⬝ᵥ (P s - P t) := by
  rcases R.eq_empty_or_nonempty with rfl | ⟨s₀, hs₀⟩
  · exact ⟨Pi.single ⟨0, hd⟩ 1, fun i => by rw [Pi.single_apply]; positivity, by simp,
      by simp⟩
  set K := stdSimplex ℝ (Fin T) ∩ (↑R : Set (Fin T))ᶜ.pi fun _ => {0}
  set L := Fintype.linearCombination ℝ P
  have hO (s) (hs : s ∈ R) (v) (hv : v ∈ orthant d) : P s + v ∈ L '' K + orthant d :=
    ⟨_, ⟨Pi.single s 1, ⟨single_mem_stdSimplex ℝ s, fun r hr =>
      Pi.single_eq_of_ne (by rintro rfl; exact hr hs) 1⟩, by simp [L]⟩, v, hv, rfl⟩
  obtain ⟨f, hf⟩ := geometric_hahn_banach_open_point
    ((((convex_stdSimplex ℝ _).inter (convex_pi fun _ _ => convex_singleton 0)).linear_image
      L).add (by simpa [orthant, Set.pi] using
        convex_pi (s := univ) fun (_ : Fin d) _ => convex_Ioi (0 : ℝ))) isOpen_orthant.add_left
    (x := P t) fun ⟨_, ⟨w, ⟨hw, hwR⟩, hwL⟩, v, hv, hwv⟩ => h ⟨w, hw.1, hwR, hw.2, fun i => by
      simpa [← hwv, ← hwL, L, Fintype.linearCombination_apply] using hv i⟩
  set e : Fin d → Fin d → ℝ := fun i j => if i = j then 1 else 0
  set c := fun i => f (e i)
  have hlin x : f x = ∑ i, x i * c i := f.toLinearMap.pi_apply_eq_sum_univ x
  have hone : f 1 = ∑ i, c i := by simp [hlin]
  have hc (i) : c i ≤ 0 := not_lt.1 fun hc => by
    set a := |f (P t) - f (P s₀) - f 1|
    have := hf _ (hO s₀ hs₀ (1 + (a / c i) • e i) fun j => by simp [e]; positivity)
    rw [map_add, map_add, map_smul, smul_eq_mul, show f (e i) = c i from rfl,
      div_mul_cancel₀ _ hc.ne'] at this
    linarith [le_abs_self (f (P t) - f (P s₀) - f 1)]
  have h1 : f 1 < 0 := (hone ▸ Finset.sum_nonpos fun i _ => hc i).lt_of_ne fun h0 => by
    simpa [hlin, (Finset.sum_eq_zero_iff_of_nonpos fun i _ => hc i).1 (hone ▸ h0)] using
      hf _ (hO s₀ hs₀ 1 fun _ => one_pos)
  have hle (s) (hs : s ∈ R) : f (P s) ≤ f (P t) := le_of_forall_pos_lt_add fun ε hε => by
    have := hf _ (hO s hs ((ε / -f 1) • 1) fun _ => by simpa using div_pos hε (neg_pos.2 h1))
    simp [div_neg, h1.ne] at this; linarith
  have hζ (x) : (fun i => c i / f 1) ⬝ᵥ x = f x / f 1 := by
    simp [hlin, dotProduct, Finset.sum_div, mul_div_assoc, mul_comm]
  refine ⟨fun i => c i / f 1, fun i => div_nonneg_of_nonpos (hc i) h1.le, by
    rw [← Finset.sum_div, ← hone, div_self h1.ne], fun s hs => by
    rw [hζ, map_sub]; exact div_nonneg_of_nonpos (sub_nonpos.2 (hle s hs)) h1.le⟩

/-- Weak reachability means no `t ∈ S` strictly covers `Sᶜ`. `→` is
`not_strictCovers_of_isWeakReachable`, `←` is `exists_weak_witness_of_not_strictCovers`. -/
theorem isWeakReachable_iff (hd : 1 ≤ d) {S : Finset (Fin T)} :
    IsWeakReachable P S ↔ ∀ t ∈ S, ¬ StrictCovers P t Sᶜ := by
  refine ⟨fun hS t ht => not_strictCovers_of_isWeakReachable hS ht, fun h t ht => ?_⟩
  obtain ⟨ζ, h0, h1, hζ⟩ := exists_weak_witness_of_not_strictCovers hd (h t ht)
  exact ⟨ζ, h0, h1, fun s hs => hζ s (Finset.mem_compl.2 hs)⟩

/-- Reachable spectra are weakly reachable. A strict covering is a covering
(`StrictCovers.covers`), so `isWeakReachable_iff` applies. -/
theorem IsReachable.isWeakReachable (hd : 1 ≤ d) {S : Finset (Fin T)} (hS : IsReachable P S) :
    IsWeakReachable P S :=
  (isWeakReachable_iff hd).2 fun t ht hc => hS t ht hc.covers

/-! ### Monotone representation -/

/-- The cluster of `b`: the indices with price `p_b`. -/
noncomputable def cluster (P : Fin T → Fin d → ℝ) (b : Fin T) : Finset (Fin T) :=
  Finset.univ.filter (P · = P b)

/-- `S ∩ C` is an upper set of `f` on `C`: `f s < f t` for `t ∈ S ∩ C`, `s ∈ C \ S`. -/
def UpperOn (f : Fin T → ℝ) (C S : Finset (Fin T)) : Prop :=
  ∀ t ∈ S, ∀ s ∉ S, s ∈ C → t ∈ C → f s < f t

/-- Spectra obtained from `A` by rematching inside `C`: weakly reachable, equal to some `S₀ ∈ A`
off `C`, and meeting `C` in an upper set of `f`. -/
def rematches (P : Fin T → Fin d → ℝ) (A : Set (Finset (Fin T))) (C : Finset (Fin T))
    (f : Fin T → ℝ) : Set (Finset (Fin T)) :=
  {S | IsWeakReachable P S ∧ (∃ S₀ ∈ A, S \ C = S₀ \ C) ∧ UpperOn f C S}

/-- `a 1_S` lies in the cone of `A` if `a ≥ 0` and `S ∈ A` unless `a = 0`. It is `0` or a
generator times `a`. -/
theorem smul_indicator_mem_indicatorCone {T : ℕ} {A : Set (Finset (Fin T))} {a : ℝ}
    {S : Finset (Fin T)} (ha : 0 ≤ a) (hS : a ≠ 0 → S ∈ A) :
    a • ((S : Set (Fin T)).indicator (1 : Fin T → ℝ)) ∈ indicatorCone A := by
  by_cases h0 : a = 0
  · rw [h0, zero_smul]; exact Submodule.zero_mem _
  · exact PointedCone.smul_mem _ ha (PointedCone.subset_span ⟨S, hS h0, rfl⟩)

/-- **Layer cake.** A nonnegative `z` is a nonnegative combination of its super-level sets
`{s | z r ≤ z s}` taken only at positive levels `z r > 0`. Induction on the number of indices with
positive value: subtract `v 1_{z ≥ v}` for the least positive value `v`. -/
theorem layer_cake {z : Fin T → ℝ} (hz : ∀ s, 0 ≤ z s) :
    ∃ c : Fin T → ℝ, (∀ r, 0 ≤ c r) ∧ (∀ r, c r ≠ 0 → 0 < z r) ∧
      z = ∑ r, c r • ((Finset.univ.filter fun s => z r ≤ z s : Finset (Fin T)) :
        Set (Fin T)).indicator 1 := by
  suffices h : ∃ c : Fin T → ℝ, (∀ r, 0 ≤ c r) ∧ (∀ r, c r ≠ 0 → 0 < z r) ∧
      ∀ s, z s = ∑ r, if z r ≤ z s then c r else 0 by
    obtain ⟨c, h0, h1, h2⟩ := h
    refine ⟨c, h0, h1, funext fun s => (h2 s).trans ?_⟩
    rw [Finset.sum_apply]
    refine Finset.sum_congr rfl fun r _ => ?_
    by_cases h : z r ≤ z s <;> simp [Set.indicator, h]
  induction' hn : (Finset.univ.filter fun s => 0 < z s).card using Nat.strong_induction_on
    with n ih generalizing z
  by_cases hpos : ∃ r, 0 < z r
  · obtain ⟨r0, hr0, hmin⟩ := Finset.exists_min_image (Finset.univ.filter fun s => 0 < z s) z
      (by simpa [Finset.Nonempty] using hpos)
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hr0 hmin
    -- subtract the least positive value `z r0` from everything above it
    have hpos' : ∀ s, 0 < max (z s - z r0) 0 ↔ z r0 < z s := fun s => by simp
    obtain ⟨c', h0, h1, h2⟩ := ih _ (hn ▸ Finset.card_lt_card (Finset.ssubset_iff_of_subset
      (fun s hs => by simp_all; linarith) |>.2 ⟨r0, by simpa using hr0, by simp⟩))
      (z := fun s => max (z s - z r0) 0) (fun s => le_max_right _ _) rfl
    refine ⟨fun r => c' r + if r = r0 then z r0 else 0, fun r => ?_, fun r hr => ?_, fun s => ?_⟩
    · exact add_nonneg (h0 r) (by split_ifs <;> linarith)
    · by_cases h : r = r0
      · rwa [h]
      · exact hr0.trans ((hpos' r).1 (h1 r (by simpa [h] using hr)))
    · have e1 : max (z s - z r0) 0 = ∑ r, if z r ≤ z s then c' r else 0 :=
        (h2 s).trans (Finset.sum_congr rfl fun r _ => by
          by_cases h : c' r = 0
          · simp [h]
          · have := (hpos' r).1 (h1 r h)
            simp [max_eq_left (by linarith : 0 ≤ z r - z r0), not_le.2 this])
      simp only [ite_add_zero, Finset.sum_add_distrib, ← e1]
      rw [Finset.sum_eq_single r0 (fun r _ hr => by simp [hr]) (by simp)]
      by_cases hs : z r0 ≤ z s
      · simp [hs]
      · have : z s = 0 := le_antisymm (not_lt.1 fun h => hs (hmin s h)) (hz s)
        simpa [hs, max_eq_right (by linarith : z s - z r0 ≤ 0)] using this
  · push_neg at hpos
    exact ⟨0, fun _ => le_rfl, fun r h => absurd rfl h, fun s => by
      simp [le_antisymm (hpos s) (hz s)]⟩

/-- **Rematching a set of equal prices.** Let all prices on `C` be equal. If `u` is weakly
reachable, meets `C` and misses a point of `C`, then `(u \ C) ∪ L` is weakly reachable for every
`L ⊆ C`. For `t ∉ C` the witness of `t` for `u` works (a point of `C` is compared like the point of
`C \ u`); for `t ∈ L` the witness of a point of `u ∩ C` works. -/
theorem isWeakReachable_rematch {C u L : Finset (Fin T)} (hC : ∀ s ∈ C, ∀ t ∈ C, P s = P t)
    (hu : IsWeakReachable P u) (hu1 : (u ∩ C).Nonempty) (hu2 : (C \ u).Nonempty) (hL : L ⊆ C) :
    IsWeakReachable P (u \ C ∪ L) := by
  obtain ⟨t₁, ht₁⟩ := hu1
  obtain ⟨s₁, hs₁⟩ := hu2
  obtain ⟨ht₁u, ht₁C⟩ := Finset.mem_inter.1 ht₁
  obtain ⟨hs₁C, hs₁u⟩ := Finset.mem_sdiff.1 hs₁
  have hout : ∀ s ∉ u \ C ∪ L, s ∉ C → s ∉ u := fun s hs hsC h =>
    hs (Finset.mem_union_left _ (Finset.mem_sdiff.2 ⟨h, hsC⟩))
  intro t ht
  by_cases hc : t ∈ C
  · obtain ⟨ζ, h0, h1, hζ⟩ := hu _ ht₁u
    refine ⟨ζ, h0, h1, fun s hs => ?_⟩
    rw [hC t hc _ ht₁C]
    by_cases hsC : s ∈ C
    · rw [hC s hsC _ ht₁C, sub_self, dotProduct_zero]
    · exact hζ s (hout s hs hsC)
  · have htu : t ∈ u := (Finset.mem_union.1 ht).elim (Finset.mem_sdiff.1 · |>.1)
      fun h => absurd (hL h) hc
    obtain ⟨ζ, h0, h1, hζ⟩ := hu t htu
    refine ⟨ζ, h0, h1, fun s hs => ?_⟩
    by_cases hsC : s ∈ C
    · rw [hC s hsC _ hs₁C]; exact hζ _ hs₁u
    · exact hζ s (hout s hs hsC)

/-- **Gluing layers.** Let `M = ∑_{u ∈ U} m_u > 0`. If every `K_u` is in `B` and, whenever
`c_r ≠ 0`, `L_r` is disjoint from `K_u` and `K_u ∪ L_r ∈ B`, then
`∑_u m_u 1_{K_u} + ∑_r c_r 1_{L_r}` is in the cone of `B`. Here `∑ c = Λ ≤ M`; padding weight
`(M − Λ)/M` on `K_u`, layer weight `c_r/M` on `K_u ∪ L_r`; `K_u ∈ B` is only needed when
`Λ < M`. -/
theorem add_mem_indicatorCone_glue {B : Set (Finset (Fin T))} {ι : Type*} (U : Finset ι)
    {m : ι → ℝ} {c : Fin T → ℝ} {K : ι → Finset (Fin T)} {L : Fin T → Finset (Fin T)}
    (hm : ∀ u, 0 ≤ m u) (hM : 0 < ∑ u ∈ U, m u) (hc : ∀ r, 0 ≤ c r)
    (hcM : ∑ r, c r ≤ ∑ u ∈ U, m u) (hK : ∀ u ∈ U, K u ∈ B)
    (hKL : ∀ u ∈ U, ∀ r, c r ≠ 0 → Disjoint (K u) (L r) ∧ K u ∪ L r ∈ B) :
    ∑ u ∈ U, m u • ((K u : Set (Fin T)).indicator (1 : Fin T → ℝ)) +
      ∑ r, c r • ((L r : Set (Fin T)).indicator 1) ∈ indicatorCone B := by
  set M := ∑ u ∈ U, m u
  set v := fun u => (K u : Set (Fin T)).indicator (1 : Fin T → ℝ)
  set ℓ := fun r => (L r : Set (Fin T)).indicator (1 : Fin T → ℝ)
  have hv : ∀ u, (m u * (M - ∑ r, c r) / M) • v u + ∑ r, (m u * c r / M) • v u = m u • v u := by
    intro u
    rw [← Finset.sum_smul, ← add_smul, ← Finset.sum_div, ← Finset.mul_sum, ← add_div, ← mul_add,
      sub_add_cancel, mul_div_cancel_right₀ _ hM.ne']
  have hℓ : ∀ r, ∑ u ∈ U, (m u * c r / M) • ℓ r = c r • ℓ r := by
    intro r
    rw [← Finset.sum_smul, ← Finset.sum_div, ← Finset.sum_mul, mul_div_cancel_left₀ _ hM.ne']
  have split : ∑ u ∈ U, m u • v u + ∑ r, c r • ℓ r = ∑ u ∈ U, ((m u * (M - ∑ r, c r) / M) • v u +
      ∑ r, (m u * c r / M) • (v u + ℓ r)) := by
    simp only [smul_add, Finset.sum_add_distrib, ← add_assoc, hv]
    rw [Finset.sum_comm]
    simp only [hℓ]
  rw [split]
  refine Submodule.sum_mem _ fun u hu => Submodule.add_mem _
    (smul_indicator_mem_indicatorCone (div_nonneg (mul_nonneg (hm u) (sub_nonneg.2 hcM)) hM.le)
      fun _ => hK u hu) (Submodule.sum_mem _ fun r _ => ?_)
  by_cases hr : c r = 0
  · rw [hr, mul_zero, zero_div, zero_smul]; exact Submodule.zero_mem _
  obtain ⟨hd, hB⟩ := hKL u hu r hr
  convert smul_indicator_mem_indicatorCone (S := K u ∪ L r)
    (div_nonneg (mul_nonneg (hm u) (hc r)) hM.le) fun _ => hB using 2
  rw [Finset.coe_union, Set.indicator_union_of_disjoint (Finset.disjoint_coe.2 hd)]; rfl

/-- **Gluing a cluster.** Let `C` be the cluster of `b`, let `U ⊆ A` be spectra splitting `C` with
masses `m ≥ 0`, and `z = ∑_{u ∈ U} m_u 1_{u ∩ C}`. Then `∑_u m_u 1_{u \ C} + z` is in the cone of
the spectra obtained from `A` by rematching inside `C` with `z`: glue the layers of `z`
(`layer_cake`) to the parts `u \ C` (`isWeakReachable_rematch`, `add_mem_indicatorCone_glue`). -/
theorem add_mem_indicatorCone_cluster {A : Set (Finset (Fin T))}
    (hA : A ⊆ weakReachableSpectra P) (b : Fin T) {U : Finset (Finset (Fin T))}
    {m : Finset (Fin T) → ℝ} (hm : ∀ u, 0 ≤ m u)
    (hU : ∀ u ∈ U, u ∈ A ∧ (u ∩ cluster P b).Nonempty ∧ (cluster P b \ u).Nonempty) :
    ∑ u ∈ U, m u • ((u \ cluster P b : Finset (Fin T)) : Set (Fin T)).indicator 1 +
        ∑ u ∈ U, m u • ((u ∩ cluster P b : Finset (Fin T)) : Set (Fin T)).indicator 1 ∈
      indicatorCone (rematches P A (cluster P b)
        (∑ u ∈ U, m u • ((u ∩ cluster P b : Finset (Fin T)) : Set (Fin T)).indicator 1)) := by
  classical
  set C := cluster P b with hCdef
  have hC : ∀ s ∈ C, ∀ t ∈ C, P s = P t := fun s hs t ht => by
    simp only [hCdef, cluster, Finset.mem_filter] at hs ht; rw [hs.2, ht.2]
  by_cases hM : ∑ u ∈ U, m u = 0
  · have h0 := (Finset.sum_eq_zero_iff_of_nonneg fun u _ => hm u).1 hM
    have e : ∀ K : Finset (Fin T) → Finset (Fin T),
        ∑ u ∈ U, m u • ((K u : Set (Fin T)).indicator (1 : Fin T → ℝ)) = 0 :=
      fun K => Finset.sum_eq_zero fun u hu => by rw [h0 u hu, zero_smul]
    rw [e (· \ C), e (· ∩ C), add_zero]
    exact Submodule.zero_mem _
  have hMpos : 0 < ∑ u ∈ U, m u := lt_of_le_of_ne (Finset.sum_nonneg fun u _ => hm u) (Ne.symm hM)
  set z := ∑ u ∈ U, m u • ((u ∩ C : Finset (Fin T)) : Set (Fin T)).indicator (1 : Fin T → ℝ)
    with hz
  have hzs : ∀ s, z s = ∑ u ∈ U, if s ∈ u ∧ s ∈ C then m u else 0 := fun s => by
    simp [hz, Finset.sum_apply, Set.indicator]
  have hz0 : ∀ s, 0 ≤ z s := fun s => hzs s ▸ Finset.sum_nonneg fun _ _ => ite_nonneg (hm _) le_rfl
  obtain ⟨c, hc0, hcz, hzv⟩ := layer_cake hz0
  set L : Fin T → Finset (Fin T) := fun r => Finset.univ.filter fun s => z r ≤ z s with hL
  have hzv' : z = ∑ r, c r • ((L r : Set (Fin T)).indicator 1) := hzv
  obtain ⟨s₀, -, hmax⟩ := Finset.exists_max_image Finset.univ z ⟨b, Finset.mem_univ _⟩
  have hcs : ∑ r, c r ≤ ∑ u ∈ U, m u := by
    have h1 := congrFun hzv' s₀
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, hL, Finset.coe_filter,
      Set.indicator, Finset.mem_univ, true_and, Set.mem_setOf_eq,
      hmax _ (Finset.mem_univ _), if_true, Pi.one_apply, mul_one] at h1
    have h2 : z s₀ ≤ ∑ u ∈ U, m u :=
      hzs s₀ ▸ Finset.sum_le_sum fun _ _ => by split_ifs <;> simp [hm]
    linarith
  have key := add_mem_indicatorCone_glue (B := rematches P A C z) (K := (· \ C)) (L := L) U hm
    hMpos hc0 hcs (fun u hu => ?_) (fun u hu r hr => ?_)
  · rwa [← hzv'] at key
  all_goals obtain ⟨huA, h1, h2⟩ := hU u hu
  · exact ⟨by simpa using isWeakReachable_rematch hC (hA huA) h1 h2 (Finset.empty_subset C),
      ⟨u, huA, Finset.sdiff_idem _ _⟩, fun t ht _ _ _ htC => ((Finset.mem_sdiff.1 ht).2 htC).elim⟩
  have hLC : L r ⊆ C := fun s hs => by
    by_contra h
    linarith [show z s = 0 by simp [hzs, h], (Finset.mem_filter.1 hs).2, hcz r hr]
  refine ⟨Finset.disjoint_of_subset_right hLC Finset.sdiff_disjoint,
    isWeakReachable_rematch hC (hA huA) h1 h2 hLC, ⟨u, huA, ?_⟩, fun t ht s hs _ htC => ?_⟩
  · rw [Finset.union_sdiff_distrib, Finset.sdiff_eq_empty_iff_subset.2 hLC, Finset.union_empty,
      Finset.sdiff_idem]
  · have htL : t ∈ L r :=
      (Finset.mem_union.1 ht).resolve_left fun h => (Finset.mem_sdiff.1 h).2 htC
    have h4 : ¬ z r ≤ z s := fun h => hs (Finset.mem_union.2 (Or.inr (by simpa [L] using h)))
    linarith [(Finset.mem_filter.1 htL).2]

/-- **One cluster made monotone.** Let `C` be the cluster of `b`. If `y` is in the cone of a family
`A` of weakly reachable spectra, then it is in the cone of the spectra obtained from `A` by
rematching inside `C` with `y`. Write `y = ∑ m_S 1_S`; the spectra not splitting `C` already
qualify, and the mass `z = ∑ m_u 1_{u ∩ C}` of the splitting ones is handled by
`add_mem_indicatorCone_cluster`; since `y - z` is constant on `C`, an upper set of `z` on `C` is an
upper set of `y` on `C`. -/
theorem mem_indicatorCone_rematch {A : Set (Finset (Fin T))} (hA : A ⊆ weakReachableSpectra P)
    (hy : y ∈ indicatorCone A) (b : Fin T) :
    y ∈ indicatorCone (rematches P A (cluster P b) y) := by
  classical
  obtain ⟨m, hm0, hmA, -, hy'⟩ := exists_coef_of_mem_indicatorCone hy
  set C := cluster P b with hCdef
  set ind : Finset (Fin T) → Fin T → ℝ := fun S => (S : Set (Fin T)).indicator 1 with hind
  set U := Finset.univ.filter (fun u => m u ≠ 0 ∧ (u ∩ C).Nonempty ∧ (C \ u).Nonempty)
  set z : Fin T → ℝ := ∑ u ∈ U, m u • ind (u ∩ C) with hz
  -- spectra outside `U` contain `C` or miss it
  have hns : ∀ S ∉ U, m S ≠ 0 → ∀ s ∈ C, ∀ t ∈ C, t ∈ S → s ∈ S :=
    fun S hS hm s hs t ht htS => by_contra fun h => hS (Finset.mem_filter.2
      ⟨Finset.mem_univ _, hm, ⟨t, Finset.mem_inter.2 ⟨htS, ht⟩⟩, s, Finset.mem_sdiff.2 ⟨hs, h⟩⟩)
  have hdec : y = ∑ S ∈ Uᶜ, m S • ind S + (∑ u ∈ U, m u • ind (u \ C) + z) := by
    rw [hy', ← Finset.sum_compl_add_sum U, hz, ← Finset.sum_add_distrib]
    refine congrArg _ (Finset.sum_congr rfl fun u _ => ?_)
    rw [← smul_add]; congr 1; ext x
    by_cases hx : x ∈ u <;> by_cases hq : x ∈ C <;> simp [hind, Set.indicator, hx, hq]
  have hconst : ∀ s ∈ C, ∀ t ∈ C, y s - z s = y t - z t := by
    have key : ∀ x ∈ C, y x - z x = ∑ S ∈ Uᶜ, m S * ind S x := fun x hx => by
      rw [hdec]; simp [Finset.sum_apply, hind, hx]
    intro s hs t ht
    rw [key s hs, key t ht]
    refine Finset.sum_congr rfl fun S hS => ?_
    by_cases hm : m S = 0
    · simp [hm]
    have h := hns S (Finset.mem_compl.1 hS) hm
    simp [hind, Set.indicator, show s ∈ S ↔ t ∈ S from ⟨h t ht s hs, h s hs t ht⟩]
  have hsub : rematches P A C z ⊆ rematches P A C y := fun S ⟨h1, h2, h3⟩ =>
    ⟨h1, h2, fun t ht s hs hsC htC => by linarith [h3 t ht s hs hsC htC, hconst s hsC t htC]⟩
  have key : ∑ S ∈ Uᶜ, m S • ind S + (∑ u ∈ U, m u • ind (u \ C) + z) ∈
      indicatorCone (rematches P A C y) := by
    refine Submodule.add_mem _ (Submodule.sum_mem _ fun S hS =>
      smul_indicator_mem_indicatorCone (hm0 S) fun hm => ?_) ?_
    · exact ⟨hA (hmA S hm), ⟨S, hmA S hm, rfl⟩,
        fun t ht s hs hsC htC => absurd (hns S (Finset.mem_compl.1 hS) hm s hsC t htC ht) hs⟩
    exact Submodule.span_mono (Set.image_mono hsub) (add_mem_indicatorCone_cluster hA b hm0
      fun u hu => ⟨hmA u (Finset.mem_filter.1 hu).2.1, (Finset.mem_filter.1 hu).2.2⟩)
  rwa [← hdec] at key

/-- **Monotone representation.** If `y` is in the cone of the weakly reachable spectra, it is in
the cone of those weakly reachable `S` that meet every cluster of equal prices in an upper set of
`y`. Induction over a finite set `B` of indices, the cluster of `b` added at each step
(`mem_indicatorCone_rematch`); indices with `P t ≠ P b` keep the property because
`S \ C = S₀ \ C`. -/
theorem mem_indicatorCone_monotone (h : y ∈ indicatorCone (weakReachableSpectra P)) :
    y ∈ indicatorCone {S | IsWeakReachable P S ∧ ∀ t ∈ S, ∀ s ∉ S, P s = P t → y s < y t} := by
  have key : ∀ B : Finset (Fin T), y ∈ indicatorCone {S | IsWeakReachable P S ∧
      ∀ t ∈ S, ∀ s ∉ S, P s = P t → t ∈ B → y s < y t} := by
    intro B
    induction B using Finset.induction_on with
    | empty =>
      refine Submodule.span_mono (Set.image_mono ?_) h
      exact fun S hS => ⟨hS, by simp⟩
    | insert b B hb ih =>
      refine Submodule.span_mono (Set.image_mono ?_)
        (mem_indicatorCone_rematch (fun S hS => hS.1) ih b)
      rintro S ⟨hS, ⟨S₀, ⟨-, h₀⟩, hag⟩, hmono⟩
      have hmem : ∀ x, x ∈ cluster P b ↔ P x = P b := fun x => by simp [cluster]
      refine ⟨hS, fun t ht s hs hP htB => ?_⟩
      by_cases hc : P t = P b
      · exact hmono t ht s hs ((hmem s).2 (hP.trans hc)) ((hmem t).2 hc)
      · have htB' : t ∈ B := (Finset.mem_insert.mp htB).resolve_left fun e => hc (e ▸ rfl)
        have hag' : ∀ x, P x ≠ P b → (x ∈ S ↔ x ∈ S₀) := fun x hx => by
          simpa [Finset.mem_sdiff, hmem, hx] using Finset.ext_iff.1 hag x
        exact h₀ t ((hag' t hc).mp ht) s (fun hs' => hs ((hag' s (hP ▸ hc)).mpr hs')) hP htB'
  refine Submodule.span_mono (Set.image_mono ?_) (key Finset.univ)
  exact fun S hS => ⟨hS.1, fun t ht s hs hP => hS.2 t ht s hs hP (Finset.mem_univ _)⟩

/-! ### The tilt -/

/-- The tilted prices `q_t = p_t - (δ ∑ⱼ log (p_t)ⱼ + δ² y_t) 1`. -/
noncomputable def tilt (P : Fin T → Fin d → ℝ) (y : Fin T → ℝ) (δ : ℝ) : Fin T → Fin d → ℝ :=
  fun t i => P t i - δ * (∑ j, Real.log (P t j) + δ * y t)

/-- **Strict concavity of `∑ log`.** For distinct `a, b > 0`,
`⟨1/a, b - a⟩ - (∑ log b - ∑ log a) > 0`. The left side is `∑ᵢ (xᵢ - 1 - log xᵢ)` with
`xᵢ = bᵢ / aᵢ`, and `x - 1 - log x ≥ 0` with equality only at `x = 1`. -/
theorem sum_log_bregman_pos {a b : Fin d → ℝ} (ha : a ∈ orthant d) (hb : b ∈ orthant d)
    (hab : a ≠ b) :
    0 < (fun i => (a i)⁻¹) ⬝ᵥ (b - a) - (∑ i, Real.log (b i) - ∑ i, Real.log (a i)) := by
  obtain ⟨j, hj⟩ := Function.ne_iff.mp hab
  have e : (fun i => (a i)⁻¹) ⬝ᵥ (b - a) - (∑ i, Real.log (b i) - ∑ i, Real.log (a i))
      = ∑ i, ((b i / a i - 1) - Real.log (b i / a i)) := by
    simp only [dotProduct, Pi.sub_apply, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Real.log_div (hb i).ne' (ha i).ne']; field_simp [(ha i).ne']
  rw [e]
  refine Finset.sum_pos' (fun i _ => ?_) ⟨j, Finset.mem_univ _, ?_⟩
  · linarith [Real.log_le_sub_one_of_pos (div_pos (hb i) (ha i))]
  · have : b j / a j ≠ 1 := fun h => hj ((div_eq_one_iff_eq (ha j).ne').1 h).symm
    linarith [Real.log_lt_sub_one_of_pos (div_pos (hb j) (ha j)) this]

/-- **Positivity of the tilted witness.** Let `∑ ζ = 1`, `⟨ζ, p_s - p_t⟩ ≥ 0`, and
`p_s ≠ p_t` or `y_s < y_t`. With `g = (1/(p_t)ᵢ)ᵢ`, `G = ∑ g`, `F_r = ∑ⱼ log (p_r)ⱼ`, one has
`⟨ζ + δ g, q_s - q_t⟩ = A + δ K + δ² R(δ)` for `q = tilt P y δ`, where `A = ⟨ζ, p_s - p_t⟩`,
`K = ⟨g, p_s - p_t⟩ - (F_s - F_t)` and `R(δ) = (y_t - y_s)(1 + δ G) - (F_s - F_t) G`.
If `p_s ≠ p_t` then `K > 0` (`sum_log_bregman_pos`); if `p_s = p_t` then `A = K = 0 < R(δ)`. -/
theorem eventually_tilt_witness_pos (hP : ∀ t, P t ∈ orthant d) {s t : Fin T}
    (hst : P s ≠ P t ∨ y s < y t) {ζ : Fin d → ℝ} (hζ : ∑ i, ζ i = 1)
    (hA : 0 ≤ ζ ⬝ᵥ (P s - P t)) :
    ∀ᶠ δ in 𝓝[>] 0, 0 < (ζ + δ • fun i => (P t i)⁻¹) ⬝ᵥ (tilt P y δ s - tilt P y δ t) := by
  set F : Fin T → ℝ := fun r => ∑ j, Real.log (P r j) with hF
  set G := ∑ i, (P t i)⁻¹ with hG
  set K := (fun i => (P t i)⁻¹) ⬝ᵥ (P s - P t) - (F s - F t) with hK
  have key : ∀ δ : ℝ, (ζ + δ • fun i => (P t i)⁻¹) ⬝ᵥ (tilt P y δ s - tilt P y δ t)
      = ζ ⬝ᵥ (P s - P t) + δ * K
        + δ ^ 2 * ((y t - y s) * (1 + δ * G) - (F s - F t) * G) := by
    intro δ
    have e : tilt P y δ s - tilt P y δ t
        = (P s - P t) - (δ * (F s - F t) + δ ^ 2 * (y s - y t)) • (1 : Fin d → ℝ) := by
      ext i; simp [tilt, hF]; ring
    have h1 : ζ ⬝ᵥ (1 : Fin d → ℝ) = 1 := by simp [dotProduct, hζ]
    have h2 : (fun i => (P t i)⁻¹) ⬝ᵥ (1 : Fin d → ℝ) = G := by simp [dotProduct, hG]
    rw [e, hK]
    simp only [add_dotProduct, dotProduct_sub, smul_dotProduct, dotProduct_smul, h1, h2,
      smul_eq_mul]
    ring
  have hδ : ∀ᶠ δ in 𝓝[>] (0:ℝ), 0 < δ := self_mem_nhdsWithin
  simp only [key]
  by_cases hne : P s = P t
  · have hy : y s < y t := hst.resolve_left (not_not.2 hne)
    have hG0 : 0 ≤ G := Finset.sum_nonneg fun i _ => (inv_pos.2 (hP t i)).le
    filter_upwards [hδ] with δ hδ
    simp only [hK, hF, hne, sub_self, dotProduct_zero, zero_mul, mul_zero, sub_zero]
    nlinarith [mul_pos (pow_pos hδ 2) (mul_pos (sub_pos.2 hy) (by positivity : 0 < 1 + δ * G))]
  · have hK0 : 0 < K := sum_log_bregman_pos (hP t) (hP s) (Ne.symm hne)
    have h : ∀ᶠ δ in 𝓝[>] (0:ℝ), 0 < K + δ * ((y t - y s) * (1 + δ * G) - (F s - F t) * G) :=
      nhdsWithin_le_nhds ((by fun_prop : Continuous fun δ : ℝ =>
        K + δ * ((y t - y s) * (1 + δ * G) - (F s - F t) * G)).continuousAt.eventually
          (lt_mem_nhds (by simpa using hK0)))
    filter_upwards [hδ, h] with δ hδ h
    nlinarith [mul_pos hδ h]

/-- For small `δ > 0`, every weakly reachable `S` meeting every cluster in an upper set of `y` is
reachable at `tilt P y δ`. There are finitely many `S`; for `t ∈ S` the witness `ζ + δ g` of
`eventually_tilt_witness_pos` works for the finitely many `s ∉ S` (`not_covers_of_pos`). -/
theorem isReachable_tilt (hP : ∀ t, P t ∈ orthant d) :
    ∀ᶠ δ in 𝓝[>] 0, {S | IsWeakReachable P S ∧ ∀ t ∈ S, ∀ s ∉ S, P s = P t → y s < y t} ⊆
      reachableSpectra (tilt P y δ) := by
  have key : ∀ S : Finset (Fin T), ∀ᶠ δ in 𝓝[>] (0:ℝ), IsWeakReachable P S ∧
      (∀ t ∈ S, ∀ s ∉ S, P s = P t → y s < y t) → IsReachable (tilt P y δ) S := by
    intro S
    by_cases hS' : IsWeakReachable P S ∧ ∀ t ∈ S, ∀ s ∉ S, P s = P t → y s < y t
    swap
    · exact .of_forall fun _ h => absurd h hS'
    obtain ⟨hS, hmono⟩ := hS'
    refine ((eventually_all_finset S).2 fun t ht => ?_).mono fun _ h _ => h
    obtain ⟨ζ, hζ0, hζ1, hζ⟩ := hS t ht
    have hs : ∀ᶠ δ in 𝓝[>] (0:ℝ), ∀ s ∈ Sᶜ,
        0 < (ζ + δ • fun i => (P t i)⁻¹) ⬝ᵥ (tilt P y δ s - tilt P y δ t) :=
      (eventually_all_finset Sᶜ).2 fun s hs => by
        have hs : s ∉ S := by simpa using hs
        exact eventually_tilt_witness_pos hP ((ne_or_eq _ _).imp_right (hmono t ht s hs)) hζ1
          (hζ s hs)
    filter_upwards [hs, self_mem_nhdsWithin] with δ h hδ
    refine not_covers_of_pos (fun i => ?_) fun s hs => h s (by simpa using hs)
    have := hζ0 i; have := hP t i; have : 0 < δ := hδ
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply]; positivity
  filter_upwards [eventually_all.2 key] with δ h S hS using h S hS

/-- `tilt P y δ → P` as `δ → 0`, and the tilted prices are eventually positive. -/
theorem tendsto_tilt (hP : ∀ t, P t ∈ orthant d) :
    Tendsto (tilt P y) (𝓝[>] 0) (𝓝 P) ∧ ∀ᶠ δ in 𝓝[>] 0, ∀ t, tilt P y δ t ∈ orthant d := by
  have hc : Continuous (tilt P y) := by
    unfold tilt
    exact continuous_pi fun t => continuous_pi fun i => by fun_prop
  have ht : Tendsto (tilt P y) (𝓝[>] 0) (𝓝 P) := by
    have h0 : tilt P y 0 = P := by funext t i; simp [tilt]
    simpa [h0] using (hc.tendsto 0).mono_left nhdsWithin_le_nhds
  exact ⟨ht, ht.eventually (eventually_all.2 fun t => ((continuous_apply t).tendsto P).eventually
    (isOpen_orthant.mem_nhds (hP t)))⟩

/-! ### Closure theorem -/

/-- **Closure theorem.** If `y` lies in the cone of the weakly reachable spectra of `P`, then `P`
is a limit of prices at which `y` is solvable. By `mem_indicatorCone_monotone`, `y` is in the cone
of the weakly reachable spectra that meet every cluster in an upper set of `y`; all of them
(finitely many) are reachable at `tilt P y δ` for small `δ > 0` (`isReachable_tilt`), so `y` is
solvable there (`neoSolvable_iff_mem_indicatorCone`), and `tilt P y δ → P`. -/
theorem mem_closure_of_weakReachable (hd : 2 ≤ d) (hP : ∀ t, P t ∈ orthant d)
    (hy : ∀ t, 0 ≤ y t) (h : y ∈ indicatorCone (weakReachableSpectra P)) :
    P ∈ closure {Q : Fin T → Fin d → ℝ | NeoSolvable Q y} := by
  obtain ⟨hlim, horth⟩ := tendsto_tilt (y := y) hP
  refine mem_closure_of_tendsto hlim ?_
  filter_upwards [isReachable_tilt (y := y) hP, horth] with δ hsub hQ
  exact (neoSolvable_iff_mem_indicatorCone hd hQ hy).2
    (Submodule.span_mono (image_mono hsub) (mem_indicatorCone_monotone h))

/-! ### Converse -/

/-- **Reachable spectra near `P` are weakly reachable at `P`.** If `S` is not weakly reachable,
some `t ∈ S` strictly covers `Sᶜ` with weights `w` (`isWeakReachable_iff`); the strict
inequalities `(∑ w q)ᵢ < (q_t)ᵢ` persist for `Q` near `P`, so `t` covers `Sᶜ` at `Q`. -/
theorem eventually_reachableSpectra_subset_weak (hd : 1 ≤ d) :
    ∀ᶠ Q in 𝓝 P, reachableSpectra Q ⊆ weakReachableSpectra P := by
  refine eventually_all.2 fun S => ?_
  by_cases hS : IsWeakReachable P S
  · exact .of_forall fun _ _ => hS
  obtain ⟨t, ht, w, hw0, hwS, hw1, hlt⟩ := by
    simpa using (isWeakReachable_iff hd).not.1 hS
  have hc (i) : Continuous fun Q : Fin T → Fin d → ℝ => (∑ r, w r • Q r) i := by
    simp only [Finset.sum_apply, Pi.smul_apply]; fun_prop
  filter_upwards [eventually_all.2 fun i => (hc i).tendsto P |>.eventually_lt
    ((by fun_prop : Continuous fun Q : Fin T → Fin d → ℝ => Q t i).tendsto P) (hlt i)]
    with Q hQ hR
  exact (hR t ht ⟨w, hw0, hwS, hw1, fun i => (hQ i).le⟩).elim

/-- **Converse.** If `P` is a limit of prices at which `y` is solvable, then `y` lies in the cone
of the weakly reachable spectra of `P`: near `P` the prices are positive, `y` lies in the cone of
`Sp(Q)` (`neoSolvable_iff_mem_indicatorCone`), and `Sp(Q) ⊆ W(P)`
(`eventually_reachableSpectra_subset_weak`). -/
theorem weakReachable_of_mem_closure (hd : 2 ≤ d) (hP : ∀ t, P t ∈ orthant d)
    (hy : ∀ t, 0 ≤ y t) (h : P ∈ closure {Q : Fin T → Fin d → ℝ | NeoSolvable Q y}) :
    y ∈ indicatorCone (weakReachableSpectra P) := by
  have h2 : ∀ᶠ Q in 𝓝 P, ∀ t, Q t ∈ orthant d :=
    eventually_all.2 fun t => ((continuous_apply t).tendsto P).eventually
      (isOpen_orthant.mem_nhds (hP t))
  obtain ⟨Q, ⟨hQ, hsub⟩, hQy⟩ := mem_closure_iff_nhds.1 h _
    (h2.and (eventually_reachableSpectra_subset_weak (by omega)))
  exact Submodule.span_mono (Set.image_mono hsub)
    ((neoSolvable_iff_mem_indicatorCone hd hQ hy).1 hQy)

end NeoTiling
