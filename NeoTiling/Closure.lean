import NeoTiling.Solvability

/-!
# Weakly reachable spectra and the closure of the solvable prices

A set `S` is *weakly reachable* (`IsWeakReachable`) if every `t ∈ S` has a nonzero `ξ ≥ 0` with
`⟨ξ, p_s - p_t⟩ ≥ 0` for all `s ∉ S`. This is the definition of `IsReachable` with `≤` in place
of `<`.

Main result: `y ≥ 0` lies in the cone of the weakly reachable spectra of `P` iff `P` is a limit of
prices at which `y` is solvable (`mem_closure_of_weakReachable`, `weakReachable_of_mem_closure`).
The converse direction is compactness of the simplex of normalized witnesses
(`eventually_reachableSpectra_subset_weak`).

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

/-- `S` is weakly reachable: every `t ∈ S` has a nonzero `ξ ≥ 0` with `⟨ξ, p_s - p_t⟩ ≥ 0` for
all `s ∉ S`. -/
def IsWeakReachable (P : Fin T → Fin d → ℝ) (S : Finset (Fin T)) : Prop :=
  ∀ t ∈ S, ∃ ξ : Fin d → ℝ, 0 ≤ ξ ∧ ξ ≠ 0 ∧ ∀ s ∉ S, 0 ≤ ξ ⬝ᵥ (P s - P t)

/-- The weakly reachable spectra. -/
def weakReachableSpectra (P : Fin T → Fin d → ℝ) : Set (Finset (Fin T)) :=
  {S | IsWeakReachable P S}

/-- Reachable spectra are weakly reachable: the same witnesses work. -/
theorem IsReachable.isWeakReachable {S : Finset (Fin T)} (hS : IsReachable P S) :
    IsWeakReachable P S := fun t ht =>
  let ⟨ξ, h0, hne, h⟩ := hS t ht
  ⟨ξ, h0, hne, fun s hs => (h s hs).le⟩

/-- A nonzero `ξ ≥ 0` has a positive multiple in the standard simplex: divide by `∑ ξ > 0`. -/
theorem exists_smul_mem_stdSimplex {ξ : Fin d → ℝ} (h0 : 0 ≤ ξ) (hne : ξ ≠ 0) :
    ∃ c : ℝ, 0 < c ∧ c • ξ ∈ stdSimplex ℝ (Fin d) := by
  obtain ⟨i, hi⟩ := Function.ne_iff.1 hne
  have hpos : 0 < ∑ i, ξ i :=
    Finset.sum_pos' (fun j _ => h0 j) ⟨i, Finset.mem_univ _, (h0 i).lt_of_ne' hi⟩
  refine ⟨(∑ i, ξ i)⁻¹, inv_pos.2 hpos, fun j => smul_nonneg (inv_pos.2 hpos).le (h0 j), ?_⟩
  simp [← Finset.mul_sum, hpos.ne']

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
reachable at `tilt P y δ`. There are finitely many `S`; for `t ∈ S` normalize the weak witness to
`ζ`, `∑ ζ = 1`; then `ζ + δ g` is a witness at `tilt P y δ` for the finitely many `s ∉ S`
(`eventually_tilt_witness_pos`). -/
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
    obtain ⟨ξ, hξ0, hξne, hξ⟩ := hS t ht
    obtain ⟨c, hc, -, hζ1⟩ := exists_smul_mem_stdSimplex hξ0 hξne
    obtain ⟨i₀, -⟩ := Function.ne_iff.1 hξne
    have hs : ∀ᶠ δ in 𝓝[>] (0:ℝ), ∀ s ∈ Sᶜ,
        0 < (c • ξ + δ • fun i => (P t i)⁻¹) ⬝ᵥ (tilt P y δ s - tilt P y δ t) :=
      (eventually_all_finset Sᶜ).2 fun s hs => by
        have hs : s ∉ S := by simpa using hs
        exact eventually_tilt_witness_pos hP ((ne_or_eq _ _).imp_right (hmono t ht s hs)) hζ1
          (by rw [smul_dotProduct, smul_eq_mul]; exact mul_nonneg hc.le (hξ s hs))
    filter_upwards [hs, self_mem_nhdsWithin] with δ h hδ
    have hpos (i) : 0 < (c • ξ + δ • fun i => (P t i)⁻¹) i := by
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      exact add_pos_of_nonneg_of_pos (mul_nonneg hc.le (hξ0 i))
        (mul_pos (show (0:ℝ) < δ from hδ) (inv_pos.2 (hP t i)))
    exact ⟨_, fun i => (hpos i).le, fun h0 => (hpos i₀).ne' (by rw [h0]; rfl),
      fun s hs => h s (by simpa using hs)⟩
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
some `t ∈ S` has, for every `ζ` in the simplex, an `s ∉ S` with `⟨ζ, p_s - p_t⟩ < 0`. This strict
inequality is open in `(Q, ζ)`, and the simplex is compact, so it persists for all `ζ` at all `Q`
near `P`. A normalized witness of reachability at `Q` would contradict it. -/
theorem eventually_reachableSpectra_subset_weak :
    ∀ᶠ Q in 𝓝 P, reachableSpectra Q ⊆ weakReachableSpectra P := by
  refine eventually_all.2 fun S => ?_
  by_cases hS : IsWeakReachable P S
  · exact .of_forall fun _ _ => hS
  obtain ⟨t, ht, hno⟩ : ∃ t ∈ S, ∀ ζ ∈ stdSimplex ℝ (Fin d), ∃ s ∉ S, ζ ⬝ᵥ (P s - P t) < 0 := by
    by_contra h
    push_neg at h
    refine hS fun t ht => ?_
    obtain ⟨ζ, hζ, hζs⟩ := h t ht
    exact ⟨ζ, fun i => hζ.1 i, fun h0 => by simpa [h0] using hζ.2, hζs⟩
  have hev : ∀ᶠ Q in 𝓝 P, ∀ ζ ∈ stdSimplex ℝ (Fin d), ∃ s ∉ S, ζ ⬝ᵥ (Q s - Q t) < 0 :=
    (isCompact_stdSimplex _).eventually_forall_of_forall_eventually fun ζ hζ => by
      obtain ⟨s, hs, hlt⟩ := hno ζ hζ
      exact ((by fun_prop : Continuous fun z : (Fin T → Fin d → ℝ) × (Fin d → ℝ) =>
        z.2 ⬝ᵥ (z.1 s - z.1 t)).continuousAt.eventually (gt_mem_nhds hlt)).mono
          fun z hz => ⟨s, hs, hz⟩
  filter_upwards [hev] with Q hQ hR
  obtain ⟨ξ, hξ0, hξne, hξ⟩ := hR t ht
  obtain ⟨c, hc, hcξ⟩ := exists_smul_mem_stdSimplex hξ0 hξne
  obtain ⟨s, hs, hlt⟩ := hQ _ hcξ
  rw [smul_dotProduct, smul_eq_mul] at hlt
  linarith [mul_pos hc (hξ s hs)]

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
    (h2.and eventually_reachableSpectra_subset_weak)
  exact Submodule.span_mono (Set.image_mono hsub)
    ((neoSolvable_iff_mem_indicatorCone hd hQ hy).1 hQy)

end NeoTiling
