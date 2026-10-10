import NeoTiling.Solvability

/-!
# Weak solvability

`y` is *weakly solvable* at prices `P` (`WeakSolvable`) if every open neighbourhood of `P`
contains positive prices at which `y` is solvable, that is, `P` lies in the closure of the
positive prices at which `y` is solvable. A set `S` is *weakly reachable* (`IsWeakReachable`) if
every `t ∈ S` has a nonzero `ξ ≥ 0` with `⟨ξ, p_s - p_t⟩ ≥ 0` for all `s ∉ S`: the definition of
`IsReachable` with `≥` in place of `>`.

Main result, `weakSolvable_iff`: for `d ≥ 2`, `P ≥ 0` and `y ≥ 0`, `y` is weakly solvable at `P`
iff it lies in the cone of the weakly reachable spectra of `P`.

* Necessity: near `P` every reachable spectrum is weakly reachable at `P`
  (`eventually_reachableSpectra_subset_weak`, compactness of the simplex of witnesses).
* Sufficiency: choose a representation `y = ∑ m_S 1_S` that maximizes `∑ m_S #{(a, b) ∈ S² |
  p_a = p_b}`. Two of its spectra never split a set of equal prices crosswise, since replacing
  their parts there by the union and the intersection would increase the sum (`uncross`). Hence
  `t ∈ S`, `s ∉ S`, `p_s = p_t` force `y_s < y_t` (`mem_indicatorCone_monotone`). The tilt
  `q_t = p_t + (δ ∑ᵢ exp (-p_tⁱ) - δ² y_t) 1` makes all such spectra reachable for small `δ > 0`
  (`isReachable_tilt`): strict convexity of `exp` separates distinct prices at order `δ`, the
  term `δ² y_t` separates equal prices at order `δ²`.
-/

open Set Filter Topology

namespace NeoTiling

variable {d T : ℕ} {P : Fin T → Fin d → ℝ} {y : Fin T → ℝ}

/-! ### Definitions -/

/-- `y` is weakly solvable at `P`: every neighbourhood of `P` contains positive prices at which
`y` is solvable (`mem_closure_iff_nhds`). -/
def WeakSolvable (P : Fin T → Fin d → ℝ) (y : Fin T → ℝ) : Prop :=
  P ∈ closure {Q | (∀ t, Q t ∈ orthant d) ∧ NeoSolvable Q y}

/-- At positive prices a solvable `y` is weakly solvable: a set lies in its closure. -/
theorem NeoSolvable.weakSolvable (hP : ∀ t, P t ∈ orthant d) (h : NeoSolvable P y) :
    WeakSolvable P y :=
  subset_closure ⟨hP, h⟩

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

/-- `a 1_S` lies in the cone of `A` if `a ≥ 0` and `S ∈ A` unless `a = 0`. It is `0` or a
generator times `a`. -/
theorem smul_indicator_mem_indicatorCone {T : ℕ} {A : Set (Finset (Fin T))} {a : ℝ}
    {S : Finset (Fin T)} (ha : 0 ≤ a) (hS : a ≠ 0 → S ∈ A) :
    a • ((S : Set (Fin T)).indicator (1 : Fin T → ℝ)) ∈ indicatorCone A := by
  by_cases h0 : a = 0
  · rw [h0, zero_smul]; exact Submodule.zero_mem _
  · exact PointedCone.smul_mem _ ha (PointedCone.subset_span ⟨S, hS h0, rfl⟩)

/-! ### Necessity -/

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

/-- **Necessity.** If `y` is weakly solvable at `P`, it lies in the cone of the weakly reachable
spectra of `P`: some positive `Q` near `P` solves `y`, so `y` is in the cone of `Sp(Q)`
(`neoSolvable_iff_mem_indicatorCone`), and `Sp(Q) ⊆ Ŝp(P)`
(`eventually_reachableSpectra_subset_weak`). -/
theorem WeakSolvable.mem_indicatorCone (hd : 2 ≤ d) (hy : ∀ t, 0 ≤ y t)
    (h : WeakSolvable P y) : y ∈ indicatorCone (weakReachableSpectra P) := by
  obtain ⟨Q, hsub, hQ, hQy⟩ := mem_closure_iff_nhds.1 h _ eventually_reachableSpectra_subset_weak
  exact Submodule.span_mono (image_mono hsub) ((neoSolvable_iff_mem_indicatorCone hd hQ hy).1 hQy)

/-! ### Extremal representation -/

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

/-- The number of ordered pairs `(a, b) ∈ S × S` with equal prices `p_a = p_b`. -/
noncomputable def eqPairs (P : Fin T → Fin d → ℝ) (S : Finset (Fin T)) : ℕ :=
  ((S ×ˢ S).filter fun x => P x.1 = P x.2).card

/-- **Uncrossing.** Let `u, u'` be weakly reachable and split the set `C` of indices with price
`p_t` crosswise: `t ∈ u \ u'`, `s ∈ u' \ u`, `p_s = p_t`. Replacing their parts in `C` by the union
and the intersection gives `A = (u \ C) ∪ ((u ∪ u') ∩ C)` and `B = (u' \ C) ∪ (u ∩ u' ∩ C)`. They
are weakly reachable (`isWeakReachable_rematch`), `1_A + 1_B = 1_u + 1_u'`, and they contain more
pairs of equal prices: no pair is lost (pairs off `C` are unchanged; inside `C` a pair in `u` or in
`u'` is in `A`, and a pair in both is in `B` too), and the pair `(t, s)` is new in `A`. -/
theorem uncross {u u' : Finset (Fin T)} (hu : IsWeakReachable P u) (hu' : IsWeakReachable P u')
    {s t : Fin T} (ht : t ∈ u) (ht' : t ∉ u') (hs : s ∈ u') (hs' : s ∉ u) (hst : P s = P t) :
    ∃ A B : Finset (Fin T), IsWeakReachable P A ∧ IsWeakReachable P B ∧
      (A : Set (Fin T)).indicator (1 : Fin T → ℝ) + (B : Set (Fin T)).indicator 1 =
        (u : Set (Fin T)).indicator 1 + (u' : Set (Fin T)).indicator 1 ∧
      eqPairs P u + eqPairs P u' < eqPairs P A + eqPairs P B := by
  classical
  set C : Finset (Fin T) := Finset.univ.filter (P · = P t) with hCdef
  have hCm : ∀ a, a ∈ C ↔ P a = P t := by simp [hCdef]
  have hC : ∀ a ∈ C, ∀ b ∈ C, P a = P b := fun a ha b hb => by
    rw [hCm] at ha hb; rw [ha, hb]
  have htC : t ∈ C := (hCm t).2 rfl
  have hsC : s ∈ C := (hCm s).2 hst
  refine ⟨u \ C ∪ (u ∪ u') ∩ C, u' \ C ∪ (u ∩ u' ∩ C), ?_, ?_, ?_, ?_⟩
  · exact isWeakReachable_rematch hC hu ⟨t, Finset.mem_inter.2 ⟨ht, htC⟩⟩
      ⟨s, Finset.mem_sdiff.2 ⟨hsC, hs'⟩⟩ Finset.inter_subset_right
  · exact isWeakReachable_rematch hC hu' ⟨s, Finset.mem_inter.2 ⟨hs, hsC⟩⟩
      ⟨t, Finset.mem_sdiff.2 ⟨htC, ht'⟩⟩ Finset.inter_subset_right
  · funext r
    by_cases h1 : r ∈ C <;> by_cases h2 : r ∈ u <;> by_cases h3 : r ∈ u' <;>
      simp [Set.indicator, h1, h2, h3]
  -- count pairs as a sum over all `(a, b)` and compare termwise
  have key : ∀ S : Finset (Fin T), eqPairs P S =
      ∑ x : Fin T × Fin T, if x.1 ∈ S ∧ x.2 ∈ S ∧ P x.1 = P x.2 then 1 else 0 := fun S => by
    rw [eqPairs, Finset.card_filter, ← Finset.sum_filter, ← Finset.sum_filter]
    congr 1; ext x; simp [and_assoc]
  simp only [key, ← Finset.sum_add_distrib]
  clear key
  refine Finset.sum_lt_sum (fun ⟨a, b⟩ _ => ?_) ⟨(t, s), Finset.mem_univ _, ?_⟩
  · by_cases hab : P a = P b
    · have hiff : a ∈ C ↔ b ∈ C := by rw [hCm, hCm, hab]
      clear hCm hCdef
      by_cases h2 : b ∈ C <;> by_cases h3 : a ∈ u <;> by_cases h4 : b ∈ u <;>
        by_cases h5 : a ∈ u' <;> by_cases h6 : b ∈ u' <;> simp [hab, hiff, h2, h3, h4, h5, h6]
    · simp [hab]
  · clear hCm hCdef
    simp [hst.symm, ht, ht', hs, hs', htC, hsC]

/-- Moving the weight `ε` from `u, u'` to `A, B` changes `∑ m_S f_S` by
`ε (f_A + f_B - f_u - f_u')`. -/
private lemma sum_smul_exchange {M : Type*} [AddCommGroup M] [Module ℝ M]
    (m : Finset (Fin T) → ℝ) (ε : ℝ) (A B u u' : Finset (Fin T)) (f : Finset (Fin T) → M) :
    ∑ S, (m S + ε * ((if S = A then 1 else 0) + (if S = B then 1 else 0) -
      (if S = u then 1 else 0) - (if S = u' then 1 else 0))) • f S =
      ∑ S, m S • f S + ε • (f A + f B - f u - f u') := by
  simp [add_smul, sub_smul, mul_smul, ite_smul, Finset.sum_add_distrib, Finset.sum_sub_distrib,
    ← Finset.smul_sum]

/-- **Extremal representation.** If `y` lies in the cone of the weakly reachable spectra, it has a
representation `y = ∑ m_S 1_S` in which no two spectra split a set of equal prices crosswise.
Among the representations with total weight `∑ m_S ≤ N` (a nonempty compact set) take one that
maximizes `∑ m_S eqPairs S`. If `u, u'` with `m_u, m_u' > 0` crossed, moving the weight
`ε = min (m_u, m_u')` from `u, u'` to the sets `A, B` of `uncross` would keep the representation
and the total weight and increase the objective by `ε (eqPairs A + eqPairs B - eqPairs u -
eqPairs u') > 0`. -/
theorem exists_uncrossed_rep (h : y ∈ indicatorCone (weakReachableSpectra P)) :
    ∃ m : Finset (Fin T) → ℝ, (∀ S, 0 ≤ m S) ∧ (∀ S, m S ≠ 0 → IsWeakReachable P S) ∧
      y = ∑ S, m S • (S : Set (Fin T)).indicator 1 ∧
      ∀ u u', 0 < m u → 0 < m u' → ∀ t ∈ u, t ∉ u' → ∀ s ∈ u', s ∉ u → P s ≠ P t := by
  classical
  obtain ⟨m₀, h0, hA, -, hy⟩ := exists_coef_of_mem_indicatorCone h
  set N := ∑ S, m₀ S
  let K : Set (Finset (Fin T) → ℝ) := {m | (∀ S, 0 ≤ m S) ∧
    (∀ S, ¬ IsWeakReachable P S → m S = 0) ∧
    ∑ S, m S • (S : Set (Fin T)).indicator (1 : Fin T → ℝ) = y ∧ ∑ S, m S ≤ N}
  have hK : IsCompact K := by
    refine (isCompact_univ_pi fun _ => isCompact_Icc (a := 0) (b := N)).of_isClosed_subset ?_ ?_
    · simp only [K, Set.setOf_and, Set.setOf_forall]
      refine (isClosed_iInter fun S => isClosed_le continuous_const (continuous_apply S)).inter
        ((isClosed_iInter fun S => ?_).inter ((isClosed_eq (by fun_prop) continuous_const).inter
          (isClosed_le (by fun_prop) continuous_const)))
      by_cases hW : IsWeakReachable P S <;> simp [hW]
      exact isClosed_eq (continuous_apply S) continuous_const
    · rintro m ⟨hm0, -, -, hmN⟩ S -
      exact ⟨hm0 S, (Finset.single_le_sum (fun S _ => hm0 S) (Finset.mem_univ S)).trans hmN⟩
  have hne : m₀ ∈ K := ⟨h0, fun S hS => by_contra fun hne => hS (hA S hne), hy.symm, le_rfl⟩
  obtain ⟨m, ⟨hm0, hmA, hmy, hmN⟩, hmax⟩ := hK.exists_isMaxOn ⟨m₀, hne⟩
    (f := fun m => ∑ S, m S • (eqPairs P S : ℝ)) (by fun_prop)
  refine ⟨m, hm0, fun S hS => by_contra fun hn => hS (hmA S hn), hmy.symm, ?_⟩
  intro u u' hu hu' t ht ht' s hs hs' hst
  have hw : ∀ S, 0 < m S → IsWeakReachable P S := fun S hS =>
    by_contra fun hn => hS.ne' (hmA S hn)
  obtain ⟨A, B, hAw, hBw, hind, hcount⟩ := uncross (hw u hu) (hw u' hu') ht ht' hs hs' hst
  have huu : u ≠ u' := fun e => ht' (e ▸ ht)
  set ε := min (m u) (m u')
  have hε : 0 < ε := lt_min hu hu'
  -- move the weight `ε` from `u, u'` to `A, B`
  let m' : Finset (Fin T) → ℝ := fun S => m S + ε * ((if S = A then 1 else 0) +
    (if S = B then 1 else 0) - (if S = u then 1 else 0) - (if S = u' then 1 else 0))
  have hm'K : m' ∈ K := by
    refine ⟨fun S => ?_, fun S hS => ?_, ?_, ?_⟩
    · have h1 : ε ≤ m u := min_le_left _ _
      have h2 : ε ≤ m u' := min_le_right _ _
      have := hm0 S
      simp only [m']
      split_ifs <;> subst_vars <;> first | exact absurd rfl huu | linarith
    · have e1 : S ≠ u := fun e => hS (e ▸ hw u hu)
      have e2 : S ≠ u' := fun e => hS (e ▸ hw u' hu')
      have e3 : S ≠ A := fun e => hS (e ▸ hAw)
      have e4 : S ≠ B := fun e => hS (e ▸ hBw)
      simp [m', e1, e2, e3, e4, hmA S hS]
    · rw [sum_smul_exchange m ε A B u u', hmy, sub_sub, hind, sub_self, smul_zero,
        add_zero]
    · have := sum_smul_exchange (M := ℝ) m ε A B u u' (fun _ => 1)
      simp only [smul_eq_mul, mul_one] at this
      simpa [m', this] using hmN
  have hle : ∑ S, m' S • (eqPairs P S : ℝ) ≤ ∑ S, m S • (eqPairs P S : ℝ) := hmax hm'K
  have hc : (eqPairs P u : ℝ) + eqPairs P u' < eqPairs P A + eqPairs P B := by
    exact_mod_cast hcount
  rw [sum_smul_exchange m ε A B u u' (fun S => (eqPairs P S : ℝ)), smul_eq_mul] at hle
  nlinarith [mul_pos hε (sub_pos.2 hc)]

/-- **Monotone representation.** If `y` is in the cone of the weakly reachable spectra, it is in
the cone of those weakly reachable `S` for which `t ∈ S`, `s ∉ S`, `p_s = p_t` imply
`y_s < y_t`. In the extremal representation (`exists_uncrossed_rep`), for such `S` with `m_S > 0`
every `U` with `m_U > 0` containing `s` contains `t`, so
`y_t - y_s = ∑_U m_U (1_U t - 1_U s) ≥ m_S > 0`. -/
theorem mem_indicatorCone_monotone (h : y ∈ indicatorCone (weakReachableSpectra P)) :
    y ∈ indicatorCone {S | IsWeakReachable P S ∧ ∀ t ∈ S, ∀ s ∉ S, P s = P t → y s < y t} := by
  obtain ⟨m, hm0, hmW, hy, hcross⟩ := exists_uncrossed_rep h
  have key : ∀ S, 0 < m S → ∀ t ∈ S, ∀ s ∉ S, P s = P t → m S ≤ y t - y s := by
    intro S hS t ht s hs hst
    have e : y t - y s = ∑ U, m U * ((U : Set (Fin T)).indicator (1 : Fin T → ℝ) t -
        (U : Set (Fin T)).indicator (1 : Fin T → ℝ) s) := by
      rw [hy]; simp [Finset.sum_apply, ← Finset.sum_sub_distrib, mul_sub]
    rw [e]
    refine le_trans (by simp [ht, hs]) (Finset.single_le_sum (fun U _ => ?_) (Finset.mem_univ S))
    rcases (hm0 U).eq_or_lt with h0 | hU
    · simp [← h0]
    refine mul_nonneg hU.le ?_
    by_cases hsU : s ∈ U <;> by_cases htU : t ∈ U
    · simp [htU, hsU]
    · exact absurd hst (hcross S U hS hU t ht htU s hsU hs)
    all_goals simp [htU, hsU]
  have hs := Submodule.sum_mem (indicatorCone {S | IsWeakReachable P S ∧
      ∀ t ∈ S, ∀ s ∉ S, P s = P t → y s < y t}) (t := Finset.univ) fun S _ =>
    smul_indicator_mem_indicatorCone (hm0 S) fun hS => ⟨hmW S hS, fun t ht s hs hst => by
      have hp := (hm0 S).lt_of_ne' hS
      linarith [key S hp t ht s hs hst]⟩
  rwa [← hy] at hs

/-! ### The tilt -/

/-- The tilted prices `q_t = p_t + (δ ∑ⱼ exp (-p_tʲ) - δ² y_t) 1`. -/
noncomputable def tilt (P : Fin T → Fin d → ℝ) (y : Fin T → ℝ) (δ : ℝ) : Fin T → Fin d → ℝ :=
  fun t i => P t i + δ * (∑ j, Real.exp (-P t j) - δ * y t)

/-- **Positivity of the tilted witness.** Let `∑ ζ = 1`, `⟨ζ, p_s - p_t⟩ ≥ 0`, and `p_s ≠ p_t` or
`y_s < y_t`. With `g = (exp (-p_tⁱ))ᵢ`, `G = ∑ g` and `φ_r = ∑ⱼ exp (-p_rʲ)`, for `q = tilt P y δ`
one has `⟨ζ + δ g, q_s - q_t⟩ = A + δ K + δ² ((y_t - y_s)(1 + δ G) + (φ_s - φ_t) G)`, where
`A = ⟨ζ, p_s - p_t⟩ ≥ 0` and `K = φ_s - φ_t + ⟨g, p_s - p_t⟩ = ∑ᵢ exp (-p_tⁱ) (e^{-x} - 1 + x)` with
`x = p_sⁱ - p_tⁱ`. If `p_s ≠ p_t` then `K > 0` (`Real.add_one_lt_exp`); if `p_s = p_t` then
`A = K = 0` and the `δ²` term is `(y_t - y_s)(1 + δ G) > 0`. -/
theorem eventually_tilt_witness_pos {s t : Fin T} (hst : P s ≠ P t ∨ y s < y t)
    {ζ : Fin d → ℝ} (hζ : ∑ i, ζ i = 1) (hA : 0 ≤ ζ ⬝ᵥ (P s - P t)) :
    ∀ᶠ δ in 𝓝[>] 0,
      0 < (ζ + δ • fun i => Real.exp (-P t i)) ⬝ᵥ (tilt P y δ s - tilt P y δ t) := by
  set F : Fin T → ℝ := fun r => ∑ j, Real.exp (-P r j) with hF
  set G := ∑ i, Real.exp (-P t i) with hG
  set K := (F s - F t) + (fun i => Real.exp (-P t i)) ⬝ᵥ (P s - P t) with hK
  have key : ∀ δ : ℝ, (ζ + δ • fun i => Real.exp (-P t i)) ⬝ᵥ (tilt P y δ s - tilt P y δ t)
      = ζ ⬝ᵥ (P s - P t) + δ * K + δ ^ 2 * ((y t - y s) * (1 + δ * G) + (F s - F t) * G) := by
    intro δ
    have e : tilt P y δ s - tilt P y δ t
        = (P s - P t) + (δ * (F s - F t) - δ ^ 2 * (y s - y t)) • (1 : Fin d → ℝ) := by
      ext i; simp [tilt, hF]; ring
    have h1 : ζ ⬝ᵥ (1 : Fin d → ℝ) = 1 := by simp [dotProduct, hζ]
    have h2 : (fun i => Real.exp (-P t i)) ⬝ᵥ (1 : Fin d → ℝ) = G := by simp [dotProduct, hG]
    rw [e, hK]
    simp only [add_dotProduct, dotProduct_add, smul_dotProduct, dotProduct_smul, h1, h2,
      smul_eq_mul]
    ring
  have hδ : ∀ᶠ δ in 𝓝[>] (0:ℝ), 0 < δ := self_mem_nhdsWithin
  simp only [key]
  have hG0 : 0 ≤ G := Finset.sum_nonneg fun i _ => (Real.exp_pos _).le
  by_cases hne : P s = P t
  · have hy : y s < y t := hst.resolve_left (not_not.2 hne)
    filter_upwards [hδ] with δ hδ
    simp only [hK, hF, hne, sub_self, dotProduct_zero, zero_mul, mul_zero, add_zero]
    nlinarith [mul_pos (pow_pos hδ 2) (mul_pos (sub_pos.2 hy) (by positivity : 0 < 1 + δ * G))]
  have hK0 : 0 < K := by
    obtain ⟨j, hj⟩ := Function.ne_iff.mp hne
    have e : K = ∑ i, Real.exp (-P t i) *
        (Real.exp (-(P s i - P t i)) - (-(P s i - P t i) + 1)) := by
      simp only [hK, hF, dotProduct, Pi.sub_apply, ← Finset.sum_sub_distrib,
        ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [show -P s i = -P t i + -(P s i - P t i) by ring, Real.exp_add]; ring
    rw [e]
    refine Finset.sum_pos' (fun i _ => mul_nonneg (Real.exp_pos _).le ?_)
      ⟨j, Finset.mem_univ _, mul_pos (Real.exp_pos _) ?_⟩
    · linarith [Real.add_one_le_exp (-(P s i - P t i))]
    · linarith [Real.add_one_lt_exp (neg_ne_zero.2 (sub_ne_zero.2 hj))]
  have h : ∀ᶠ δ in 𝓝[>] (0:ℝ), 0 < K + δ * ((y t - y s) * (1 + δ * G) + (F s - F t) * G) :=
    nhdsWithin_le_nhds ((by fun_prop : Continuous fun δ : ℝ =>
      K + δ * ((y t - y s) * (1 + δ * G) + (F s - F t) * G)).continuousAt.eventually
        (lt_mem_nhds (by simpa using hK0)))
  filter_upwards [hδ, h] with δ hδ h
  nlinarith [mul_pos hδ h]

/-- For small `δ > 0`, every weakly reachable `S` for which `t ∈ S`, `s ∉ S`, `p_s = p_t` imply
`y_s < y_t` is reachable at `tilt P y δ`. There are finitely many `S`; for `t ∈ S` normalize the
weak witness to `ζ`, `∑ ζ = 1`; then `ζ + δ g > 0` is a witness at `tilt P y δ` for the finitely
many `s ∉ S` (`eventually_tilt_witness_pos`). -/
theorem isReachable_tilt :
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
        0 < (c • ξ + δ • fun i => Real.exp (-P t i)) ⬝ᵥ (tilt P y δ s - tilt P y δ t) :=
      (eventually_all_finset Sᶜ).2 fun s hs => by
        have hs : s ∉ S := by simpa using hs
        exact eventually_tilt_witness_pos ((ne_or_eq _ _).imp_right (hmono t ht s hs)) hζ1
          (by rw [smul_dotProduct, smul_eq_mul]; exact mul_nonneg hc.le (hξ s hs))
    filter_upwards [hs, self_mem_nhdsWithin] with δ h hδ
    have hpos (i) : 0 < (c • ξ + δ • fun i => Real.exp (-P t i)) i :=
      add_pos_of_nonneg_of_pos (mul_nonneg hc.le (hξ0 i))
        (mul_pos (show (0:ℝ) < δ from hδ) (Real.exp_pos _))
    exact ⟨_, fun i => (hpos i).le, fun h0 => (hpos i₀).ne' (by rw [h0]; rfl),
      fun s hs => h s (by simpa using hs)⟩
  filter_upwards [eventually_all.2 key] with δ h S hS using h S hS

/-- `tilt P y δ → P` as `δ → 0`, and for `P ≥ 0` the tilted prices are eventually positive:
`q_tⁱ ≥ δ (∑ⱼ exp (-p_tʲ) - δ y_t) > 0` for small `δ > 0`. -/
theorem tendsto_tilt (hP : ∀ t, 0 ≤ P t) :
    Tendsto (tilt P y) (𝓝[>] 0) (𝓝 P) ∧ ∀ᶠ δ in 𝓝[>] 0, ∀ t, tilt P y δ t ∈ orthant d := by
  have hc : Continuous (tilt P y) := continuous_pi fun t => continuous_pi fun i => by
    unfold tilt; fun_prop
  have h0 : tilt P y 0 = P := by funext t i; simp [tilt]
  refine ⟨by simpa [h0] using (hc.tendsto 0).mono_left nhdsWithin_le_nhds, ?_⟩
  have hpos (t i) : ∀ᶠ δ in 𝓝[>] (0:ℝ), 0 < ∑ j, Real.exp (-P t j) - δ * y t :=
    nhdsWithin_le_nhds ((by fun_prop : Continuous fun δ : ℝ =>
      ∑ j, Real.exp (-P t j) - δ * y t).continuousAt.eventually (lt_mem_nhds (by
        simpa using (Real.exp_pos (-P t i)).trans_le (Finset.single_le_sum
          (f := fun j => Real.exp (-P t j)) (fun j _ => (Real.exp_pos _).le) (Finset.mem_univ i)))))
  filter_upwards [eventually_all.2 fun t => eventually_all.2 (hpos t), self_mem_nhdsWithin]
    with δ h hδ t i
  exact add_pos_of_nonneg_of_pos (hP t i) (mul_pos hδ (h t i))

/-! ### Criterion -/

/-- **Sufficiency.** If `P ≥ 0` and `y` lies in the cone of the weakly reachable spectra of `P`,
then `y` is weakly solvable at `P`. By `mem_indicatorCone_monotone` it lies in the cone of the
weakly reachable `S` with `t ∈ S`, `s ∉ S`, `p_s = p_t ⇒ y_s < y_t`; for small `δ > 0` they are
all reachable at the positive prices `tilt P y δ` (`isReachable_tilt`, `tendsto_tilt`), so `y` is
solvable there (`neoSolvable_iff_mem_indicatorCone`), and `tilt P y δ → P`. -/
theorem weakSolvable_of_mem_indicatorCone (hd : 2 ≤ d) (hP : ∀ t, 0 ≤ P t) (hy : ∀ t, 0 ≤ y t)
    (h : y ∈ indicatorCone (weakReachableSpectra P)) : WeakSolvable P y := by
  obtain ⟨hlim, horth⟩ := tendsto_tilt (y := y) hP
  refine mem_closure_of_tendsto hlim ?_
  filter_upwards [isReachable_tilt (P := P) (y := y), horth] with δ hsub hQ
  exact ⟨hQ, (neoSolvable_iff_mem_indicatorCone hd hQ hy).2
    (Submodule.span_mono (image_mono hsub) (mem_indicatorCone_monotone h))⟩

/-- **Criterion of weak solvability.** For `d ≥ 2`, `P ≥ 0` and `y ≥ 0`, `y` is weakly solvable
at `P` iff it lies in the cone of the weakly reachable spectra of `P`. -/
theorem weakSolvable_iff (hd : 2 ≤ d) (hP : ∀ t, 0 ≤ P t) (hy : ∀ t, 0 ≤ y t) :
    WeakSolvable P y ↔ y ∈ indicatorCone (weakReachableSpectra P) :=
  ⟨WeakSolvable.mem_indicatorCone hd hy, weakSolvable_of_mem_indicatorCone hd hP hy⟩

end NeoTiling
