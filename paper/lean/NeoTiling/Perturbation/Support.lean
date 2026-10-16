import NeoTiling.Core.Closure

/-!
# Supporting functionals for the box criterion

For prices `P` and a set `S`, a point `z` is *supported* if some nonzero `ξ ≥ 0` has
`⟨ξ, P r - z⟩ ≥ 0` for every `r ∉ S` (it is not interior to the hull of `{P r | r ∉ S}` plus the
orthant), and *strictly supported* if the inequalities are strict. `S` is weakly reachable iff
every `P t`, `t ∈ S`, is supported. These two properties carry the proof of `box_iff`.
-/

namespace NeoTiling.Perturbation

open Finset
open scoped Classical

variable {d N M : ℕ}

/-- `z` is supported by `{P r | r ∉ S}`. -/
def Supported (P : Fin N → Fin d → ℝ) (S : Finset (Fin N)) (z : Fin d → ℝ) : Prop :=
  ∃ ξ : Fin d → ℝ, 0 ≤ ξ ∧ ξ ≠ 0 ∧ ∀ r ∉ S, 0 ≤ ξ ⬝ᵥ (P r - z)

/-- `z` is strictly supported by `{P r | r ∉ S}`. -/
def StrictlySupported (P : Fin N → Fin d → ℝ) (S : Finset (Fin N)) (z : Fin d → ℝ) : Prop :=
  ∃ ξ : Fin d → ℝ, 0 ≤ ξ ∧ ξ ≠ 0 ∧ ∀ r ∉ S, 0 < ξ ⬝ᵥ (P r - z)

variable {P : Fin N → Fin d → ℝ} {S : Finset (Fin N)}

/-- For `ξ ≥ 0`, `⟨ξ, g - z⟩` does not decrease when `z` decreases. -/
private theorem dotProduct_sub_le {ξ z z' : Fin d → ℝ} (h0 : 0 ≤ ξ) (hz : z' ≤ z)
    (g : Fin d → ℝ) : ξ ⬝ᵥ (g - z) ≤ ξ ⬝ᵥ (g - z') := by
  simp only [dotProduct, Pi.sub_apply]
  exact Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_left (by linarith [hz i]) (h0 i)

theorem StrictlySupported.supported {z : Fin d → ℝ} (h : StrictlySupported P S z) :
    Supported P S z :=
  let ⟨ξ, h0, hne, h⟩ := h; ⟨ξ, h0, hne, fun r hr => (h r hr).le⟩

/-- Supported points form a down-set. -/
theorem Supported.mono {z z' : Fin d → ℝ} (h : Supported P S z) (hz : z' ≤ z) :
    Supported P S z' :=
  let ⟨ξ, h0, hne, h⟩ := h; ⟨ξ, h0, hne, fun r hr => (h r hr).trans (dotProduct_sub_le h0 hz _)⟩

/-- A point of a weakly reachable set is supported: this is the definition. -/
theorem IsWeakReachable.supported (hS : IsWeakReachable P S) {t : Fin N} (ht : t ∈ S) :
    Supported P S (P t) :=
  hS t ht

/-- A strictly supported price `P r` has `r ∈ S`: otherwise `r` gives `0 < ⟨ξ, 0⟩`. -/
theorem StrictlySupported.mem {r : Fin N} (h : StrictlySupported P S (P r)) : r ∈ S := by
  by_contra hr
  obtain ⟨ξ, -, -, h⟩ := h
  simpa using h r hr

/-- **Transfer of reachability.** If the points `W u`, `u ∈ R`, are supported by
`{P r | r ∉ S}` and the points `W u`, `u ∉ R`, are not strictly supported, then `R` is weakly
reachable at `W`. The witness `ξ` of `W t` works: if `⟨ξ, W u - W t⟩ < 0` for some `u ∉ R`, then
`⟨ξ, P r - W u⟩ > ⟨ξ, P r - W t⟩ ≥ 0` for all `r ∉ S`, so `W u` is strictly supported. -/
theorem isWeakReachable_of_supported {W : Fin M → Fin d → ℝ} {R : Finset (Fin M)}
    (h1 : ∀ u ∈ R, Supported P S (W u)) (h2 : ∀ u ∉ R, ¬ StrictlySupported P S (W u)) :
    IsWeakReachable W R := by
  intro t ht
  obtain ⟨ξ, h0, hne, hξ⟩ := h1 t ht
  refine ⟨ξ, h0, hne, fun u hu => ?_⟩
  by_contra hlt
  push_neg at hlt
  refine h2 u hu ⟨ξ, h0, hne, fun r hr => ?_⟩
  have e : ξ ⬝ᵥ (P r - W u) = ξ ⬝ᵥ (P r - W t) - ξ ⬝ᵥ (W u - W t) := by
    simp only [dotProduct_sub]; ring
  linarith [hξ r hr]

/-- The pairs `(P, z)` with `z` supported by `{P r | r ∉ S}` form a closed set: normalise `ξ`
into the compact standard simplex and project along it. -/
theorem isClosed_setOf_supported_pair (S : Finset (Fin N)) :
    IsClosed {p : (Fin N → Fin d → ℝ) × (Fin d → ℝ) | Supported p.1 S p.2} := by
  haveI : CompactSpace (stdSimplex ℝ (Fin d)) :=
    isCompact_iff_compactSpace.mp (isCompact_stdSimplex _)
  let C : Set (stdSimplex ℝ (Fin d) × ((Fin N → Fin d → ℝ) × (Fin d → ℝ))) :=
    {q | ∀ r ∉ S, 0 ≤ (q.1 : Fin d → ℝ) ⬝ᵥ (q.2.1 r - q.2.2)}
  have hC : IsClosed C := by
    simp only [C, Set.setOf_forall]
    exact isClosed_iInter fun r => isClosed_iInter fun _ => isClosed_le continuous_const
      ((continuous_subtype_val.comp continuous_fst).dotProduct
        (((continuous_apply r).comp (continuous_fst.comp continuous_snd)).sub
          (continuous_snd.comp continuous_snd)))
  convert isClosedMap_snd_of_compactSpace _ hC using 1
  ext p
  constructor
  · rintro ⟨ξ, h0, hne, h⟩
    obtain ⟨c, hc, hcξ⟩ := exists_smul_mem_stdSimplex h0 hne
    refine ⟨(⟨c • ξ, hcξ⟩, p), fun r hr => ?_, rfl⟩
    show 0 ≤ (c • ξ) ⬝ᵥ (p.1 r - p.2)
    rw [smul_dotProduct]; exact mul_nonneg hc.le (h r hr)
  · rintro ⟨⟨⟨ξ, hξ⟩, p'⟩, h, rfl⟩
    refine ⟨ξ, hξ.1, ?_, h⟩
    rintro rfl
    simpa using hξ.2

/-- Supported points form a closed set: a slice of `isClosed_setOf_supported_pair`. -/
theorem isClosed_setOf_supported : IsClosed {z : Fin d → ℝ | Supported P S z} :=
  (isClosed_setOf_supported_pair S).preimage (continuous_const.prodMk continuous_id)

/-- Strictly supported points form an open set: finitely many strict inequalities. -/
theorem isOpen_setOf_strictlySupported : IsOpen {z : Fin d → ℝ | StrictlySupported P S z} := by
  simp only [StrictlySupported, Set.setOf_exists]
  refine isOpen_iUnion fun ξ => ?_
  by_cases hξ : 0 ≤ ξ ∧ ξ ≠ 0
  · simp only [hξ.1, hξ.2, ne_eq, not_false_eq_true, true_and, Set.setOf_forall]
    exact isOpen_iInter_of_finite fun r => isOpen_iInter_of_finite fun _ =>
      isOpen_lt continuous_const (continuous_const.dotProduct (continuous_const.sub continuous_id))
  · rw [not_and_or] at hξ
    rcases hξ with h | h <;> simp [h]

/-- **A point between two semicontinuous functions.** If `lo ≤ hi` on `[0, 1]`, `hi` is upper and
`lo` lower semicontinuous, `c ≤ hi 0` and `lo 1 ≤ c`, then `lo s ≤ c ≤ hi s` for some
`s ∈ [0, 1]`. The closed sets `{lo ≤ c}` and `{c ≤ hi}` cover the connected `[0, 1]` (as
`lo ≤ hi`) and meet it at `1` and `0`, so they intersect (`isPreconnected_closed_iff`). -/
theorem exists_mem_Icc_between {hi lo : ℝ → ℝ} {c : ℝ} (hhi : UpperSemicontinuous hi)
    (hlo : LowerSemicontinuous lo) (hle : ∀ s ∈ Set.Icc (0 : ℝ) 1, lo s ≤ hi s)
    (h0 : c ≤ hi 0) (h1 : lo 1 ≤ c) :
    ∃ s ∈ Set.Icc (0 : ℝ) 1, lo s ≤ c ∧ c ≤ hi s := by
  obtain ⟨s, hs, h2, h3⟩ := isPreconnected_closed_iff.1 isPreconnected_Icc _ _
    (hlo.isClosed_preimage c) (hhi.isClosed_preimage c)
    (fun s hs => (le_total (lo s) c).imp id fun h => h.trans (hle s hs))
    ⟨1, ⟨zero_le_one, le_rfl⟩, h1⟩ ⟨0, ⟨le_rfl, zero_le_one⟩, h0⟩
  exact ⟨s, hs, h2, h3⟩

/-- **Between two indicators.** If every `R` with `Rmin ⊆ R ⊆ Rmax` lies in `A` and
`1_Rmin ≤ v ≤ 1_Rmax`, then `v` lies in the cone of `A` (`cube_mem_span` with
`O = Rmin`, `B = Rmax \ Rmin`). -/
theorem mem_indicatorCone_of_ind_le {T : ℕ} {A : Set (Finset (Fin T))}
    {Rmin Rmax : Finset (Fin T)} (hA : ∀ R, Rmin ⊆ R → R ⊆ Rmax → R ∈ A) (v : Fin T → ℝ)
    (hlo : ∀ t, (Rmin : Set (Fin T)).indicator 1 t ≤ v t)
    (hhi : ∀ t, v t ≤ (Rmax : Set (Fin T)).indicator 1 t) :
    v ∈ indicatorCone A := by
  have hsub : Rmin ⊆ Rmax := by
    intro t ht
    have h1 := hlo t
    have h2 := hhi t
    by_contra h
    simp [ht, h] at h1 h2
    linarith
  set z : Fin T → ℝ := fun t => v t - (Rmin : Set (Fin T)).indicator 1 t with hzdef
  have hz0 : ∀ q, 0 ≤ z q := fun q => sub_nonneg.2 (hlo q)
  have hz1 : ∀ q, z q ≤ ind (Rmax \ Rmin) q := by
    intro q
    have h1 := hlo q
    have h2 := hhi q
    simp only [hzdef, ind]
    by_cases hq : q ∈ Rmin
    · simp [hq, hsub hq] at h1 h2 ⊢
      linarith
    · by_cases hq' : q ∈ Rmax
      · simp [hq, hq']
        simpa [hq, hq'] using h2
      · simp [hq, hq'] at h2 ⊢
        linarith
  have hmem := cube_mem_span Rmin (Rmax \ Rmin) Finset.disjoint_sdiff z hz0 hz1
  have hv : (fun q => ind Rmin q + z q) = v := by
    funext q; simp [hzdef, ind]
  rw [hv] at hmem
  refine Submodule.span_mono ?_ hmem
  rintro _ ⟨B', hB', rfl⟩
  refine ⟨Rmin ∪ B', hA _ Finset.subset_union_left ?_, rfl⟩
  intro t ht
  rcases Finset.mem_union.1 ht with h | h
  · exact hsub h
  · exact (Finset.mem_sdiff.1 (hB' h)).1

/-- **Between two weighted sums of indicators.** If `Σ m_k 1_{Rmin k} ≤ y ≤ Σ m_k 1_{Rmax k}`
with `m ≥ 0`, `Rmin k ⊆ Rmax k` and every set between them in `A`, then `y` lies in the cone of
`A`. Write `y t = lo t + θ t (hi t - lo t)` with `θ t ∈ [0, 1]` and split
`y = Σ m_k (1_{Rmin k} + θ (1_{Rmax k} - 1_{Rmin k}))`. -/
theorem mem_indicatorCone_of_between {T n : ℕ} {A : Set (Finset (Fin T))} (m : Fin n → ℝ)
    (hm : ∀ k, 0 ≤ m k) (Rmin Rmax : Fin n → Finset (Fin T)) (hsub : ∀ k, Rmin k ⊆ Rmax k)
    (hA : ∀ k R, Rmin k ⊆ R → R ⊆ Rmax k → R ∈ A) (y : Fin T → ℝ)
    (hlo : ∀ t, (∑ k, if t ∈ Rmin k then m k else 0) ≤ y t)
    (hhi : ∀ t, y t ≤ ∑ k, if t ∈ Rmax k then m k else 0) :
    y ∈ indicatorCone A := by
  set lo : Fin T → ℝ := fun t => ∑ k, if t ∈ Rmin k then m k else 0 with hlodef
  set hi : Fin T → ℝ := fun t => ∑ k, if t ∈ Rmax k then m k else 0 with hhidef
  set θ : Fin T → ℝ := fun t => if lo t < hi t then (y t - lo t) / (hi t - lo t) else 0 with hθ
  have hθ0 : ∀ t, 0 ≤ θ t := by
    intro t; simp only [hθ]; split_ifs with h
    · exact div_nonneg (sub_nonneg.2 (hlo t)) (by linarith)
    · exact le_rfl
  have hθ1 : ∀ t, θ t ≤ 1 := by
    intro t; simp only [hθ]; split_ifs with h
    · rw [div_le_one (by linarith)]; linarith [hhi t]
    · norm_num
  have hθy : ∀ t, lo t + θ t * (hi t - lo t) = y t := by
    intro t; simp only [hθ]; split_ifs with h
    · field_simp [(sub_pos.2 h).ne']; ring
    · have : lo t = y t := le_antisymm (hlo t) (by linarith [hhi t, not_lt.1 h])
      simp [this]
  let v : Fin n → Fin T → ℝ := fun k t =>
    (Rmin k : Set (Fin T)).indicator 1 t +
      θ t * ((Rmax k : Set (Fin T)).indicator 1 t - (Rmin k : Set (Fin T)).indicator 1 t)
  have hv : ∀ k, v k ∈ indicatorCone A := by
    intro k
    have hle : ∀ t, (Rmin k : Set (Fin T)).indicator (1 : Fin T → ℝ) t ≤
        (Rmax k : Set (Fin T)).indicator 1 t := by
      intro t
      by_cases h : t ∈ Rmin k
      · simp [h, hsub k h]
      · simp [h]; exact Set.indicator_nonneg (fun _ _ => zero_le_one) t
    refine mem_indicatorCone_of_ind_le (hA k) (v k) (fun t => ?_) (fun t => ?_)
    · have := hθ0 t; have := hle t; simp only [v]; nlinarith
    · have := hθ1 t; have := hle t; simp only [v]; nlinarith
  have hy : y = ∑ k, (⟨m k, hm k⟩ : NNReal) • v k := by
    funext t
    simp only [Finset.sum_apply, Pi.smul_apply]
    rw [← hθy t]
    simp only [v, hlodef, hhidef, Finset.mul_sum, ← Finset.sum_sub_distrib,
      ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun k _ => ?_
    by_cases h1 : t ∈ Rmin k <;> by_cases h2 : t ∈ Rmax k <;> simp [h1, h2] <;> ring
  rw [hy]
  exact Submodule.sum_mem _ fun k _ => Submodule.smul_mem _ _ (hv k)

/-- **Corner set.** If `S` is weakly reachable at `Q` with `L ≤ Q ≤ U`, the corners
`castAdd t` with `L t` supported by `{Q r | r ∉ S}` and `natAdd t` with `U t` strictly
supported form a weakly reachable set `S'` at `Fin.append L U` (`isWeakReachable_of_supported`).
It contains `castAdd t` for `t ∈ S` (`Q t` supported and `L t ≤ Q t`) and no `natAdd t` for
`t ∉ S` (`Q t ≤ U t` and `r = t` forbid strict support). -/
theorem exists_corner_set {T : ℕ} {Q L U : Fin T → Fin d → ℝ} {S : Finset (Fin T)}
    (hS : IsWeakReachable Q S) (hQ : ∀ t i, L t i ≤ Q t i ∧ Q t i ≤ U t i) :
    ∃ S' ∈ weakReachableSpectra (Fin.append L U),
      ∀ t, (t ∈ S → Fin.castAdd T t ∈ S') ∧ (Fin.natAdd T t ∈ S' → t ∈ S) := by
  let pred : Fin (T + T) → Prop := Fin.addCases (fun t => Supported Q S (L t))
    (fun t => StrictlySupported Q S (U t))
  refine ⟨Finset.univ.filter pred, ?_, fun t => ⟨fun ht => ?_, fun ht => ?_⟩⟩
  · refine isWeakReachable_of_supported (P := Q) (S := S) (W := Fin.append L U) (fun u hu => ?_)
      (fun u hu => ?_)
    · induction u using Fin.addCases with
      | left t => simpa [pred] using hu
      | right t =>
        rw [Fin.append_right]
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, pred] at hu
        rw [Fin.addCases_right] at hu
        exact hu.supported
    · induction u using Fin.addCases with
      | left t =>
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, pred] at hu
        rw [Fin.addCases_left] at hu
        rw [Fin.append_left]
        exact fun h => hu h.supported
      | right t =>
        rw [Fin.append_right]
        simpa only [Finset.mem_filter, Finset.mem_univ, true_and, pred, Fin.addCases_right]
          using hu
  · simp only [Finset.mem_filter, Finset.mem_univ, true_and, pred, Fin.addCases_left]
    exact (IsWeakReachable.supported hS ht).mono fun i => (hQ t i).1
  · -- `r = t` would give `0 < ⟨ξ, Q t - U t⟩ ≤ 0`
    by_contra htS
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, pred, Fin.addCases_right] at ht
    obtain ⟨ξ, h0, -, h⟩ := ht
    have := h t htS
    have : ξ ⬝ᵥ (Q t - U t) ≤ 0 :=
      Finset.sum_nonpos fun i _ => mul_nonpos_of_nonneg_of_nonpos (h0 i) (by simp [(hQ t i).2])
    linarith

end NeoTiling.Perturbation
