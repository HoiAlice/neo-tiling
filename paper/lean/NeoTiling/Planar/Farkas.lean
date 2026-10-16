import NeoTiling.Planar.FlowLP

/-!
# The column problem and the Farkas certificate in the plane

Mode `b` and the chain graph as in `Planar.FlowLP`.

**Results.**
* `min_family_eq_min_path`: for costs `c`, the least cost `Σ_{q ∈ S} c_q` of a (weakly)
  reachable set equals the least weight of a source–sink path, the arc `e` weighing
  `Σ_{Out e} c + β Σ_{Bnd e} min(c, 0)`. So `nonneg_family_iff_path`: `c ≥ 0` on the family iff
  every path has nonnegative weight, one shortest-path computation in an acyclic graph.
* `not_mem_indicatorCone_iff`: Farkas' lemma for an indicator cone, `y ∉ cone A` iff some `c`
  has `⟨c, y⟩ < 0` and `Σ_{q ∈ S} c_q ≥ 0` for all `S ∈ A`.
* `not_mem_iff_path_certificate`: in the plane the Farkas vector `c` is checked by one
  shortest-path computation.
-/

namespace NeoTiling.Planar

open Finset
open scoped Classical

/-! ## Farkas' lemma for an indicator cone -/

section Farkas

variable {T : ℕ}

/-- The hull of the nonempty indicators lies in the cone and in the half-space `Σ x ≥ 1`. -/
theorem mem_convexHull_bounds {A : Set (Finset (Fin T))} {x : Fin T → ℝ}
    (hx : x ∈ convexHull ℝ ((fun S : Finset (Fin T) => (S : Set (Fin T)).indicator 1) ''
      {S | S ∈ A ∧ S.Nonempty})) :
    x ∈ indicatorCone A ∧ 1 ≤ ∑ q, x q := by
  have hconv : Convex ℝ {x : Fin T → ℝ | x ∈ indicatorCone A ∧ 1 ≤ ∑ q, x q} := by
    intro x hx y hy a b ha hb hab
    refine ⟨(indicatorCone A).add_mem ((PointedCone.smul_mem _ ha hx.1))
      (PointedCone.smul_mem _ hb hy.1), ?_⟩
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Finset.sum_add_distrib, ← Finset.mul_sum]
    nlinarith [hx.2, hy.2]
  refine convexHull_min ?_ hconv hx
  rintro _ ⟨S, ⟨hS, hne⟩, rfl⟩
  refine ⟨Submodule.subset_span ⟨S, hS, rfl⟩, ?_⟩
  simp [Set.indicator_apply, Finset.sum_ite_mem]
  exact hne

/-- **Farkas, positive case.** If `y ∉ cone A` and `Σ y > 0`, separate the compact hull `C` of
the nonempty indicators from the ray `ℝ₊ y` (disjoint by `mem_convexHull_bounds`):
`f < u` on `C`, `v < f` on the ray, `u < v`. Then `v < 0` (the ray contains `0`), `f y ≥ 0`, and
`c_q = -f(e_q) - μ` with `μ = -u / (T + 1)` works: `Σ_{q ∈ S} c_q = -f(1_S) - μ|S| > -u - μ T > 0`
and `⟨c, y⟩ = -f y - μ Σ y < 0`. -/
theorem exists_farkas_of_sum_pos {A : Set (Finset (Fin T))} {y : Fin T → ℝ}
    (hy : y ∉ indicatorCone A) (hpos : 0 < ∑ q, y q) :
    ∃ c : Fin T → ℝ, ∑ q, c q * y q < 0 ∧ ∀ S ∈ A, 0 ≤ ∑ q ∈ S, c q := by
  set G := (fun S : Finset (Fin T) => (S : Set (Fin T)).indicator (1 : Fin T → ℝ)) ''
    {S | S ∈ A ∧ S.Nonempty} with hG
  set R : Set (Fin T → ℝ) := (fun s : ℝ => s • y) '' Set.Ici 0 with hR
  -- the ray is closed: the image of `[0, ∞)` under the closed embedding `s ↦ s • y`
  have hy0 : y ≠ 0 := by rintro rfl; simp at hpos
  have hRc : IsClosed R :=
    ((LinearMap.toSpanSingleton ℝ _ y).isClosedEmbedding_of_injective
      (LinearMap.ker_eq_bot.2 (smul_left_injective ℝ hy0))).isClosedMap _ isClosed_Ici
  have hRv : Convex ℝ R := by
    have := (convex_Ici (0:ℝ)).linear_image (LinearMap.toSpanSingleton ℝ (Fin T → ℝ) y)
    simpa [hR, LinearMap.toSpanSingleton_apply] using this
  have hGc : IsCompact (convexHull ℝ G) := (Set.toFinite G).isCompact_convexHull
  -- the hull misses the ray: `s • y` in the hull has `Σ ≥ 1` and lies in the cone
  have hdisj : Disjoint (convexHull ℝ G) R := by
    rw [Set.disjoint_left]
    intro x hxC ⟨s, hs, hsx⟩
    obtain ⟨hxm, hx1⟩ := mem_convexHull_bounds hxC
    subst hsx
    have hs' : 0 ≤ s := hs
    rcases hs'.eq_or_lt with h0 | h0
    · subst h0; simp at hx1; linarith
    · apply hy
      have := Submodule.smul_mem _ (⟨s⁻¹, inv_nonneg.2 h0.le⟩ : {r : ℝ // 0 ≤ r}) hxm
      simpa [smul_smul, h0.ne'] using this
  obtain ⟨f, u, v, hfu, huv, hfv⟩ :=
    geometric_hahn_banach_compact_closed (convex_convexHull ℝ G) hGc hRv hRc hdisj
  have hv : v < 0 := by
    have := hfv 0 ⟨0, Set.mem_Ici.2 le_rfl, zero_smul _ _⟩
    simpa using this
  have hfy : 0 ≤ f y := by
    by_contra h
    push_neg at h
    have hs : 0 < v / f y := div_pos_of_neg_of_neg hv h
    have := hfv _ ⟨v / f y, hs.le, rfl⟩
    rw [map_smul, smul_eq_mul, div_mul_cancel₀ _ h.ne] at this
    exact lt_irrefl _ this
  have hfx (x : Fin T → ℝ) : f x = ∑ q, x q * f (Pi.single q 1) := by
    rw [← f.coe_coe, f.toLinearMap.pi_apply_eq_sum_univ]
    simp only [smul_eq_mul, ContinuousLinearMap.coe_coe]
    exact Finset.sum_congr rfl fun q _ => by congr; ext j; simp [Pi.single_apply, eq_comm]
  have hu : u < 0 := huv.trans hv
  have hμ : 0 < -u / (T + 1) := div_pos (by linarith) (by positivity)
  refine ⟨fun q => -f (Pi.single q 1) - -u / (T + 1), ?_, ?_⟩
  · have : ∑ q, (-f (Pi.single q 1) - -u / (T + 1)) * y q =
        -f y - (-u / (T + 1)) * ∑ q, y q := by
      rw [hfx y]; simp only [sub_mul, Finset.sum_sub_distrib, Finset.sum_neg_distrib, neg_mul,
        Finset.mul_sum]
      simp only [mul_comm]
    rw [this]
    nlinarith [mul_pos hμ hpos]
  · intro S hS
    rcases S.eq_empty_or_nonempty with rfl | hne
    · simp
    · have hmem : (S : Set (Fin T)).indicator (1 : Fin T → ℝ) ∈ convexHull ℝ G :=
        subset_convexHull ℝ G ⟨S, ⟨hS, hne⟩, rfl⟩
      have h1 := hfu _ hmem
      rw [hfx] at h1
      have h2 : ∑ q, (S : Set (Fin T)).indicator (1 : Fin T → ℝ) q * f (Pi.single q 1) =
          ∑ q ∈ S, f (Pi.single q 1) := by
        simp [Set.indicator_apply, Finset.sum_ite_mem]
      rw [h2] at h1
      have h3 : (S.card : ℝ) ≤ T := by
        have := Finset.card_le_univ S
        simpa using this
      simp only [Finset.sum_sub_distrib, Finset.sum_neg_distrib, Finset.sum_const, nsmul_eq_mul]
      nlinarith [mul_le_mul_of_nonneg_left h3 hμ.le,
        div_mul_cancel₀ (-u) (show ((T:ℝ) + 1) ≠ 0 by positivity)]

/-- **Farkas' lemma for an indicator cone.** `y ∉ cone{1_S | S ∈ A}` iff some `c` has
`⟨c, y⟩ < 0` and `c(S) ≥ 0` on `A`. (⇐) by `indicatorCone_pairing_nonneg`. (⇒) if some
`y_q < 0`, take `c = e_q`; otherwise `y ≥ 0`, `y ≠ 0` (as `0` is in the cone), so `Σ y > 0` and
`exists_farkas_of_sum_pos` applies. -/
theorem not_mem_indicatorCone_iff (A : Set (Finset (Fin T))) (y : Fin T → ℝ) :
    y ∉ indicatorCone A ↔
      ∃ c : Fin T → ℝ, ∑ q, c q * y q < 0 ∧ ∀ S ∈ A, 0 ≤ ∑ q ∈ S, c q := by
  constructor
  · intro hy
    by_cases hq : ∃ q, y q < 0
    · obtain ⟨q, hq⟩ := hq
      refine ⟨Pi.single q 1, ?_, fun S _ => Finset.sum_nonneg fun i _ => ?_⟩
      · simpa [Pi.single_apply] using hq
      · by_cases h : i = q <;> simp [Pi.single_apply, h]
    · push_neg at hq
      have hne : ∃ q, 0 < y q := by
        by_contra h
        push_neg at h
        apply hy
        have : y = 0 := funext fun q => le_antisymm (h q) (hq q)
        rw [this]; exact zero_mem _
      obtain ⟨q, hq'⟩ := hne
      exact exists_farkas_of_sum_pos hy
        (Finset.sum_pos' (fun i _ => hq i) ⟨q, Finset.mem_univ _, hq'⟩)
  · rintro ⟨c, hc, hA⟩ hy
    have := indicatorCone_pairing_nonneg
      (∑ q, c q • LinearMap.proj (R := ℝ) (φ := fun _ : Fin T => ℝ) q)
      (fun S hS => by simpa [Set.indicator_apply] using hA S hS) hy
    simp only [LinearMap.coe_sum, Finset.sum_apply, LinearMap.smul_apply, LinearMap.proj_apply,
      smul_eq_mul] at this
    linarith

end Farkas

/-! ## The column problem -/

variable {T : ℕ} (P : Fin T → Fin 2 → ℝ)

/-- Weight of the arc `u → v` for costs `c`: `Σ_{Out} c + β Σ_{Bnd} min(c, 0)`. -/
noncomputable def arcW (b : Bool) (c : Fin T → ℝ) (u v : Node T) : ℝ :=
  ∑ q ∈ Out P u v, c q + beta b * ∑ q ∈ Bnd P u v, min (c q) 0

/-- Weight of the path `w 0, …, w L`. -/
noncomputable def pathW (b : Bool) (c : Fin T → ℝ) (w : ℕ → Node T) (L : ℕ) : ℝ :=
  ∑ i ∈ range L, arcW P b c (w i) (w (i + 1))

/-- The path weight is linear in the path vector. -/
theorem pathW_eq_sum_pathVec (b : Bool) (c : Fin T → ℝ) (w : ℕ → Node T) (L : ℕ) :
    pathW P b c w L = ∑ u, ∑ v, pathVec w L u v * arcW P b c u v :=
  (sum_pathVec_mul w L _).symm

/-- Along a source–sink path the sets of different arcs are disjoint (`path_ind_eq`), so the
path weight is `Σ_{Out(π)} c + β Σ_{Bnd(π)} min(c, 0)`. -/
theorem pathW_eq {w : ℕ → Node T} {L : ℕ} (hw : IsPath (Arc P) .src .snk w L) (b : Bool)
    (c : Fin T → ℝ) :
    pathW P b c w L = ∑ q ∈ pathOut P w L, c q + beta b * ∑ q ∈ pathBnd P w L, min (c q) 0 := by
  have key : ∀ (S : Finset (Fin T)) (F : Fin T → ℝ), ∑ q ∈ S, F q = ∑ q, F q * ind S q := by
    intro S F
    simp [ind, Set.indicator_apply, Finset.sum_ite_mem]
  have swap : ∀ (X : Node T → Node T → Finset (Fin T)) (G : Fin T → ℝ),
      ∑ u, ∑ v, pathVec w L u v * ∑ q ∈ X u v, G q =
        ∑ q, G q * ∑ u, ∑ v, pathVec w L u v * ind (X u v) q := by
    intro X G
    simp only [key (X _ _) G, Finset.mul_sum]
    rw [Finset.sum_congr rfl fun u _ => Finset.sum_comm, Finset.sum_comm]
    refine Finset.sum_congr rfl fun q _ => Finset.sum_congr rfl fun u _ =>
      Finset.sum_congr rfl fun v _ => ?_
    ring
  obtain ⟨h1, h2, -⟩ := path_ind_eq P hw
  rw [pathW_eq_sum_pathVec, key (pathOut P w L), key (pathBnd P w L) (fun q => min (c q) 0), h1,
    h2]
  simp only [arcW, mul_add, Finset.sum_add_distrib, swap (Out P) c, mul_left_comm _ (beta b),
    ← Finset.mul_sum, swap (Bnd P) fun q => min (c q) 0]

/-- **The column problem is a shortest path.** (a) Every path is matched by a (weakly) reachable
set of the same cost: `Out(π) ∪ {q ∈ Bnd(π) | c_q < 0}` (weak) or `Out(π)` (strict).
(b) Every (weakly) reachable set `S = Out(π) ∪ B'`, `B' ⊆ β Bnd(π)`, costs at least the weight of
its path, since `Σ_{B'} c ≥ Σ_{Bnd(π)} min(c, 0)`. -/
theorem min_family_eq_min_path (b : Bool) (c : Fin T → ℝ) :
    (∀ (w : ℕ → Node T) (L : ℕ), IsPath (Arc P) .src .snk w L →
      ∃ S, IsReachableB b P S ∧ ∑ q ∈ S, c q = pathW P b c w L) ∧
    (∀ S, IsReachableB b P S →
      ∃ (w : ℕ → Node T) (L : ℕ), IsPath (Arc P) .src .snk w L ∧
        pathW P b c w L ≤ ∑ q ∈ S, c q) := by
  cases b
  · refine ⟨fun w L hw => ?_, fun S hS => ?_⟩
    · -- weak mode: add the boundary points of negative cost
      obtain ⟨-, -, hd⟩ := path_ind_eq P hw
      refine ⟨pathOut P w L ∪ (pathBnd P w L).filter (fun q => c q < 0),
        (isReachableB_iff_path P false _).2 ⟨w, L, hw, subset_union_left, ?_⟩, ?_⟩
      · simpa using union_subset_union_right (filter_subset _ _)
      · rw [pathW_eq P hw, sum_union (hd.mono_right (filter_subset _ _)), sum_filter]
        simp only [beta, Bool.false_eq_true, if_false, one_mul]
        congr 1
        refine sum_congr rfl fun q _ => ?_
        rcases lt_or_ge (c q) 0 with h | h
        · simp [h, min_eq_left h.le]
        · simp [not_lt.2 h, min_eq_right h]
    · -- `Σ_S c = Σ_{Out} c + Σ_{S \ Out} c ≥ Σ_{Out} c + Σ_{Bnd} min(c, 0)`
      obtain ⟨w, L, hw, h1, h2⟩ := (isReachableB_iff_path P false S).1 hS
      refine ⟨w, L, hw, ?_⟩
      rw [pathW_eq P hw, ← sum_sdiff h1 (f := c)]
      have hsub : S \ pathOut P w L ⊆ pathBnd P w L := fun q hq => by
        have := h2 (mem_sdiff.1 hq).1
        simpa [(mem_sdiff.1 hq).2] using this
      have : ∑ q ∈ pathBnd P w L, min (c q) 0 ≤ ∑ q ∈ S \ pathOut P w L, min (c q) 0 :=
        sum_le_sum_of_subset_of_nonpos hsub fun q _ _ => min_le_right _ _
      have h3 : ∑ q ∈ S \ pathOut P w L, min (c q) 0 ≤ ∑ q ∈ S \ pathOut P w L, c q :=
        sum_le_sum fun q _ => min_le_left _ _
      have hb : beta false = 1 := by simp [beta]
      rw [hb]; linarith
  · -- strict mode: `S = Out(π)`
    refine ⟨fun w L hw => ⟨pathOut P w L,
      (isReachableB_iff_path P true _).2 ⟨w, L, hw, subset_rfl, by simp⟩, ?_⟩, fun S hS => ?_⟩
    · simp [pathW_eq P hw, beta]
    · obtain ⟨w, L, hw, h1, h2⟩ := (isReachableB_iff_path P true S).1 hS
      refine ⟨w, L, hw, ?_⟩
      simp only [if_true, union_empty] at h2
      rw [pathW_eq P hw, Finset.Subset.antisymm h2 h1]
      simp [beta]

/-- Costs are nonnegative on the family iff every source–sink path has nonnegative weight. -/
theorem nonneg_family_iff_path (b : Bool) (c : Fin T → ℝ) :
    (∀ S, IsReachableB b P S → 0 ≤ ∑ q ∈ S, c q) ↔
      ∀ (w : ℕ → Node T) (L : ℕ), IsPath (Arc P) .src .snk w L → 0 ≤ pathW P b c w L := by
  obtain ⟨ha, hb⟩ := min_family_eq_min_path P b c
  refine ⟨fun h w L hw => ?_, fun h S hS => ?_⟩
  · obtain ⟨S, hS, e⟩ := ha w L hw
    exact e ▸ h S hS
  · obtain ⟨w, L, hw, le⟩ := hb S hS
    exact (h w L hw).trans le

/-! ## The Farkas certificate -/

/-- **Farkas certificate.** `y` is outside the cone of (weakly) reachable spectra iff some `c`
has `⟨c, y⟩ < 0` and `c(S) ≥ 0` for all (weakly) reachable `S`. -/
theorem not_mem_iff_farkas (b : Bool) (y : Fin T → ℝ) :
    y ∉ indicatorCone {S | IsReachableB b P S} ↔
      ∃ c : Fin T → ℝ, ∑ q, c q * y q < 0 ∧ ∀ S, IsReachableB b P S → 0 ≤ ∑ q ∈ S, c q :=
  not_mem_indicatorCone_iff _ y

/-- **The NO certificate is checked by a shortest path.** `y` is outside the cone of (weakly)
reachable spectra iff some `c` has `⟨c, y⟩ < 0` and every source–sink path of the chain graph
has nonnegative weight for `c`. -/
theorem not_mem_iff_path_certificate (b : Bool) (y : Fin T → ℝ) :
    y ∉ indicatorCone {S | IsReachableB b P S} ↔
      ∃ c : Fin T → ℝ, ∑ q, c q * y q < 0 ∧
        ∀ (w : ℕ → Node T) (L : ℕ), IsPath (Arc P) .src .snk w L → 0 ≤ pathW P b c w L := by
  simp only [not_mem_iff_farkas, nonneg_family_iff_path]

end NeoTiling.Planar
