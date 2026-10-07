import NeoTiling.ReachableSpectra

/-!
# Prices not in general position

Notes, section "Алгоритм регулярной разрешимости". The cone criterion `thm:admissible-cone`
(`PricesGeneralPosition.neoSolvable_iff_mem_span_reachableSpectra`) assumes general position of
the prices only because it passes through regular solvability. Here the hypothesis is removed,
and the reachable spectra at degenerate prices are compared with those at nearby prices in
general position.

Main results (all for prices `P` in `ℝ²₊₊`):

* `exists_spectrum_eq_reachableSpectra_of_pos`: one `h ∈ Φ̂₂` has `Sp(h, P) = Sp(P)`
  (`lem:patch` for the whole family, no `lem:gp-approx`).
* `neoSolvable_iff_mem_span_reachableSpectra`: `thm:admissible-cone` without general position,
  `y ≥ 0` is neoclassically solvable iff `y ∈ cone {1_S | S ∈ Sp(P)}`.
* `not_regularlySolvable`, `neoSolvable_one`: at prices not in general position nothing is
  regularly solvable, but `y = 1` is neoclassically solvable; so `thm:regular-solvability`
  genuinely needs general position.
* `eventually_reachableSpectra_subset`: `Sp(P) ⊆ Sp(Q)` for all `Q` near `P` (covering is a
  closed condition, `isClosed_setOf_covers`).
* `exists_pricesGeneralPosition_not_mem`: every `S ∉ Sp(P)` is outside `Sp(Q)` for some `Q` in
  general position arbitrarily close to `P` (strict covering is an open condition,
  `eventually_covers`, and prices with distinct coordinates are dense,
  `dense_injective_coords`).

The last two together: `Sp(P)` is the intersection of `Sp(Q)` over the prices `Q` in general
position in any small enough neighbourhood of `P`.
-/

open Set Filter Topology

namespace NeoTiling

variable {T : ℕ} {P : Fin T → ℝ × ℝ}

/-! ### The cone criterion without general position -/

/-- **Remark after `thm:admissible-cone`, any positive prices**: some `h ∈ Φ̂₂` has
`Sp(h, P) = Sp(P)`.

Proof: `lem:patch` (`exists_polyMin_patch`) for the whole finite family `Sp(P)` gives a polygonal
`h` with `Sp(P) ⊆ Sp(h, P)`; the reverse inclusion is
`IsNeoclassical.spectrum_subset_reachableSpectra`. -/
theorem exists_spectrum_eq_reachableSpectra_of_pos (hP : ∀ t, P t ∈ orthant) :
    ∃ h, IsPosNeoclassical h ∧ spectrum h P = reachableSpectra P := by
  classical
  set 𝒮 := Finset.univ.filter fun S : Finset (Fin T) => IsReachable P S
  obtain ⟨K, _, _, ξ, hξ, hspec⟩ :=
    exists_polyMin_patch hP (fun i => (𝒮.equivFin.symm i : Finset (Fin T)))
      fun i => (Finset.mem_filter.1 (𝒮.equivFin.symm i).2).2
  have hh := isPosNeoclassical_polyMin hξ
  refine ⟨_, hh, (hh.toIsNeoclassical.spectrum_subset_reachableSpectra hP).antisymm
    fun S hS => ?_⟩
  simpa using hspec (𝒮.equivFin ⟨S, Finset.mem_filter.2 ⟨Finset.mem_univ _, hS⟩⟩)

/-- **Theorem `thm:admissible-cone` without general position**: at positive prices, outputs
`y ≥ 0` are neoclassically solvable iff `y ∈ cone {1_S | S ∈ Sp(P)}`.

Proof: `→` is `NeoSolvable.mem_span_reachableSpectra`. `←`: the `h` with `Sp(h, P) = Sp(P)`
(`exists_spectrum_eq_reachableSpectra_of_pos`) realizes `y` at `P` (`lem:signature-points`), and
at every `Q` near `P`, since `Sp(h, P) ⊆ Sp(h, Q)` there
(`IsNeoclassical.eventually_spectrum_subset`, `Realizes.mono_spectrum`). -/
theorem neoSolvable_iff_mem_span_reachableSpectra (hP : ∀ t, P t ∈ orthant) {y : Fin T → ℝ}
    (hy : ∀ t, 0 ≤ y t) :
    NeoSolvable P y ↔ y ∈ PointedCone.span ℝ
      ((fun S : Finset (Fin T) => (S : Set (Fin T)).indicator 1) '' reachableSpectra P) := by
  refine ⟨fun hN => hN.mem_span_reachableSpectra hP hy, fun hmem => ?_⟩
  obtain ⟨h, hh, hSp⟩ := exists_spectrum_eq_reachableSpectra_of_pos hP
  have hR : Realizes h P y := (hh.toIsNeoclassical.realizes_iff_mem_span hP hy).2 (hSp ▸ hmem)
  refine ⟨h, hh.toIsNeoclassical, ?_⟩
  filter_upwards [hh.toIsNeoclassical.eventually_spectrum_subset hP, eventually_mem_orthant hP]
    with Q hQ hQo
  exact hR.mono_spectrum hh.toIsNeoclassical hP hh.toIsNeoclassical hQo hQ

/-- At prices not in general position no output is regularly solvable: regular solvability
forces general position of the prices (`regularlySolvable_iff`). -/
theorem not_regularlySolvable (hP : ¬ PricesGeneralPosition P) (y : Fin T → ℝ) :
    ¬ RegularlySolvable P y :=
  fun hy => hP (regularlySolvable_iff.1 hy).1

/-- The output `y = 1` is neoclassically solvable at any positive prices: `[T]` is a reachable
spectrum (vacuously) and `1 = 1_{[T]}`. With `not_regularlySolvable`, neoclassical and regular
solvability differ at every positive `P` not in general position. -/
theorem neoSolvable_one (hP : ∀ t, P t ∈ orthant) : NeoSolvable P fun _ => 1 := by
  refine (neoSolvable_iff_mem_span_reachableSpectra hP fun _ => zero_le_one).2
    (Submodule.subset_span ⟨Finset.univ, fun t _ s hs => absurd (Finset.mem_univ s) hs, ?_⟩)
  ext t
  simp

/-! ### Reachable spectra near `P` -/

/-- Covering is a closed condition on the prices: `Covers Q t s r` says that
`(Q, μ) ↦ Q t - (μ Q s + (1 - μ) Q r)` is `≥ 0` for some `μ ∈ [0, 1]`, a projection of a closed
set along the compact `[0, 1]`. -/
theorem isClosed_setOf_covers (t s r : Fin T) :
    IsClosed {Q : Fin T → ℝ × ℝ | Covers Q t s r} := by
  classical
  haveI : CompactSpace (Icc (0 : ℝ) 1) := isCompact_iff_compactSpace.mp isCompact_Icc
  have hA : IsClosed {p : (Fin T → ℝ × ℝ) × Icc (0 : ℝ) 1 |
      (1 - (p.2 : ℝ)) • p.1 s + (p.2 : ℝ) • p.1 r ≤ p.1 t} := by
    refine isClosed_le ?_ ?_ <;> fun_prop
  have hset : {Q : Fin T → ℝ × ℝ | Covers Q t s r} =
      Prod.fst '' {p : (Fin T → ℝ × ℝ) × Icc (0 : ℝ) 1 |
        (1 - (p.2 : ℝ)) • p.1 s + (p.2 : ℝ) • p.1 r ≤ p.1 t} := by
    ext Q
    simp only [mem_setOf_eq, mem_image, Covers, segment_eq_image]
    constructor
    · rintro ⟨q, ⟨θ, hθ, rfl⟩, hq⟩
      exact ⟨(Q, ⟨θ, hθ⟩), hq, rfl⟩
    · rintro ⟨⟨Q', θ⟩, hp, rfl⟩
      exact ⟨_, ⟨θ, θ.2, rfl⟩, hp⟩
  rw [hset]
  exact isClosedMap_fst_of_compactSpace _ hA

/-- **`Sp(P)` does not shrink near `P`.** Each of the finitely many conditions `¬ Covers P t s r`
is open (`isClosed_setOf_covers`), so all that hold at `P` hold near `P`, and a set reachable at
`P` stays reachable. -/
theorem eventually_reachableSpectra_subset :
    ∀ᶠ Q in 𝓝 P, reachableSpectra P ⊆ reachableSpectra Q := by
  have H : ∀ t s r, ∀ᶠ Q in 𝓝 P, ¬ Covers P t s r → ¬ Covers Q t s r := fun t s r => by
    by_cases hc : Covers P t s r
    · exact Eventually.of_forall fun _ h => absurd hc h
    · filter_upwards [(isClosed_setOf_covers t s r).isOpen_compl.mem_nhds hc] with Q hQ _
      exact hQ
  filter_upwards [eventually_all.2 fun t => eventually_all.2 fun s => eventually_all.2 (H t s)]
    with Q hQ S hS t ht s hs r hr
  exact hQ t s r (hS t ht s hs r hr)

/-! ### Prices in general position near `P` -/

/-- Strict covering is an open condition: if `P t - (a P s + b P r) ∈ ℝ²₊₊` for some weights
`a, b ≥ 0`, `a + b = 1`, then `Covers Q t s r` for all `Q` near `P`, with the same weights. -/
theorem eventually_covers {t s r : Fin T} {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b = 1)
    (h : P t - (a • P s + b • P r) ∈ orthant) : ∀ᶠ Q in 𝓝 P, Covers Q t s r := by
  have hcont : Continuous fun Q : Fin T → ℝ × ℝ => Q t - (a • Q s + b • Q r) := by fun_prop
  filter_upwards [(hcont.tendsto P).eventually (isOpen_orthant.mem_nhds h)] with Q hQ
  obtain ⟨hQ1, hQ2⟩ := mem_orthant.1 hQ
  refine ⟨a • Q s + b • Q r, ⟨a, b, ha, hb, hab, rfl⟩, ?_⟩
  simp only [Prod.fst_sub, Prod.snd_sub] at hQ1 hQ2
  exact Prod.le_def.2 ⟨by linarith, by linarith⟩

/-- Prices with pairwise distinct first and pairwise distinct second coordinates are dense: each
condition `(Q a).i ≠ (Q b).i`, `a ≠ b`, is the complement of a proper affine hyperplane. -/
theorem dense_injective_coords :
    Dense {Q : Fin T → ℝ × ℝ |
      Function.Injective (fun t => (Q t).1) ∧ Function.Injective (fun t => (Q t).2)} := by
  rw [dense_iff_inter_open]
  intro U hUo hUne
  obtain ⟨Q₀, hQ₀⟩ := hUne
  set Qε : ℝ → Fin T → ℝ × ℝ := fun ε t => Q₀ t + ε • ((t : ℝ), (t : ℝ))
  have hcont : Continuous Qε := by simp only [Qε]; fun_prop
  have hQε0 : Qε 0 = Q₀ := by funext t; simp [Qε]
  have hmem : ∀ᶠ ε in 𝓝[≠] (0 : ℝ), Qε ε ∈ U := by
    have := (hcont.tendsto 0).eventually (hQε0 ▸ hUo.mem_nhds hQ₀)
    exact this.filter_mono nhdsWithin_le_nhds
  -- for `a ≠ b`, the set of `ε` making the first (resp. second) coordinates of `Qε ε` agree at
  -- `a, b` is at most a point, hence eventually avoided in `𝓝[≠] 0`
  have hkey : ∀ a b : Fin T, a ≠ b → ∀ c : ℝ, ∀ᶠ ε in 𝓝[≠] (0 : ℝ), ε * ((a : ℝ) - b) ≠ c := by
    intro a b hab c
    have hd : (a : ℝ) - (b : ℝ) ≠ 0 :=
      sub_ne_zero.2 (fun h => hab (Fin.val_injective (by exact_mod_cast h)))
    rcases eq_or_ne c 0 with hc | hc
    · subst hc
      filter_upwards [self_mem_nhdsWithin] with ε hε
      exact mul_ne_zero hε hd
    · filter_upwards [(eventually_ne_nhds (div_ne_zero hc hd).symm).filter_mono
          nhdsWithin_le_nhds] with ε hε heq
      exact hε (by field_simp at heq ⊢; linarith)
  have hbad : ∀ᶠ ε in 𝓝[≠] (0 : ℝ),
      Function.Injective (fun t => (Qε ε t).1) ∧ Function.Injective (fun t => (Qε ε t).2) := by
    have h1 : ∀ᶠ ε in 𝓝[≠] (0 : ℝ), ∀ a b : Fin T, a ≠ b → (Qε ε a).1 ≠ (Qε ε b).1 := by
      refine eventually_all.2 fun a => eventually_all.2 fun b => ?_
      by_cases hab : a = b
      · exact Eventually.of_forall fun _ h => absurd hab h
      · filter_upwards [hkey a b hab ((Q₀ b).1 - (Q₀ a).1)] with ε hε _
        simp only [Qε, Prod.fst_add, Prod.smul_fst, smul_eq_mul]
        intro heq
        exact hε (by linarith)
    have h2 : ∀ᶠ ε in 𝓝[≠] (0 : ℝ), ∀ a b : Fin T, a ≠ b → (Qε ε a).2 ≠ (Qε ε b).2 := by
      refine eventually_all.2 fun a => eventually_all.2 fun b => ?_
      by_cases hab : a = b
      · exact Eventually.of_forall fun _ h => absurd hab h
      · filter_upwards [hkey a b hab ((Q₀ b).2 - (Q₀ a).2)] with ε hε _
        simp only [Qε, Prod.snd_add, Prod.smul_snd, smul_eq_mul]
        intro heq
        exact hε (by linarith)
    filter_upwards [h1, h2] with ε hε1 hε2
    exact ⟨fun a b hab => by_contra fun h => hε1 a b h hab,
      fun a b hab => by_contra fun h => hε2 a b h hab⟩
  obtain ⟨ε, hε⟩ := (hmem.and hbad).exists
  exact ⟨Qε ε, hε.1, hε.2⟩

/-- **Non-reachable sets stay non-reachable at nearby prices in general position.** If
`S ∉ Sp(P)`, then every neighbourhood of `P` contains prices `Q` in general position with
`S ∉ Sp(Q)`.

Proof: some `t ∈ S` covers `s, r ∉ S`: `q ≤ p_t` for a point `q ∈ [p_s, p_r]`. Replace `p_t` by
`(1 + δ) p_t` with small `δ > 0` (`t ≠ s, r`); then `p_t - q + δ p_t ∈ ℝ²₊₊` and the covering is
strict, hence holds on a neighbourhood (`eventually_covers`). Prices in general position are
dense there (`dense_injective_coords`). -/
theorem exists_pricesGeneralPosition_not_mem (hP : ∀ t, P t ∈ orthant) {S : Finset (Fin T)}
    (hS : S ∉ reachableSpectra P) {U : Set (Fin T → ℝ × ℝ)} (hU : U ∈ 𝓝 P) :
    ∃ Q ∈ U, PricesGeneralPosition Q ∧ S ∉ reachableSpectra Q := by
  simp only [reachableSpectra, mem_setOf_eq, IsReachable, not_forall, not_not] at hS ⊢
  obtain ⟨t, ht, s, hs, r, hr, q, ⟨a, b, ha, hb, hab, rfl⟩, hq⟩ := hS
  have hts : s ≠ t := fun h => hs (h ▸ ht)
  have htr : r ≠ t := fun h => hr (h ▸ ht)
  -- `Q_δ`: the price `p_t` scaled by `1 + δ`
  set Qδ : ℝ → Fin T → ℝ × ℝ := fun δ => Function.update P t ((1 + δ) • P t)
  have hcont : Continuous Qδ := by
    simp only [Qδ]
    fun_prop
  have hQ0 : Qδ 0 = P := by simp [Qδ]
  obtain ⟨δ, hδU, hδ⟩ : ∃ δ, Qδ δ ∈ interior U ∧ 0 < δ :=
    ((((hcont.tendsto 0).eventually (hQ0 ▸ interior_mem_nhds.2 hU)).filter_mono
      nhdsWithin_le_nhds).and (self_mem_nhdsWithin (s := Ioi (0 : ℝ)))).exists
  set Q₀ := Qδ δ
  have hQ₀o : ∀ u, Q₀ u ∈ orthant := fun u => by
    by_cases hu : u = t
    · subst hu; simpa [Q₀, Qδ] using smul_mem_orthant (by linarith) (hP u)
    · simpa [Q₀, Qδ, hu] using hP u
  -- strict covering at `Q₀`
  have hstrict : Q₀ t - (a • Q₀ s + b • Q₀ r) ∈ orthant := by
    simp only [Q₀, Qδ, Function.update_self, Function.update_of_ne hts,
      Function.update_of_ne htr]
    obtain ⟨h1, h2⟩ := mem_orthant.1 (hP t)
    obtain ⟨hq1, hq2⟩ := Prod.le_def.1 hq
    simp only [Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd, smul_eq_mul] at hq1 hq2
    refine mem_orthant.2 ⟨?_, ?_⟩ <;> simp <;> nlinarith
  have hV : interior U ∩ {Q | Covers Q t s r ∧ ∀ u, Q u ∈ orthant} ∈ 𝓝 Q₀ :=
    inter_mem (isOpen_interior.mem_nhds hδU)
      ((eventually_covers ha hb hab hstrict).and (eventually_mem_orthant hQ₀o))
  obtain ⟨Q, ⟨hQU, hQc, hQo⟩, hQ1, hQ2⟩ := mem_closure_iff_nhds.1 (dense_injective_coords Q₀) _ hV
  exact ⟨Q, interior_subset hQU, ⟨hQo, hQ1, hQ2⟩, t, ht, s, hs, r, hr, hQc⟩

end NeoTiling
