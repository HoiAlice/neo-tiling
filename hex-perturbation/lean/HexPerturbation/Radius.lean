import HexPerturbation.Proj
import HexPerturbation.LocalConstancy

namespace NeoTiling.HexPerturbation

open NeoTiling Real Filter Topology

variable {d T : ℕ}

/-- Some prices within `projDist`-distance `ρ` of `P` (at every `t`) make `y` weakly solvable. -/
def Feasible (P : Fin T → Fin d → ℝ) (y : Fin T → ℝ) (ρ : ℝ) : Prop :=
  ∃ Q : Fin T → Fin d → ℝ, (∀ t, Q t ∈ orthant d) ∧ (∀ t, projDist (Q t) (P t) ≤ ρ) ∧
    WeakSolvable Q y

/-- The `2T + d` homogenized vectors in `ℝ^{d+1}` at radius `ρ`: the lower corners
`(e^{-ρ} P t, 1)`, the upper corners `(e^{ρ} P t, 1)` and the coordinate directions `(e_i, 0)`. -/
noncomputable def cornerVec (P : Fin T → Fin d → ℝ) (ρ : ℝ) :
    Fin T ⊕ Fin T ⊕ Fin d → Fin (d + 1) → ℝ :=
  Sum.elim (fun t => Fin.snoc (exp (-ρ) • P t) 1)
    (Sum.elim (fun t => Fin.snoc (exp ρ • P t) 1) (fun i => Fin.snoc (Pi.single i 1) 0))

/-- Feasibility is monotone in the radius: the same prices work. -/
theorem Feasible.mono {P : Fin T → Fin d → ℝ} {y : Fin T → ℝ} {ρ ρ' : ℝ} (h : Feasible P y ρ)
    (hρ : ρ ≤ ρ') : Feasible P y ρ' := by
  obtain ⟨Q, hQ, hd, hw⟩ := h
  exact ⟨Q, hQ, fun t => (hd t).trans hρ, hw⟩

/-- Feasibility is closed from the right: if every radius `> ρ` is feasible, so is `ρ`. Rescaling
factors `c` for the radii `ρ + 1/(n+1)` lie in a compact box; a limit point `c` has
`e^{-ρ} ≤ c t ≤ e^{ρ}`, and `WeakSolvable` (membership in a closure) passes to the limit. -/
theorem feasible_of_forall_gt (hd : 2 ≤ d) (P : Fin T → Fin d → ℝ) (hP : ∀ t, P t ∈ orthant d)
    (y : Fin T → ℝ) (hy : ∀ t, 0 ≤ y t) {ρ : ℝ} (hρ : 0 ≤ ρ)
    (h : ∀ ρ', ρ < ρ' → Feasible P y ρ') : Feasible P y ρ := by
  have hn : ∀ n : ℕ, ∃ c : Fin T → ℝ, (∀ t, exp (-(ρ + 1 / ((n:ℝ) + 1))) ≤ c t ∧
      c t ≤ exp (ρ + 1 / ((n:ℝ) + 1))) ∧ WeakSolvable (fun t => c t • P t) y := fun n => by
    have hpos : (0:ℝ) < 1 / ((n:ℝ) + 1) := by positivity
    exact (proj_iff_scale hd P hP y hy (by linarith)).1 (h _ (by linarith))
  choose c hc hws using hn
  let K : Set (Fin T → ℝ) := Set.pi Set.univ (fun _ => Set.Icc (exp (-(ρ + 1))) (exp (ρ + 1)))
  have hcK : ∀ n, c n ∈ K := by
    intro n t _
    have h1 : 1 / ((n:ℝ) + 1) ≤ 1 := by
      rw [div_le_one (by positivity)]; linarith [(Nat.cast_nonneg n : (0:ℝ) ≤ n)]
    exact ⟨le_trans (exp_le_exp.2 (by linarith)) (hc n t).1,
      le_trans (hc n t).2 (exp_le_exp.2 (by linarith))⟩
  obtain ⟨c0, -, φ, hφ, hlim⟩ := (isCompact_univ_pi fun _ => isCompact_Icc).tendsto_subseq hcK
  have hε : Tendsto (fun n => 1 / (((φ n : ℕ) : ℝ) + 1)) atTop (𝓝 0) :=
    tendsto_one_div_add_atTop_nhds_zero_nat.comp hφ.tendsto_atTop
  have hcoord : ∀ t, Tendsto (fun n => c (φ n) t) atTop (𝓝 (c0 t)) := fun t =>
    (continuous_apply t).continuousAt.tendsto.comp hlim
  have hlo : Tendsto (fun n => exp (-(ρ + 1 / (((φ n : ℕ) : ℝ) + 1)))) atTop (𝓝 (exp (-ρ))) := by
    simpa using ((by fun_prop : Continuous fun x : ℝ => exp (-(ρ + x))).tendsto 0).comp hε
  have hhi : Tendsto (fun n => exp (ρ + 1 / (((φ n : ℕ) : ℝ) + 1))) atTop (𝓝 (exp ρ)) := by
    simpa using ((by fun_prop : Continuous fun x : ℝ => exp (ρ + x)).tendsto 0).comp hε
  have hcl : IsClosed {c : Fin T → ℝ | WeakSolvable (fun t => c t • P t) y} :=
    isClosed_closure.preimage (by fun_prop)
  refine (proj_iff_scale hd P hP y hy hρ).2 ⟨c0, fun t => ⟨?_, ?_⟩, ?_⟩
  · exact le_of_tendsto_of_tendsto' hlo (hcoord t) (fun n => (hc _ t).1)
  · exact le_of_tendsto_of_tendsto' (hcoord t) hhi (fun n => (hc _ t).2)
  · exact hcl.mem_of_tendsto hlim (Eventually.of_forall fun n => hws _)

/-- The `2T` corners at radius `ρ`: lower corners `e^{-ρ} P t`, then upper corners `e^{ρ} P t`. -/
noncomputable abbrev corners (P : Fin T → Fin d → ℝ) (ρ : ℝ) : Fin (T + T) → Fin d → ℝ :=
  Fin.append (fun t => exp (-ρ) • P t) (fun t => exp ρ • P t)

/-- The index in `cornerVec` of the corner `r`. -/
def cornerIdx : Fin (T + T) → Fin T ⊕ Fin T ⊕ Fin d :=
  Fin.addCases Sum.inl fun t => Sum.inr (Sum.inl t)

/-- The homogenized corner `r` is `(corners P ρ r, 1)`. -/
theorem cornerVec_cornerIdx (P : Fin T → Fin d → ℝ) (ρ : ℝ) (r : Fin (T + T)) :
    cornerVec P ρ (cornerIdx r) = Fin.snoc (corners P ρ r) 1 := by
  induction r using Fin.addCases with
  | left t => simp [cornerIdx, cornerVec, corners, Fin.append_left]
  | right t =>
    simp only [cornerIdx, corners, Fin.addCases_right, Fin.append_right]
    simp [cornerVec]

/-- Each homogenized corner vector is continuous in the radius. -/
theorem continuous_cornerVec (P : Fin T → Fin d → ℝ) (j : Fin T ⊕ Fin T ⊕ Fin d) :
    Continuous fun ρ => cornerVec P ρ j := by
  rcases j with t | t | i
  · refine continuous_pi fun k => Fin.lastCases ?_ (fun i => ?_) k
    · simp [cornerVec, Fin.snoc_last]; exact continuous_const
    · simp [cornerVec, Fin.snoc_castSucc]; fun_prop
  · refine continuous_pi fun k => Fin.lastCases ?_ (fun i => ?_) k
    · simp [cornerVec, Fin.snoc_last]; exact continuous_const
    · simp [cornerVec, Fin.snoc_castSucc]; fun_prop
  · simp only [cornerVec, Sum.elim_inr]; exact continuous_const

/-- With at least one point the homogenized corner vectors span `ℝ^{d+1}`: they contain the
`(e_i, 0)` and one `(x, 1)`. -/
theorem span_cornerVec (P : Fin T → Fin d → ℝ) (t₀ : Fin T) (ρ : ℝ) :
    Submodule.span ℝ (Set.range (cornerVec P ρ)) = ⊤ := by
  have hi : ∀ i : Fin d, (Pi.single (Fin.castSucc i) 1 : Fin (d + 1) → ℝ) ∈
      Submodule.span ℝ (Set.range (cornerVec P ρ)) := by
    intro i
    have : (Pi.single (Fin.castSucc i) 1 : Fin (d + 1) → ℝ) =
        cornerVec P ρ (Sum.inr (Sum.inr i)) := by
      ext k
      refine Fin.lastCases ?_ (fun j => ?_) k
      · simp [cornerVec, Fin.snoc_last]
      · simp [cornerVec, Fin.snoc_castSucc, Pi.single_apply]
    rw [this]; exact Submodule.subset_span ⟨_, rfl⟩
  have hl : (Pi.single (Fin.last d) 1 : Fin (d + 1) → ℝ) ∈
      Submodule.span ℝ (Set.range (cornerVec P ρ)) := by
    have : (Pi.single (Fin.last d) 1 : Fin (d + 1) → ℝ) = cornerVec P ρ (Sum.inl t₀) -
        ∑ i, (exp (-ρ) * P t₀ i) • (Pi.single (Fin.castSucc i) 1 : Fin (d + 1) → ℝ) := by
      ext k
      refine Fin.lastCases ?_ (fun j => ?_) k
      · simp [cornerVec, Fin.snoc_last, Finset.sum_apply, Fin.castSucc_ne_last]
      · simp [cornerVec, Fin.snoc_castSucc, Finset.sum_apply, Pi.single_apply,
          Fin.castSucc_inj, Fin.castSucc_ne_last]
    rw [this]
    exact Submodule.sub_mem _ (Submodule.subset_span ⟨_, rfl⟩)
      (Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (hi i))
  rw [eq_top_iff, ← (Pi.basisFun ℝ (Fin (d + 1))).span_eq, Submodule.span_le]
  rintro _ ⟨k, rfl⟩
  simp only [Pi.basisFun_apply]
  exact Fin.lastCases hl hi k

/-- **Homogenization of a witness.** `ξ ≥ 0`, `ξ ≠ 0` with `ξ ⬝ᵥ (W s - W t) ≥ 0` off `S` is
the same as a functional `η` on `ℝ^{d+1}` vanishing on `(W t, 1)`, nonnegative on `(W s, 1)`
off `S` and on every `(e_i, 0)`, and nonzero on some `(e_i, 0)`: take `η = (ξ, -ξ ⬝ᵥ W t)`, and
back `ξ i = η (e_i, 0)`. -/
theorem witness_iff_homogeneous {N : ℕ} (W : Fin N → Fin d → ℝ) (S : Finset (Fin N))
    (t : Fin N) :
    (∃ ξ : Fin d → ℝ, 0 ≤ ξ ∧ ξ ≠ 0 ∧ ∀ s ∉ S, 0 ≤ ξ ⬝ᵥ (W s - W t)) ↔
      ∃ η : Fin (d + 1) → ℝ, η ⬝ᵥ Fin.snoc (W t) 1 = 0 ∧
        (∀ s ∉ S, 0 ≤ η ⬝ᵥ Fin.snoc (W s) 1) ∧
        (∀ i, 0 ≤ η ⬝ᵥ Fin.snoc (Pi.single i 1) 0) ∧
        ∃ i, η ⬝ᵥ Fin.snoc (Pi.single i 1) 0 ≠ 0 := by
  have key : ∀ (a : Fin d → ℝ) (b : ℝ) (x : Fin d → ℝ) (c : ℝ),
      (Fin.snoc a b : Fin (d + 1) → ℝ) ⬝ᵥ Fin.snoc x c = a ⬝ᵥ x + b * c := by
    intro a b x c
    simp [dotProduct, Fin.sum_univ_castSucc, Fin.snoc_castSucc, Fin.snoc_last]
  have e2 : ∀ (ξ : Fin d → ℝ) b i,
      (Fin.snoc ξ b : Fin (d + 1) → ℝ) ⬝ᵥ Fin.snoc (Pi.single i 1) 0 = ξ i := by
    intro ξ b i; rw [key]; simp
  constructor
  · rintro ⟨ξ, h0, hne, hS⟩
    have e : ∀ s, (Fin.snoc ξ (-(ξ ⬝ᵥ W t)) : Fin (d + 1) → ℝ) ⬝ᵥ Fin.snoc (W s) 1
        = ξ ⬝ᵥ (W s - W t) := by
      intro s; rw [key, dotProduct_sub]; ring
    refine ⟨Fin.snoc ξ (-(ξ ⬝ᵥ W t)), ?_, fun s hs => ?_, fun i => ?_, ?_⟩
    · rw [e]; simp
    · rw [e]; exact hS s hs
    · rw [e2]; exact h0 i
    · obtain ⟨i, hi⟩ := Function.ne_iff.1 hne
      exact ⟨i, by rw [e2]; exact hi⟩
  · rintro ⟨η, h1, h2, h3, i, hi⟩
    obtain ⟨ξ, b, rfl⟩ : ∃ (ξ : Fin d → ℝ) (b : ℝ), η = Fin.snoc ξ b :=
      ⟨fun j => η (Fin.castSucc j), η (Fin.last d), by
        ext k; refine Fin.lastCases ?_ (fun j => ?_) k <;> simp⟩
    refine ⟨ξ, fun j => ?_, ?_, fun s hs => ?_⟩
    · simpa [e2] using h3 j
    · intro h; apply hi; rw [e2]; exact congrFun h i
    · have := h2 s hs
      rw [key] at this h1
      rw [dotProduct_sub]; linarith

/-- **Weakly reachable spectra persist** near a radius `ρs` at which no determinant of the
homogenized corner vectors vanishes unless it vanishes identically: homogenize each witness
(`witness_iff_homogeneous`) and move it along with `ρ` (`eventually_exists_sign_eq`). -/
theorem eventually_isWeakReachable (P : Fin T → Fin d → ℝ) (t₀ : Fin T) {ρs : ℝ}
    (H : ∀ I : Fin (d + 1) → Fin T ⊕ Fin T ⊕ Fin d,
      (Matrix.of fun j => cornerVec P ρs (I j)).det = 0 →
        ∀ ρ, (Matrix.of fun j => cornerVec P ρ (I j)).det = 0)
    {S : Finset (Fin (T + T))} (hS : IsWeakReachable (corners P ρs) S) :
    ∀ᶠ ρ in 𝓝 ρs, IsWeakReachable (corners P ρ) S := by
  have hall : ∀ t ∈ S, ∀ᶠ ρ in 𝓝 ρs, ∃ ξ : Fin d → ℝ, 0 ≤ ξ ∧ ξ ≠ 0 ∧
      ∀ s ∉ S, 0 ≤ ξ ⬝ᵥ (corners P ρ s - corners P ρ t) := by
    intro t ht
    obtain ⟨η₀, h1, h2, h3, i₀, hi₀⟩ := (witness_iff_homogeneous _ S t).1 (hS t ht)
    filter_upwards [eventually_exists_sign_eq (cornerVec P) (continuous_cornerVec P)
      (span_cornerVec P t₀ ρs) H η₀] with ρ ⟨η, hη⟩
    refine (witness_iff_homogeneous _ S t).2 ⟨η, ?_, fun s hs => ?_, fun i => ?_, i₀, ?_⟩
    · have := hη (cornerIdx t)
      rw [cornerVec_cornerIdx, cornerVec_cornerIdx] at this
      rw [← _root_.sign_eq_zero_iff, this, _root_.sign_eq_zero_iff]; exact h1
    · have := hη (cornerIdx s)
      rw [cornerVec_cornerIdx, cornerVec_cornerIdx] at this
      rw [← _root_.sign_nonneg_iff, this, _root_.sign_nonneg_iff]; exact h2 s hs
    · have : SignType.sign (η ⬝ᵥ Fin.snoc (Pi.single i 1) 0) =
          SignType.sign (η₀ ⬝ᵥ Fin.snoc (Pi.single i 1) 0) := hη (Sum.inr (Sum.inr i))
      rw [← _root_.sign_nonneg_iff, this, _root_.sign_nonneg_iff]; exact h3 i
    · have : SignType.sign (η ⬝ᵥ Fin.snoc (Pi.single i₀ 1) 0) =
          SignType.sign (η₀ ⬝ᵥ Fin.snoc (Pi.single i₀ 1) 0) := hη (Sum.inr (Sum.inr i₀))
      rw [Ne, ← _root_.sign_eq_zero_iff, this, _root_.sign_eq_zero_iff]; exact hi₀
  exact (Filter.eventually_all_finset S).2 hall

/-- If `ρs > 0` is feasible and no determinant vanishes at `ρs` without vanishing identically,
then some smaller radius is feasible: the corner certificate `w` of `ρs` (`proj_iff_corners`) is
built from finitely many spectra, all of them still weakly reachable slightly below `ρs`
(`eventually_isWeakReachable`). -/
theorem exists_feasible_lt (hd : 2 ≤ d) (P : Fin T → Fin d → ℝ) (hP : ∀ t, P t ∈ orthant d)
    (y : Fin T → ℝ) (hy : ∀ t, 0 ≤ y t) {ρs : ℝ} (hρs : 0 < ρs) (hfeas : Feasible P y ρs)
    (H : ∀ I : Fin (d + 1) → Fin T ⊕ Fin T ⊕ Fin d,
      (Matrix.of fun j => cornerVec P ρs (I j)).det = 0 →
        ∀ ρ, (Matrix.of fun j => cornerVec P ρ (I j)).det = 0) :
    ∃ ρ, 0 ≤ ρ ∧ ρ < ρs ∧ Feasible P y ρ := by
  rcases isEmpty_or_nonempty (Fin T) with hT | ⟨⟨t₀⟩⟩
  · obtain ⟨Q, hQ, -, hW⟩ := hfeas
    exact ⟨0, le_rfl, hρs, Q, hQ, fun t => (IsEmpty.false t).elim, hW⟩
  obtain ⟨w, hw, h1, h2⟩ := (proj_iff_corners hd P hP y hy hρs.le).1 hfeas
  have hev : ∀ᶠ ρ in 𝓝 ρs, ∀ S ∈ weakReachableSpectra (corners P ρs),
      IsWeakReachable (corners P ρ) S :=
    (Set.toFinite _).eventually_all.2 fun S hS => eventually_isWeakReachable P t₀ H hS
  obtain ⟨ρ, hρ, hρI⟩ := ((hev.filter_mono nhdsWithin_le_nhds).and
    (Ioo_mem_nhdsLT (by linarith : ρs / 2 < ρs))).exists
  refine ⟨ρ, by linarith [hρI.1], hρI.2,
    (proj_iff_corners hd P hP y hy (by linarith [hρI.1])).2 ⟨w, ?_, h1, h2⟩⟩
  exact Submodule.span_mono (Set.image_mono hρ) hw

/-- **The least radius is a breakpoint.** If some radius is feasible, the feasible radii form a
closed ray `[ρ*, ∞)`, and either `ρ* = 0` or some `(d+1) × (d+1)` determinant of the homogenized
corner vectors vanishes at `ρ*` without vanishing identically in `ρ`.

Proof. Feasibility is monotone (`Feasible.mono`) and closed from the right
(`feasible_of_forall_gt`), so `ρ* = inf {ρ ≥ 0 | Feasible ρ}` is feasible and the feasible radii
are `[ρ*, ∞)`. If `ρ* > 0` and every determinant vanishing at `ρ*` vanished identically, a
smaller radius would be feasible (`exists_feasible_lt`), contradicting minimality. -/
theorem least_radius_breakpoint (hd : 2 ≤ d) (P : Fin T → Fin d → ℝ) (hP : ∀ t, P t ∈ orthant d)
    (y : Fin T → ℝ) (hy : ∀ t, 0 ≤ y t) (hfeas : ∃ ρ, 0 ≤ ρ ∧ Feasible P y ρ) :
    ∃ ρs, 0 ≤ ρs ∧ (∀ ρ, 0 ≤ ρ → (Feasible P y ρ ↔ ρs ≤ ρ)) ∧
      (ρs = 0 ∨ ∃ I : Fin (d + 1) → Fin T ⊕ Fin T ⊕ Fin d,
        (Matrix.of fun j => cornerVec P ρs (I j)).det = 0 ∧
          ∃ ρ, (Matrix.of fun j => cornerVec P ρ (I j)).det ≠ 0) := by
  obtain ⟨r0, hr0, hr0f⟩ := hfeas
  set A : Set ℝ := {ρ | 0 ≤ ρ ∧ Feasible P y ρ}
  have hne : A.Nonempty := ⟨r0, hr0, hr0f⟩
  have hbdd : BddBelow A := ⟨0, fun a ha => ha.1⟩
  have h0 : 0 ≤ sInf A := le_csInf hne fun a ha => ha.1
  have hF : Feasible P y (sInf A) := by
    refine feasible_of_forall_gt hd P hP y hy h0 fun ρ' hρ' => ?_
    obtain ⟨a, ha, hlt⟩ := exists_lt_of_csInf_lt hne hρ'
    exact ha.2.mono hlt.le
  refine ⟨sInf A, h0, fun ρ hρ => ⟨fun h => csInf_le hbdd ⟨hρ, h⟩, fun h => hF.mono h⟩, ?_⟩
  rcases eq_or_lt_of_le h0 with h | h
  · exact Or.inl h.symm
  right
  by_contra hcon
  push_neg at hcon
  obtain ⟨ρ, hρ0, hρlt, hρf⟩ := exists_feasible_lt hd P hP y hy h hF hcon
  exact absurd (csInf_le hbdd ⟨hρ0, hρf⟩) (not_le.2 hρlt)

end NeoTiling.HexPerturbation
