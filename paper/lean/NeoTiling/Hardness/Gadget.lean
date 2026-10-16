import NeoTiling.Core.Closure

/-!
# The paraboloid gadget

Planar points are lifted to the paraboloid along `𝟙 = (1, 1, 1)`:
`lift a = (a₀, a₁, -a₀ - a₁) + (1 + |a|²) 𝟙`. For a centre `c` the covector `wit c` satisfies
`⟨wit c, lift a⟩ = 3 (1 + |a - c|² - |c|²)` and `⟨wit c, 𝟙⟩ = 3`, and `wit c ≥ 0` for
`|c₀| + |c₁| ≤ 1/4`. So a disk centred at `c` is a witness: a point lifted from inside the disk
lies below the points lifted from outside.

A gadget on a graph with edges `{eu k, ev k}`: a marker `(1/4) 𝟙` below everything, a reward
`lift (a v)` at every vertex, a heavy point `lift (mid) + η k 𝟙` above the midpoint of every
edge. The output vector is `1` at the marker and the heavy points and `1 - s v` at the reward `v`.

`Gadget.mem_cone_iff`: if the heavy points lie above the chords (`η k > |a_u - a_v|²/4`) and every
edge has, for every independent set `I`, a disk that is deep at its midpoint and avoids the
rewards of `I` (`Gadget.Valid`), then the output vector lies in the cone of (weakly) reachable
spectra iff `s` lies in the stable set polytope. The disks may depend on `I`: this is what lets
edges cross.
-/

set_option linter.unusedSectionVars false

namespace NeoTiling.NPHardness

open Finset

/-! ### Two modes -/

/-- `Ok b u`: `0 < u` in the strict mode (`b = true`), `0 ≤ u` in the weak mode. -/
def Ok (b : Bool) (u : ℝ) : Prop := if b then 0 < u else 0 ≤ u

/-- Reachability with `Ok b` witnesses: `IsReachable` for `b = true`, `IsWeakReachable` for
`b = false`. -/
def IsReachableB {d T : ℕ} (b : Bool) (P : Fin T → Fin d → ℝ) (S : Finset (Fin T)) : Prop :=
  ∀ t ∈ S, ∃ ξ : Fin d → ℝ, 0 ≤ ξ ∧ ξ ≠ 0 ∧ ∀ s ∉ S, Ok b (ξ ⬝ᵥ (P s - P t))

theorem Ok.of_pos {b : Bool} {u : ℝ} (h : 0 < u) : Ok b u := by cases b <;> simp [Ok, h, h.le]

theorem Ok.nonneg {b : Bool} {u : ℝ} (h : Ok b u) : 0 ≤ u := by
  cases b <;> simp [Ok] at h <;> linarith

/-! ### The plane and the paraboloid -/

/-- Squared Euclidean norm in the plane. -/
def sqn (a : Fin 2 → ℝ) : ℝ := a 0 ^ 2 + a 1 ^ 2

/-- Midpoint of two planar points. -/
noncomputable def mid (a b : Fin 2 → ℝ) : Fin 2 → ℝ := fun i => (a i + b i) / 2

/-- The vector `𝟙 = (1, 1, 1)`. -/
def one3 : Fin 3 → ℝ := fun _ => 1

/-- Lift of a planar point to the paraboloid. -/
def lift (a : Fin 2 → ℝ) : Fin 3 → ℝ := ![a 0, a 1, -a 0 - a 1] + (1 + sqn a) • one3

/-- The witness of the disk centred at `c`. -/
def wit (c : Fin 2 → ℝ) : Fin 3 → ℝ :=
  ![1 - 4 * c 0 + 2 * c 1, 1 - 4 * c 1 + 2 * c 0, 1 + 2 * c 0 + 2 * c 1]

/-- **The witness of a disk.** `⟨wit c, lift a - (lift m + η 𝟙)⟩ = 3 (|a - c|² - η - |m - c|²)`:
the disk centred at `c` separates `a` from the point at height `η` above `m`. -/
theorem wit_dot (c m a : Fin 2 → ℝ) (η : ℝ) :
    wit c ⬝ᵥ (lift a - (lift m + η • one3)) = 3 * (sqn (a - c) - η - sqn (m - c)) := by
  simp [dotProduct, Fin.sum_univ_three, lift, wit, sqn, one3, Matrix.vecHead, Matrix.vecTail]
  ring

/-- For a centre in the box `1/4` the witness is a nonzero covector `≥ 0`. -/
theorem wit_nonneg_ne_zero {c : Fin 2 → ℝ} (hc : |c 0| + |c 1| ≤ 1 / 4) :
    0 ≤ wit c ∧ wit c ≠ 0 := by
  have := abs_nonneg (c 0); have := abs_nonneg (c 1)
  have := abs_le.mp (le_refl |c 0|); have := abs_le.mp (le_refl |c 1|)
  refine ⟨fun i => ?_, fun h => ?_⟩
  · fin_cases i <;> simp [wit] <;> linarith
  · have := congrFun h 2; simp [wit] at this; linarith

/-- A nonzero covector `ξ ≥ 0` is positive on vectors with positive coordinates. -/
theorem dot_pos {ξ x : Fin 3 → ℝ} (hξ0 : 0 ≤ ξ) (hξ : ξ ≠ 0) (hx : ∀ i, 0 < x i) :
    0 < ξ ⬝ᵥ x := by
  obtain ⟨j, hj⟩ := Function.ne_iff.mp hξ
  exact Finset.sum_pos' (fun i _ => mul_nonneg (hξ0 i) (hx i).le)
    ⟨j, Finset.mem_univ _, mul_pos ((hξ0 j).lt_of_ne' hj) (hx j)⟩

/-- **The chord covers the point above its midpoint.** For `q = lift (mid a b) + η 𝟙` with
`η > |a - b|²/4` no `ξ ≥ 0, ξ ≠ 0` has both `⟨ξ, lift a - q⟩ ≥ 0` and `⟨ξ, lift b - q⟩ ≥ 0`:
by `lift a + lift b = 2 lift (mid a b) + (|a - b|²/2) 𝟙` their sum is
`(|a - b|²/2 - 2η) ⟨ξ, 𝟙⟩ < 0`. -/
theorem not_both_nonneg {a b : Fin 2 → ℝ} {η : ℝ} (hη : sqn (a - b) / 4 < η)
    {ξ : Fin 3 → ℝ} (hξ0 : 0 ≤ ξ) (hξ : ξ ≠ 0) :
    ¬ (0 ≤ ξ ⬝ᵥ (lift a - (lift (mid a b) + η • one3)) ∧
        0 ≤ ξ ⬝ᵥ (lift b - (lift (mid a b) + η • one3))) := by
  rintro ⟨h1, h2⟩
  have hs := dot_pos hξ0 hξ (x := one3) fun _ => one_pos
  simp [dotProduct, Fin.sum_univ_three, lift, mid, sqn, one3, Matrix.vecHead, Matrix.vecTail]
    at h1 h2 hs hη
  nlinarith [mul_pos (sub_pos.2 hη) hs]

/-! ### The stable set polytope -/

variable {V E : Type*} [Fintype V] [DecidableEq V] [Fintype E]

/-- `I` is independent for the edges `{eu k, ev k}`. -/
def IsIndep (eu ev : E → V) (I : Finset V) : Prop := ∀ k, ¬ (eu k ∈ I ∧ ev k ∈ I)

/-- `s` lies in the stable set polytope: a convex combination of indicators of independent
sets. -/
def InStab (eu ev : E → V) (s : V → ℝ) : Prop :=
  ∃ μ : Finset V → ℝ, (∀ I, 0 ≤ μ I) ∧ (∀ I, μ I ≠ 0 → IsIndep eu ev I) ∧ ∑ I, μ I = 1 ∧
    ∀ v, s v = ∑ I, if v ∈ I then μ I else 0

/-! ### The gadget -/

/-- The output vector for `s`: `1` at the marker (`none`) and at the heavy points, `1 - s v` at
the reward `v`. -/
def output (s : V → ℝ) : Option (V ⊕ E) → ℝ
  | none => 1
  | some (.inl v) => 1 - s v
  | some (.inr _) => 1

/-- A gadget: a graph with edges `{eu k, ev k}`, a planar point `a v` for every vertex and a
height `η k` for every edge. -/
structure Gadget (V E : Type*) where
  eu : E → V
  ev : E → V
  a : V → Fin 2 → ℝ
  η : E → ℝ

namespace Gadget

variable (Γ : Gadget V E)

/-- The prices: the marker (`none`), the rewards and the heavy points. -/
noncomputable def price : Option (V ⊕ E) → Fin 3 → ℝ
  | none => (1 / 4 : ℝ) • one3
  | some (.inl v) => lift (Γ.a v)
  | some (.inr k) => lift (mid (Γ.a (Γ.eu k)) (Γ.a (Γ.ev k))) + Γ.η k • one3

/-- The hypotheses of the gadget theorem. The rewards are distinct points of the box
`|a₀| + |a₁| ≤ 1/8`; the heavy point of an edge lies above its chord; for every independent set
`I` some disk centred in the box `1/4` avoids the rewards of `I` and is deeper than `η k` at the
midpoint of the edge. -/
structure Valid : Prop where
  box : ∀ v, |Γ.a v 0| + |Γ.a v 1| ≤ 1 / 8
  inj : Function.Injective Γ.a
  high : ∀ k, sqn (Γ.a (Γ.eu k) - Γ.a (Γ.ev k)) / 4 < Γ.η k
  disks : ∀ k (I : Finset V), IsIndep Γ.eu Γ.ev I → ∃ c : Fin 2 → ℝ, |c 0| + |c 1| ≤ 1 / 4 ∧
    ∀ w ∈ I, Γ.η k + sqn (mid (Γ.a (Γ.eu k)) (Γ.a (Γ.ev k)) - c) < sqn (Γ.a w - c)

variable {Γ}

/-- The marker `(1/4) 𝟙` is coordinatewise strictly below every other price: the coordinates of
`lift a` are `≥ 1 - |a₀| - |a₁| ≥ 7/8` in the box, and the heights are positive. -/
theorem price_none_lt (hΓ : Γ.Valid) {x : Option (V ⊕ E)} (hx : x ≠ none) (i : Fin 3) :
    Γ.price none i < Γ.price x i := by
  have hlift : ∀ a : Fin 2 → ℝ, |a 0| + |a 1| ≤ 1 / 8 → ∀ i, 7 / 8 ≤ lift a i := by
    intro a ha i
    have := abs_le.mp (le_refl |a 0|); have := abs_le.mp (le_refl |a 1|)
    fin_cases i <;> simp [lift, sqn, one3] <;> nlinarith [sq_nonneg (a 0), sq_nonneg (a 1)]
  rcases x with _ | v | k
  · exact absurd rfl hx
  · simpa [price, one3] using (by linarith [hlift _ (hΓ.box v) i] : 1 / 4 < lift (Γ.a v) i)
  · have hm : |mid (Γ.a (Γ.eu k)) (Γ.a (Γ.ev k)) 0| + |mid (Γ.a (Γ.eu k)) (Γ.a (Γ.ev k)) 1|
        ≤ 1 / 8 := by
      simp only [mid, abs_div, abs_two]
      linarith [hΓ.box (Γ.eu k), hΓ.box (Γ.ev k), abs_add_le (Γ.a (Γ.eu k) 0) (Γ.a (Γ.ev k) 0),
        abs_add_le (Γ.a (Γ.eu k) 1) (Γ.a (Γ.ev k) 1)]
    have h1 := hlift _ hm i
    have h2 : 0 ≤ sqn (Γ.a (Γ.eu k) - Γ.a (Γ.ev k)) := by unfold sqn; positivity
    simp only [price, Pi.add_apply, Pi.smul_apply, one3, smul_eq_mul] at h1 ⊢
    linarith [hΓ.high k]

/-- All prices are positive. -/
theorem price_pos (hΓ : Γ.Valid) (x : Option (V ⊕ E)) (i : Fin 3) : 0 < Γ.price x i := by
  have h : (0 : ℝ) < Γ.price none i := by simp [price, one3]
  by_cases hx : x = none
  · exact hx ▸ h
  · exact h.trans (price_none_lt hΓ hx i)

/-- **The marker is in every nonempty spectrum**: a witness `ξ ≥ 0, ξ ≠ 0` of any price would
give `⟨ξ, p_marker - p_t⟩ < 0`. -/
theorem marker_mem (hΓ : Γ.Valid) {b : Bool} {T : ℕ} {e : Option (V ⊕ E) ≃ Fin T}
    {S : Finset (Fin T)} (hS : IsReachableB b (fun t => Γ.price (e.symm t)) S) {t : Fin T}
    (ht : t ∈ S) : e none ∈ S := by
  by_contra hn
  obtain ⟨ξ, h0, hne, h⟩ := hS t ht
  by_cases hx : e.symm t = none
  · exact hn (e.symm_apply_eq.mp hx ▸ ht)
  have hge := (h (e none) hn).nonneg
  have hlt := dot_pos h0 hne fun i => sub_pos.2 (price_none_lt hΓ hx i)
  simp only [Equiv.symm_apply_apply, dotProduct, Fin.sum_univ_three, Pi.sub_apply] at hge hlt
  linarith

/-- **The rewards outside a spectrum with all heavy points are independent**: if both ends of
the edge `k` were outside, the witness of the heavy point would contradict
`not_both_nonneg`. -/
theorem indep_outside (hΓ : Γ.Valid) {b : Bool} {T : ℕ} {e : Option (V ⊕ E) ≃ Fin T}
    {S : Finset (Fin T)} (hS : IsReachableB b (fun t => Γ.price (e.symm t)) S)
    (hheavy : ∀ k, e (some (.inr k)) ∈ S) :
    IsIndep Γ.eu Γ.ev (univ.filter fun v => e (some (.inl v)) ∉ S) := by
  intro k ⟨h1, h2⟩
  simp only [mem_filter, mem_univ, true_and] at h1 h2
  obtain ⟨ξ, h0, hne, h⟩ := hS _ (hheavy k)
  have e1 := h _ h1; have e2 := h _ h2
  simp only [Equiv.symm_apply_apply, price] at e1 e2
  exact not_both_nonneg (hΓ.high k) h0 hne ⟨e1.nonneg, e2.nonneg⟩

/-- **The complement of the rewards of an independent set `I` is a spectrum.** Strict
witnesses: `𝟙` for the marker (all other prices lie strictly above it), `wit (a v)` for a
reward `v ∉ I` (`⟨wit (a v), lift (a w) - lift (a v)⟩ = 3 |a w - a v|² > 0`), the disk of
`Valid.disks` for a heavy point. -/
theorem compl_mem (hΓ : Γ.Valid) (b : Bool) {T : ℕ} (e : Option (V ⊕ E) ≃ Fin T)
    {I : Finset V} (hI : IsIndep Γ.eu Γ.ev I) :
    IsReachableB b (fun t => Γ.price (e.symm t)) (univ \ I.image fun v => e (some (.inl v))) := by
  intro t ht
  have hnot : ∀ s ∉ (univ \ I.image fun v => e (some (.inl v))), ∃ w ∈ I, e (some (.inl w)) = s :=
    fun s hs => by simpa using hs
  rcases hx : e.symm t with _ | v | k
  · have h1 : (0 : Fin 3 → ℝ) ≤ one3 ∧ one3 ≠ 0 :=
      ⟨fun i => by simp [one3], fun h0 => by simpa [one3] using congrFun h0 0⟩
    refine ⟨one3, h1.1, h1.2, fun s hs => ?_⟩
    obtain ⟨w, _, rfl⟩ := hnot s hs
    simp only [Equiv.symm_apply_apply, hx]
    exact Ok.of_pos (dot_pos h1.1 h1.2 fun i => sub_pos.2 (price_none_lt hΓ (by simp) i))
  · have hvI : v ∉ I := fun hv => by simp [e.symm_apply_eq.mp hx] at ht; exact ht hv
    obtain ⟨h0, hne⟩ := wit_nonneg_ne_zero (c := Γ.a v) (by linarith [hΓ.box v])
    refine ⟨wit (Γ.a v), h0, hne, fun s hs => ?_⟩
    obtain ⟨w, hwI, rfl⟩ := hnot s hs
    have hpos : 0 < sqn (Γ.a w - Γ.a v) := by
      obtain ⟨i, hi⟩ := Function.ne_iff.mp (fun h => hvI (hΓ.inj h ▸ hwI) : Γ.a w ≠ Γ.a v)
      have := sub_ne_zero.mpr hi
      fin_cases i <;> simp [sqn] at this ⊢ <;> positivity
    have := wit_dot (Γ.a v) (Γ.a v) (Γ.a w) 0
    simp only [zero_smul, add_zero, sub_self, sub_zero] at this
    simp only [Equiv.symm_apply_apply, hx, price]
    exact Ok.of_pos (by simp [sqn] at this hpos ⊢; nlinarith)
  · obtain ⟨c, hc, hcd⟩ := hΓ.disks k I hI
    refine ⟨wit c, (wit_nonneg_ne_zero hc).1, (wit_nonneg_ne_zero hc).2, fun s hs => ?_⟩
    obtain ⟨w, hwI, rfl⟩ := hnot s hs
    have := wit_dot c (mid (Γ.a (Γ.eu k)) (Γ.a (Γ.ev k))) (Γ.a w) (Γ.η k)
    simp only [Equiv.symm_apply_apply, hx, price]
    exact Ok.of_pos (by linarith [hcd w hwI])

variable (Γ)

/-- **The gadget theorem.** In both modes, the output vector for `s` lies in the cone of the
(weakly) reachable spectra iff `s` lies in the stable set polytope.
(→) Every nonempty spectrum of a decomposition contains the marker, so the weights sum to `1`;
then every spectrum contains all heavy points, and a heavy point is covered by the two ends of
its edge, so the rewards outside a spectrum form an independent set.
(←) The complement of the rewards of an independent set `I` is reachable: `𝟙` is a witness for
the marker, `wit (a v)` for a reward, the disk of `Valid.disks` for a heavy point. -/
theorem mem_cone_iff (hΓ : Γ.Valid) (b : Bool) {T : ℕ} (e : Option (V ⊕ E) ≃ Fin T)
    (s : V → ℝ) :
    (fun t => output (E := E) s (e.symm t)) ∈
        indicatorCone {S | IsReachableB b (fun t => Γ.price (e.symm t)) S} ↔
      InStab Γ.eu Γ.ev s := by
  classical
  set y : Fin T → ℝ := fun t => output (E := E) s (e.symm t) with hy_def
  have hyz : y (e none) = 1 := by simp [hy_def, output]
  have hyh : ∀ k, y (e (some (.inr k))) = 1 := fun k => by simp [hy_def, output]
  have hyr : ∀ v, y (e (some (.inl v))) = 1 - s v := fun v => by simp [hy_def, output]
  constructor
  · intro hy
    obtain ⟨m, hm0, hmA, -, hym⟩ := exists_coef_of_mem_indicatorCone hy
    -- keep only the spectra containing the marker: the others have zero weight or are empty
    set w : Finset (Fin T) → ℝ := fun S => if e none ∈ S then m S else 0 with hw
    have hw0 : ∀ S, 0 ≤ w S := fun S => by simp only [hw]; split_ifs <;> simp [hm0]
    have hyw : ∀ t, y t = ∑ S, w S * (if t ∈ S then 1 else 0) := fun t => by
      simp only [hym, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Set.indicator_apply,
        mem_coe, Pi.one_apply]
      refine Finset.sum_congr rfl fun S _ => ?_
      by_cases hm : m S = 0
      · simp [hw, hm]
      by_cases ht : t ∈ S
      · simp [hw, ht, marker_mem hΓ (hmA S hm) ht]
      · simp [ht]
    have hsum : ∑ S, w S = 1 := by
      rw [← hyz, hyw]; refine Finset.sum_congr rfl fun S _ => ?_
      by_cases hz : e none ∈ S <;> simp [hw, hz]
    -- the heavy points lie in every spectrum of positive weight
    have hheavy : ∀ S, w S ≠ 0 → ∀ k, e (some (.inr k)) ∈ S := by
      intro S hS k
      by_contra h
      have : ∑ S, w S * (if e (some (.inr k)) ∈ S then 1 else 0) < ∑ S, w S :=
        Finset.sum_lt_sum (fun S _ => by split_ifs <;> simp [hw0])
          ⟨S, mem_univ _, by simp [h, (hw0 S).lt_of_ne' hS]⟩
      rw [← hyw, hyh, hsum] at this
      exact lt_irrefl _ this
    -- `μ I`: the weight of the spectra whose rewards outside form `I`
    set F : Finset (Fin T) → Finset V := fun S => univ.filter fun v => e (some (.inl v)) ∉ S
      with hF
    set μ : Finset V → ℝ := fun I => ∑ S, if F S = I then w S else 0 with hμ
    have push : ∀ g : Finset V → ℝ, ∑ I, μ I * g I = ∑ S, w S * g (F S) := fun g => by
      simp only [hμ, Finset.sum_mul, ite_mul, zero_mul]; rw [Finset.sum_comm]; simp
    refine ⟨μ, fun I => Finset.sum_nonneg fun S _ => by split_ifs <;> simp [hw0], fun I hI => ?_,
      by simpa [hsum] using push 1, fun v => ?_⟩
    · obtain ⟨S, -, hS⟩ := Finset.exists_ne_zero_of_sum_ne_zero hI
      have hFS : F S = I := by by_contra h; simp [h] at hS
      have hwS : w S ≠ 0 := by simpa [hFS] using hS
      exact hFS ▸ indep_outside hΓ (hmA S fun h => hwS (by simp [hw, h])) (hheavy S hwS)
    · have h1 : ∀ S, (if v ∈ F S then w S else 0) =
          w S - w S * (if e (some (.inl v)) ∈ S then 1 else 0) := fun S => by
        by_cases h : e (some (.inl v)) ∈ S <;> simp [hF, h]
      have h2 := push fun I => if v ∈ I then 1 else 0
      simp only [mul_ite, mul_one, mul_zero] at h2
      rw [h2, Finset.sum_congr rfl fun S _ => h1 S, Finset.sum_sub_distrib, hsum, ← hyw, hyr]
      ring
  · rintro ⟨μ, hμ0, hμI, hμ1, hs⟩
    have hy : y = ∑ I, μ I • ((univ \ I.image fun v => e (some (.inl v)) : Finset (Fin T)) :
        Set (Fin T)).indicator 1 := by
      funext t
      obtain ⟨x, rfl⟩ := e.surjective t
      simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Set.indicator_apply,
        Finset.mem_coe, Pi.one_apply]
      rcases x with _ | v | k
      · simpa [hyz] using hμ1.symm
      · rw [hyr, hs]; conv_lhs => rw [← hμ1]
        rw [← Finset.sum_sub_distrib]
        exact Finset.sum_congr rfl fun I _ => by by_cases h : v ∈ I <;> simp [h]
      · simpa [hyh] using hμ1.symm
    rw [hy]
    exact Submodule.sum_mem _ fun I _ => smul_indicator_mem_indicatorCone (hμ0 I) fun h =>
      compl_mem hΓ b e (hμI I h)

/-- **Neoclassical solvability encodes the stable set polytope** (`s ≤ 1`). -/
theorem neoSolvable_iff (hΓ : Γ.Valid) {T : ℕ} (e : Option (V ⊕ E) ≃ Fin T) (s : V → ℝ)
    (hs : ∀ v, s v ≤ 1) :
    NeoSolvable (fun t => Γ.price (e.symm t)) (fun t => output (E := E) s (e.symm t)) ↔
      InStab Γ.eu Γ.ev s := by
  have hy : ∀ t, 0 ≤ output (E := E) s (e.symm t) := fun t => by
    rcases e.symm t with _ | v | k <;> simp [output, hs]
  rw [neoSolvable_iff_mem_indicatorCone (by norm_num) (fun t => price_pos hΓ _) hy,
    ← mem_cone_iff Γ hΓ true e s]
  simp only [reachableSpectra, IsReachable, IsReachableB, Ok, if_true]

/-- **Weak solvability encodes the stable set polytope** (`s ≤ 1`). -/
theorem weakSolvable_iff (hΓ : Γ.Valid) {T : ℕ} (e : Option (V ⊕ E) ≃ Fin T) (s : V → ℝ)
    (hs : ∀ v, s v ≤ 1) :
    WeakSolvable (fun t => Γ.price (e.symm t)) (fun t => output (E := E) s (e.symm t)) ↔
      InStab Γ.eu Γ.ev s := by
  have hy : ∀ t, 0 ≤ output (E := E) s (e.symm t) := fun t => by
    rcases e.symm t with _ | v | k <;> simp [output, hs]
  rw [NeoTiling.weakSolvable_iff (by norm_num) (fun t i => (price_pos hΓ _ i).le) hy,
    ← mem_cone_iff Γ hΓ false e s]
  simp only [weakReachableSpectra, IsWeakReachable, IsReachableB, Ok, Bool.false_eq_true,
    if_false]

end Gadget

end NeoTiling.NPHardness
