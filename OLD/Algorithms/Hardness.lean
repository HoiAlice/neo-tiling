import Algorithms.Cuts

/-!
# Hardness: a reduction from set cover

Sets `A j ⊆ Fin d` (`j : Fin n`, the sets containing the element `j`, each nonempty) and a
number `k` with `k ≤ |I| + #{j | A j ∩ I = ∅}` for every `I` (every `I` together with one set
per uncovered element is a cover, so the minimal cover size is such a `k`).

The prices: one index `s` with `p_s = 1`, and two copies `e j 0`, `e j 1` of every element
with `p^i = 1 + δ` for `i ∈ A j` and `p^i = M := (1 + δ)(1 + dδ)` otherwise. The dominance
relaxation asks every copy not to dominate `q_s` strictly: some `i` has `q^i_{e j c} ≤ q^i_s`.

Main results:

* `cover_bound`: `k ≤ ∑ᵢ xᵢ + ∑ⱼ (1 - max_{i ∈ A j} xᵢ)` for `x ∈ [0, 1]ᵈ` (layer cake: the
  right side is a convex combination of the values `|I| + #uncovered(I)`).
* `hardness_lower`: every such `Q` has `totalPert P Q ≥ k δ`.
-/

namespace NeoTiling

variable {d n T : ℕ}

/-- Peeling the lowest layer: with `I = {i | 0 < x i}`, `θ ≤ x` on `I` and
`x' = x - θ 1_I`, the maximum over `A` drops by `θ` exactly when `A` meets `I`. -/
theorem sup'_peel (A : Finset (Fin d)) (hA : A.Nonempty) (x : Fin d → ℝ) (hx0 : ∀ i, 0 ≤ x i)
    {θ : ℝ} (hθ : ∀ i, 0 < x i → θ ≤ x i) :
    A.sup' hA x = (if Disjoint A (Finset.univ.filter fun i => 0 < x i) then 0 else θ) +
      A.sup' hA (fun i => x i - if 0 < x i then θ else 0) := by
  split_ifs with h
  · have hz : ∀ i ∈ A, x i = 0 := fun i hi => by
      by_contra hne
      exact Finset.disjoint_left.1 h hi (by simp [lt_of_le_of_ne (hx0 i) (Ne.symm hne)])
    obtain ⟨a, ha⟩ := hA
    have h1 : A.sup' ⟨a, ha⟩ x = 0 := le_antisymm
      (Finset.sup'_le _ _ fun i hi => (hz i hi).le) (by simpa [hz a ha] using Finset.le_sup' x ha)
    have h2 : A.sup' ⟨a, ha⟩ (fun i => x i - if 0 < x i then θ else 0) = 0 := le_antisymm
      (Finset.sup'_le _ _ fun i hi => by simp [hz i hi])
      (by simpa [hz a ha] using Finset.le_sup' (fun i => x i - if 0 < x i then θ else 0) ha)
    rw [h1, h2]; simp
  · obtain ⟨i₀, hi₀, hp⟩ := Finset.not_disjoint_iff.1 h
    have hp : 0 < x i₀ := by simpa using hp
    have hle := Finset.le_sup' x hi₀
    have hle' := Finset.le_sup' (fun i => x i - if 0 < x i then θ else 0) hi₀
    simp only [if_pos hp] at hle'
    apply le_antisymm
    · refine Finset.sup'_le _ _ fun i hi => ?_
      have := Finset.le_sup' (fun i => x i - if 0 < x i then θ else 0) hi
      by_cases hi' : 0 < x i
      · simp only [if_pos hi'] at this; linarith
      · have : x i = 0 := le_antisymm (not_lt.1 hi') (hx0 i)
        linarith
    · have : A.sup' hA (fun i => x i - if 0 < x i then θ else 0) ≤ A.sup' hA x - θ := by
        refine Finset.sup'_le _ _ fun i hi => ?_
        have h3 := Finset.le_sup' x hi
        by_cases hi' : 0 < x i
        · simp only [if_pos hi']; linarith
        · simp only [if_neg hi']; linarith [hθ i₀ hp]
      linarith

/-- Scaled version of `cover_bound`, by induction on the number of positive coordinates:
`x = θ 1_I + x'` with `I = {x > 0}`, `θ = min_I x`, gives `f_c(x) = θ g(I) + f_{c-θ}(x')`. -/
theorem cover_bound_aux (A : Fin n → Finset (Fin d)) (hA : ∀ j, (A j).Nonempty) (k : ℕ)
    (hk : ∀ I : Finset (Fin d),
      (k : ℝ) ≤ I.card + (Finset.univ.filter fun j => Disjoint (A j) I).card) :
    ∀ m : ℕ, ∀ (c : ℝ) (x : Fin d → ℝ), 0 ≤ c → (∀ i, 0 ≤ x i) → (∀ i, x i ≤ c) →
      (Finset.univ.filter fun i => 0 < x i).card = m →
      c * k ≤ ∑ i, x i + ∑ j, (c - (A j).sup' (hA j) x) := by
  intro m
  induction m using Nat.strong_induction_on with
  | _ m ih =>
  intro c x hc hx0 hxc hm
  set I : Finset (Fin d) := Finset.univ.filter fun i => 0 < x i with hIdef
  by_cases hI : I.Nonempty
  · obtain ⟨i₀, hi₀I, hi₀⟩ := Finset.exists_mem_eq_inf' hI x
    set θ := I.inf' hI x with hθdef
    have hi₀pos : 0 < x i₀ := by simpa [hIdef] using hi₀I
    have hθpos : 0 < θ := hi₀ ▸ hi₀pos
    have hθle : ∀ i, 0 < x i → θ ≤ x i := fun i hi =>
      Finset.inf'_le x (by simpa [hIdef] using hi)
    have hθc : θ ≤ c := by rw [hi₀]; exact hxc i₀
    set x' : Fin d → ℝ := fun i => x i - if 0 < x i then θ else 0 with hx'
    have hx'0 : ∀ i, 0 ≤ x' i := by
      intro i; simp only [hx']; split_ifs with h
      · linarith [hθle i h]
      · simpa using hx0 i
    have hx'c : ∀ i, x' i ≤ c - θ := by
      intro i; simp only [hx']; split_ifs with h
      · linarith [hxc i]
      · linarith [hx0 i]
    have hsub : (Finset.univ.filter fun i => 0 < x' i) ⊂ I := by
      rw [Finset.ssubset_iff_of_subset]
      · refine ⟨i₀, hi₀I, ?_⟩
        have : x' i₀ = 0 := by simp [hx', hi₀pos, hi₀]
        simp [this]
      · intro i hi
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, hx'] at hi ⊢
        by_contra h
        have h' : ¬ 0 < x i := fun h' => h (by simp [hIdef, h'])
        simp [h'] at hi
    have hlt : (Finset.univ.filter fun i => 0 < x' i).card < m := hm ▸ Finset.card_lt_card hsub
    have IH := ih _ hlt (c - θ) x' (by linarith) hx'0 hx'c rfl
    have hsum : ∑ i, x i = θ * I.card + ∑ i, x' i := by
      have : ∑ i, x i = ∑ i, (x' i + if 0 < x i then θ else 0) := by
        refine Finset.sum_congr rfl fun i _ => by simp [hx']
      rw [this, Finset.sum_add_distrib, ← Finset.sum_filter]
      simp [hIdef, mul_comm]; ring
    have hj : ∀ j, c - (A j).sup' (hA j) x =
        (c - θ - (A j).sup' (hA j) x') + if Disjoint (A j) I then θ else 0 := by
      intro j
      rw [sup'_peel (A j) (hA j) x hx0 hθle]
      split_ifs <;> ring
    have hsum2 : ∑ j, (c - (A j).sup' (hA j) x) =
        ∑ j, (c - θ - (A j).sup' (hA j) x') +
          θ * (Finset.univ.filter fun j => Disjoint (A j) I).card := by
      rw [Finset.sum_congr rfl fun j _ => hj j, Finset.sum_add_distrib, ← Finset.sum_filter]
      simp [mul_comm]
    rw [hsum, hsum2]
    have := hk I
    nlinarith [mul_le_mul_of_nonneg_left this hθpos.le]
  · have hI0 : I = ∅ := Finset.not_nonempty_iff_eq_empty.mp hI
    have hx : ∀ i, x i = 0 := fun i => by
      have : ¬ 0 < x i := fun h => by
        have : i ∈ I := by simp [hIdef, h]
        simp [hI0] at this
      linarith [hx0 i]
    have hs : ∀ j, (A j).sup' (hA j) x = 0 := fun j => by
      apply le_antisymm
      · exact Finset.sup'_le _ _ fun i _ => (hx i).le
      · obtain ⟨i, hi⟩ := hA j
        exact (hx i).symm.le.trans (Finset.le_sup' x hi)
    have hk0 := hk ∅
    have e1 : ∑ i, x i = 0 := Finset.sum_eq_zero fun i _ => hx i
    have e2 : ∑ j, (c - (A j).sup' (hA j) x) = c * n := by simp [hs, mul_comm]
    have e3 : ((Finset.univ.filter fun j => Disjoint (A j) (∅ : Finset (Fin d))).card : ℝ) = n := by
      simp
    rw [e3] at hk0
    rw [e1, e2]
    have hk1 : (k:ℝ) ≤ n := by simpa using hk0
    nlinarith [mul_le_mul_of_nonneg_left hk1 hc]

/-- **Fractional covers.** For `x ∈ [0, 1]ᵈ`, `k ≤ ∑ᵢ xᵢ + ∑ⱼ (1 - max_{i ∈ A j} xᵢ)`, if
`k ≤ |I| + #{j | Disjoint (A j) I}` for every `I`. -/
theorem cover_bound (A : Fin n → Finset (Fin d)) (hA : ∀ j, (A j).Nonempty) (x : Fin d → ℝ)
    (hx0 : ∀ i, 0 ≤ x i) (hx1 : ∀ i, x i ≤ 1) (k : ℕ)
    (hk : ∀ I : Finset (Fin d),
      (k : ℝ) ≤ I.card + (Finset.univ.filter fun j => Disjoint (A j) I).card) :
    (k : ℝ) ≤ ∑ i, x i + ∑ j, (1 - (A j).sup' (hA j) x) := by
  simpa using cover_bound_aux A hA k hk _ 1 x zero_le_one hx0 hx1 rfl

/-- Row `s` term: `δ min(σ/δ, 1) ≤ pert 1 q` with `σ = max (q - 1) 0`. -/
theorem pert_one_ge {δ q : ℝ} (hδ : 0 < δ) :
    δ * min (max (q - 1) 0 / δ) 1 ≤ pert 1 q := by
  have h0 := pert_nonneg 1 q
  have h1 : q - 1 ≤ pert 1 q := by
    unfold pert
    refine le_trans ?_ (le_max_left _ _)
    simpa using le_abs_self (q - 1)
  calc δ * min (max (q - 1) 0 / δ) 1 ≤ δ * (max (q - 1) 0 / δ) :=
        mul_le_mul_of_nonneg_left (min_le_left _ _) hδ.le
    _ = max (q - 1) 0 := by field_simp
    _ ≤ pert 1 q := max_le h1 h0

/-- Copy term: a coordinate where the copy does not exceed `q_s`. -/
theorem copy_term {δ D p q σ x m : ℝ} (hδ0 : 0 < δ) (hδ1 : δ ≤ 1) (hq : 0 < q)
    (hσ0 : 0 ≤ σ) (hqσ : q ≤ 1 + σ) (hσD : σ < D) (hx : x = min (σ / δ) 1) (hm0 : 0 ≤ m) (hp : (p = 1 + δ ∧ x ≤ m) ∨ p = (1 + δ) * (1 + D)) :
    δ * (1 - m) / 2 ≤ pert p q := by
  have hp0 : 0 < p := by
    rcases hp with ⟨h, _⟩ | h <;> rw [h] <;> nlinarith
  have hs : 0 < 1 + σ := by linarith
  have hge : p / (1 + σ) - 1 ≤ pert p q := by
    rw [pert_eq_max_div hp0 hq]
    have : p / (1 + σ) ≤ p / q := div_le_div_of_nonneg_left hp0.le hq hqσ
    linarith [le_max_right (q / p) (p / q)]
  rcases hp with ⟨h, hxm⟩ | h
  · subst h
    by_cases hc : δ ≤ σ
    · have : x = 1 := by
        rw [hx]; exact min_eq_right ((one_le_div hδ0).2 hc)
      nlinarith [pert_nonneg (1 + δ) q]
    · push_neg at hc
      have hx' : x = σ / δ := by
        rw [hx]; exact min_eq_left ((div_le_one hδ0).2 hc.le)
      have h2 : δ * (1 - x) = δ - σ := by rw [hx']; field_simp
      have h3 : (δ - σ) / 2 ≤ (1 + δ) / (1 + σ) - 1 := by
        rw [div_sub_one hs.ne', div_le_div_iff₀ (by norm_num) hs]
        nlinarith
      nlinarith
  · subst h
    have : (1 + δ) ≤ (1 + δ) * (1 + D) / (1 + σ) := by
      rw [le_div_iff₀ hs]; nlinarith
    nlinarith

/-- The rows `s` and `e j c` are distinct, all rows are nonnegative. -/
theorem sum_rows_ge (r : Fin T → ℝ) (hr : ∀ t, 0 ≤ r t) (s : Fin T) (e : Fin n → Fin 2 → Fin T)
    (he : Function.Injective fun jc : Fin n × Fin 2 => e jc.1 jc.2) (hs : ∀ j c, e j c ≠ s) :
    r s + ∑ j, ∑ c, r (e j c) ≤ ∑ t, r t := by
  have h1 : ∑ j, ∑ c, r (e j c) = ∑ jc : Fin n × Fin 2, r (e jc.1 jc.2) :=
    (Fintype.sum_prod_type' (fun j c => r (e j c))).symm
  have h2 : ∑ jc : Fin n × Fin 2, r (e jc.1 jc.2) =
      ∑ t ∈ Finset.univ.image (fun jc : Fin n × Fin 2 => e jc.1 jc.2), r t :=
    (Finset.sum_image (fun a _ b _ h => he h)).symm
  have hn : s ∉ Finset.univ.image (fun jc : Fin n × Fin 2 => e jc.1 jc.2) := by
    simp only [Finset.mem_image, Finset.mem_univ, true_and, not_exists]
    exact fun a => hs a.1 a.2
  rw [h1, h2, ← Finset.sum_insert hn]
  exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (fun t _ _ => hr t)

/-- **Lower bound of the reduction.** On the set-cover prices, every `Q > 0` in which no copy
strictly dominates `q_s` costs at least `k δ`. -/
theorem hardness_lower (P Q : Fin T → Fin d → ℝ) (hQ : ∀ t, Q t ∈ orthant d)
    (A : Fin n → Finset (Fin d)) (hA : ∀ j, (A j).Nonempty) {δ : ℝ} (hδ0 : 0 < δ)
    (hδ1 : δ ≤ 1) (s : Fin T) (e : Fin n → Fin 2 → Fin T)
    (he : Function.Injective fun jc : Fin n × Fin 2 => e jc.1 jc.2) (hs : ∀ j c, e j c ≠ s)
    (hPs : ∀ i, P s i = 1)
    (hPe : ∀ j c i, P (e j c) i = if i ∈ A j then 1 + δ else (1 + δ) * (1 + d * δ))
    (hP : ∀ t, P t ∈ orthant d)
    (hdom : ∀ j c, ∃ i, Q (e j c) i ≤ Q s i) (k : ℕ)
    (hk : ∀ I : Finset (Fin d),
      (k : ℝ) ≤ I.card + (Finset.univ.filter fun j => Disjoint (A j) I).card) :
    k * δ ≤ totalPert P Q := by
  classical
  have hkd : (k : ℝ) ≤ d := by
    have h0 : (Finset.univ.filter fun j => Disjoint (A j) (Finset.univ : Finset (Fin d))) = ∅ := by
      refine Finset.filter_eq_empty_iff.2 fun j _ => ?_
      rw [← Finset.top_eq_univ, disjoint_top]
      exact (hA j).ne_empty
    simpa [h0] using hk Finset.univ
  unfold totalPert
  by_cases h : (d : ℝ) * δ ≤ ∑ t, ∑ i, pert (P t i) (Q t i)
  · exact (mul_le_mul_of_nonneg_right hkd hδ0.le).trans h
  push_neg at h
  set r : Fin T → ℝ := fun t => ∑ i, pert (P t i) (Q t i) with hr
  have hr0 : ∀ t, 0 ≤ r t := fun t => Finset.sum_nonneg fun i _ => pert_nonneg _ _
  have hrle : ∀ t, r t ≤ ∑ t, r t := fun t =>
    Finset.single_le_sum (f := r) (fun t _ => hr0 t) (Finset.mem_univ t)
  have hpi : ∀ t i, pert (P t i) (Q t i) ≤ r t := fun t i =>
    Finset.single_le_sum (f := fun i => pert (P t i) (Q t i)) (fun i _ => pert_nonneg _ _)
      (Finset.mem_univ i)
  have hQpos : ∀ t i, 0 < Q t i := fun t i => hQ t i
  set σ : Fin d → ℝ := fun i => max (Q s i - 1) 0 with hσ
  set x : Fin d → ℝ := fun i => min (σ i / δ) 1 with hx
  have hσ0 : ∀ i, 0 ≤ σ i := fun i => le_max_right _ _
  have hx0 : ∀ i, 0 ≤ x i := fun i => le_min (div_nonneg (hσ0 i) hδ0.le) zero_le_one
  have hx1 : ∀ i, x i ≤ 1 := fun i => min_le_right _ _
  set m : Fin n → ℝ := fun j => (A j).sup' (hA j) x with hm
  have hmx : ∀ j, ∀ i ∈ A j, x i ≤ m j := fun j i hi => Finset.le_sup' x hi
  have hm1 : ∀ j, m j ≤ 1 := fun j => Finset.sup'_le _ _ fun i _ => hx1 i
  have hm0 : ∀ j, 0 ≤ m j := fun j => (hx0 _).trans (hmx j _ (hA j).choose_spec)
  have hσpert : ∀ i, σ i ≤ pert (P s i) (Q s i) := by
    intro i
    rw [hPs i]
    unfold pert
    have h1 : Q s i - 1 ≤ |Q s i / 1 - 1| := by rw [div_one]; exact le_abs_self _
    exact max_le (h1.trans (le_max_left _ _)) ((abs_nonneg _).trans (le_max_left _ _))
  have hσlt : ∀ i, σ i < d * δ := fun i =>
    ((hσpert i).trans ((hpi s i).trans (hrle s))).trans_lt h
  have hrow : δ * ∑ i, x i ≤ r s := by
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun i _ => ?_
    have h2 : pert 1 (Q s i) = pert (P s i) (Q s i) := by rw [hPs i]
    exact h2 ▸ pert_one_ge (q := Q s i) hδ0
  have hcopy : ∀ j, δ * (1 - m j) ≤ ∑ c, r (e j c) := by
    intro j
    have key : ∀ c, δ * (1 - m j) / 2 ≤ r (e j c) := by
      intro c
      obtain ⟨i, hi⟩ := hdom j c
      have hq : Q (e j c) i ≤ 1 + σ i := by
        have := le_max_left (Q s i - 1) 0
        simp only [hσ]
        linarith
      have := copy_term (D := d * δ) (p := P (e j c) i) hδ0 hδ1 (hQpos _ _) (hσ0 i) hq
        (hσlt i) rfl (hm0 j)
        (by
          rw [hPe]
          split_ifs with h
          · exact Or.inl ⟨rfl, hmx j i h⟩
          · exact Or.inr rfl)
      exact this.trans (hpi _ _)
    rw [Fin.sum_univ_two]
    linarith [key 0, key 1]
  have hsum := sum_rows_ge r hr0 s e he hs
  have hcb : (k : ℝ) ≤ ∑ i, x i + ∑ j, (1 - m j) := cover_bound A hA x hx0 hx1 k hk
  have h3 : δ * ∑ j, (1 - m j) ≤ ∑ j, ∑ c, r (e j c) := by
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum fun j _ => hcopy j
  have h4 := mul_le_mul_of_nonneg_left hcb hδ0.le
  rw [mul_add] at h4
  nlinarith

/-- The set-cover prices are positive. -/
theorem setCover_pos (P : Fin T → Fin d → ℝ) (A : Fin n → Finset (Fin d)) {δ : ℝ}
    (hδ0 : 0 < δ) (s : Fin T) (e : Fin n → Fin 2 → Fin T)
    (hall : ∀ t, t = s ∨ ∃ j c, t = e j c) (hPs : ∀ i, P s i = 1)
    (hPe : ∀ j c i, P (e j c) i = if i ∈ A j then 1 + δ else (1 + δ) * (1 + d * δ)) :
    ∀ t, P t ∈ orthant d := by
  intro t i
  rcases hall t with rfl | ⟨j, c, rfl⟩
  · rw [hPs]; norm_num
  · rw [hPe]; split_ifs <;> positivity

/-- **Upper bound of the reduction.** Raising `q_s` to `1 + δ` on a cover `I` makes `y` (equal to
`1` at `s` and `2` at every copy) weakly solvable, at total perturbation `|I| δ`.

Proof: rows `t ≠ s` are unchanged, row `s` costs `δ` on `I`. The vector `y` is
`1_univ + 1_U` with `U` the set of copies: `univ` is vacuously weakly reachable (here `d ≥ 1` is
needed for a nonzero witness), and for a copy `e j c` the witness `e_i` with `i ∈ A j ∩ I` gives
`q^i_s - q^i_{e j c} = 0`. -/
theorem hardness_upper (hd : 1 ≤ d) (P : Fin T → Fin d → ℝ) (A : Fin n → Finset (Fin d)) {δ : ℝ}
    (hδ0 : 0 < δ) (s : Fin T) (e : Fin n → Fin 2 → Fin T) (hs : ∀ j c, e j c ≠ s)
    (hall : ∀ t, t = s ∨ ∃ j c, t = e j c) (hPs : ∀ i, P s i = 1)
    (hPe : ∀ j c i, P (e j c) i = if i ∈ A j then 1 + δ else (1 + δ) * (1 + d * δ))
    (y : Fin T → ℝ) (hys : y s = 1) (hye : ∀ j c, y (e j c) = 2)
    (I : Finset (Fin d)) (hI : ∀ j, ¬ Disjoint (A j) I) :
    let Q : Fin T → Fin d → ℝ := fun t i => if t = s then (if i ∈ I then 1 + δ else 1) else P t i
    (∀ t, Q t ∈ orthant d) ∧ y ∈ indicatorCone (weakReachableSpectra Q) ∧
      totalPert P Q = I.card * δ := by
  classical
  intro Q
  have hPpos := setCover_pos P A hδ0 s e hall hPs hPe
  have hQs : ∀ i, Q s i = if i ∈ I then 1 + δ else 1 := fun i => by simp [Q]
  have hQt : ∀ t, t ≠ s → Q t = P t := fun t ht => by funext i; simp [Q, ht]
  refine ⟨?_, ?_, ?_⟩
  · intro t i
    by_cases ht : t = s
    · subst ht; rw [hQs]; split_ifs <;> linarith
    · rw [hQt t ht]; exact hPpos t i
  · set U : Finset (Fin T) := Finset.univ.erase s with hU
    have hy : y = (1 : ℝ) • ((Finset.univ : Finset (Fin T)) : Set (Fin T)).indicator 1 +
        (1 : ℝ) • ((U : Set (Fin T)).indicator 1) := by
      funext t
      rcases hall t with rfl | ⟨j, c, rfl⟩
      · simp [U, hys]
      · simp [U, hs j c, hye]; norm_num
    rw [hy]
    refine Submodule.add_mem _ (smul_indicator_mem_indicatorCone zero_le_one fun _ => ?_)
      (smul_indicator_mem_indicatorCone zero_le_one fun _ => ?_)
    · intro t _
      refine ⟨Pi.single ⟨0, hd⟩ 1, Pi.single_nonneg.2 zero_le_one, fun h => ?_,
        fun u hu => absurd (Finset.mem_univ u) hu⟩
      simpa using congr_fun h ⟨0, hd⟩
    · intro t ht
      have hts : t ≠ s := Finset.ne_of_mem_erase ht
      obtain ⟨j, c, rfl⟩ := (hall t).resolve_left hts
      obtain ⟨i, hiA, hiI⟩ := Finset.not_disjoint_iff.1 (hI j)
      refine ⟨Pi.single i 1, Pi.single_nonneg.2 zero_le_one, fun h => ?_, fun u hu => ?_⟩
      · simpa using congr_fun h i
      · have hu' : u = s := by
          by_contra h; exact hu (Finset.mem_erase.2 ⟨h, Finset.mem_univ _⟩)
        subst hu'
        rw [single_dotProduct, Pi.sub_apply, hQs, hQt _ (hs j c), hPe]
        simp [hiA, hiI]
  · show ∑ t, ∑ i, pert (P t i) (Q t i) = I.card * δ
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ s)]
    have h0 : ∑ t ∈ Finset.univ.erase s, ∑ i, pert (P t i) (Q t i) = 0 :=
      Finset.sum_eq_zero fun t ht => by
        rw [hQt t (Finset.ne_of_mem_erase ht)]
        exact Finset.sum_eq_zero fun i _ => pert_self (hPpos t i)
    have h1 : ∀ i, pert (P s i) (Q s i) = if i ∈ I then δ else 0 := by
      intro i
      rw [hPs, hQs]
      split_ifs
      · have h2 : 1 / (1 + δ) ≤ (1 + δ) / 1 := by
          rw [div_one, div_le_iff₀ (by linarith)]; nlinarith
        rw [pert_eq_max_div one_pos (by linarith), max_eq_left h2]; ring
      · exact pert_self one_pos
    rw [h0, add_zero, Finset.sum_congr rfl fun i _ => h1 i]
    simp [Finset.sum_ite_mem]

/-- **The reduction.** On the set-cover prices, `ρ(P, y) = k δ` for the minimal cover size `k`
(`k` is attained by a cover `I₀` and bounds `|I| + #uncovered(I)` from below). -/
theorem minPert_setCover (hd : 2 ≤ d) (P : Fin T → Fin d → ℝ) (A : Fin n → Finset (Fin d))
    (hA : ∀ j, (A j).Nonempty) {δ : ℝ} (hδ0 : 0 < δ) (hδ1 : δ ≤ 1) (s : Fin T)
    (e : Fin n → Fin 2 → Fin T) (he : Function.Injective fun jc : Fin n × Fin 2 => e jc.1 jc.2)
    (hs : ∀ j c, e j c ≠ s) (hall : ∀ t, t = s ∨ ∃ j c, t = e j c) (hPs : ∀ i, P s i = 1)
    (hPe : ∀ j c i, P (e j c) i = if i ∈ A j then 1 + δ else (1 + δ) * (1 + d * δ))
    (y : Fin T → ℝ) (hys : y s = 1) (hye : ∀ j c, y (e j c) = 2) (k : ℕ)
    (hk : ∀ I : Finset (Fin d),
      (k : ℝ) ≤ I.card + (Finset.univ.filter fun j => Disjoint (A j) I).card)
    (I₀ : Finset (Fin d)) (hI₀ : ∀ j, ¬ Disjoint (A j) I₀) (hcard : I₀.card = k) :
    minPert P y = k * δ := by
  classical
  have hP := setCover_pos P A hδ0 s e hall hPs hPe
  have hy : ∀ t, 0 ≤ y t := by
    intro t; rcases hall t with rfl | ⟨j, c, rfl⟩ <;> simp [hys, hye]
  obtain ⟨hQ, hyQ, hT⟩ :=
    hardness_upper (by omega) P A hδ0 s e hs hall hPs hPe y hys hye I₀ hI₀
  have hup : minPert P y ≤ k * δ := by
    rw [← hcard]; exact (minPert_le hP hQ
      ((weakSolvable_iff hd (fun t i => (hQ t i).le) hy).2 hyQ)).trans hT.le
  refine le_antisymm hup ?_
  refine le_minPert_of_relaxation hd hP hy hup (fun Q => ∀ j c, ∃ i, Q (e j c) i ≤ Q s i) ?_ ?_
  · intro Q _ hyQ j c
    by_contra h
    push_neg at h
    have := le_of_dominates hyQ h
    rw [hys, hye] at this; norm_num at this
  · intro Q hΦ hbox
    have hD : 0 ≤ (k : ℝ) * δ := by positivity
    have hQ' : ∀ t, Q t ∈ orthant d := fun t i =>
      lt_of_lt_of_le (div_pos (hP t i) (by linarith)) (hbox t i).1
    exact hardness_lower P Q hQ' A hA hδ0 hδ1 s e he hs hPs hPe hP hΦ k hk

end NeoTiling
