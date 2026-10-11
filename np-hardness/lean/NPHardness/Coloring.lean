import NPHardness.Layout

/-!
# `s ∈ STAB(H)` iff `G` is 3-colourable

(←) A proper colouring `c` and a shift `σ ∈ ℤ/3` give the independent set of the copies of the
corners `(v, c v + σ)` and the anticopies of the other corners. The three shifts average to `s`:
a copy is chosen for one shift out of three, an anticopy for two.

(→) The triangle inequalities `x(T) ≤ 1` and the edge inequalities `x_p + x_q ≤ 1` hold on every
independent set, and `s` satisfies the triangle and the copy–anticopy inequalities with equality.
So every independent set of a decomposition of `s` contains exactly one corner per triangle and
exactly one end of every copy–anticopy edge. Then all copies of a corner are chosen with it, and
the junction edge of the column `(k, i)` forbids choosing the corners `(lo k, i)` and `(hi k, i)`
together: the chosen corners form a proper colouring.
-/

namespace NeoTiling.NPHardness

open Finset

namespace Graph

variable {n m : ℕ} (G : Graph n m)

/-! ### Copies and anticopies -/

/-- The vertex of `G` a node belongs to: `v` on the row `(v, i)`; on the column `(k, i)` the
nodes `0, 1` belong to `lo k`, the others to `hi k`. -/
def owner : G.Node → Fin n
  | .inl (v, _, _) => v
  | .inr ⟨k, _, j⟩ => if (j : ℕ) ≤ 1 then G.lo k else G.hi k

/-- The colour of a node: `i` on the row or column `(·, i)`. -/
def color : G.Node → Fin 3
  | .inl (_, i, _) => i
  | .inr ⟨_, i, _⟩ => i

/-- Copies: the even row nodes, and the column nodes `1` and `2, 4, 6, …`. -/
def IsCopy : G.Node → Prop
  | .inl (_, _, j) => (j : ℕ) % 2 = 0
  | .inr ⟨_, _, j⟩ => (j : ℕ) = 1 ∨ ((j : ℕ) % 2 = 0 ∧ (j : ℕ) ≠ 0)

instance : DecidablePred G.IsCopy := fun p => by cases p <;> unfold IsCopy <;> infer_instance

lemma sval_eq (p : G.Node) : G.sval p = if G.IsCopy p then 1 / 3 else 2 / 3 := by
  cases p <;> simp [sval, IsCopy]

/-- The ends of edge `k` are `lo k` and `hi k`. -/
lemma lo_hi_ne (c : Fin n → Fin 3) (k : Fin m) :
    c (G.lo k) ≠ c (G.hi k) ↔ c (G.eu k) ≠ c (G.ev k) := by
  rcases le_total (G.eu k) (G.ev k) with h | h <;> simp [lo, hi, h, ne_comm]

/-! ### (←) Three shifted independent sets -/

/-- The independent set of the colouring `c` shifted by `σ`: the copies of the corners
`(v, c v + σ)` and the anticopies of the other corners. -/
def shifted (c : Fin n → Fin 3) (σ : Fin 3) : Finset G.Node :=
  univ.filter fun p => (c (G.owner p) + σ = G.color p ↔ G.IsCopy p)

/-- Every edge joins a copy and an anticopy of the same corner, or two corners of a triangle, or
(junction) copies of the corners `(lo k, i)` and `(hi k, i)`, which have different colours. -/
lemma shifted_indep {c : Fin n → Fin 3} (hc : ∀ k, c (G.eu k) ≠ c (G.ev k)) (σ : Fin 3) :
    IsIndep G.linkU G.linkV (G.shifted c σ) := by
  rintro (⟨v, i, j⟩ | ⟨k, i, j⟩ | ⟨k, i, b⟩ | ⟨v, t⟩) <;>
    simp only [linkU, linkV, row, col, shifted, owner, color, IsCopy, mem_filter, mem_univ,
      true_and, Fin.val_castSucc, Fin.val_succ] <;> rintro ⟨h1, h2⟩
  · -- row edge: the parities of `j` and `j + 1` differ
    by_cases h : c v + σ = i <;> simp only [h, true_iff, false_iff] at h1 h2 <;> omega
  · -- column edge: `0 — 1` same owner, `1 — 2` junction, `≥ 2` same owner
    rcases (by omega : (j : ℕ) = 0 ∨ (j : ℕ) = 1 ∨ 2 ≤ (j : ℕ)) with h | h | h
    · by_cases h3 : c (G.lo k) + σ = i <;> simp_all
    · simp [h] at h1 h2
      exact (G.lo_hi_ne c k).2 (hc k) (add_right_cancel (h1.trans h2.symm))
    · simp only [show ¬ (j : ℕ) ≤ 1 by omega, show ¬ (j : ℕ) + 1 ≤ 1 by omega, if_false] at h1 h2
      by_cases h5 : c (G.hi k) + σ = i <;> simp only [h5, true_iff, false_iff] at h1 h2 <;> omega
  · -- attachment of a column end to its row (the row node `jA` is even)
    have := G.lo_lt_hi k
    cases b <;> simp_all [jA, colLen, show ¬ 4 * ((G.hi k : ℕ) - G.lo k) ≤ 2 by omega] <;> omega
  · -- triangle edge: both corners `(v, t)`, `(v, t + 1)` would be chosen
    revert h1 h2; simp; generalize c v + σ = a; revert a t; decide

/-- A copy is chosen for one shift out of three, an anticopy for two. -/
lemma sum_shifted (c : Fin n → Fin 3) (p : G.Node) :
    (∑ σ : Fin 3, if p ∈ G.shifted c σ then (1 / 3 : ℝ) else 0) = G.sval p := by
  rw [sval_eq]; simp only [shifted, mem_filter, mem_univ, true_and]
  generalize c (G.owner p) = a; generalize G.color p = b
  by_cases h : G.IsCopy p <;> simp only [h, iff_true, iff_false] <;>
    fin_cases a <;> fin_cases b <;> simp (config := {decide := true}) [Fin.sum_univ_three] <;>
    norm_num

theorem inStab_of_colorable (hG : G.Colorable) : InStab G.linkU G.linkV G.sval := by
  obtain ⟨c, hc⟩ := hG
  refine ⟨fun I => ∑ σ : Fin 3, if G.shifted c σ = I then 1 / 3 else 0, fun I => ?_,
    fun I hI => ?_, ?_, fun p => ?_⟩
  · exact sum_nonneg fun σ _ => by split_ifs <;> norm_num
  · obtain ⟨σ, -, hσ⟩ := exists_ne_zero_of_sum_ne_zero hI
    obtain rfl : G.shifted c σ = I := by by_contra h; simp [h] at hσ
    exact G.shifted_indep hc σ
  · rw [sum_comm]; simp
  · beta_reduce
    rw [← sum_filter, sum_comm, ← G.sum_shifted c p]; simp

/-! ### (→) Tight inequalities -/

/-- **Tight cliques.** If no independent set meets `A` twice and `s` sums to `1` over `A`, then
every independent set of a decomposition of `s` meets `A`. -/
lemma tight {μ : Finset G.Node → ℝ} (hμ : (∀ I, 0 ≤ μ I) ∧
      (∀ I, μ I ≠ 0 → IsIndep G.linkU G.linkV I) ∧ ∑ I, μ I = 1 ∧
      ∀ p, G.sval p = ∑ I, if p ∈ I then μ I else 0) {A : Finset G.Node}
    (hA : ∀ J, IsIndep G.linkU G.linkV J → ∀ p ∈ A, ∀ q ∈ A, p ∈ J → q ∈ J → p = q)
    (hA1 : ∑ p ∈ A, G.sval p = 1) {I : Finset G.Node} (hI : μ I ≠ 0) : ∃ p ∈ A, p ∈ I := by
  obtain ⟨hμ0, hμI, hμ1, hs⟩ := hμ
  -- `1 = ∑ s(A) = ∑ μ_J |A ∩ J|` with `|A ∩ J| ≤ 1`, so `|A ∩ I| = 1`
  have hsum : ∑ p ∈ A, G.sval p = ∑ J, μ J * (A ∩ J).card := by
    simp_rw [hs]; rw [sum_comm]
    refine sum_congr rfl fun J _ => ?_
    rw [← sum_filter, filter_mem_eq_inter, sum_const, nsmul_eq_mul, mul_comm]
  have hz : ∑ J, μ J * (1 - (A ∩ J).card) = 0 := by
    simp_rw [mul_sub, mul_one, sum_sub_distrib, hμ1, ← hsum, hA1]; ring
  have hnn : ∀ J ∈ (univ : Finset (Finset G.Node)), 0 ≤ μ J * (1 - (A ∩ J).card) := fun J _ => by
    by_cases h : μ J = 0
    · simp [h]
    · have : ((A ∩ J).card : ℝ) ≤ 1 := by
        exact_mod_cast card_le_one.2 fun p hp q hq => by
          simp only [mem_inter] at hp hq; exact hA J (hμI J h) p hp.1 q hq.1 hp.2 hq.2
      exact mul_nonneg (hμ0 J) (by linarith)
  have h0 := (mul_eq_zero.1 ((sum_eq_zero_iff_of_nonneg hnn).1 hz I (mem_univ _))).resolve_left hI
  obtain ⟨p, hp⟩ := card_pos.1 (by exact_mod_cast (by linarith : (0 : ℝ) < (A ∩ I).card))
  exact ⟨p, mem_inter.1 hp⟩

/-- **Alternation along a path.** If exactly one of any two consecutive nodes `j, j + 1` of the
path `a, …, b` lies in a set, then two nodes are both in or both out iff their positions have the
same parity. -/
lemma alternate {P : ℕ → Prop} {a b : ℕ} (h : ∀ j, a ≤ j → j < b → (P j ↔ ¬ P (j + 1)))
    {i j : ℕ} (hi : a ≤ i ∧ i ≤ b) (hj : a ≤ j ∧ j ≤ b) : (P i ↔ P j) ↔ i % 2 = j % 2 := by
  have key : ∀ j, a ≤ j → j ≤ b → ((P j ↔ P a) ↔ j % 2 = a % 2) := by
    intro j hj; induction j, hj using Nat.le_induction with
    | base => simp
    | succ j hj ih =>
      intro hb
      have := h j hj (by omega); have := ih (by omega)
      have : (j + 1) % 2 = a % 2 ↔ ¬ j % 2 = a % 2 := by omega
      tauto
  have := key i hi.1 hi.2; have := key j hj.1 hj.2
  have : i % 2 = j % 2 ↔ (i % 2 = a % 2 ↔ j % 2 = a % 2) := by omega
  tauto

/-- **Copies follow their corner.** If every copy–anticopy edge has exactly one end in `I`, then
a node is in `I` iff (its corner is in `I` iff it is a copy): along a row, and along each of
the two halves of a column, the nodes in `I` alternate starting from the corner. -/
lemma follow {I : Finset G.Node}
    (hI : ∀ e, ¬ (G.IsCopy (G.linkU e) ↔ G.IsCopy (G.linkV e)) →
      (G.linkU e ∈ I ↔ G.linkV e ∉ I))
    (p : G.Node) : p ∈ I ↔ (G.row (G.owner p) (G.color p) 0 ∈ I ↔ G.IsCopy p) := by
  -- 1. rows: alternation from the corner
  have hrow : ∀ v i (j : Fin (12 * m + 1)),
      G.row v i j ∈ I ↔ (G.row v i 0 ∈ I ↔ (j : ℕ) % 2 = 0) := by
    intro v i ⟨j, hj⟩
    have := alternate (P := fun j => if h : j < 12 * m + 1 then G.row v i ⟨j, h⟩ ∈ I else False)
      (a := 0) (b := 12 * m) (fun j _ hj => by
        have := hI (.inl (v, i, ⟨j, hj⟩)) (by simp [linkU, linkV, row, IsCopy]; omega)
        simpa [linkU, linkV, row, hj, hj.le] using this)
      (i := j) (j := 0) (by omega) (by omega)
    simp [hj] at this
    tauto
  -- 2. the attachment row node `jA k i` is even, so it is in `I` iff its corner is
  have hatt : ∀ k i r, G.row r i (jA k i) ∈ I ↔ G.row r i 0 ∈ I := fun k i r => by
    simpa [show (jA k i : ℕ) % 2 = 0 by simp [jA]; omega] using hrow r i (jA k i)
  -- 3. the upper half of a column alternates from its top node, attached to the corner `(hi k, i)`
  have hup : ∀ k i (j : Fin (G.colLen k)), 2 ≤ (j : ℕ) →
      (G.col k i j ∈ I ↔ (G.row (G.hi k) i 0 ∈ I ↔ (j : ℕ) % 2 = 0)) := by
    rintro k i ⟨j, hj⟩ (h2 : 2 ≤ j)
    have hL : G.colLen k % 4 = 0 := by unfold colLen; omega
    have htop := hI (.inr (.inr (.inl (k, i, true)))) (by
      simp [linkU, linkV, col, row, IsCopy, jA]; omega)
    have := alternate (P := fun j => if h : j < G.colLen k then G.col k i ⟨j, h⟩ ∈ I else False)
      (a := 2) (b := G.colLen k - 1) (fun j _ hj => by
        have := hI (.inr (.inl ⟨k, i, ⟨j, hj⟩⟩)) (by simp [linkU, linkV, col, IsCopy]; omega)
        simpa [linkU, linkV, col, show j < G.colLen k by omega, show j + 1 < G.colLen k by omega]
          using this)
      (i := j) (j := G.colLen k - 1) (by omega) (by omega)
    simp [hj, G.colLen_pos k, col] at this
    have : j % 2 = (G.colLen k - 1) % 2 ↔ ¬ j % 2 = 0 := by omega
    simp only [linkU, linkV, hatt, col] at htop ⊢
    tauto
  rcases p with ⟨v, i, j⟩ | ⟨k, i, ⟨j, hj⟩⟩
  · simpa [owner, color, IsCopy] using hrow v i j
  -- 4. the lower half: node `0` is attached to the corner `(lo k, i)`, node `1` follows node `0`
  have hL : 4 ≤ G.colLen k := by have := G.lo_lt_hi k; unfold colLen; omega
  have h0 := hI (.inr (.inr (.inl (k, i, false)))) (by
    simp [linkU, linkV, col, row, IsCopy, jA]; omega)
  have h1 := hI (.inr (.inl ⟨k, i, ⟨0, by omega⟩⟩)) (by simp [linkU, linkV, col, IsCopy])
  simp only [linkU, linkV, hatt, col] at h0 h1
  -- 5. the nodes `0`, `1` and the upper half
  rcases (by omega : j = 0 ∨ j = 1 ∨ 2 ≤ j) with rfl | rfl | h
  · simpa [owner, color, IsCopy] using h0
  · simp [owner, color, IsCopy]; tauto
  · simpa [owner, color, IsCopy, col, show ¬ j ≤ 1 by omega, show j ≠ 1 by omega,
      show j ≠ 0 by omega] using hup k i ⟨j, hj⟩ h

theorem colorable_of_inStab (h : InStab G.linkU G.linkV G.sval) : G.Colorable := by
  obtain ⟨μ, hμ⟩ := h
  -- an independent set `I` of the decomposition
  obtain ⟨I, -, hI⟩ : ∃ I ∈ (univ : Finset (Finset G.Node)), μ I ≠ 0 :=
    exists_ne_zero_of_sum_ne_zero (by rw [hμ.2.2.1]; exact one_ne_zero)
  have hind := hμ.2.1 I hI
  -- 1. exactly one end of every copy–anticopy edge lies in `I`
  have hedge : ∀ e, ¬ (G.IsCopy (G.linkU e) ↔ G.IsCopy (G.linkV e)) →
      (G.linkU e ∈ I ↔ G.linkV e ∉ I) := by
    intro e he
    have hne : G.linkU e ≠ G.linkV e := fun h => he (h ▸ Iff.rfl)
    obtain ⟨p, hp, hpI⟩ := G.tight hμ (A := {G.linkU e, G.linkV e})
      (fun J hJ p hp q hq hpJ hqJ => by
        simp only [mem_insert, mem_singleton] at hp hq
        rcases hp with rfl | rfl <;> rcases hq with rfl | rfl <;>
          first | rfl | exact (hJ e ⟨‹_›, ‹_›⟩).elim)
      (by rw [sum_pair hne, sval_eq, sval_eq]; split_ifs <;> norm_num <;> tauto) hI
    have := hind e; simp only [mem_insert, mem_singleton] at hp
    rcases hp with rfl | rfl <;> tauto
  -- 2. exactly one corner of every triangle lies in `I`: the colour `c v`
  have hcol : ∀ v, ∃ i, G.row v i 0 ∈ I := by
    intro v
    have key : ∀ f : Fin 3 → Bool, (∀ t, ¬ (f t ∧ f (t + 1))) → ∀ t t', f t → f t' → t = t' := by
      decide
    obtain ⟨p, hp, hpI⟩ := G.tight hμ (A := univ.image fun i => G.row v i 0)
      (fun J hJ p hp q hq hpJ hqJ => by
        simp only [mem_image, mem_univ, true_and] at hp hq
        obtain ⟨t, rfl⟩ := hp; obtain ⟨t', rfl⟩ := hq
        rw [key (fun t => decide (G.row v t 0 ∈ J))
          (fun t => by simpa using hJ (.inr (.inr (.inr (v, t))))) t t' (by simpa) (by simpa)])
      (by rw [sum_image fun a _ b _ h => by simpa [row] using h]; simp [sval, row]) hI
    obtain ⟨t, -, rfl⟩ := mem_image.1 hp; exact ⟨t, hpI⟩
  choose c hc using hcol
  -- 3. the junction edge of the column `(k, c (lo k))` forbids equal colours
  refine ⟨c, fun k => (G.lo_hi_ne c k).1 fun hk => ?_⟩
  have hL : 4 ≤ G.colLen k := by have := G.lo_lt_hi k; unfold colLen; omega
  have h1 := G.follow hedge (G.col k (c (G.lo k)) ⟨1, by omega⟩)
  have h2 := G.follow hedge (G.col k (c (G.lo k)) ⟨2, by omega⟩)
  simp [col, owner, color, IsCopy, hc, hk ▸ hc (G.hi k)] at h1 h2
  exact hind (.inr (.inl ⟨k, c (G.lo k), ⟨1, by omega⟩⟩)) ⟨h1, h2⟩

/-- **The colouring lemma.** -/
theorem inStab_iff_colorable : InStab G.linkU G.linkV G.sval ↔ G.Colorable :=
  ⟨G.colorable_of_inStab, G.inStab_of_colorable⟩

end Graph

end NeoTiling.NPHardness
