import NeoTiling.Hardness.Gadget

/-!
# Lattice drawings give empty disks

A lattice drawing places the vertices at distinct points of `ℤ²`. For an edge `ab` and a vertex
`w` put `u_w = 2 w - a - b`, twice the vector from the midpoint of the edge to `w`. The vertex `w`
lies in the closed disk with diameter `ab` iff `|u_w|² ≤ |a - b|²`, on its boundary circle iff
`|u_w|² = |a - b|²`. A `Drawing` asks for every edge of length at most `4` that

* no vertex lies strictly inside the disk with diameter `ab` (`Drawing.empty`);
* besides `a` and `b` the circle carries at most one vertex, or exactly the two ends of an edge
  (`Drawing.circle`).

Then an independent set `I` has at most two vertices on the circle, and they are not antipodal
(antipodal vertices on the circle are `a, b` or the ends of the edge on it). So the disk centred
at `m - δ ∑_{w ∈ I on the circle} u_w` (`m` the midpoint, `δ = 1/256`) avoids `I`: vertices on the
circle move out by the shift, every other vertex has `|w - m|² ≥ |a - b|²/4 + 1/4` and stays
outside (`Drawing.gadget_valid`).
-/

set_option linter.unusedSectionVars false

namespace NeoTiling.NPHardness

open Finset

/-- Squared length of an integer vector. -/
def nrm (p : ℤ × ℤ) : ℤ := p.1 ^ 2 + p.2 ^ 2

/-- A lattice point as a point of the plane. -/
def toR (p : ℤ × ℤ) : Fin 2 → ℝ := ![(p.1 : ℝ), (p.2 : ℝ)]

variable {V E : Type*} [Fintype V] [DecidableEq V] [Fintype E]

/-- The vertices other than `eu k`, `ev k` on the circle with diameter the edge `k`. -/
def onCircle (pos : V → ℤ × ℤ) (eu ev : E → V) (k : E) : Finset V :=
  univ.filter fun w => w ≠ eu k ∧ w ≠ ev k ∧
    nrm (2 • pos w - pos (eu k) - pos (ev k)) = nrm (pos (ev k) - pos (eu k))

/-- A lattice drawing with empty disks: distinct lattice points, edges of length `≤ 4`, no
vertex inside the disk with diameter an edge, and on its circle at most one more vertex or the
two ends of an edge. -/
structure Drawing (eu ev : E → V) where
  pos : V → ℤ × ℤ
  inj : Function.Injective pos
  short : ∀ k, nrm (pos (ev k) - pos (eu k)) ≤ 16
  empty : ∀ k w, nrm (pos (ev k) - pos (eu k)) ≤ nrm (2 • pos w - pos (eu k) - pos (ev k))
  circle : ∀ k, (onCircle pos eu ev k).card ≤ 1 ∨ ∃ k', onCircle pos eu ev k = {eu k', ev k'}

namespace Drawing

variable {eu ev : E → V} (D : Drawing eu ev)

/-- The gadget of a drawing scaled by `σ`, with heights `σ² (|a - b|²/4 + 1/512)`. -/
noncomputable def gadget (σ : ℝ) : Gadget V E where
  eu := eu
  ev := ev
  a v := σ • toR (D.pos v)
  η k := σ ^ 2 * ((nrm (D.pos (ev k) - D.pos (eu k)) : ℝ) / 4 + 1 / 512)

/-- `u_w = 2 w - a - b` for the edge `k = ab`: twice the vector from its midpoint to `w`. -/
def u (k : E) (w : V) : ℤ × ℤ := 2 • D.pos w - D.pos (eu k) - D.pos (ev k)

/-- The squared length `|a - b|²` of the edge `k`. -/
def len (k : E) : ℤ := nrm (D.pos (ev k) - D.pos (eu k))

/-- The vertices of `I` on the circle with diameter the edge `k` (its ends included). -/
def circ (k : E) (I : Finset V) : Finset V := I.filter fun w => nrm (D.u k w) = D.len k

/-- The shift `v = ∑ u_w` over the vertices `w` of `I` on the circle. -/
def shift (k : E) (I : Finset V) : ℤ × ℤ := ∑ w ∈ D.circ k I, D.u k w

/-- Inner product of integer vectors. -/
def dot (p q : ℤ × ℤ) : ℤ := p.1 * q.1 + p.2 * q.2

/-- **An independent set has at most two vertices on the circle, and they are not antipodal.**
It contains at most one end of the edge and at most one vertex of `onCircle` (by
`Drawing.circle`), and the only vertex antipodal to an end is the other end. -/
theorem circ_pair {k : E} {I : Finset V} (hI : IsIndep eu ev I) {w : V} (hw : w ∈ D.circ k I) :
    ((D.circ k I).erase w).card ≤ 1 ∧ ∀ w' ∈ (D.circ k I).erase w, D.u k w + D.u k w' ≠ 0 := by
  set C := D.circ k I
  have hI' : ∀ x ∈ C, x ∈ I := fun x hx => (mem_filter.1 hx).1
  -- `I` contains at most one end of every edge
  have hend : ∀ k, ∀ x ∈ I, ∀ y ∈ I, (x = eu k ∨ x = ev k) → (y = eu k ∨ y = ev k) → x = y := by
    rintro k x hx y hy (rfl | rfl) (rfl | rfl) <;>
      first | rfl | exact absurd ⟨hx, hy⟩ (hI _) | exact absurd ⟨hy, hx⟩ (hI _)
  -- the vertices of `C` other than the ends lie in `onCircle`; there is at most one of them
  have hon : ∀ x ∈ C, ¬(x = eu k ∨ x = ev k) → x ∈ onCircle D.pos eu ev k := fun x hx h => by
    push_neg at h
    simp only [onCircle, mem_filter, mem_univ, true_and]
    exact ⟨h.1, h.2, (mem_filter.1 hx).2⟩
  have hoo : ∀ x ∈ C, ∀ y ∈ C, x ∈ onCircle D.pos eu ev k → y ∈ onCircle D.pos eu ev k →
      x = y := fun x hx y hy ox oy => by
    rcases D.circle k with h | ⟨k', hk'⟩
    · exact card_le_one.1 h x ox y oy
    · rw [hk', mem_insert, mem_singleton] at ox oy
      exact hend k' x (hI' x hx) y (hI' y hy) ox oy
  -- of two distinct vertices of `C` exactly one is an end
  have hkind : ∀ x ∈ C, ∀ y ∈ C, x ≠ y → ((x = eu k ∨ x = ev k) ↔ ¬(y = eu k ∨ y = ev k)) :=
    fun x hx y hy hxy => ⟨fun ex ey => hxy (hend k x (hI' x hx) y (hI' y hy) ex ey),
      fun ey => by_contra fun ex => hxy (hoo x hx y hy (hon x hx ex) (hon y hy ey))⟩
  refine ⟨card_le_one.2 fun x hx y hy => ?_, fun y hy h0 => ?_⟩
  · rw [mem_erase] at hx hy
    have := hkind x hx.2 w hw hx.1; have := hkind y hy.2 w hw hy.1
    by_cases ex : x = eu k ∨ x = ev k
    · exact hend k x (hI' x hx.2) y (hI' y hy.2) ex (by tauto)
    · exact hoo x hx.2 y hy.2 (hon x hx.2 ex) (hon y hy.2 (by tauto))
  · rw [mem_erase] at hy
    -- `u_w + u_y = 0` means `w + y = a + b`: the partner of an end is the other end
    have hsum : D.pos w + D.pos y = D.pos (eu k) + D.pos (ev k) := by
      simp [u, Prod.ext_iff] at h0 ⊢; omega
    have hanti : ∀ x z, (x = eu k ∨ x = ev k) →
        D.pos x + D.pos z = D.pos (eu k) + D.pos (ev k) → (z = eu k ∨ z = ev k) := by
      rintro x z (rfl | rfl) h
      · exact Or.inr (D.inj (add_left_cancel h))
      · exact Or.inl (D.inj (add_left_cancel (h.trans (add_comm _ _))))
    have := hkind w hw y hy.2 (Ne.symm hy.1)
    by_cases ew : w = eu k ∨ w = ev k
    · exact this.1 ew (hanti w y ew hsum)
    · exact ew (hanti y w (by tauto) ((add_comm _ _).trans hsum))

/-- **The shift pushes the circle out**: `⟨u_w, v⟩ ≥ 1` for the vertices `w` of `I` on the
circle, and `|v|² ≤ 64`. With a second vertex `w'`: `⟨u_w, v⟩ = |a - b|² + ⟨u_w, u_w'⟩`, and
`|u_w + u_w'|² > 0` gives `⟨u_w, u_w'⟩ > -|a - b|²`. -/
theorem shift_spec {k : E} {I : Finset V} (hI : IsIndep eu ev I) :
    nrm (D.shift k I) ≤ 64 ∧ ∀ w ∈ D.circ k I, 1 ≤ dot (D.u k w) (D.shift k I) := by
  have hL : D.len k ≤ 16 := D.short k
  have key : ∀ w ∈ D.circ k I, 1 ≤ dot (D.u k w) (D.shift k I) ∧ nrm (D.shift k I) ≤ 64 := by
    intro w hw
    obtain ⟨hcard, hanti⟩ := D.circ_pair hI hw
    have hwL : nrm (D.u k w) = D.len k := (mem_filter.1 hw).2
    have hv : D.shift k I = D.u k w + ∑ x ∈ (D.circ k I).erase w, D.u k x :=
      (add_sum_erase _ _ hw).symm
    rcases (D.circ k I).erase w |>.eq_empty_or_nonempty with he | ⟨w', hw'⟩
    · -- `w` alone: `v = u_w` and `⟨u_w, v⟩ = |a - b|² ≥ 1`, as `a = b` would put `w ∈ I` at `a`
      rw [he, sum_empty, add_zero] at hv
      have hL1 : 1 ≤ D.len k := by
        by_contra h
        have h0 : ∀ p : ℤ × ℤ, nrm p ≤ 0 → p = 0 := fun p hp => by
          simp only [nrm] at hp; ext <;> simp <;> nlinarith [sq_nonneg p.1, sq_nonneg p.2]
        have hab : ev k = eu k := D.inj (sub_eq_zero.1 (h0 _ (by simp only [len] at h; omega)))
        have hw0 := h0 _ (by omega : nrm (D.u k w) ≤ 0)
        have hwa : w = eu k := D.inj (by simp [u, hab, Prod.ext_iff] at hw0 ⊢; omega)
        exact hI k (by rw [hab, ← hwa]; exact ⟨(mem_filter.1 hw).1, (mem_filter.1 hw).1⟩)
      rw [hv]
      have e : dot (D.u k w) (D.u k w) = nrm (D.u k w) := by simp [dot, nrm, sq]
      exact ⟨by omega, by omega⟩
    · -- `C = {w, w'}`
      have hw'L : nrm (D.u k w') = D.len k := (mem_filter.1 (mem_erase.1 hw').2).2
      rw [eq_singleton_iff_unique_mem.2 ⟨hw', fun x hx => card_le_one.1 hcard x hx w' hw'⟩,
        sum_singleton] at hv
      have hne := hanti w' hw'
      rw [hv]
      generalize D.u k w = a at *; generalize D.u k w' = b at *
      obtain ⟨a1, a2⟩ := a; obtain ⟨b1, b2⟩ := b
      simp only [nrm, dot, Prod.mk_add_mk, ne_eq, Prod.mk_eq_zero, not_and_or] at *
      -- `|u_w + u_w'|² > 0` as `u_w + u_w' ≠ 0`, and `|u_w - u_w'|² ≥ 0`
      have hpos : 0 < (a1 + b1) ^ 2 + (a2 + b2) ^ 2 := by
        rcases hne with h | h <;>
          nlinarith [sq_pos_of_ne_zero h, sq_nonneg (a1 + b1), sq_nonneg (a2 + b2)]
      constructor <;> nlinarith [sq_nonneg (a1 - b1), sq_nonneg (a2 - b2)]
  refine ⟨?_, fun w hw => (key w hw).1⟩
  rcases (D.circ k I).eq_empty_or_nonempty with he | ⟨w, hw⟩
  · simp [shift, he, nrm]
  · exact (key w hw).2

/-- **The shifted disk avoids `I`**, in lattice units: `|u_w|²/4 + δ ⟨u_w, v⟩` exceeds
`|a - b|²/4 + 1/512` for `w ∈ I`, `δ = 1/256`. On the circle `⟨u_w, v⟩ ≥ 1`. Off the circle
`|u_w|² ≥ |a - b|² + 1` (`Drawing.empty`), and `⟨u_w, v⟩² ≤ 64 |u_w|²` is too small to
compensate. -/
theorem gap {k : E} {I : Finset V} (hI : IsIndep eu ev I) {w : V} (hw : w ∈ I) :
    (D.len k : ℝ) / 4 + 1 / 512 < (nrm (D.u k w) : ℝ) / 4 + dot (D.u k w) (D.shift k I) / 256 := by
  obtain ⟨hv, hd⟩ := D.shift_spec (k := k) hI
  by_cases hc : w ∈ D.circ k I
  · have h1 : (1 : ℝ) ≤ dot (D.u k w) (D.shift k I) := by exact_mod_cast hd w hc
    rw [(mem_filter.1 hc).2]; linarith
  · have hN : D.len k + 1 ≤ nrm (D.u k w) := by
      have : D.len k ≤ nrm (D.u k w) := D.empty k w
      have : nrm (D.u k w) ≠ D.len k := fun h => hc (mem_filter.2 ⟨hw, h⟩)
      omega
    -- Cauchy–Schwarz: `⟨u_w, v⟩² ≤ |u_w|² |v|² ≤ 64 |u_w|²`
    have hcs : dot (D.u k w) (D.shift k I) ^ 2 ≤ nrm (D.u k w) * nrm (D.shift k I) := by
      unfold dot nrm
      nlinarith [sq_nonneg ((D.u k w).1 * (D.shift k I).2 - (D.u k w).2 * (D.shift k I).1)]
    have hX : 128 * D.len k + 1 < 128 * nrm (D.u k w) + 2 * dot (D.u k w) (D.shift k I) := by
      by_contra hcon
      have : D.len k ≤ 16 := D.short k
      nlinarith [mul_le_mul_of_nonneg_left hv (by unfold nrm; positivity :
        0 ≤ nrm (D.u k w))]
    have : ((128 * D.len k + 1 : ℤ) : ℝ) <
        ((128 * nrm (D.u k w) + 2 * dot (D.u k w) (D.shift k I) : ℤ) : ℝ) := by exact_mod_cast hX
    push_cast at this; linarith

/-- **Empty disks.** A drawing scaled into the box `1/16` satisfies the hypotheses of the
gadget theorem. -/
theorem gadget_valid {σ : ℝ} (hσ : 0 < σ) (hσ1 : σ ≤ 1 / 16)
    (hbox : ∀ v, σ * (|((D.pos v).1 : ℝ)| + |((D.pos v).2 : ℝ)|) ≤ 1 / 16) :
    (D.gadget σ).Valid := by
  refine ⟨fun v => ?_, fun x y h => D.inj ?_, fun k => ?_, fun k I hI => ?_⟩
  · simp only [gadget, toR, Pi.smul_apply, smul_eq_mul, abs_mul, abs_of_pos hσ,
      Matrix.cons_val_zero, Matrix.cons_val_one]
    linarith [hbox v]
  · have h0 := congrFun h 0
    have h1 := congrFun h 1
    simp [gadget, toR, hσ.ne'] at h0 h1
    exact Prod.ext (by exact_mod_cast h0) (by exact_mod_cast h1)
  · simp only [gadget, sqn, toR, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, Matrix.cons_val_zero,
      Matrix.cons_val_one, nrm]
    push_cast [Prod.fst_sub, Prod.snd_sub]
    nlinarith [mul_pos hσ hσ]
  -- the centre `σ (m - δ v)`, `m` the midpoint of the edge, `v` the shift, `δ = 1/256`
  obtain ⟨hv, -⟩ := D.shift_spec (k := k) hI
  set v := D.shift k I
  refine ⟨σ • (mid (toR (D.pos (eu k))) (toR (D.pos (ev k))) - (1 / 256 : ℝ) • toR v), ?_,
    fun w hw => ?_⟩
  · -- `σ |m₀| + σ |m₁| ≤ 1/16` (average of two points of the box) and `|v₀|, |v₁| ≤ 8`
    have hv' : (v.1 : ℝ) ^ 2 + (v.2 : ℝ) ^ 2 ≤ 64 := by unfold nrm at hv; exact_mod_cast hv
    have h0 := abs_le_of_sq_le_sq (by nlinarith [sq_nonneg (v.2 : ℝ)] : (v.1 : ℝ) ^ 2 ≤ 8 ^ 2)
      (by norm_num)
    have h1 := abs_le_of_sq_le_sq (by nlinarith [sq_nonneg (v.1 : ℝ)] : (v.2 : ℝ) ^ 2 ≤ 8 ^ 2)
      (by norm_num)
    have key : ∀ x y z : ℝ,
        |σ * ((x + y) / 2 - 1 / 256 * z)| ≤ σ * (|x| + |y|) / 2 + σ * |z| / 256 := by
      intro x y z
      have : |(x + y) / 2 - 1 / 256 * z| ≤ (|x| + |y|) / 2 + |z| / 256 := by
        rw [abs_le]; constructor <;> cases abs_cases x <;> cases abs_cases y <;>
          cases abs_cases z <;> linarith
      rw [abs_mul, abs_of_pos hσ]; nlinarith
    simp only [toR, mid, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, Matrix.cons_val_zero,
      Matrix.cons_val_one]
    nlinarith [hbox (eu k), hbox (ev k), key ((D.pos (eu k)).1) ((D.pos (ev k)).1) v.1,
      key ((D.pos (eu k)).2) ((D.pos (ev k)).2) v.2]
  · -- `|a_w - c|² - |m' - c|² = σ² (|u_w|²/4 + δ ⟨u_w, v⟩)`; multiply `gap` by `σ²`
    have h := mul_lt_mul_of_pos_left (D.gap (k := k) hI hw) (pow_pos hσ 2)
    simp only [gadget, sqn, mid, toR, Pi.sub_apply, Pi.smul_apply, smul_eq_mul,
      Matrix.cons_val_zero, Matrix.cons_val_one, len, u, nrm, dot, Prod.fst_sub, Prod.snd_sub,
      Prod.smul_fst, Prod.smul_snd] at h ⊢
    push_cast [nsmul_eq_mul] at h ⊢
    nlinarith [h]

end Drawing

end NeoTiling.NPHardness
