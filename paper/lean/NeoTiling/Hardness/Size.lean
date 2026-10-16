import NeoTiling.Hardness.Instance

/-!
# Bit size of the instance

Let `B = 24m + 8n + 8` (`bnd n m`), so that `scaleQ n m = 1 / (16 B)` and all coordinates of
`pos` lie in `[0, B]` (`pos_bound`). Every price entry is a polynomial of degree `≤ 2` in
`scaleQ n m` with coefficients in `ℤ / 512`, so it times `D = 2^17 B^2 = 512 (16 B)^2` is an
integer (`priceQ_mul_int`), and it is at most `2` in absolute value (`abs_priceQ_le`). Hence

* `pricesQ_den_le`: `den ≤ 2^17 B^2`;
* `pricesQ_num_le`: `|num| ≤ 2^18 B^2`;
* `outputsQ_den_le`, `outputsQ_num_le`: the outputs are `1, 1/3, 2/3`, so `den, |num| ≤ 3`.
-/

namespace NeoTiling.NPHardness

/-- If `q * D` is an integer, then `den q ≤ D`. -/
lemma den_le_of_mul_eq_int {q : ℚ} {D : ℕ} (hD : 0 < D) {N : ℤ} (h : q * D = N) :
    q.den ≤ D := by
  have hq : q = N / D := by rw [← h]; field_simp
  have := Rat.den_dvd N D
  rw [Rat.divInt_eq_div] at this
  push_cast at this
  rw [← hq] at this
  exact Nat.le_of_dvd hD (by exact_mod_cast this)

/-- If `q * D` is an integer and `|q| ≤ c`, then `|num q| ≤ c D`. -/
lemma natAbs_num_le_of_mul_eq_int {q : ℚ} {D : ℕ} (hD : 0 < D) {N : ℤ} (h : q * D = N)
    {c : ℕ} (hq : |q| ≤ c) : q.num.natAbs ≤ c * D := by
  have hden := den_le_of_mul_eq_int hD h
  have h1 : (q.num.natAbs : ℚ) = |q| * q.den := by
    rw [Nat.cast_natAbs, Int.cast_abs, ← Rat.mul_den_eq_num, abs_mul]; simp
  have h2 : (q.num.natAbs : ℚ) ≤ c * D := by
    rw [h1]; exact mul_le_mul hq (by exact_mod_cast hden) (by positivity) (by positivity)
  exact_mod_cast h2

namespace Graph

variable {n m : ℕ} (G : Graph n m)

/-- The bound `B = 24m + 8n + 8` on the coordinates. -/
def bnd (n m : ℕ) : ℕ := 24 * m + 8 * n + 8

/-- The common denominator `D = 2^17 B^2 = 512 (16 B)^2`. -/
def denom (n m : ℕ) : ℕ := 2 ^ 17 * bnd n m ^ 2

lemma denom_pos : 0 < denom n m := by unfold denom bnd; positivity

/-- `scaleQ n m * (16 B) = 1`. -/
lemma scaleQ_mul : scaleQ n m * (16 * (bnd n m : ℚ)) = 1 := by
  unfold scaleQ bnd; push_cast; field_simp

/-- Every price entry times `D` is an integer. -/
lemma priceQ_mul_int (x : Option (G.Node ⊕ G.Link)) (i : Fin 3) :
    ∃ N : ℤ, G.priceQ x i * (denom n m : ℕ) = N := by
  have hs := scaleQ_mul (n := n) (m := m)
  have hD : ((denom n m : ℕ) : ℚ) = 512 * (16 * (bnd n m : ℚ)) ^ 2 := by
    unfold denom; push_cast; ring
  rw [hD]
  obtain ⟨K, hK⟩ : ∃ K : ℤ, (K : ℚ) = 16 * (bnd n m : ℚ) := ⟨16 * bnd n m, by push_cast; ring⟩
  rw [← hK] at hs ⊢
  have hK0 : (K : ℚ) ≠ 0 := by intro h; rw [h] at hs; simp at hs
  rcases x with _ | v | k
  · refine ⟨128 * K ^ 2, ?_⟩
    simp only [priceQ]; push_cast; ring
  · fin_cases i <;> simp [priceQ, liftQ, sqnQ, aQ]
    all_goals
      generalize (G.pos v).1 = a
      generalize (G.pos v).2 = b
      generalize scaleQ n m = s at hs ⊢
      have hs' : s = 1 / K := by field_simp; linarith
      subst hs'
    · exact ⟨512 * (K * a + K ^ 2 + a ^ 2 + b ^ 2), by push_cast; field_simp; ring⟩
    · exact ⟨512 * (K * b + K ^ 2 + a ^ 2 + b ^ 2), by push_cast; field_simp; ring⟩
    · exact ⟨512 * (-(K * a) - K * b + K ^ 2 + a ^ 2 + b ^ 2), by push_cast; field_simp; ring⟩
  · fin_cases i <;> simp [priceQ, liftQ, sqnQ, aQ, ηQ, Matrix.vecHead, Matrix.vecTail]
    all_goals
      generalize (G.pos (G.linkU k)).1 = a1
      generalize (G.pos (G.linkU k)).2 = b1
      generalize (G.pos (G.linkV k)).1 = a2
      generalize (G.pos (G.linkV k)).2 = b2
      generalize nrm (G.pos (G.linkV k) - G.pos (G.linkU k)) = r
      generalize scaleQ n m = s at hs ⊢
      have hs' : s = 1 / K := by field_simp; linarith
      subst hs'
    · exact ⟨256 * K * (a1 + a2) + 512 * K ^ 2 + 128 * ((a1 + a2) ^ 2 + (b1 + b2) ^ 2) +
        128 * r + 1, by push_cast; field_simp; ring⟩
    · exact ⟨256 * K * (b1 + b2) + 512 * K ^ 2 + 128 * ((a1 + a2) ^ 2 + (b1 + b2) ^ 2) +
        128 * r + 1, by push_cast; field_simp; ring⟩
    · exact ⟨-256 * K * (a1 + a2 + b1 + b2) + 512 * K ^ 2 +
        128 * ((a1 + a2) ^ 2 + (b1 + b2) ^ 2) + 128 * r + 1, by push_cast; field_simp; ring⟩

/-- The lift of a point of the box `0 ≤ a, a₀ + a₁ ≤ 1/16` has entries in `[0, 3/2]`. -/
lemma liftQ_bound (a : Fin 2 → ℚ) (h0 : 0 ≤ a 0) (h1 : 0 ≤ a 1) (h : a 0 + a 1 ≤ 1 / 16)
    (i : Fin 3) : 0 ≤ liftQ a i ∧ liftQ a i ≤ 3 / 2 := by
  have hq : 0 ≤ sqnQ a := by unfold sqnQ; positivity
  have hq2 : sqnQ a ≤ 1 / 256 := by
    unfold sqnQ; nlinarith [mul_nonneg h0 h1]
  fin_cases i <;> simp [liftQ] <;> constructor <;> linarith

/-- Every price entry is at most `2` in absolute value. -/
lemma abs_priceQ_le (x : Option (G.Node ⊕ G.Link)) (i : Fin 3) :
    |G.priceQ x i| ≤ ((2 : ℕ) : ℚ) := by
  have hs : 0 < scaleQ n m := by unfold scaleQ; positivity
  have hB : (8 : ℚ) ≤ bnd n m := by
    unfold bnd; push_cast; linarith [(by positivity : (0:ℚ) ≤ 24 * m + 8 * n)]
  have hsB := scaleQ_mul (n := n) (m := m)
  have hs8 : scaleQ n m ≤ 1 / 128 := by nlinarith
  have hpt : ∀ w, 0 ≤ G.aQ w 0 ∧ 0 ≤ G.aQ w 1 ∧ G.aQ w 0 + G.aQ w 1 ≤ 1 / 16 := by
    intro w
    obtain ⟨a, b, c⟩ := G.pos_bound w
    have a' : (0:ℚ) ≤ (G.pos w).1 := by exact_mod_cast a
    have b' : (0:ℚ) ≤ (G.pos w).2 := by exact_mod_cast b
    have c' : (((G.pos w).1 : ℤ) : ℚ) + ((G.pos w).2 : ℤ) ≤ bnd n m := by
      have : (G.pos w).1 + (G.pos w).2 ≤ ((bnd n m : ℕ) : ℤ) := by
        unfold bnd; push_cast; linarith
      exact_mod_cast this
    simp only [aQ, Matrix.cons_val_zero, Matrix.cons_val_one]
    refine ⟨by positivity, by positivity, ?_⟩
    nlinarith
  rcases x with _ | v | k
  · simp [priceQ, abs_of_pos]; norm_num
  · obtain ⟨h0, h1, h2⟩ := hpt v
    have := liftQ_bound _ h0 h1 h2 i
    simp only [priceQ]; rw [abs_le]; push_cast; constructor <;> linarith [this.1, this.2]
  · obtain ⟨h0, h1, h2⟩ := hpt (G.linkU k)
    obtain ⟨g0, g1, g2⟩ := hpt (G.linkV k)
    have := liftQ_bound (fun j => (G.aQ (G.linkU k) j + G.aQ (G.linkV k) j) / 2)
      (by simp only; linarith) (by simp only; linarith) (by simp only; linarith) i
    have hn := G.drawing.short k
    have hn0 : (0:ℚ) ≤ nrm (G.pos (G.linkV k) - G.pos (G.linkU k)) := by
      unfold nrm; positivity
    have hn16 : (nrm (G.pos (G.linkV k) - G.pos (G.linkU k)) : ℚ) ≤ 16 := by
      exact_mod_cast hn
    have he : 0 ≤ G.ηQ k ∧ G.ηQ k ≤ 1 / 1000 := by
      unfold ηQ
      constructor
      · positivity
      · have h2 : scaleQ n m ^ 2 ≤ 1 / 16384 := by nlinarith
        have h3 : (nrm (G.pos (G.linkV k) - G.pos (G.linkU k)) : ℚ) / 4 + 1 / 512 ≤ 5 := by
          linarith
        have h4 : 0 ≤ (nrm (G.pos (G.linkV k) - G.pos (G.linkU k)) : ℚ) / 4 + 1 / 512 := by
          linarith
        calc _ ≤ (1 / 16384) * 5 := mul_le_mul h2 h3 h4 (by norm_num)
          _ ≤ _ := by norm_num
    simp only [priceQ, Pi.add_apply]; rw [abs_le]; push_cast
    constructor <;> linarith [this.1, this.2, he.1, he.2]

theorem pricesQ_den_le (t : Fin G.numPricesQ) (i : Fin 3) :
    (G.pricesQ t i).den ≤ 2 ^ 17 * bnd n m ^ 2 := by
  obtain ⟨N, h⟩ := G.priceQ_mul_int (G.indexQ.symm t) i
  exact den_le_of_mul_eq_int denom_pos h

theorem pricesQ_num_le (t : Fin G.numPricesQ) (i : Fin 3) :
    (G.pricesQ t i).num.natAbs ≤ 2 ^ 18 * bnd n m ^ 2 := by
  obtain ⟨N, h⟩ := G.priceQ_mul_int (G.indexQ.symm t) i
  have := natAbs_num_le_of_mul_eq_int denom_pos h (G.abs_priceQ_le _ i)
  unfold denom at this; simp only [pricesQ]; omega

/-- The outputs are `1`, `2/3` or `1/3`. -/
lemma outputQ_cases (x : Option (G.Node ⊕ G.Link)) :
    G.outputQ x = 1 ∨ G.outputQ x = 2 / 3 ∨ G.outputQ x = 1 / 3 := by
  rcases x with _ | (⟨_, _, j⟩ | ⟨_, _, j⟩) | k <;> simp only [outputQ, svalQ] <;>
    (try split_ifs) <;> norm_num

theorem outputsQ_den_le (t : Fin G.numPricesQ) : (G.outputsQ t).den ≤ 3 := by
  rcases G.outputQ_cases (G.indexQ.symm t) with h | h | h <;> simp only [outputsQ, h] <;>
    decide +kernel

theorem outputsQ_num_le (t : Fin G.numPricesQ) : (G.outputsQ t).num.natAbs ≤ 3 := by
  rcases G.outputQ_cases (G.indexQ.symm t) with h | h | h <;> simp only [outputsQ, h] <;>
    decide +kernel

end Graph

end NeoTiling.NPHardness
