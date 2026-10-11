import Complexity

/-!
# The column problem on the gadget, and dimensions `d ≥ 3`

* `exists_col_iff_exists_indep` (Theorem 3.4): with weights `0` at the marker, `-1` at the
  rewards and `n + 1` at the heavy points, some (weakly) reachable `S` has weight at least
  `(n + 1) m - n + k` iff the graph has an independent set of size at least `k`. So
  `max w(S) = (n + 1) m - n + α(G)`.
* `isReachableB_dupCoord` (Corollary 3.6): repeating coordinate `0` in the coordinates
  `i ≥ d₀` does not change the (weakly) reachable sets.
-/

namespace NeoTiling.Complexity

open Finset

/-- **Gabriel disks.** The conversion of the Gabriel hypotheses into the `hdisk` hypothesis of
`isReachableB_compl`, as in the proof of `mem_indicatorCone_iff_inStabB_of_gabriel`. -/
theorem hdisk_of_gabriel {b : Bool} {n m : ℕ} {eu ev : Fin m → Fin n} {a : Fin n → Fin 2 → ℝ}
    {η : Fin m → ℝ} {γ : ℝ} (hγ0 : 0 < γ) (hγ1 : γ ≤ 1 / 2)
    (ha : ∀ v, |a v 0| + |a v 1| ≤ 1 / 8)
    (hne : ∀ k, a (eu k) ≠ a (ev k))
    (hgab : ∀ k, ∀ w, w ≠ eu k → w ≠ ev k →
      sqn (a (eu k) - a (ev k)) / 4 + γ ≤ sqn (a w - mid (a (eu k)) (a (ev k))))
    (hηγ : ∀ k, Ok b (sqn (a (eu k) - a (ev k)) * (1 / 4 + γ) - η k)) :
    ∀ k, ∀ x, (x = eu k ∨ x = ev k) → ∃ c : Fin 2 → ℝ, |c 0| + |c 1| ≤ 1 / 4 ∧
      ∀ w, w ≠ x → Ok b (sqn (a w - c) - η k - sqn (mid (a (eu k)) (a (ev k)) - c)) := by
  -- `sqn (u - v)` and `mid u v` are symmetric, so the edge may be oriented towards `x`
  have hmid : ∀ u v : Fin 2 → ℝ, mid u v = mid v u := fun u v => by funext i; simp [mid, add_comm]
  have hsqn : ∀ u v : Fin 2 → ℝ, sqn (u - v) = sqn (v - u) := fun u v => by simp [sqn]; ring
  have huv : ∀ k, eu k ≠ ev k := fun k h => hne k (by rw [h])
  intro k x hx
  rcases hx with rfl | rfl
  · obtain ⟨c, hc, hcw⟩ := exists_disk_of_gabriel a ha hγ0 hγ1 (huv k).symm
      fun w h1 h2 => by rw [hsqn, hmid]; exact hgab k w h2 h1
    refine ⟨c, hc, fun w hw => ?_⟩
    have := (hηγ k).add_nonneg (sub_nonneg.2 (hcw w hw))
    rw [hsqn, hmid] at this
    convert this using 1; ring
  · obtain ⟨c, hc, hcw⟩ := exists_disk_of_gabriel a ha hγ0 hγ1 (huv k) (hgab k)
    refine ⟨c, hc, fun w hw => ?_⟩
    convert (hηγ k).add_nonneg (sub_nonneg.2 (hcw w hw)) using 1; ring

/-- **Weight of a set.** With `w z = 0`, `w (rew v) = -1`, `w (hv k) = n + 1`, the weight of
`S` is `(n + 1) · #{k | hv k ∈ S} - #{v | rew v ∈ S}`. -/
theorem sum_weight {n m T : ℕ} {z : Fin T} {rew : Fin n → Fin T} {hv : Fin m → Fin T}
    (hrew_inj : Function.Injective rew) (hhv_inj : Function.Injective hv)
    (hz_rew : ∀ v, rew v ≠ z) (hz_hv : ∀ k, hv k ≠ z)
    (hrew_hv : ∀ v k, rew v ≠ hv k)
    (hall : ∀ t, t = z ∨ (∃ v, t = rew v) ∨ ∃ k, t = hv k)
    (w : Fin T → ℤ) (hwz : w z = 0) (hwr : ∀ v, w (rew v) = -1)
    (hwh : ∀ k, w (hv k) = n + 1) (S : Finset (Fin T)) :
    ∑ t ∈ S, w t = (n + 1) * ((univ.filter fun k => hv k ∈ S).card : ℤ) -
      (univ.filter fun v => rew v ∈ S).card := by
  classical
  -- `w t = (n + 1) · #{k | hv k = t} - #{v | rew v = t}`, then swap the sums
  have hw : ∀ t, w t = (n + 1) * ∑ k, (if hv k = t then 1 else 0) -
      ∑ v, (if rew v = t then 1 else 0) := by
    have := fun v k => (hrew_hv v k).symm
    intro t
    rcases hall t with rfl | ⟨v, rfl⟩ | ⟨k, rfl⟩ <;>
      simp [hwz, hwr, hwh, hz_rew, hz_hv, hrew_hv, this, hrew_inj.eq_iff, hhv_inj.eq_iff]
  rw [sum_congr rfl fun t _ => hw t, sum_sub_distrib, ← mul_sum, sum_comm, sum_comm (s := S)]
  simp [sum_boole]

/-- **Column problem on the gadget (Theorem 3.4).** Same gadget hypotheses as
`mem_indicatorCone_iff_inStabB_of_gabriel`, heavy indices pairwise distinct. With the weights
`w z = 0`, `w (rew v) = -1`, `w (hv k) = n + 1`, a (weakly) reachable set of weight at least
`(n + 1) m - n + k` exists iff an independent set of size at least `k` exists.
By `sum_weight`, `w(S) = (n + 1) · #(heavy in S) - #(rewards in S)`.
(→) If a heavy point is missing, `w(S) ≤ (n + 1)(m - 1) < (n + 1) m - n`. So all heavy points
lie in `S`, the missing rewards `I` are independent (`indep_of_isWeakReachable`) and
`w(S) = (n + 1) m - n + |I|`. (←) `S = univ \ rew '' I` is reachable by `isReachableB_compl`
(disks from `hdisk_of_gabriel`) and has the same weight. -/
theorem exists_col_iff_exists_indep {b : Bool} {n m T : ℕ}
    {P : Fin T → Fin 3 → ℝ} {z : Fin T} {rew : Fin n → Fin T} {hv : Fin m → Fin T}
    {eu ev : Fin m → Fin n} {a : Fin n → Fin 2 → ℝ} {η : Fin m → ℝ}
    {γ : ℝ} (hγ0 : 0 < γ) (hγ1 : γ ≤ 1 / 2)
    (hrew_inj : Function.Injective rew) (hhv_inj : Function.Injective hv)
    (hz_rew : ∀ v, rew v ≠ z) (hz_hv : ∀ k, hv k ≠ z)
    (hrew_hv : ∀ v k, rew v ≠ hv k)
    (hall : ∀ t, t = z ∨ (∃ v, t = rew v) ∨ ∃ k, t = hv k)
    (hPz : ∀ t, t ≠ z → ∀ i, P z i < P t i)
    (hPrew : ∀ v, P (rew v) = lift (a v))
    (hPhv : ∀ k, P (hv k) = lift (mid (a (eu k)) (a (ev k))) + η k • one3)
    (ha : ∀ v, |a v 0| + |a v 1| ≤ 1 / 8)
    (hsep : ∀ v w, v ≠ w → Ok b (sqn (a w - a v)))
    (hne : ∀ k, a (eu k) ≠ a (ev k))
    (hgab : ∀ k, ∀ w, w ≠ eu k → w ≠ ev k →
      sqn (a (eu k) - a (ev k)) / 4 + γ ≤ sqn (a w - mid (a (eu k)) (a (ev k))))
    (hη : ∀ k, sqn (a (eu k) - a (ev k)) / 4 < η k)
    (hηγ : ∀ k, Ok b (sqn (a (eu k) - a (ev k)) * (1 / 4 + γ) - η k))
    (w : Fin T → ℤ) (hwz : w z = 0) (hwr : ∀ v, w (rew v) = -1)
    (hwh : ∀ k, w (hv k) = n + 1) (k : ℕ) :
    (∃ S : Finset (Fin T), IsReachableB b P S ∧
        ((n + 1) * m - n + k : ℤ) ≤ ∑ t ∈ S, w t) ↔
      ∃ I : Finset (Fin n), Indep eu ev I ∧ k ≤ I.card := by
  classical
  have hW := sum_weight hrew_inj hhv_inj hz_rew hz_hv hrew_hv hall w hwz hwr hwh
  constructor
  · rintro ⟨S, hS, hw⟩
    rw [hW] at hw
    set H := (univ.filter fun k => hv k ∈ S).card
    have hH : H ≤ m := by simpa using card_filter_le (univ : Finset (Fin m)) (fun k => hv k ∈ S)
    have hR : ((univ.filter fun v => rew v ∈ S).card : ℤ) +
        (univ.filter fun v => rew v ∉ S).card = n := by
      have := card_filter_add_card_filter_not (s := univ) (fun v => rew v ∈ S)
      exact_mod_cast (by simpa using this)
    -- a missing heavy point costs `n + 1`, more than all rewards can bring
    have hfull : H = m := by
      by_contra hne
      have : (H : ℤ) + 1 ≤ m := by exact_mod_cast (by omega : H + 1 ≤ m)
      nlinarith
    have hheavy : ∀ k, hv k ∈ S :=
      fun k => card_filter_eq_iff.1 (by simpa using hfull) k (mem_univ _)
    refine ⟨_, indep_of_isWeakReachable hPrew hPhv hη hS.isWeakReachable hheavy, ?_⟩
    rw [hfull] at hw
    exact_mod_cast (by linarith : (k : ℤ) ≤ (univ.filter fun v => rew v ∉ S).card)
  · rintro ⟨I, hI, hk⟩
    refine ⟨univ \ I.image rew,
      isReachableB_compl hz_rew hall hPz hPrew hPhv (fun v => (ha v).trans (by norm_num))
        hsep (hdisk_of_gabriel hγ0 hγ1 ha hne hgab hηγ) hI, ?_⟩
    -- all heavy points and the rewards outside `I` are in the set
    have e1 : (univ.filter fun k => hv k ∈ univ \ I.image rew) = univ :=
      filter_true_of_mem fun k _ => by simpa using fun v _ => hrew_hv v k
    have e2 : (univ.filter fun v => rew v ∈ univ \ I.image rew) = univ \ I := by
      ext v; simp [hrew_inj.eq_iff]
    have hI : I.card ≤ n := by simpa using card_le_univ I
    rw [hW, e1, e2, card_sdiff_of_subset (subset_univ I)]
    simp only [card_univ, Fintype.card_fin]
    push_cast [hI]
    linarith [(by exact_mod_cast hk : (k : ℤ) ≤ I.card)]

/-- Prices in dimension `d ≥ d₀`: coordinate `i < d₀` is kept, every coordinate `i ≥ d₀`
repeats coordinate `0`. -/
def dupCoord {T d₀ : ℕ} (d : ℕ) (hd₀ : 0 < d₀) (P : Fin T → Fin d₀ → ℝ) :
    Fin T → Fin d → ℝ :=
  fun t i => if h : (i : ℕ) < d₀ then P t ⟨i, h⟩ else P t ⟨0, hd₀⟩

/-- **Higher dimensions (Corollary 3.6).** Repeating a coordinate does not change the
(weakly) reachable sets: a witness `ξ` for the new prices gives the witness
`(ξ₀ + ∑_{i ≥ d₀} ξᵢ, ξ₁, …, ξ_{d₀-1})` with the same inner products, and a witness for the
old prices padded by zeros is a witness for the new ones. -/
theorem isReachableB_dupCoord {b : Bool} {T d₀ d : ℕ} (hd₀ : 0 < d₀) (hd : d₀ ≤ d)
    (P : Fin T → Fin d₀ → ℝ) (S : Finset (Fin T)) :
    IsReachableB b (dupCoord d hd₀ P) S ↔ IsReachableB b P S := by
  obtain ⟨r, rfl⟩ := Nat.exists_eq_add_of_le hd
  set o : Fin d₀ := ⟨0, hd₀⟩
  -- the first `d₀` new coordinates are the old ones, the last `r` repeat coordinate `o`
  have hc : ∀ t j, dupCoord (d₀ + r) hd₀ P t (Fin.castAdd r j) = P t j := by
    simp [dupCoord]
  have hn : ∀ t i, dupCoord (d₀ + r) hd₀ P t (Fin.natAdd d₀ i) = P t o := by simp [dupCoord, o]
  constructor
  · intro hS t ht
    obtain ⟨ξ, h0, hne, hξ⟩ := hS t ht
    -- move the weight `R` of the repeated coordinates to coordinate `o`
    set R := ∑ i, ξ (Fin.natAdd d₀ i)
    have hR : 0 ≤ R := sum_nonneg fun i _ => h0 _
    let ξ' : Fin d₀ → ℝ := fun j => ξ (Fin.castAdd r j) + if j = o then R else 0
    have hξ' : ∀ j, 0 ≤ ξ (Fin.castAdd r j) ∧ 0 ≤ if j = o then R else 0 :=
      fun j => ⟨h0 _, by split_ifs <;> simp [hR]⟩
    have hdot : ∀ s, ξ ⬝ᵥ dupCoord (d₀ + r) hd₀ P s = ξ' ⬝ᵥ P s := fun s => by
      simp [dotProduct, Fin.sum_univ_add, hc, hn, ξ', R, add_mul, sum_add_distrib, sum_mul]
    refine ⟨ξ', fun j => add_nonneg (hξ' j).1 (hξ' j).2, fun h => hne ?_, fun s hs => ?_⟩
    · -- if `ξ' = 0` then both nonnegative summands of every `ξ' j` vanish
      have hz : ∀ j, ξ (Fin.castAdd r j) = 0 ∧ (if j = o then R else 0) = 0 :=
        fun j => (add_eq_zero_iff_of_nonneg (hξ' j).1 (hξ' j).2).1 (congrFun h j)
      have hr := (sum_eq_zero_iff_of_nonneg fun i _ => h0 (Fin.natAdd d₀ i)).1
        (by simpa using (hz o).2 : R = 0)
      funext i
      refine Fin.addCases (fun j => (hz j).1) (fun i => hr i (mem_univ _)) i
    · simpa [dotProduct_sub, hdot] using hξ s hs
  · intro hS t ht
    obtain ⟨ξ, h0, hne, hξ⟩ := hS t ht
    -- pad by zeros
    have hdot : ∀ s, Fin.append ξ 0 ⬝ᵥ dupCoord (d₀ + r) hd₀ P s = ξ ⬝ᵥ P s := fun s => by
      simp [dotProduct, Fin.sum_univ_add, hc]
    refine ⟨Fin.append ξ 0, Fin.addCases (fun j => by simpa using h0 j) (by simp),
      fun h => hne (funext fun j => by simpa using congrFun h (Fin.castAdd r j)),
      fun s hs => by simpa [dotProduct_sub, hdot] using hξ s hs⟩

end NeoTiling.Complexity
