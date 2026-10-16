import NeoTiling.Perturbation.Support

/-!
# Weak solvability in a box of prices

Each point `t` may take any price vector `Q t` in the box `[L t, U t]` (coordinatewise, zero
widths allowed).

* `path_of_corners`, `diag_of_corners`: if the corners carry a suitable vector of the cone of
  weakly reachable spectra, the prices can be taken on any prescribed continuous paths from the
  lower to the upper corners (e.g. the diagonals).
* `box_iff` (`d ≥ 2`): some `Q` in the boxes makes `y` weakly solvable iff the `2T` corners
  `L 0, …, L (T-1), U 0, …, U (T-1)` carry a vector `w` of the cone of weakly reachable spectra
  with `w (lower corner of t) ≥ y t ≥ w (upper corner of t)`. At `d = 2` this is one flow linear
  program (`Planar.mem_indicatorCone_iff_flow`), so the box problem is polynomial.
-/

/-! ### Prices on prescribed paths through the boxes -/

namespace NeoTiling.Perturbation

open scoped Classical

variable {d T : ℕ}

/-- **A point of a path between the two weights.** For weights `m ≥ 0` on sets `S k`, if the
start `z 0` of a continuous path has supported weight `≥ c` and its end `z 1` strictly supported
weight `≤ c`, then some `z s`, `s ∈ [0, 1]`, has strictly supported weight `≤ c ≤` supported
weight. Along the path the supported weight is upper and the strictly supported weight lower
semicontinuous (sums of indicators of closed and open sets), so `exists_mem_Icc_between`
applies. -/
theorem exists_path_between {N d n : ℕ} {P : Fin N → Fin d → ℝ} {S : Fin n → Finset (Fin N)}
    (m : Fin n → ℝ) (hm : ∀ k, 0 ≤ m k) {z : ℝ → Fin d → ℝ} (hz : Continuous z) {c : ℝ}
    (h0 : c ≤ ∑ k, if Supported P (S k) (z 0) then m k else 0)
    (h1 : (∑ k, if StrictlySupported P (S k) (z 1) then m k else 0) ≤ c) :
    ∃ s ∈ Set.Icc (0 : ℝ) 1,
      (∑ k, if StrictlySupported P (S k) (z s) then m k else 0) ≤ c ∧
        c ≤ ∑ k, if Supported P (S k) (z s) then m k else 0 := by
  have hsum : ∀ (p : Finset (Fin N) → (Fin d → ℝ) → Prop) (s : ℝ),
      (∑ k, if p (S k) (z s) then m k else 0) =
        ∑ k, Set.indicator {s | p (S k) (z s)} (fun _ => m k) s := by
    intro p s; simp [Set.indicator]
  have hup : UpperSemicontinuous fun s => ∑ k, if Supported P (S k) (z s) then m k else 0 := by
    simp_rw [hsum]
    exact upperSemicontinuous_sum fun k _ =>
      (isClosed_setOf_supported.preimage hz).upperSemicontinuous_indicator (hm k)
  have hlow : LowerSemicontinuous fun s =>
      ∑ k, if StrictlySupported P (S k) (z s) then m k else 0 := by
    simp_rw [hsum]
    exact lowerSemicontinuous_sum fun k _ =>
      (isOpen_setOf_strictlySupported.preimage hz).lowerSemicontinuous_indicator (hm k)
  obtain ⟨s, hs, h1', h2'⟩ := exists_mem_Icc_between hup hlow
    (fun s _ => Finset.sum_le_sum fun k _ => by
      by_cases h : StrictlySupported P (S k) (z s)
      · simp [h, h.supported]
      · simp only [h, if_false]; split_ifs <;> simp [hm k])
    h0 h1
  exact ⟨s, hs, h1', h2'⟩

/-- **Prices on paths from the corners.** For `d ≥ 2`, if `w = Σ m_k 1_{S_k}` in the cone of
weakly reachable spectra of the corners `Fin.append L U` has `y t ≤ w (L-corner of t)` and
`w (U-corner of t) ≤ y t`, then every `Q t` can be taken on a continuous path `z t` from
`z t 0 = L t` to `z t 1 = U t` through nonnegative prices so that `y` is weakly solvable at `Q`.

Proof. On path `t` some point `z t (s t)` has strictly supported weight `≤ y t ≤` supported
weight (`exists_path_between`). Every set between the strictly supported and the supported
indices is weakly reachable at `Q` (`isWeakReachable_of_supported`), and
`mem_indicatorCone_of_between` splits `y` over these sets. -/
theorem path_of_corners (hd : 2 ≤ d) (L U : Fin T → Fin d → ℝ) (z : Fin T → ℝ → Fin d → ℝ)
    (hz : ∀ t, Continuous (z t)) (hz0 : ∀ t, z t 0 = L t) (hz1 : ∀ t, z t 1 = U t)
    (hpos : ∀ t, ∀ s ∈ Set.Icc (0 : ℝ) 1, 0 ≤ z t s) (y : Fin T → ℝ) (hy : ∀ t, 0 ≤ y t)
    (h : ∃ w ∈ indicatorCone (weakReachableSpectra (Fin.append L U)),
      (∀ t, y t ≤ w (Fin.castAdd T t)) ∧ (∀ t, w (Fin.natAdd T t) ≤ y t)) :
    ∃ s : Fin T → ℝ, (∀ t, s t ∈ Set.Icc (0 : ℝ) 1) ∧
      WeakSolvable (fun t => z t (s t)) y := by
  obtain ⟨w, hw, hlow, hupp⟩ := h
  set W := Fin.append L U with hW
  obtain ⟨n, f, g, hfg⟩ := Submodule.mem_span_set'.1 hw
  choose S hS hSg using fun k => (g k).2
  let m : Fin n → ℝ := fun k => f k
  have hwS : ∀ u, w u = ∑ k, if u ∈ S k then m k else 0 := by
    intro u
    simp only [← hfg, Finset.sum_apply, ← hSg, Pi.smul_apply, Set.indicator_apply,
      Finset.mem_coe, Pi.one_apply, smul_ite, smul_zero]
    exact Finset.sum_congr rfl fun k _ => by
      split_ifs
      · exact mul_one _
      · rfl
  have hpt : ∀ t, ∃ s ∈ Set.Icc (0 : ℝ) 1,
      (∑ k, if StrictlySupported W (S k) (z t s) then m k else 0) ≤ y t ∧
        y t ≤ ∑ k, if Supported W (S k) (z t s) then m k else 0 := by
    intro t
    refine exists_path_between m (fun k => (f k).2) (hz t) ?_ ?_
    · refine (hlow t).trans ((hwS _).trans_le (Finset.sum_le_sum fun k _ => ?_))
      have := IsWeakReachable.supported (hS k) (t := Fin.castAdd T t)
      rw [hW, Fin.append_left, ← hz0 t] at this
      split_ifs with h1 h2 <;> first | exact absurd (this h1) h2 | simp [m]
    · refine (Finset.sum_le_sum fun k _ => ?_).trans ((hwS _).symm.trans_le (hupp t))
      have := StrictlySupported.mem (P := W) (S := S k) (r := Fin.natAdd T t)
      rw [hW, Fin.append_right, ← hz1 t] at this
      split_ifs with h1 h2 <;> first | exact absurd (this h1) h2 | simp [m]
  choose s hs hQlo hQhi using hpt
  refine ⟨s, hs, (weakSolvable_iff hd (fun t => hpos t (s t) (hs t)) hy).2 ?_⟩
  refine mem_indicatorCone_of_between m (fun k => (f k).2)
    (fun k => Finset.univ.filter fun t => StrictlySupported W (S k) (z t (s t)))
    (fun k => Finset.univ.filter fun t => Supported W (S k) (z t (s t)))
    (fun k t ht => by simpa using (by simpa using ht : StrictlySupported W (S k) _).supported)
    (fun k R h1 h2 => isWeakReachable_of_supported (fun t ht => by simpa using h2 ht)
      fun t ht hst => ht (h1 (by simpa using hst)))
    y (fun t => by simpa using hQlo t) (fun t => by simpa using hQhi t)

/-- `path_of_corners` with every `Q t` on the diagonal `L t + s t • (U t - L t)`. -/
theorem diag_of_corners (hd : 2 ≤ d) (L U : Fin T → Fin d → ℝ) (y : Fin T → ℝ)
    (hL : ∀ t, 0 ≤ L t) (hLU : ∀ t i, L t i ≤ U t i) (hy : ∀ t, 0 ≤ y t)
    (h : ∃ w ∈ indicatorCone (weakReachableSpectra (Fin.append L U)),
      (∀ t, y t ≤ w (Fin.castAdd T t)) ∧ (∀ t, w (Fin.natAdd T t) ≤ y t)) :
    ∃ s : Fin T → ℝ, (∀ t, s t ∈ Set.Icc (0 : ℝ) 1) ∧
      WeakSolvable (fun t => L t + s t • (U t - L t)) y := by
  refine path_of_corners hd L U (fun t s => L t + s • (U t - L t)) (fun t => by fun_prop)
    (fun t => by simp) (fun t => by simp) (fun t s hs i => ?_) y hy h
  have := mul_nonneg hs.1 (sub_nonneg.2 (hLU t i))
  simp only [Pi.add_apply, Pi.smul_apply, Pi.sub_apply, smul_eq_mul, Pi.zero_apply]
  linarith [show (0 : ℝ) ≤ L t i from hL t i]

/-! ### The box criterion -/

/-- Weak solvability in a box: for `d ≥ 2`, nonnegative lower corners and `y ≥ 0`, some `Q` with
`L ≤ Q ≤ U` makes `y` weakly solvable iff some `w` in the cone of weakly reachable spectra of the
corners `Fin.append L U` has `y t ≤ w (L-corner of t)` and `w (U-corner of t) ≤ y t`.

Proof. `→`: write `y = Σ λ_k 1_{S_k}` with `S_k` weakly reachable at `Q`; the corner set of
`S_k` (`exists_corner_set`: lower corners supported, upper corners strictly supported by
`{Q r | r ∉ S_k}`) is weakly reachable at the corners and gives `w`. `←`: `path_of_corners` on
the diagonals `L t + s • (U t - L t)`, which stay in the boxes. -/
theorem box_iff (hd : 2 ≤ d) (L U : Fin T → Fin d → ℝ) (y : Fin T → ℝ)
    (hL : ∀ t, 0 ≤ L t) (hLU : ∀ t i, L t i ≤ U t i) (hy : ∀ t, 0 ≤ y t) :
    (∃ Q : Fin T → Fin d → ℝ, (∀ t i, L t i ≤ Q t i ∧ Q t i ≤ U t i) ∧ WeakSolvable Q y) ↔
      ∃ w ∈ indicatorCone (weakReachableSpectra (Fin.append L U)),
        (∀ t, y t ≤ w (Fin.castAdd T t)) ∧ (∀ t, w (Fin.natAdd T t) ≤ y t) := by
  classical
  set W := Fin.append L U with hW
  constructor
  · rintro ⟨Q, hQ, hws⟩
    have hy' := (weakSolvable_iff hd (fun t i => (hL t i).trans (hQ t i).1) hy).1 hws
    suffices ∀ x ∈ indicatorCone (weakReachableSpectra Q),
        ∃ w ∈ indicatorCone (weakReachableSpectra W),
          ∀ t, x t ≤ w (Fin.castAdd T t) ∧ w (Fin.natAdd T t) ≤ x t by
      obtain ⟨w, hw, h⟩ := this y hy'
      exact ⟨w, hw, fun t => (h t).1, fun t => (h t).2⟩
    intro x hx
    induction hx using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨S, hS, rfl⟩ := hx
      obtain ⟨S', hS', h⟩ := exists_corner_set hS hQ
      refine ⟨(S' : Set _).indicator 1, Submodule.subset_span ⟨S', hS', rfl⟩, fun t => ⟨?_, ?_⟩⟩
      · simp only [Set.indicator_apply, Finset.mem_coe, Pi.one_apply]
        split_ifs with h1 h2 <;> first | exact absurd ((h t).1 h1) h2 | norm_num
      · simp only [Set.indicator_apply, Finset.mem_coe, Pi.one_apply]
        split_ifs with h1 h2 <;> first | exact absurd ((h t).2 h1) h2 | norm_num
    | zero => exact ⟨0, zero_mem _, fun t => by simp⟩
    | add x z _ _ hx hz =>
      obtain ⟨w, hw, h⟩ := hx
      obtain ⟨w', hw', h'⟩ := hz
      exact ⟨w + w', add_mem hw hw', fun t =>
        ⟨add_le_add (h t).1 (h' t).1, add_le_add (h t).2 (h' t).2⟩⟩
    | smul c x _ hx =>
      obtain ⟨w, hw, h⟩ := hx
      refine ⟨c • w, Submodule.smul_mem _ c hw, fun t => ⟨?_, ?_⟩⟩ <;>
        simpa only [Pi.smul_apply, NNReal.smul_def, smul_eq_mul] using
          mul_le_mul_of_nonneg_left (by first | exact (h t).1 | exact (h t).2) c.2
  · intro h
    obtain ⟨s, hs, hws⟩ := diag_of_corners hd L U y hL hLU hy h
    refine ⟨fun t => L t + s t • (U t - L t), fun t i => ⟨?_, ?_⟩, hws⟩ <;>
      simp only [Pi.add_apply, Pi.smul_apply, Pi.sub_apply, smul_eq_mul]
    · nlinarith [(hs t).1, hLU t i]
    · nlinarith [(hs t).2, hLU t i]

end NeoTiling.Perturbation
