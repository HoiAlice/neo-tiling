import NeoTiling.Perturbation.Support

/-!
# Weak solvability in a box of prices

Copied unchanged from `OLD/box-perturbation/lean` (not part of the `NeoTiling` library).

Each point `t` may take any price vector `Q t` in the box `[L t, U t]` (coordinatewise, zero
widths allowed).

* `box_iff` (`d ≥ 2`): some `Q` in the boxes makes `y` weakly solvable iff the `2T` corners
  `L 0, …, L (T-1), U 0, …, U (T-1)` carry a vector `w` of the cone of weakly reachable spectra
  with `w (lower corner of t) ≥ y t ≥ w (upper corner of t)`. At `d = 2` this is one flow linear
  program (`PolyHardness.mem_indicatorCone_iff_flow`), so the box problem is polynomial.
-/

namespace NeoTiling.BoxPerturbation

open NeoTiling

variable {d T : ℕ}

/-- Weak solvability in a box: for `d ≥ 2`, positive lower corners and `y ≥ 0`, some `Q` with
`L ≤ Q ≤ U` makes `y` weakly solvable iff some `w` in the cone of weakly reachable spectra of the
corners `Fin.append L U` has `y t ≤ w (L-corner of t)` and `w (U-corner of t) ≤ y t`.

Proof (`Support.lean`). `→`: write `y = Σ λ_k 1_{S_k}` with `S_k` weakly reachable at `Q`; the
corner set of `S_k` (`exists_corner_set`: lower corners supported, upper corners strictly
supported by `{Q r | r ∉ S_k}`) is weakly reachable at the corners and gives `w`. `←`: write
`w = Σ m_k 1_{S_k}`. On the diagonal of box `t` the supported weight is upper and the strictly
supported weight lower semicontinuous, so some `Q t` has strictly supported weight `≤ y t ≤`
supported weight (`exists_point_between`). Every set between the strictly supported and the
supported indices is weakly reachable at `Q` (`isWeakReachable_of_supported`), and
`mem_indicatorCone_of_between` splits `y` over these sets. -/
theorem box_iff (hd : 2 ≤ d) (L U : Fin T → Fin d → ℝ) (y : Fin T → ℝ)
    (hL : ∀ t, L t ∈ orthant d) (hLU : ∀ t i, L t i ≤ U t i) (hy : ∀ t, 0 ≤ y t) :
    (∃ Q : Fin T → Fin d → ℝ, (∀ t i, L t i ≤ Q t i ∧ Q t i ≤ U t i) ∧ WeakSolvable Q y) ↔
      ∃ w ∈ indicatorCone (weakReachableSpectra (Fin.append L U)),
        (∀ t, y t ≤ w (Fin.castAdd T t)) ∧ (∀ t, w (Fin.natAdd T t) ≤ y t) := by
  classical
  set W := Fin.append L U with hW
  constructor
  · rintro ⟨Q, hQ, hws⟩
    have hy' := (weakSolvable_iff hd (fun t i => (hL t i).le.trans (hQ t i).1) hy).1 hws
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
  · rintro ⟨w, hw, hlow, hupp⟩
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
    -- a point of each box between the strictly supported and the supported weight
    have hpt : ∀ t, ∃ q, L t ≤ q ∧ q ≤ U t ∧
        (∑ k, if StrictlySupported W (S k) q then m k else 0) ≤ y t ∧
          y t ≤ ∑ k, if Supported W (S k) q then m k else 0 := by
      intro t
      refine exists_point_between m (fun k => (f k).2) (fun i => hLU t i) ?_ ?_
      · refine (hlow t).trans ((hwS _).trans_le (Finset.sum_le_sum fun k _ => ?_))
        have := IsWeakReachable.supported (hS k) (t := Fin.castAdd T t)
        rw [hW, Fin.append_left] at this
        split_ifs with h1 h2 <;> first | exact absurd (this h1) h2 | simp [m]
      · refine (Finset.sum_le_sum fun k _ => ?_).trans ((hwS _).symm.trans_le (hupp t))
        have := StrictlySupported.mem (P := W) (S := S k) (r := Fin.natAdd T t)
        rw [hW, Fin.append_right] at this
        split_ifs with h1 h2 <;> first | exact absurd (this h1) h2 | simp [m]
    choose Q hQL hQU hQlo hQhi using hpt
    refine ⟨Q, fun t i => ⟨hQL t i, hQU t i⟩,
      (weakSolvable_iff hd (fun t i => (hL t i).le.trans (hQL t i)) hy).2 ?_⟩
    refine mem_indicatorCone_of_between m (fun k => (f k).2)
      (fun k => Finset.univ.filter fun t => StrictlySupported W (S k) (Q t))
      (fun k => Finset.univ.filter fun t => Supported W (S k) (Q t))
      (fun k t ht => by simpa using (by simpa using ht : StrictlySupported W (S k) (Q t)).supported)
      (fun k R h1 h2 => isWeakReachable_of_supported (fun t ht => by simpa using h2 ht)
        fun t ht hst => ht (h1 (by simpa using hst)))
      y (fun t => by simpa using hQlo t) (fun t => by simpa using hQhi t)

end NeoTiling.BoxPerturbation
