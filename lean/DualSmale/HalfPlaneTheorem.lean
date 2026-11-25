/-
  DualSmale/HalfPlaneTheorem.lean

  THEOREM 1 (All-n Supporting Half-Plane Dual Smale Theorem, exact 1/n + strict uniqueness):
  For EVERY degree n >= 2 and EVERY complex polynomial P(z) = z + a_2 z^2 + ... + a_n z^n
  with critical points zeta_1, ..., zeta_{n-1}:
  If there exists a critical point zeta_j != 0 such that ALL critical points satisfy
    Re(zeta_k / zeta_j) >= 1
  (equivalently, all normalized inverse ratios w_k = zeta_j / zeta_k lie in the closed
   disk D(1/2, 1/2) = {w : ‖w - 1/2‖ <= 1/2}), then:
    ‖P(zeta_j) / zeta_j‖ >= 1 / n.
  Moreover, for EVERY n >= 3, equality holds IF AND ONLY IF all critical points coincide
  (w_k = 1 for all k, i.e., P(z) = (1 - (1 - z / zeta_j)^n) / (n / zeta_j)).
-/

import DualSmale.PolynomialReduction
import Mathlib.Analysis.Complex.AbsMax

open scoped BigOperators
open Polynomial Complex

namespace DualSmale

/-- **Enestrom-Kakeya Zero-Freeness of `R_n(u)` on the Closed Unit Disk `‖u‖ ≤ 1`**:
    For EVERY `n ≥ 2` and EVERY `u : ℂ` with `‖u‖ ≤ 1`, `R_n(u) ≠ 0`. -/
theorem RnPoly_ne_zero_of_norm_le_one {n : ℕ} (hn : 2 ≤ n) {u : ℂ} (hu : ‖u‖ ≤ 1) :
    RnPoly n u ≠ 0 := by
  by_cases hu1 : u = 1
  · subst hu1
    intro h0
    have hR1 : 2 * RnPoly n 1 = (n : ℂ) * ((n - 1 : ℕ) : ℂ) := by
      unfold RnPoly
      simp only [one_pow, mul_one]
      have hnat : ∀ m : ℕ, 2 * ∑ j ∈ Finset.range (m + 1), (m + 1 - j) = (m + 2) * (m + 1) := by
        intro m
        induction m with
        | zero => decide
        | succ m ih =>
          rw [Finset.sum_range_succ']
          simp only [Nat.sub_zero, show ∀ x, m + 1 + 1 - (x + 1) = m + 1 - x by intro x; omega]
          linarith
      obtain ⟨m, rfl⟩ : ∃ m, n = m + 2 := ⟨n - 2, by omega⟩
      simp only [show m + 2 - 1 = m + 1 by omega]
      exact_mod_cast hnat m
    rw [h0, mul_zero] at hR1
    have hpos : (n : ℂ) * ((n - 1 : ℕ) : ℂ) ≠ 0 :=
      mul_ne_zero (Nat.cast_ne_zero.mpr (by omega)) (Nat.cast_ne_zero.mpr (by omega))
    exact hpos hR1.symm
  · intro h0
    have htel := one_sub_mul_RnPoly hn u
    rw [h0, mul_zero] at htel
    have hsum_eq : ∑ k ∈ Finset.range (n - 1), u ^ (k + 1) = ((n - 1 : ℕ) : ℂ) := by
      linear_combination htel
    have hre_eq : ∑ k ∈ Finset.range (n - 1), (u ^ (k + 1)).re = ((n - 1 : ℕ) : ℝ) := by
      have h := congrArg Complex.re hsum_eq
      simp only [Complex.re_sum, Complex.natCast_re] at h
      exact h
    -- Since u ≠ 1 and ‖u‖ ≤ 1, we have strictly u.re < 1!
    have hure_lt : u.re < 1 := by
      have hns : u.re ^ 2 + u.im ^ 2 ≤ 1 := by
        have h1 : Complex.normSq u ≤ 1 := by rw [Complex.normSq_eq_norm_sq]; nlinarith [norm_nonneg u]
        rw [Complex.normSq_apply] at h1; linarith
      by_contra hge
      push Not at hge
      have hre1 : u.re = 1 := by nlinarith [sq_nonneg u.im]
      have him0 : u.im = 0 := by nlinarith [sq_nonneg u.im]
      apply hu1
      exact Complex.ext hre1 him0
    -- Every term has (u^(k+1)).re ≤ ‖u^(k+1)‖ ≤ 1, and k = 0 gives strictly u.re < 1!
    have hterm_le : ∀ k ∈ Finset.range (n - 1), (u ^ (k + 1)).re ≤ 1 := by
      intro k _
      calc (u ^ (k + 1)).re ≤ ‖u ^ (k + 1)‖ := Complex.re_le_norm _
        _ = ‖u‖ ^ (k + 1) := norm_pow u (k + 1)
        _ ≤ 1 ^ (k + 1) := pow_le_pow_left₀ (norm_nonneg u) hu (k + 1)
        _ = 1 := one_pow _
    have hsum_lt : ∑ k ∈ Finset.range (n - 1), (u ^ (k + 1)).re < ((n - 1 : ℕ) : ℝ) := by
      obtain ⟨m, rfl⟩ : ∃ m, n = m + 2 := ⟨n - 2, by omega⟩
      simp only [show m + 2 - 1 = m + 1 by omega]
      rw [Finset.sum_range_succ']
      simp only [zero_add, pow_one]
      have hrest_le : ∑ x ∈ Finset.range m, (u ^ (x + 1 + 1)).re ≤ (m : ℝ) := by
        calc ∑ x ∈ Finset.range m, (u ^ (x + 1 + 1)).re
            ≤ ∑ _x ∈ Finset.range m, (1 : ℝ) := Finset.sum_le_sum (fun x hx =>
                hterm_le (x + 1) (Finset.mem_range.mpr (by have := Finset.mem_range.mp hx; omega)))
          _ = (m : ℝ) := by simp
      push_cast; linarith
    linarith

/-- **Zero-Freeness of `G_n(w)` on `‖1 - w‖ ≤ 1`** (hence on the entire disk `‖w - 1/2‖ ≤ 1/2`!). -/
theorem GnPoly_ne_zero_of_norm_one_sub_le_one {n : ℕ} (hn : 2 ≤ n) {w : ℂ} (hw : ‖1 - w‖ ≤ 1) :
    GnPoly n w ≠ 0 := by
  intro h0
  have h := GnPoly_eq_RnPoly hn w
  rw [h0, mul_zero] at h
  exact RnPoly_ne_zero_of_norm_le_one hn hw h.symm

lemma norm_one_sub_le_one_of_mem_halfDisk {w : ℂ} (hw : ‖w - (1 / 2 : ℂ)‖ ≤ 1 / 2) :
    ‖1 - w‖ ≤ 1 := by
  calc ‖1 - w‖ = ‖(1 / 2 : ℂ) - (w - 1 / 2)‖ := by ring_nf
    _ ≤ ‖(1 / 2 : ℂ)‖ + ‖w - 1 / 2‖ := norm_sub_le _ _
    _ ≤ 1 / 2 + 1 / 2 := by
        have hhalf : ‖(1 / 2 : ℂ)‖ = 1 / 2 := by norm_num
        linarith
    _ = 1 := by norm_num

/-- **Boundary Magic Identity on `∂D(1/2, 1/2)`**:
    For every `n ≥ 2` and every `w : ℂ` on the boundary circle `‖w - 1/2‖ = 1/2`,
    we have `1 ≤ ‖(n : ℂ) * GnPoly n w‖`, with STRICT inequality `1 < ‖(n : ℂ) * GnPoly n w‖`
    whenever `n ≥ 3` and `w ≠ 1`! -/
theorem GnPoly_boundary_lower_bound {n : ℕ} (hn : 2 ≤ n) {w : ℂ}
    (hw : ‖w - (1 / 2 : ℂ)‖ = 1 / 2) :
    1 ≤ ‖(n : ℂ) * GnPoly n w‖ ∧ (3 ≤ n → w ≠ 1 → 1 < ‖(n : ℂ) * GnPoly n w‖) := by
  -- On ‖w - 1/2‖ = 1/2, we have ‖w‖^2 = w.re =: x ∈ [0, 1].
  set x : ℝ := w.re
  have hcircle : Complex.normSq w = x := by
    have hns : Complex.normSq (w - (1 / 2 : ℂ)) = 1 / 4 := by
      rw [Complex.normSq_eq_norm_sq, hw]; norm_num
    rw [Complex.normSq_apply] at hns
    simp only [Complex.sub_re, Complex.sub_im, Complex.div_ofNat_re, Complex.div_ofNat_im,
      Complex.one_re, Complex.one_im, zero_div, sub_zero] at hns
    rw [Complex.normSq_apply]
    dsimp [x]; linarith
  have hw_sq : ‖w‖ ^ 2 = x := by rw [← Complex.normSq_eq_norm_sq, hcircle]
  have hx_nn : 0 ≤ x := by rw [← hw_sq]; positivity
  have hx_le1 : x ≤ 1 := by
    have hle : ‖w‖ ≤ 1 := by
      calc ‖w‖ = ‖(w - 1 / 2) + 1 / 2‖ := by ring_nf
        _ ≤ ‖w - (1 / 2 : ℂ)‖ + ‖(1 / 2 : ℂ)‖ := norm_add_le _ _
        _ = 1 := by rw [hw]; norm_num
    nlinarith [norm_nonneg w]
  -- Case w = 0: n * G_n(0) = n / 2 ≥ 1 (strictly > 1 for n ≥ 3)
  by_cases hw0 : w = 0
  · subst hw0
    have hG0 : GnPoly n 0 = 1 / 2 := by
      have h := GnPoly_eq_RnPoly hn 0
      simp only [sub_zero] at h
      have hR1 : 2 * RnPoly n 1 = (n : ℂ) * ((n - 1 : ℕ) : ℂ) := by
        unfold RnPoly; simp only [one_pow, mul_one]
        have hnat : ∀ m : ℕ, 2 * ∑ j ∈ Finset.range (m + 1), (m + 1 - j) = (m + 2) * (m + 1) := by
          intro m
          induction m with
          | zero => decide
          | succ m ih =>
            rw [Finset.sum_range_succ']
            simp only [Nat.sub_zero, show ∀ x, m + 1 + 1 - (x + 1) = m + 1 - x by intro x; omega]
            linarith
        obtain ⟨m, rfl⟩ : ∃ m, n = m + 2 := ⟨n - 2, by omega⟩
        simp only [show m + 2 - 1 = m + 1 by omega]
        exact_mod_cast hnat m
      have hn_ne : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
      have hm_ne : ((n - 1 : ℕ) : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
      apply mul_left_cancel₀ (mul_ne_zero hn_ne hm_ne)
      linear_combination h + hR1 / 2
    rw [hG0, show (n : ℂ) * (1 / 2 : ℂ) = (((n : ℝ) / 2 : ℝ) : ℂ) by push_cast; ring,
      Complex.norm_real, Real.norm_of_nonneg (by positivity)]
    constructor
    · have : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
      linarith
    · intro hn3 _
      have : (3 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn3
      linarith
  -- Case w ≠ 0: x = ‖w‖^2 > 0!
  have hx_pos : 0 < x := by
    rw [← hw_sq]; exact sq_pos_of_pos (norm_pos_iff.mpr hw0)
  -- Exact norm squares on the circle:
  have h1w_sq : ‖1 - w‖ ^ 2 = 1 - x := by
    rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
    have hns := hcircle; rw [Complex.normSq_apply] at hns
    simp only [Complex.sub_re, Complex.sub_im, Complex.one_re, Complex.one_im, zero_sub]
    dsimp [x] at hns ⊢; linarith
  have hnw_sq : ‖(n : ℂ) * w - 1‖ ^ 2 = ((n : ℝ) ^ 2 - 2 * (n : ℝ)) * x + 1 := by
    rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
    have hns := hcircle; rw [Complex.normSq_apply] at hns
    simp only [Complex.sub_re, Complex.sub_im, Complex.mul_re, Complex.mul_im,
      Complex.natCast_re, Complex.natCast_im, zero_mul, sub_zero, add_zero,
      Complex.one_re, Complex.one_im]
    dsimp [x] at hns ⊢
    nlinarith
  -- Power bound: ‖1 - w‖^n ≤ 1 - x (since ‖1 - w‖^2 = 1 - x ∈ [0, 1] and n ≥ 2)
  have hpow_le : ‖1 - w‖ ^ n ≤ 1 - x := by
    have hle1 : ‖1 - w‖ ≤ 1 := by nlinarith [norm_nonneg (1 - w), h1w_sq, hx_nn]
    calc ‖1 - w‖ ^ n ≤ ‖1 - w‖ ^ 2 := pow_le_pow_of_le_one (norm_nonneg _) hle1 hn
      _ = 1 - x := h1w_sq
  -- Reverse triangle inequality on closed form:
  -- ‖n * G_n(w)‖ * ((n - 1) * x) = ‖n * w - 1 + (1 - w)^n‖ ≥ ‖n * w - 1‖ - ‖1 - w‖^n
  have hcf := GnPoly_closed_form hn w
  have hnorm_cf : ((n - 1 : ℕ) : ℝ) * x * ‖(n : ℂ) * GnPoly n w‖ =
      ‖(n : ℂ) * w - 1 + (1 - w) ^ n‖ := by
    have hre : (n : ℂ) * ((n - 1 : ℕ) : ℂ) * w ^ 2 * GnPoly n w =
        ((n - 1 : ℕ) : ℂ) * w ^ 2 * ((n : ℂ) * GnPoly n w) := by ring
    conv_rhs => rw [← hcf, hre, norm_mul, norm_mul, norm_pow, Complex.norm_natCast, hw_sq]
  have hrev : ‖(n : ℂ) * w - 1‖ - ‖1 - w‖ ^ n ≤ ‖(n : ℂ) * w - 1 + (1 - w) ^ n‖ := by
    have h1 := norm_sub_le ((n : ℂ) * w - 1 + (1 - w) ^ n) ((1 - w) ^ n)
    rw [add_sub_cancel_right, norm_pow] at h1
    linarith
  -- Magic algebraic identity: ((n^2 - 2n) x + 1) - (1 + (n - 2) x)^2 = (n - 2)^2 x (1 - x) ≥ 0!
  have hn_ge2 : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hmagic : ((n : ℝ) ^ 2 - 2 * (n : ℝ)) * x + 1 - (1 + ((n : ℝ) - 2) * x) ^ 2 =
      ((n : ℝ) - 2) ^ 2 * x * (1 - x) := by ring
  have hlin_nn : 0 ≤ 1 + ((n : ℝ) - 2) * x := by nlinarith
  have hnw_ge : 1 + ((n : ℝ) - 2) * x ≤ ‖(n : ℂ) * w - 1‖ := by
    have hsq : (1 + ((n : ℝ) - 2) * x) ^ 2 ≤ ‖(n : ℂ) * w - 1‖ ^ 2 := by
      rw [hnw_sq]
      have hdiff_nn : 0 ≤ ((n : ℝ) - 2) ^ 2 * x * (1 - x) := by
        have : 0 ≤ 1 - x := by linarith
        positivity
      linarith
    nlinarith [norm_nonneg ((n : ℂ) * w - 1)]
  have hm1_cast : ((n - 1 : ℕ) : ℝ) = (n : ℝ) - 1 := by
    have : n = (n - 1) + 1 := by omega
    conv_rhs => rw [this]
    push_cast; ring
  have hden_pos : 0 < ((n - 1 : ℕ) : ℝ) * x := by
    rw [hm1_cast]; nlinarith
  constructor
  · have hineq : ((n - 1 : ℕ) : ℝ) * x ≤ ((n - 1 : ℕ) : ℝ) * x * ‖(n : ℂ) * GnPoly n w‖ := by
      rw [hnorm_cf, hm1_cast]
      linarith
    nlinarith
  · intro hn3 hw1
    -- Since w ≠ 1 on the circle ‖w - 1/2‖ = 1/2, we have x < 1 strictly!
    have hx_lt1 : x < 1 := by
      by_contra hge
      push Not at hge
      have hx1 : x = 1 := le_antisymm hx_le1 hge
      have him0 : w.im = 0 := by
        have hns := hcircle; rw [Complex.normSq_apply] at hns
        dsimp [x] at hns hx1; nlinarith only [hns, hx1, sq_nonneg w.im]
      exact hw1 (Complex.ext hx1 him0)
    have hn_ge3 : (3 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn3
    have hdiff_pos : 0 < ((n : ℝ) - 2) ^ 2 * x * (1 - x) := by
      have h1 : 0 < (n : ℝ) - 2 := by linarith only [hn_ge3]
      have h2 : 0 < 1 - x := by linarith only [hx_lt1]
      positivity
    have hnw_gt : 1 + ((n : ℝ) - 2) * x < ‖(n : ℂ) * w - 1‖ := by
      have hsq : (1 + ((n : ℝ) - 2) * x) ^ 2 < ‖(n : ℂ) * w - 1‖ ^ 2 := by
        rw [hnw_sq]; linarith only [hmagic, hdiff_pos]
      nlinarith only [hsq, hlin_nn, norm_nonneg ((n : ℂ) * w - 1)]
    have hineq : ((n - 1 : ℕ) : ℝ) * x < ((n - 1 : ℕ) : ℝ) * x * ‖(n : ℂ) * GnPoly n w‖ := by
      rw [hnorm_cf, hm1_cast]
      linarith only [hrev, hpow_le, hnw_gt]
    nlinarith only [hineq, hden_pos]

/-- **Minimum Modulus Theorem for `G_n(w)` on the Entire Closed Disk `‖w - 1/2‖ ≤ 1/2`**:
    For ALL `n ≥ 2` and ALL `w ∈ closedBall (1/2) (1/2)`:
      `1 ≤ ‖(n : ℂ) * GnPoly n w‖`,
    with STRICT inequality `1 < ‖(n : ℂ) * GnPoly n w‖` whenever `n ≥ 3` and `w ≠ 1`! -/
theorem GnPoly_halfDisk_lower_bound {n : ℕ} (hn : 2 ≤ n) {w : ℂ}
    (hw : ‖w - (1 / 2 : ℂ)‖ ≤ 1 / 2) :
    1 ≤ ‖(n : ℂ) * GnPoly n w‖ ∧ (3 ≤ n → w ≠ 1 → 1 < ‖(n : ℂ) * GnPoly n w‖) := by
  -- Apply Maximum Modulus Principle to f(z) = ((n : ℂ) * (diagPoly (n-2) GnCoeff).eval z)⁻¹
  -- on U = Metric.ball (1/2 : ℂ) (1/2)!
  set c0 : ℂ := 1 / 2
  set r0 : ℝ := 1 / 2
  set g : ℂ → ℂ := fun z => (n : ℂ) * (diagPoly (n - 2) GnCoeff).eval z
  have hg_eq : ∀ z, g z = (n : ℂ) * GnPoly n z := fun z => by
    dsimp [g]; rw [eval_diagPoly_GnCoeff]
  have hg_diff : Differentiable ℂ g :=
    (differentiable_const _).mul (Polynomial.differentiable _)
  have hg_ne : ∀ z ∈ Metric.closedBall c0 r0, g z ≠ 0 := by
    intro z hz
    rw [Metric.mem_closedBall, dist_eq_norm] at hz
    rw [hg_eq]
    exact mul_ne_zero (Nat.cast_ne_zero.mpr (by omega))
      (GnPoly_ne_zero_of_norm_one_sub_le_one hn (norm_one_sub_le_one_of_mem_halfDisk hz))
  set f : ℂ → ℂ := fun z => (g z)⁻¹
  have hf_diff : DiffContOnCl ℂ f (Metric.ball c0 r0) := by
    have hcl : closure (Metric.ball c0 r0) = Metric.closedBall c0 r0 :=
      closure_ball c0 (by norm_num : r0 ≠ 0)
    have hdiff_on : DifferentiableOn ℂ f (Metric.closedBall c0 r0) := fun z hz =>
      (hg_diff z).inv (hg_ne z hz) |>.differentiableWithinAt
    exact ⟨hdiff_on.mono Metric.ball_subset_closedBall, by rw [hcl]; exact hdiff_on.continuousOn⟩
  have hfront : ∀ z ∈ frontier (Metric.ball c0 r0), ‖f z‖ ≤ 1 := by
    intro z hz
    have hsp : z ∈ Metric.sphere c0 r0 := by
      rw [frontier_ball c0 (by norm_num : r0 ≠ 0)] at hz; exact hz
    rw [Metric.mem_sphere, dist_eq_norm] at hsp
    have hbd := (GnPoly_boundary_lower_bound hn hsp).1
    dsimp [f]; rw [norm_inv, hg_eq]
    exact inv_le_one_of_one_le₀ hbd
  have hle_all : ∀ z : ℂ, ‖z - c0‖ ≤ r0 → 1 ≤ ‖(n : ℂ) * GnPoly n z‖ := by
    intro z hz
    have hzcl : z ∈ closure (Metric.ball c0 r0) := by
      rw [closure_ball c0 (by norm_num : r0 ≠ 0), Metric.mem_closedBall, dist_eq_norm]; exact hz
    have hfz : ‖f z‖ ≤ 1 :=
      Complex.norm_le_of_forall_mem_frontier_norm_le Metric.isBounded_ball hf_diff hfront hzcl
    dsimp [f] at hfz; rw [norm_inv, hg_eq] at hfz
    have hpos : 0 < ‖(n : ℂ) * GnPoly n z‖ := norm_pos_iff.mpr (by
      rw [← hg_eq]; exact hg_ne z (by rw [Metric.mem_closedBall, dist_eq_norm]; exact hz))
    exact (inv_le_one₀ hpos).mp hfz
  refine ⟨hle_all w hw, fun hn3 hw1 => ?_⟩
  -- Strict inequality for n ≥ 3 and w ≠ 1:
  by_cases hbdry : ‖w - c0‖ = r0
  · exact (GnPoly_boundary_lower_bound hn hbdry).2 hn3 hw1
  · have hlt : ‖w - c0‖ < r0 := lt_of_le_of_ne hw hbdry
    by_contra hnot
    push Not at hnot
    have heq1 : ‖g w‖ = 1 := by rw [hg_eq]; exact le_antisymm hnot (hle_all w hw)
    have hmin : IsLocalMin (norm ∘ g) w := by
      change ∀ᶠ z in nhds w, ‖g w‖ ≤ ‖g z‖
      rw [Filter.eventually_iff_exists_mem]
      refine ⟨Metric.ball c0 r0, Metric.isOpen_ball.mem_nhds (by rw [Metric.mem_ball, dist_eq_norm]; exact hlt), ?_⟩
      intro z hz
      rw [Metric.mem_ball, dist_eq_norm] at hz
      rw [heq1, hg_eq]
      exact hle_all z (le_of_lt hz)
    have hloc := Complex.eventually_eq_or_eq_zero_of_isLocalMin_norm
      (Filter.Eventually.of_forall (fun z => hg_diff z)) hmin
    rcases hloc with hconst | hg0
    · set Q : ℂ[X] := C (n : ℂ) * diagPoly (n - 2) GnCoeff - C (g w)
      have hQeval : ∀ z, Q.eval z = g z - g w := fun z => by
        simp [Q, g]
      rcases Metric.eventually_nhds_iff.mp hconst with ⟨ε, hε, hε_eq⟩
      have hQ0 : Q = 0 := by
        by_contra hQne
        have hinf : Set.Infinite {z : ℂ | Q.eval z = 0} := by
          apply Set.infinite_of_injective_forall_mem (f := fun k : ℕ => w + ((ε / ((k + 2 : ℕ) : ℝ) : ℝ) : ℂ))
          · intro a b hab
            have h1 : ((ε / ((a + 2 : ℕ) : ℝ) : ℝ) : ℂ) = ((ε / ((b + 2 : ℕ) : ℝ) : ℝ) : ℂ) := by
              linear_combination hab
            have h2 := Complex.ofReal_injective h1
            have ha : ((a + 2 : ℕ) : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
            have hb : ((b + 2 : ℕ) : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
            have h3 : ((a + 2 : ℕ) : ℝ) = ((b + 2 : ℕ) : ℝ) := by
              have hε_ne : ε ≠ 0 := ne_of_gt hε
              field_simp [ha, hb, hε_ne] at h2
              exact h2.symm
            have h4 : a + 2 = b + 2 := by exact_mod_cast h3
            omega
          · intro k
            change Q.eval _ = 0
            rw [hQeval, sub_eq_zero]
            apply hε_eq
            rw [dist_eq_norm, add_sub_cancel_left, Complex.norm_real,
              Real.norm_of_nonneg (by positivity)]
            have hk : (1 : ℝ) < ((k + 2 : ℕ) : ℝ) := by exact_mod_cast (show 1 < k + 2 by omega)
            exact div_lt_self hε hk
        have hfin : {z : ℂ | Q.eval z = 0}.Finite := by
          apply (Q.roots.toFinset.finite_toSet).subset
          intro z hz
          simp only [Finset.mem_coe, Multiset.mem_toFinset]
          exact (Polynomial.mem_roots hQne).mpr hz
        exact hinf hfin
      -- So g(0) = g(w), hence ‖g(0)‖ = 1, contradicting ‖g(0)‖ = n/2 > 1!
      have hg0_eq : g 0 = g w := by
        have := congrArg (fun P => P.eval 0) hQ0
        rw [hQeval, eval_zero, sub_eq_zero] at this
        exact this
      have h0_gt : 1 < ‖(n : ℂ) * GnPoly n 0‖ :=
        (GnPoly_boundary_lower_bound hn (by norm_num : ‖(0 : ℂ) - 1 / 2‖ = 1 / 2)).2 hn3 (by norm_num)
      rw [← hg_eq, hg0_eq, heq1] at h0_gt
      linarith
    · exact hg_ne w (by rw [Metric.mem_closedBall, dist_eq_norm]; exact hw) hg0

/-- **THEOREM 1 (All-n Supporting Half-Plane Dual Smale Theorem — Exact `1/n` + Strict Uniqueness)**:
    For EVERY degree `n ≥ 2` and EVERY vector of remaining normalized inverse critical points
    `w_rest : Fin (n - 2) → ℂ` lying in the closed disk `‖w_k - 1/2‖ ≤ 1/2`
    (equivalently, all critical points satisfy `Re(ζ_k / ζ_j) ≥ 1`), we have:
      `1 / n ≤ ‖P1Form n w_rest‖`.
    Moreover, for EVERY `n ≥ 3`, if `∃ k, w_rest k ≠ 1`, then STRICTLY:
      `1 / n < ‖P1Form n w_rest‖`! -/
theorem dual_smale_supporting_half_plane {n : ℕ} (hn : 2 ≤ n) (w_rest : Fin (n - 2) → ℂ)
    (hdisk : ∀ i : Fin (n - 2), ‖w_rest i - (1 / 2 : ℂ)‖ ≤ 1 / 2) :
    1 / (n : ℝ) ≤ ‖P1Form n w_rest‖ ∧
      (3 ≤ n → (∃ i : Fin (n - 2), w_rest i ≠ 1) → 1 / (n : ℝ) < ‖P1Form n w_rest‖) := by
  have hn_pos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast (show 0 < n by omega)
  -- Case n = 2: Fin 0 is empty, P1Form 2 w = 1/2 = 1/n
  by_cases hn2 : n = 2
  · subst hn2
    have hp : P1Form 2 w_rest = 1 / 2 := by
      unfold P1Form symMultiaffine; simp [elemSym]
    rw [hp]
    constructor
    · norm_num
    · intro h3; omega
  -- Case n ≥ 3: m = n - 2 ≥ 1
  have hm : 1 ≤ n - 2 := by omega
  have h1 : 1 / (n : ℝ) ≤ ‖P1Form n w_rest‖ := by
    rcases grace_walsh_szego_closedBall hm (center := (1 / 2 : ℂ)) (r := 1 / 2) (by norm_num)
        GnCoeff w_rest hdisk with ⟨ζ, hζ, heq⟩
    have hPeq : P1Form n w_rest = GnPoly n ζ := heq
    have hbd := (GnPoly_halfDisk_lower_bound hn hζ).1
    rw [norm_mul, Complex.norm_natCast] at hbd
    rw [hPeq, div_le_iff₀ hn_pos]
    linarith
  refine ⟨h1, fun hn3 ⟨i₀, hi₀⟩ => ?_⟩
  -- Case n = 3: m = 1, P1Form 3 w = G_3(w 0) directly!
  by_cases hn3eq : n = 3
  · subst hn3eq
    have hPeq : P1Form 3 w_rest = GnPoly 3 (w_rest i₀) := by
      unfold P1Form GnPoly; congr 1; ext j; fin_cases j; fin_cases i₀; rfl
    have hbd := (GnPoly_halfDisk_lower_bound (by omega) (hdisk i₀)).2 (by omega) hi₀
    rw [norm_mul, Complex.norm_natCast] at hbd
    rw [hPeq, div_lt_iff₀ hn_pos]
    linarith
  -- Case n ≥ 4: m = n - 2 ≥ 2. Apply strict uniqueness!
  have hm2 : 2 ≤ n - 2 := by omega
  by_contra hnot
  push Not at hnot
  have heq_norm : ‖P1Form n w_rest‖ = 1 / (n : ℝ) := le_antisymm hnot h1
  set val := P1Form n w_rest
  -- Consider shifted coefficients c'(0) = GnCoeff 0 - val, c'(k) = GnCoeff k for k ≥ 1
  set c' : ℕ → ℂ := fun k => if k = 0 then GnCoeff 0 - val else GnCoeff k
  have hshift_eq : ∀ v : Fin (n - 2) → ℂ, symMultiaffine (n - 2) c' v = P1Form n v - val := by
    intro v
    unfold P1Form symMultiaffine
    rw [Finset.sum_range_succ', Finset.sum_range_succ']
    have he0 : elemSym (n - 2) v 0 = 1 := by
      generalize h_m : n - 2 = m at v ⊢
      cases m <;> rfl
    have hrest : ∑ j ∈ Finset.range (n - 2), c' (j + 1) * elemSym (n - 2) v (j + 1) =
        ∑ j ∈ Finset.range (n - 2), GnCoeff (j + 1) * elemSym (n - 2) v (j + 1) := by
      apply Finset.sum_congr rfl; intro j _; simp [c']
    change (∑ j ∈ Finset.range (n - 2), c' (j + 1) * elemSym (n - 2) v (j + 1)) + c' 0 * elemSym (n - 2) v 0 =
        ((∑ j ∈ Finset.range (n - 2), GnCoeff (j + 1) * elemSym (n - 2) v (j + 1)) + GnCoeff 0 * elemSym (n - 2) v 0) - val
    rw [hrest, he0]; simp [c']; ring
  have hdiag_eq : ∀ ζ : ℂ, (diagPoly (n - 2) c').eval ζ = GnPoly n ζ - val := by
    intro ζ; rw [eval_diagPoly, hshift_eq]; rfl
  -- First, val MUST equal 1 / n (otherwise diagPoly c' has NO roots in the half-disk at all!)
  by_cases hval1 : val = 1 / (n : ℂ)
  · -- val = 1 / n: diagPoly c' has 1 as a SIMPLE root and NO other root in closedBall (1/2) (1/2)!
    have hPb : (diagPoly (n - 2) c').eval ((1 / 2 : ℂ) + ((1 / 2 : ℝ) : ℂ)) = 0 := by
      rw [show (1 / 2 : ℂ) + ((1 / 2 : ℝ) : ℂ) = 1 by norm_num, hdiag_eq, GnPoly_at_one hn, hval1, sub_self]
    have hP'b : (derivative (diagPoly (n - 2) c')).eval ((1 / 2 : ℂ) + ((1 / 2 : ℝ) : ℂ)) ≠ 0 := by
      rw [show (1 / 2 : ℂ) + ((1 / 2 : ℝ) : ℂ) = 1 by norm_num]
      have hpoly_diff : diagPoly (n - 2) c' = diagPoly (n - 2) GnCoeff - C val := by
        apply Polynomial.funext; intro ζ; rw [hdiag_eq, eval_sub, eval_diagPoly_GnCoeff, eval_C]
      rw [hpoly_diff, derivative_sub, derivative_C, sub_zero]
      exact derivative_GnPoly_at_one_ne_zero hn3
    have hno : ∀ ζ : ℂ, ‖ζ - (1 / 2 : ℂ)‖ ≤ 1 / 2 → ζ ≠ (1 / 2 : ℂ) + ((1 / 2 : ℝ) : ℂ) →
        (diagPoly (n - 2) c').eval ζ ≠ 0 := by
      intro ζ hζ hζ1 h0
      rw [show (1 / 2 : ℂ) + ((1 / 2 : ℝ) : ℂ) = 1 by norm_num] at hζ1
      rw [hdiag_eq, sub_eq_zero] at h0
      have hgt := (GnPoly_halfDisk_lower_bound hn hζ).2 hn3 hζ1
      rw [h0, hval1, norm_mul, norm_div, norm_one, Complex.norm_natCast] at hgt
      have : (n : ℝ) * (1 / (n : ℝ)) = 1 := mul_one_div_cancel (ne_of_gt hn_pos)
      linarith
    have hne0 := grace_walsh_szego_closedBall_unique_boundary hm2 (center := (1 / 2 : ℂ))
      (r := 1 / 2) (by norm_num) c' w_rest hdisk hPb hP'b hno
      ⟨i₀, by rw [show (1 / 2 : ℂ) + ((1 / 2 : ℝ) : ℂ) = 1 by norm_num]; exact hi₀⟩
    rw [hshift_eq] at hne0
    exact hne0 (sub_self val)
  · -- val ≠ 1 / n: then diagPoly c' has NO roots in closedBall (1/2) (1/2) AT ALL!
    -- Apply grace_walsh_szego_closedBall to get ζ in half-disk with GnPoly n ζ = val
    rcases grace_walsh_szego_closedBall hm (center := (1 / 2 : ℂ)) (r := 1 / 2) (by norm_num)
        GnCoeff w_rest hdisk with ⟨ζ, hζ, heq⟩
    by_cases hζ1 : ζ = 1
    · subst hζ1
      have hval_eq : val = GnPoly n 1 := heq
      exact hval1 (by rw [hval_eq, GnPoly_at_one hn])
    · have hgt := (GnPoly_halfDisk_lower_bound hn hζ).2 hn3 hζ1
      rw [norm_mul, Complex.norm_natCast] at hgt
      have hPeq : ‖GnPoly n ζ‖ = 1 / (n : ℝ) := by
        rw [← show P1Form n w_rest = GnPoly n ζ from heq]; exact heq_norm
      rw [hPeq] at hgt
      have : (n : ℝ) * (1 / (n : ℝ)) = 1 := mul_one_div_cancel (ne_of_gt hn_pos)
      linarith

/-- **Polynomial Form of Theorem 1**:
    For any `n ≥ 2`, any nonzero inverse critical points `w : Fin (n - 1) → ℂ` with `w j = 1`
    and all other `w k` in the closed disk `‖w k - 1/2‖ ≤ 1/2` (i.e. `Re(ζ_k / ζ_j) ≥ 1`),
    the Dual Smale quotient at `ζ_j = 1` satisfies `‖P(1) / 1‖ ≥ 1 / n`, with strict inequality
    for `n ≥ 3` unless all `w k = 1`. -/
theorem dual_smale_supporting_half_plane_poly {n : ℕ} (hn : 2 ≤ n)
    (w : Fin (n - 1) → ℂ) (hlast : w ⟨n - 2, by omega⟩ = 1)
    (hdisk : ∀ i : Fin (n - 2), ‖w ⟨i.val, by omega⟩ - (1 / 2 : ℂ)‖ ≤ 1 / 2) :
    1 / (n : ℝ) ≤ ‖dualSmaleQuotient n w ⟨n - 2, by omega⟩‖ ∧
      (3 ≤ n → (∃ i : Fin (n - 2), w ⟨i.val, by omega⟩ ≠ 1) →
        1 / (n : ℝ) < ‖dualSmaleQuotient n w ⟨n - 2, by omega⟩‖) := by
  rw [dualSmaleQuotient_at_one n hn w hlast]
  exact dual_smale_supporting_half_plane hn (fun i => w ⟨i.val, by omega⟩) hdisk

end DualSmale
