/-
  DualSmale/UnivalentCriticalValue.lean

  THEOREM 2 (Sharp Zero-Free Disk & All-n Grace-Walsh-Szego Critical-Value Lower Bound):
    For EVERY degree n >= 2 and EVERY complex polynomial P(z) = z + a_2 z^2 + ... + a_n z^n
    with critical points zeta_1, ..., zeta_{n-1} and r_min = min_j |zeta_j| > 0:

    Part A (Sharp Zero-Free Disk):
      Every nonzero root z_0 of P satisfies |z_0| >= 2 * sin(pi / n) * r_min.
      (Sharp at P_n(z) = (1 - (1 - z)^n) / n.)

    Part B (Elementary Polynomial Mountain Pass Theorem):
      If P(0) = 0, P'(0) != 0, deg P >= 2, P has no zeros on 0 < |z| <= r, and
      |P(z)| >= M > 0 on |z| = r, then there exists a critical point zeta of P
      with |P(zeta)| >= M. (Proved via explicit continuous Newton-cutoff path deformation!)

    Part C (All-n GWS Critical-Value Lower Bound):
      max_{P'(zeta) = 0} |P(zeta)| >= (49 / (50 * n)) * r_min = (0.98 / n) * r_min
      for EVERY n >= 2 (and exact (1 / n) * r_min for n = 2, 3)!

    Corollaries (ALL n >= 2):
      - Equal-Modulus Dual Smale to 98%: |zeta_1| = ... = |zeta_{n-1}| => max |P(zeta_j)/zeta_j| >= 49 / (50 n).
      - Bounded-Spread Dual Smale: max |P(zeta_j)/zeta_j| >= 49 / (50 * kappa(P) * n),
        where kappa(P) = r_max / r_min (strictly beating the general O(1/n^2) barrier whenever kappa < 0.98 n).
-/

import DualSmale.PolynomialReduction
import Mathlib.Analysis.Complex.AbsMax
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.Complex.Arg

open scoped BigOperators
open Polynomial Complex

namespace DualSmale

/-! ### Part A: Sharp Zero-Free Disk `|z₀| ≥ 2 sin(π / n) * r_min` -/

/-- If `n ≥ 2`, `v ≠ 0`, and `(1 - v)^n = 1`, then `2 * Real.sin (Real.pi / n) ≤ ‖v‖`. -/
lemma norm_ge_two_sin_pi_div_of_one_sub_pow_eq_one {n : ℕ} (hn : 2 ≤ n) {v : ℂ}
    (hv : v ≠ 0) (hpow : (1 - v) ^ n = 1) :
    2 * Real.sin (Real.pi / (n : ℝ)) ≤ ‖v‖ := by
  set u : ℂ := 1 - v
  have hu_ne : u ≠ 0 := by
    intro h0; rw [h0, zero_pow (by omega : n ≠ 0)] at hpow; exact zero_ne_one hpow
  have hu_norm : ‖u‖ = 1 := by
    have h1 : ‖u‖ ^ n = 1 := by rw [← norm_pow, hpow, norm_one]
    have hnn : 0 ≤ ‖u‖ := norm_nonneg u
    by_contra hne
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · have : ‖u‖ ^ n < 1 ^ n := pow_lt_pow_left₀ hlt hnn (by omega)
      rw [one_pow] at this; linarith
    · have : 1 ^ n < ‖u‖ ^ n := pow_lt_pow_left₀ hgt (by norm_num) (by omega)
      rw [one_pow] at this; linarith
  -- Write u = exp(i * θ) where θ = u.arg ∈ (-π, π]
  set θ : ℝ := u.arg
  have hu_exp : u = Complex.exp (↑θ * Complex.I) := by
    have h := Complex.norm_mul_exp_arg_mul_I u
    rw [hu_norm, Complex.ofReal_one, one_mul] at h
    exact h.symm
  have hθ_ne : θ ≠ 0 := by
    intro h0
    have hu1 : u = 1 := by rw [hu_exp, h0, Complex.ofReal_zero, zero_mul, Complex.exp_zero]
    exact hv (by dsimp [u] at hu1; linear_combination -hu1)
  have hpow_exp : Complex.exp (↑((n : ℝ) * θ) * Complex.I) = 1 := by
    have h1 : u ^ n = Complex.exp (↑n * (↑θ * Complex.I)) := by
      rw [hu_exp, ← Complex.exp_nat_mul]
    rw [hpow] at h1
    rw [show (↑((n : ℝ) * θ) * Complex.I : ℂ) = ↑n * (↑θ * Complex.I) by push_cast; ring]
    exact h1.symm
  rcases Complex.exp_eq_one_iff.mp hpow_exp with ⟨k, hk⟩
  have hk_real : (n : ℝ) * θ = (k : ℝ) * (2 * Real.pi) := by
    have hI : Complex.I ≠ 0 := Complex.I_ne_zero
    have h1 : (↑((n : ℝ) * θ) : ℂ) = (↑((k : ℝ) * (2 * Real.pi)) : ℂ) := by
      apply mul_right_cancel₀ hI
      calc (↑((n : ℝ) * θ) : ℂ) * Complex.I = (k : ℂ) * (2 * ↑Real.pi * Complex.I) := hk
        _ = (↑((k : ℝ) * (2 * Real.pi)) : ℂ) * Complex.I := by push_cast; ring
    exact Complex.ofReal_injective h1
  have hk_ne : k ≠ 0 := by
    intro hk0
    rw [hk0, Int.cast_zero, zero_mul] at hk_real
    have hn_ne : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
    exact hθ_ne ((mul_eq_zero.mp hk_real).resolve_left hn_ne)
  have hk_abs : (1 : ℝ) ≤ |(k : ℝ)| := by
    have h1 : (1 : ℤ) ≤ |k| := Int.one_le_abs hk_ne
    exact_mod_cast h1
  have hn_pos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast (show 0 < n by omega)
  have hθ_lb : 2 * Real.pi / (n : ℝ) ≤ |θ| := by
    have h1 : (n : ℝ) * |θ| = |(k : ℝ)| * (2 * Real.pi) := by
      have habs := congrArg abs hk_real
      rw [abs_mul, abs_mul, abs_of_pos hn_pos, abs_of_pos (by positivity : 0 < 2 * Real.pi)] at habs
      exact habs
    rw [div_le_iff₀ hn_pos]
    nlinarith [Real.pi_pos]
  have hθ_ub : |θ| ≤ Real.pi := Complex.abs_arg_le_pi u
  -- Exact identity: ‖v‖ = ‖1 - exp(i θ)‖ = 2 * sin(|θ| / 2)
  have hv_sq : ‖v‖ ^ 2 = (2 * Real.sin (|θ| / 2)) ^ 2 := by
    have hv_eq : v = 1 - Complex.exp (↑θ * Complex.I) := by dsimp [u] at hu_exp; linear_combination -hu_exp
    rw [hv_eq, ← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
    rw [Complex.exp_mul_I]
    simp only [Complex.sub_re, Complex.sub_im, Complex.add_re, Complex.add_im, Complex.one_re,
      Complex.one_im, Complex.cos_ofReal_re, Complex.cos_ofReal_im, Complex.sin_ofReal_re,
      Complex.sin_ofReal_im, Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im,
      mul_zero, mul_one, sub_zero, zero_add, add_zero, zero_sub]
    have hcs : Real.cos θ ^ 2 + Real.sin θ ^ 2 = 1 := Real.cos_sq_add_sin_sq θ
    have hcos_half : Real.cos θ = 1 - 2 * Real.sin (|θ| / 2) ^ 2 := by
      have h1 : Real.cos |θ| = Real.cos (2 * (|θ| / 2)) := by ring_nf
      rw [← Real.cos_abs θ, h1, Real.cos_two_mul']
      have h2 := Real.sin_sq_add_cos_sq (|θ| / 2)
      linarith
    nlinarith
  have hsin_nn : 0 ≤ Real.sin (|θ| / 2) :=
    Real.sin_nonneg_of_nonneg_of_le_pi (by positivity) (by linarith [Real.pi_pos])
  have hv_eq_sin : ‖v‖ = 2 * Real.sin (|θ| / 2) := by
    nlinarith [norm_nonneg v, hv_sq, hsin_nn]
  rw [hv_eq_sin]
  have hsin_mono : Real.sin (Real.pi / (n : ℝ)) ≤ Real.sin (|θ| / 2) := by
    apply Real.sin_le_sin_of_le_of_le_pi_div_two
    · have : 0 < Real.pi / (n : ℝ) := div_pos Real.pi_pos hn_pos
      linarith [Real.pi_pos]
    · linarith [hθ_ub]
    · have hhalf : (2 * Real.pi / (n : ℝ)) / 2 = Real.pi / (n : ℝ) := by ring
      linarith [hθ_lb, hhalf]
  linarith

/-- **THEOREM 2A (Sharp Zero-Free Disk for ALL `n ≥ 2`)**:
    If `P(z) = polyFromInvCrits n w` has all inverse critical points `‖w k‖ ≤ 1 / r_min`
    (`r_min > 0`, i.e., all critical points satisfy `|ζ_k| ≥ r_min`), then `P` has NO zeros
    in the punctured disk `0 < ‖z‖ < 2 * sin(π / n) * r_min`! -/
theorem dual_smale_zero_free_disk {n : ℕ} (hn : 2 ≤ n) (w : Fin (n - 1) → ℂ)
    {r_min : ℝ} (hr : 0 < r_min) (hw : ∀ k : Fin (n - 1), ‖w k‖ ≤ 1 / r_min)
    {z : ℂ} (hz0 : z ≠ 0) (hz : ‖z‖ < 2 * Real.sin (Real.pi / (n : ℝ)) * r_min) :
    (polyFromInvCrits n w).eval z ≠ 0 := by
  rw [polyFromInvCrits_eval_eq_mul_symMultiaffine (by omega) w z]
  apply mul_ne_zero hz0
  set R : ℝ := ‖z‖ / r_min
  have hR_pos : 0 < R := div_pos (norm_pos_iff.mpr hz0) hr
  have hR_lt : R < 2 * Real.sin (Real.pi / (n : ℝ)) := by
    dsimp [R]; rw [div_lt_iff₀ hr]; exact hz
  have hbound : ∀ k : Fin (n - 1), ‖w k * z‖ ≤ R := by
    intro k
    rw [norm_mul]
    calc ‖w k‖ * ‖z‖ ≤ (1 / r_min) * ‖z‖ := mul_le_mul_of_nonneg_right (hw k) (norm_nonneg z)
      _ = R := by dsimp [R]; ring
  rcases grace_walsh_szego_disk (m := n - 1) (by omega) hR_pos
      (fun m => (-1 : ℂ) ^ m / ((m + 1 : ℕ) : ℂ)) (fun k => w k * z) hbound with ⟨v, hv_le, heq⟩
  rw [heq]
  by_cases hv0 : v = 0
  · subst hv0
    unfold symMultiaffine
    obtain ⟨k, hk⟩ : ∃ k, n - 1 = k + 1 := ⟨n - 2, by omega⟩
    rw [hk, Finset.sum_range_succ']
    have hrest : ∑ x ∈ Finset.range (k + 1),
        ((-1 : ℂ) ^ (x + 1) / ((x + 1 + 1 : ℕ) : ℂ)) * elemSym (k + 1) (fun _ => (0 : ℂ)) (x + 1) = 0 := by
      apply Finset.sum_eq_zero; intro x _
      rw [elemSym_const, zero_pow (Nat.succ_ne_zero x), mul_zero, mul_zero]
    rw [hrest, zero_add]
    have he0 : elemSym (k + 1) (fun _ => (0 : ℂ)) 0 = 1 := rfl
    rw [he0]; norm_num
  · intro hF0
    have hcf := diag_polyFromInvCrits_closed_form (by omega : 1 ≤ n) v
    rw [hF0, mul_zero] at hcf
    have hpow : (1 - v) ^ n = 1 := by linear_combination hcf
    have hlb := norm_ge_two_sin_pi_div_of_one_sub_pow_eq_one hn hv0 hpow
    linarith

/-! ### Part B: Elementary Polynomial Mountain Pass Theorem -/

/-- Purely algebraic Taylor remainder bound for monomials `X^k`:
    on `‖z‖ ≤ R`, `‖h‖ ≤ 1`, `‖(z + h)^k - z^k - k * z^(k-1) * h‖ ≤ C * ‖h‖^2`. -/
lemma monomial_taylor_bound (R : ℝ) (hR : 0 ≤ R) :
    ∀ k : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ z h : ℂ, ‖z‖ ≤ R → ‖h‖ ≤ 1 →
      ‖(z + h) ^ k - z ^ k - (k : ℂ) * z ^ (k - 1) * h‖ ≤ C * ‖h‖ ^ 2 := by
  intro k
  induction k with
  | zero =>
    refine ⟨0, le_refl 0, fun z h _ _ => by simp⟩
  | succ k ih =>
    cases k with
    | zero =>
      refine ⟨0, le_refl 0, fun z h _ _ => by simp⟩
    | succ m =>
      rcases ih with ⟨C, hC, hih⟩
      -- (z+h)^(m+2) - z^(m+2) - (m+2)*z^(m+1)*h
      --   = z * ((z+h)^(m+1) - z^(m+1) - (m+1)*z^m*h) + h * ((z+h)^(m+1) - z^(m+1))
      -- Bound ‖(z+h)^(m+1) - z^(m+1)‖ ≤ (m+1) * (R+1)^m * ‖h‖ via geom_sum₂_mul!
      have hdiff_bnd : ∀ z h : ℂ, ‖z‖ ≤ R → ‖h‖ ≤ 1 →
          ‖(z + h) ^ (m + 1) - z ^ (m + 1)‖ ≤ ((m + 1 : ℕ) : ℝ) * (R + 1) ^ m * ‖h‖ := by
        intro z h hz hh
        have hfac : (z + h) ^ (m + 1) - z ^ (m + 1) =
            h * ∑ i ∈ Finset.range (m + 1), (z + h) ^ i * z ^ (m - i) := by
          have hg := geom_sum₂_mul (z + h) z (m + 1)
          have hsub : z + h - z = h := by ring
          rw [hsub] at hg
          rw [mul_comm, ← hg]
          rfl
        rw [hfac, norm_mul]
        have hzh : ‖z + h‖ ≤ R + 1 := le_trans (norm_add_le z h) (by linarith)
        have hsum_le : ‖∑ i ∈ Finset.range (m + 1), (z + h) ^ i * z ^ (m - i)‖ ≤
            ((m + 1 : ℕ) : ℝ) * (R + 1) ^ m := by
          calc ‖∑ i ∈ Finset.range (m + 1), (z + h) ^ i * z ^ (m - i)‖
              ≤ ∑ i ∈ Finset.range (m + 1), ‖(z + h) ^ i * z ^ (m - i)‖ := norm_sum_le _ _
            _ ≤ ∑ _i ∈ Finset.range (m + 1), (R + 1) ^ m := by
                apply Finset.sum_le_sum
                intro i hi
                have hi_le : i ≤ m := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
                rw [norm_mul, norm_pow, norm_pow]
                have h1 : ‖z + h‖ ^ i ≤ (R + 1) ^ i := pow_le_pow_left₀ (norm_nonneg _) hzh i
                have h2 : ‖z‖ ^ (m - i) ≤ (R + 1) ^ (m - i) :=
                  pow_le_pow_left₀ (norm_nonneg _) (by linarith) (m - i)
                calc ‖z + h‖ ^ i * ‖z‖ ^ (m - i)
                    ≤ (R + 1) ^ i * (R + 1) ^ (m - i) := mul_le_mul h1 h2 (by positivity) (by positivity)
                  _ = (R + 1) ^ (i + (m - i)) := (pow_add _ _ _).symm
                  _ = (R + 1) ^ m := by rw [Nat.add_sub_of_le hi_le]
            _ = ((m + 1 : ℕ) : ℝ) * (R + 1) ^ m := by simp
        rw [mul_comm]
        exact mul_le_mul_of_nonneg_right hsum_le (norm_nonneg h)
      refine ⟨R * C + ((m + 1 : ℕ) : ℝ) * (R + 1) ^ m, by positivity, fun z h hz hh => ?_⟩
      have hid : (z + h) ^ (m + 2) - z ^ (m + 2) - ((m + 2 : ℕ) : ℂ) * z ^ (m + 1) * h =
          z * ((z + h) ^ (m + 1) - z ^ (m + 1) - ((m + 1 : ℕ) : ℂ) * z ^ m * h) +
          h * ((z + h) ^ (m + 1) - z ^ (m + 1)) := by
        push_cast; ring
      rw [show m + 1 + 1 - 1 = m + 1 by omega]
      rw [hid]
      have h1 := hih z h hz hh
      simp only [Nat.add_sub_cancel] at h1
      have h2 := hdiff_bnd z h hz hh
      calc ‖z * ((z + h) ^ (m + 1) - z ^ (m + 1) - ((m + 1 : ℕ) : ℂ) * z ^ m * h) +
            h * ((z + h) ^ (m + 1) - z ^ (m + 1))‖
          ≤ ‖z * ((z + h) ^ (m + 1) - z ^ (m + 1) - ((m + 1 : ℕ) : ℂ) * z ^ m * h)‖ +
            ‖h * ((z + h) ^ (m + 1) - z ^ (m + 1))‖ := norm_add_le _ _
        _ = ‖z‖ * ‖(z + h) ^ (m + 1) - z ^ (m + 1) - ((m + 1 : ℕ) : ℂ) * z ^ m * h‖ +
            ‖h‖ * ‖(z + h) ^ (m + 1) - z ^ (m + 1)‖ := by rw [norm_mul, norm_mul]
        _ ≤ R * (C * ‖h‖ ^ 2) + ‖h‖ * (((m + 1 : ℕ) : ℝ) * (R + 1) ^ m * ‖h‖) := by
            apply add_le_add
            · exact mul_le_mul hz h1 (norm_nonneg _) hR
            · exact mul_le_mul_of_nonneg_left h2 (norm_nonneg h)
        _ = (R * C + ((m + 1 : ℕ) : ℝ) * (R + 1) ^ m) * ‖h‖ ^ 2 := by ring

/-- Purely algebraic Taylor remainder bound for any complex polynomial `P` on `‖z‖ ≤ R, ‖h‖ ≤ 1`. -/
lemma poly_taylor_bound (P : ℂ[X]) (R : ℝ) (hR : 0 ≤ R) :
    ∃ C : ℝ, 0 < C ∧ ∀ z h : ℂ, ‖z‖ ≤ R → ‖h‖ ≤ 1 →
      ‖P.eval (z + h) - P.eval z - (derivative P).eval z * h‖ ≤ C * ‖h‖ ^ 2 := by
  induction P using Polynomial.induction_on' with
  | add p q ihp ihq =>
    rcases ihp with ⟨Cp, hCp, hp⟩
    rcases ihq with ⟨Cq, hCq, hq⟩
    refine ⟨Cp + Cq, by linarith, fun z h hz hh => ?_⟩
    have hid : (p + q).eval (z + h) - (p + q).eval z - (derivative (p + q)).eval z * h =
        (p.eval (z + h) - p.eval z - (derivative p).eval z * h) +
        (q.eval (z + h) - q.eval z - (derivative q).eval z * h) := by
      simp [eval_add, derivative_add]; ring
    rw [hid]
    calc ‖_ + _‖ ≤ ‖p.eval (z + h) - p.eval z - (derivative p).eval z * h‖ +
          ‖q.eval (z + h) - q.eval z - (derivative q).eval z * h‖ := norm_add_le _ _
      _ ≤ Cp * ‖h‖ ^ 2 + Cq * ‖h‖ ^ 2 := add_le_add (hp z h hz hh) (hq z h hz hh)
      _ = (Cp + Cq) * ‖h‖ ^ 2 := by ring
  | monomial k a =>
    rcases monomial_taylor_bound R hR k with ⟨C, hC, hk⟩
    refine ⟨‖a‖ * C + 1, by positivity, fun z h hz hh => ?_⟩
    have hid : (monomial k a).eval (z + h) - (monomial k a).eval z -
        (derivative (monomial k a)).eval z * h =
        a * ((z + h) ^ k - z ^ k - (k : ℂ) * z ^ (k - 1) * h) := by
      rw [derivative_monomial]
      simp only [eval_monomial]
      cases k with
      | zero => simp
      | succ m => simp only [Nat.add_sub_cancel]; ring
    rw [hid, norm_mul]
    calc ‖a‖ * ‖(z + h) ^ k - z ^ k - (k : ℂ) * z ^ (k - 1) * h‖
        ≤ ‖a‖ * (C * ‖h‖ ^ 2) := mul_le_mul_of_nonneg_left (hk z h hz hh) (norm_nonneg a)
      _ ≤ (‖a‖ * C + 1) * ‖h‖ ^ 2 := by nlinarith [sq_nonneg ‖h‖]

/-- **THEOREM 2B (Elementary Polynomial Mountain Pass Theorem)**:
    Let `P : ℂ[X]` have `2 ≤ P.natDegree`, `P.eval 0 = 0`, `(derivative P).eval 0 ≠ 0`.
    Suppose for some `r > 0` and `M > 0`:
      (1) `P` has no zeros on `0 < ‖z‖ ≤ r`, and
      (2) `M ≤ ‖P.eval z‖` for all `z` on the circle `‖z‖ = r`.
    Then there exists a critical point `ζ : ℂ` of `P` (`(derivative P).eval ζ = 0`)
    with `M ≤ ‖P.eval ζ‖`! -/
theorem polynomial_mountain_pass (P : ℂ[X]) (hdeg : 2 ≤ P.natDegree)
    (hP0 : P.eval 0 = 0) (hP'0 : (derivative P).eval 0 ≠ 0)
    {r M : ℝ} (hr : 0 < r) (hM : 0 < M)
    (hnozero : ∀ z : ℂ, 0 < ‖z‖ → ‖z‖ ≤ r → P.eval z ≠ 0)
    (hcircle : ∀ z : ℂ, ‖z‖ = r → M ≤ ‖P.eval z‖) :
    ∃ ζ : ℂ, (derivative P).eval ζ = 0 ∧ M ≤ ‖P.eval ζ‖ := by
  -- Step 1: Find a nonzero root z₁ of P with ‖z₁‖ > r!
  have hXdvd : X ∣ P := Polynomial.X_dvd_iff.mpr (by simpa [Polynomial.coeff_zero_eq_eval_zero] using hP0)
  rcases hXdvd with ⟨Q, hPQ⟩
  have hQne : Q ≠ 0 := by intro h0; rw [h0, mul_zero] at hPQ; rw [hPQ] at hdeg; simp at hdeg
  have hQdeg : 1 ≤ Q.natDegree := by
    have h1 : P.natDegree = 1 + Q.natDegree := by
      rw [hPQ, Polynomial.natDegree_mul X_ne_zero hQne, Polynomial.natDegree_X]
    omega
  obtain ⟨z₁, hz₁Q⟩ := Complex.exists_root (show 0 < Q.degree by
    rw [Polynomial.degree_eq_natDegree hQne]; exact_mod_cast (show 0 < Q.natDegree by omega))
  have hz₁_root : P.eval z₁ = 0 := by rw [hPQ, eval_mul, eval_X, hz₁Q, mul_zero]
  have hz₁_ne0 : z₁ ≠ 0 := by
    intro h0; subst h0
    rw [hPQ, derivative_mul, derivative_X, one_mul, eval_add, eval_mul, eval_X, zero_mul, add_zero] at hP'0
    exact hP'0 hz₁Q
  have hz₁_gt : r < ‖z₁‖ := by
    by_contra hle; push Not at hle
    exact hnozero z₁ (norm_pos_iff.mpr hz₁_ne0) hle hz₁_root
  -- Step 2: Define the minimax (mountain pass) level L_* = sInf S
  set S : Set ℝ := {B : ℝ | ∃ γ : ℝ → ℂ, ContinuousOn γ (Set.Icc 0 1) ∧
    γ 0 = 0 ∧ γ 1 = z₁ ∧ ∀ t ∈ Set.Icc (0 : ℝ) 1, ‖P.eval (γ t)‖ ≤ B}
  have hS_nonempty : S.Nonempty := by
    set γ₀ : ℝ → ℂ := fun t => (t : ℂ) * z₁
    have hcont : ContinuousOn (fun t : ℝ => ‖P.eval (γ₀ t)‖) (Set.Icc 0 1) :=
      ((P.continuous.comp (Complex.continuous_ofReal.mul continuous_const)).norm).continuousOn
    obtain ⟨t₀, _, ht₀⟩ := isCompact_Icc.exists_isMaxOn (Set.nonempty_Icc.mpr zero_le_one) hcont
    exact ⟨‖P.eval (γ₀ t₀)‖, γ₀, (Complex.continuous_ofReal.mul continuous_const).continuousOn,
      by simp [γ₀], by simp [γ₀], fun t ht => ht₀ ht⟩
  have hS_lb : ∀ B ∈ S, M ≤ B := by
    intro B ⟨γ, hγc, hγ0, hγ1, hγB⟩
    have hnorm_c : ContinuousOn (fun t => ‖γ t‖) (Set.Icc 0 1) := hγc.norm
    have hmem : r ∈ Set.Icc (‖γ 0‖) (‖γ 1‖) := by
      rw [hγ0, hγ1, norm_zero]; exact ⟨le_of_lt hr, le_of_lt hz₁_gt⟩
    obtain ⟨t₀, ht₀, hrt₀⟩ := intermediate_value_Icc zero_le_one hnorm_c hmem
    exact le_trans (hcircle (γ t₀) hrt₀) (hγB t₀ ht₀)
  set L : ℝ := sInf S
  have hL_ge : M ≤ L := le_csInf hS_nonempty hS_lb
  have hL_pos : 0 < L := lt_of_lt_of_le hM hL_ge
  -- Step 3: Suppose for contradiction that no critical point ζ of P has ‖P.eval ζ‖ = L!
  by_contra hno_crit
  push Not at hno_crit
  -- Actually we only need to rule out ∃ ζ, P'(ζ) = 0 ∧ ‖P(ζ)‖ = L (since L ≥ M!)
  have hno_eq : ∀ ζ : ℂ, (derivative P).eval ζ = 0 → ‖P.eval ζ‖ ≠ L := by
    intro ζ hζ hEq
    have hlt := hno_crit ζ hζ
    linarith
  -- Since (derivative P).roots is finite, there exists ε ∈ (0, L/2) such that no critical point
  -- has ‖P(ζ)‖ ∈ [L - ε, L + ε]!
  have hP'ne : derivative P ≠ 0 := by intro h0; rw [h0, eval_zero] at hP'0; exact hP'0 rfl
  have hex_eps : ∃ ε : ℝ, 0 < ε ∧ ε < L / 2 ∧
      ∀ ζ : ℂ, (derivative P).eval ζ = 0 → |‖P.eval ζ‖ - L| > ε := by
    set S_roots : Finset ℂ := (derivative P).roots.toFinset
    by_cases hempty : S_roots.Nonempty
    · set dmin : ℝ := S_roots.inf' hempty (fun ζ => |‖P.eval ζ‖ - L|)
      have hdmin_pos : 0 < dmin := by
        rw [Finset.lt_inf'_iff]
        intro ζ hζ
        have hroot : (derivative P).eval ζ = 0 :=
          (Polynomial.mem_roots hP'ne).mp (Multiset.mem_toFinset.mp hζ)
        exact abs_pos.mpr (sub_ne_zero.mpr (hno_eq ζ hroot))
      refine ⟨min (dmin / 2) (L / 4), by positivity, by linarith [min_le_right (dmin / 2) (L / 4)], ?_⟩
      intro ζ hζ
      have hmem : ζ ∈ S_roots := Multiset.mem_toFinset.mpr ((Polynomial.mem_roots hP'ne).mpr hζ)
      have hle : dmin ≤ |‖P.eval ζ‖ - L| := Finset.inf'_le _ hmem
      linarith [min_le_left (dmin / 2) (L / 4)]
    · refine ⟨L / 4, by linarith, by linarith, fun ζ hζ => ?_⟩
      have hmem : ζ ∈ S_roots := Multiset.mem_toFinset.mpr ((Polynomial.mem_roots hP'ne).mpr hζ)
      exact absurd ⟨ζ, hmem⟩ hempty
  rcases hex_eps with ⟨ε, hε_pos, hε_lt, hε_gap⟩
  -- Step 4: Compactness of K = { z : ℂ | L - ε ≤ ‖P.eval z‖ ∧ ‖P.eval z‖ ≤ L + ε }
  set K : Set ℂ := {z : ℂ | L - ε ≤ ‖P.eval z‖ ∧ ‖P.eval z‖ ≤ L + ε}
  -- Coercivity of P (deg P ≥ 2 ≥ 1): ∃ R ≥ 0, ∀ z, ‖P(z)‖ ≤ L + ε → ‖z‖ ≤ R
  have hK_bdd : Bornology.IsBounded K := by
    have hPdeg1 : 0 < P.degree := by
      have hPne : P ≠ 0 := by intro h0; rw [h0] at hdeg; simp at hdeg
      rw [Polynomial.degree_eq_natDegree hPne]; exact_mod_cast (show 0 < P.natDegree by omega)
    have hlim : Filter.Tendsto (fun z : ℂ => ‖P.eval z‖) (Filter.cocompact ℂ) Filter.atTop :=
      Polynomial.tendsto_norm_atTop P hPdeg1 (tendsto_norm_cocompact_atTop (E := ℂ))
    have hev := hlim.eventually (Filter.eventually_gt_atTop (L + ε))
    rcases (Filter.hasBasis_cocompact.eventually_iff).mp hev with ⟨s, hs_comp, hs_out⟩
    exact hs_comp.isBounded.subset (fun z hz => by
      by_contra hnot; have := hs_out hnot; linarith only [this, hz.2])
  have hK_closed : IsClosed K := by
    have h1 : IsClosed {z : ℂ | L - ε ≤ ‖P.eval z‖} :=
      isClosed_le continuous_const P.continuous.norm
    have h2 : IsClosed {z : ℂ | ‖P.eval z‖ ≤ L + ε} :=
      isClosed_le P.continuous.norm continuous_const
    exact h1.inter h2
  have hK_comp : IsCompact K := Metric.isCompact_of_isClosed_isBounded hK_closed hK_bdd
  -- Get R ≥ 0 bounding K
  rcases hK_bdd.subset_closedBall (0 : ℂ) with ⟨R0, hKR0⟩
  set R : ℝ := max R0 0
  have hR_nn : 0 ≤ R := le_max_right R0 0
  have hKR : ∀ z ∈ K, ‖z‖ ≤ R := fun z hz => by
    have h := hKR0 hz; rw [Metric.mem_closedBall, dist_zero_right] at h
    exact le_trans h (le_max_left R0 0)
  -- Minimum of ‖P'(z)‖ on K is strictly positive (if K empty, use δ = 1)
  have hex_delta : ∃ δ : ℝ, 0 < δ ∧ ∀ z ∈ K, δ ≤ ‖(derivative P).eval z‖ := by
    by_cases hKne : K.Nonempty
    · obtain ⟨z₀, hz₀, hmin⟩ := hK_comp.exists_isMinOn hKne (derivative P).continuous.norm.continuousOn
      have hpos : 0 < ‖(derivative P).eval z₀‖ := by
        rw [norm_pos_iff]
        intro h0
        have hgap := hε_gap z₀ h0
        have habs : |‖P.eval z₀‖ - L| ≤ ε := abs_le.mpr ⟨by linarith [hz₀.1], by linarith [hz₀.2]⟩
        linarith
      exact ⟨‖(derivative P).eval z₀‖, hpos, fun z hz => hmin hz⟩
    · exact ⟨1, one_pos, fun z hz => absurd ⟨z, hz⟩ hKne⟩
  rcases hex_delta with ⟨δ, hδ_pos, hδ_le⟩
  -- Taylor bound C on ‖z‖ ≤ R, ‖h‖ ≤ 1
  rcases poly_taylor_bound P R hR_nn with ⟨C, hC_pos, hTaylor⟩
  -- Step 5: Construct continuous Newton-cutoff vector field v(z) and small step s > 0!
  set V : ℝ := (L + ε) / δ
  have hV_pos : 0 < V := div_pos (by linarith) hδ_pos
  set s : ℝ := min (1 / 2) (min (1 / V) ((L - ε) / (2 * C * V ^ 2)))
  have hs_pos : 0 < s := by
    have h1 : 0 < L - ε := by linarith
    positivity
  have hs_le_half : s ≤ 1 / 2 := min_le_left _ _
  have hsV_le1 : s * V ≤ 1 := by
    have h1 : s ≤ 1 / V := le_trans (min_le_right _ _) (min_le_left _ _)
    calc s * V ≤ (1 / V) * V := mul_le_mul_of_nonneg_right h1 (le_of_lt hV_pos)
      _ = 1 := one_div_mul_cancel (ne_of_gt hV_pos)
  have hs_quad : C * s * V ^ 2 ≤ (L - ε) / 2 := by
    have h1 : s ≤ (L - ε) / (2 * C * V ^ 2) := le_trans (min_le_right _ _) (min_le_right _ _)
    have hden : 0 < 2 * C * V ^ 2 := by positivity
    calc C * s * V ^ 2 = s * (C * V ^ 2) := by ring
      _ ≤ ((L - ε) / (2 * C * V ^ 2)) * (C * V ^ 2) := mul_le_mul_of_nonneg_right h1 (by positivity)
      _ = (L - ε) / 2 := by field_simp [ne_of_gt hC_pos, ne_of_gt hV_pos]
  -- Pick a near-optimal path γ with max ‖P(γ t)‖ ≤ L + η
  set η : ℝ := min (ε / 2) (s * (L - ε) / 4)
  have hη_pos : 0 < η := by
    have h1 : 0 < L - ε := by linarith
    positivity
  have hex_B : ∃ B ∈ S, B < L + η := exists_lt_of_csInf_lt hS_nonempty (by linarith)
  rcases hex_B with ⟨B, ⟨γ, hγc, hγ0, hγ1, hγB⟩, hB_lt⟩
  -- Define continuous cutoff φ(y) = max 0 (min 1 ((y - (L - ε)) / (ε / 2)))
  set φ : ℝ → ℝ := fun y => max 0 (min 1 ((y - (L - ε)) / (ε / 2)))
  have hφ_cont : Continuous φ :=
    continuous_const.max (continuous_const.min ((continuous_id.sub continuous_const).div_const _))
  -- Define continuous vector field v(z) = φ(‖P z‖) * P(z) * conj(P'(z)) / max(‖P'(z)‖^2, δ^2/2)
  set v : ℂ → ℂ := fun z =>
    ((φ ‖P.eval z‖ : ℝ) : ℂ) * P.eval z * starRingEnd ℂ ((derivative P).eval z) /
      ((max (‖(derivative P).eval z‖ ^ 2) (δ ^ 2 / 2) : ℝ) : ℂ)
  have hv_cont : Continuous v := by
    have hnum : Continuous (fun z : ℂ =>
        ((φ ‖P.eval z‖ : ℝ) : ℂ) * P.eval z * starRingEnd ℂ ((derivative P).eval z)) :=
      ((Complex.continuous_ofReal.comp (hφ_cont.comp P.continuous.norm)).mul P.continuous).mul
        (Complex.continuous_conj.comp (derivative P).continuous)
    have hden : Continuous (fun z : ℂ => ((max (‖(derivative P).eval z‖ ^ 2) (δ ^ 2 / 2) : ℝ) : ℂ)) :=
      Complex.continuous_ofReal.comp ((derivative P).continuous.norm.pow 2 |>.max continuous_const)
    have hne : ∀ z : ℂ, ((max (‖(derivative P).eval z‖ ^ 2) (δ ^ 2 / 2) : ℝ) : ℂ) ≠ 0 := fun z =>
      Complex.ofReal_ne_zero.mpr (ne_of_gt (lt_of_lt_of_le (by positivity : 0 < δ ^ 2 / 2) (le_max_right _ _)))
    exact hnum.div hden hne
  -- Deformed path γ̃(t) = γ(t) - s * v(γ(t))
  set γ' : ℝ → ℂ := fun t => γ t - (s : ℂ) * v (γ t)
  have hγ'_cont : ContinuousOn γ' (Set.Icc 0 1) :=
    hγc.sub (continuousOn_const.mul (hv_cont.comp_continuousOn hγc))
  have hφ0 : φ 0 = 0 := by
    dsimp [φ]
    have hneg : (0 - (L - ε)) / (ε / 2) ≤ 0 := div_nonpos_of_nonpos_of_nonneg (by linarith) (by positivity)
    rw [min_eq_right (by linarith), max_eq_left hneg]
  have hγ'0 : γ' 0 = 0 := by
    dsimp [γ', v]; rw [hγ0, hP0, norm_zero, hφ0]; simp
  have hγ'1 : γ' 1 = z₁ := by
    dsimp [γ', v]; rw [hγ1, hz₁_root, norm_zero, hφ0]; simp
  -- Show ∀ t ∈ [0, 1], ‖P(γ' t)‖ ≤ L - min (ε / 2) (s * (L - ε) / 4) < L!
  set drop : ℝ := min (ε / 2) (s * (L - ε) / 4)
  have hdrop_pos : 0 < drop := hη_pos
  have hγ'_bound : ∀ t ∈ Set.Icc (0 : ℝ) 1, ‖P.eval (γ' t)‖ ≤ L - drop := by
    intro t ht
    set z := γ t
    have hz_ub : ‖P.eval z‖ ≤ L + η := le_trans (hγB t ht) (le_of_lt hB_lt)
    have hz_ub_eps : ‖P.eval z‖ ≤ L + ε := by linarith [min_le_left (ε / 2) (s * (L - ε) / 4)]
    by_cases hlow : ‖P.eval z‖ ≤ L - ε
    · have hφz : φ ‖P.eval z‖ = 0 := by
        dsimp [φ]
        have hneg : (‖P.eval z‖ - (L - ε)) / (ε / 2) ≤ 0 :=
          div_nonpos_of_nonpos_of_nonneg (by linarith) (by positivity)
        rw [min_eq_right (by linarith), max_eq_left hneg]
      have hγ'z : γ' t = z := by dsimp [γ', v]; rw [hφz]; simp [z]
      rw [hγ'z]; linarith [min_le_left (ε / 2) (s * (L - ε) / 4)]
    · -- z ∈ K!
      push Not at hlow
      have hzK : z ∈ K := ⟨le_of_lt hlow, hz_ub_eps⟩
      have hP'z_ge : δ ≤ ‖(derivative P).eval z‖ := hδ_le z hzK
      have hP'z_ne : (derivative P).eval z ≠ 0 := norm_pos_iff.mp (lt_of_lt_of_le hδ_pos hP'z_ge)
      have hmax_eq : max (‖(derivative P).eval z‖ ^ 2) (δ ^ 2 / 2) = ‖(derivative P).eval z‖ ^ 2 :=
        max_eq_left (by nlinarith)
      have hv_eq : v z = ((φ ‖P.eval z‖ : ℝ) : ℂ) * P.eval z / (derivative P).eval z := by
        dsimp [v]; rw [hmax_eq]
        have hns : (derivative P).eval z * starRingEnd ℂ ((derivative P).eval z) =
            ((‖(derivative P).eval z‖ ^ 2 : ℝ) : ℂ) := by
          rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]
        have hden_ne : ((‖(derivative P).eval z‖ ^ 2 : ℝ) : ℂ) ≠ 0 :=
          Complex.ofReal_ne_zero.mpr (ne_of_gt (sq_pos_of_pos (lt_of_lt_of_le hδ_pos hP'z_ge)))
        field_simp [hP'z_ne, hden_ne]
        linear_combination (((φ ‖P.eval z‖ : ℝ) : ℂ) * P.eval z) * hns
      have hφ_nn : 0 ≤ φ ‖P.eval z‖ := le_max_left _ _
      have hφ_le1 : φ ‖P.eval z‖ ≤ 1 := max_le zero_le_one (min_le_left _ _)
      have hv_norm : ‖v z‖ ≤ φ ‖P.eval z‖ * V := by
        rw [hv_eq, norm_div, norm_mul, Complex.norm_real, Real.norm_of_nonneg hφ_nn]
        have h1 : ‖P.eval z‖ / ‖(derivative P).eval z‖ ≤ V := by
          dsimp [V]
          exact div_le_div₀ (by linarith) hz_ub_eps hδ_pos hP'z_ge
        calc φ ‖P.eval z‖ * ‖P.eval z‖ / ‖(derivative P).eval z‖
            = φ ‖P.eval z‖ * (‖P.eval z‖ / ‖(derivative P).eval z‖) := by ring
          _ ≤ φ ‖P.eval z‖ * V := mul_le_mul_of_nonneg_left h1 hφ_nn
      set h : ℂ := -((s : ℂ) * v z)
      have hh_norm : ‖h‖ ≤ s * φ ‖P.eval z‖ * V := by
        dsimp [h]; rw [norm_neg, norm_mul, Complex.norm_real, Real.norm_of_nonneg (le_of_lt hs_pos)]
        calc s * ‖v z‖ ≤ s * (φ ‖P.eval z‖ * V) := mul_le_mul_of_nonneg_left hv_norm (le_of_lt hs_pos)
          _ = s * φ ‖P.eval z‖ * V := by ring
      have hh_le1 : ‖h‖ ≤ 1 := by
        calc ‖h‖ ≤ s * φ ‖P.eval z‖ * V := hh_norm
          _ ≤ s * 1 * V := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hφ_le1 (le_of_lt hs_pos)) (le_of_lt hV_pos)
          _ = s * V := by ring
          _ ≤ 1 := hsV_le1
      have hTay := hTaylor z h (hKR z hzK) hh_le1
      have hlin : P.eval z + (derivative P).eval z * h =
          (((1 - s * φ ‖P.eval z‖) : ℝ) : ℂ) * P.eval z := by
        dsimp [h]; rw [hv_eq]
        field_simp [hP'z_ne]; push_cast; ring
      have h1sφ_nn : 0 ≤ 1 - s * φ ‖P.eval z‖ := by nlinarith [hs_le_half, hφ_le1, hs_pos]
      have hstep : ‖P.eval (z + h)‖ ≤ ‖P.eval z‖ - s * φ ‖P.eval z‖ * ((L - ε) / 2) := by
        have htri : ‖P.eval (z + h)‖ ≤ ‖P.eval z + (derivative P).eval z * h‖ + C * ‖h‖ ^ 2 := by
          have h1 := norm_add_le (P.eval z + (derivative P).eval z * h)
            (P.eval (z + h) - P.eval z - (derivative P).eval z * h)
          have h2 : P.eval z + (derivative P).eval z * h +
              (P.eval (z + h) - P.eval z - (derivative P).eval z * h) = P.eval (z + h) := by ring
          rw [h2] at h1
          linarith
        rw [hlin, norm_mul, Complex.norm_real, Real.norm_of_nonneg h1sφ_nn] at htri
        have hh2_le : C * ‖h‖ ^ 2 ≤ s * φ ‖P.eval z‖ * (C * s * V ^ 2) := by
          have hsq : ‖h‖ ^ 2 ≤ (s * φ ‖P.eval z‖ * V) ^ 2 :=
            pow_le_pow_left₀ (norm_nonneg h) hh_norm 2
          have hφ2 : φ ‖P.eval z‖ ^ 2 ≤ φ ‖P.eval z‖ := by nlinarith
          calc C * ‖h‖ ^ 2 ≤ C * (s * φ ‖P.eval z‖ * V) ^ 2 := mul_le_mul_of_nonneg_left hsq (le_of_lt hC_pos)
            _ = s * (φ ‖P.eval z‖ ^ 2) * (C * s * V ^ 2) := by ring
            _ ≤ s * φ ‖P.eval z‖ * (C * s * V ^ 2) := by
                apply mul_le_mul_of_nonneg_right
                · exact mul_le_mul_of_nonneg_left hφ2 (le_of_lt hs_pos)
                · positivity
        have hcs : s * φ ‖P.eval z‖ * (C * s * V ^ 2) ≤ s * φ ‖P.eval z‖ * ((L - ε) / 2) :=
          mul_le_mul_of_nonneg_left hs_quad (by positivity)
        have hPge : s * φ ‖P.eval z‖ * (L - ε) ≤ s * φ ‖P.eval z‖ * ‖P.eval z‖ :=
          mul_le_mul_of_nonneg_left (le_of_lt hlow) (by positivity)
        linarith
      have hγ'eq : γ' t = z + h := by dsimp [γ', h, z]; ring
      rw [hγ'eq]
      by_cases hmid : ‖P.eval z‖ ≤ L - ε / 2
      · have : 0 ≤ s * φ ‖P.eval z‖ * ((L - ε) / 2) := by
          have : 0 < L - ε := by linarith
          positivity
        linarith [min_le_left (ε / 2) (s * (L - ε) / 4)]
      · push Not at hmid
        have hφ1 : φ ‖P.eval z‖ = 1 := by
          dsimp [φ]
          have hge1 : 1 ≤ (‖P.eval z‖ - (L - ε)) / (ε / 2) := by
            rw [le_div_iff₀ (by positivity : 0 < ε / 2)]; linarith
          rw [min_eq_left hge1, max_eq_right zero_le_one]
        rw [hφ1, mul_one] at hstep
        linarith [min_le_right (ε / 2) (s * (L - ε) / 4)]
  -- Contradiction: L - drop ∈ S, so L ≤ L - drop!
  have hmemS : L - drop ∈ S := ⟨γ', hγ'_cont, hγ'0, hγ'1, hγ'_bound⟩
  have hleL : L ≤ L - drop := csInf_le ⟨M, hS_lb⟩ hmemS
  linarith

/-! ### Part C: Circle Lower Bound `‖1 - (1 - u)^n‖ ≥ 49/50` for ALL `n ≥ 2` -/

/-- Exact 4-term Taylor lower bound for `exp(-t)` on `t ≥ 0`:
    `1 - t + t^2 / 2 - t^3 / 6 ≤ Real.exp (-t)`. -/
lemma one_sub_add_sq_sub_cube_le_exp_neg {t : ℝ} (ht : 0 ≤ t) :
    1 - t + t ^ 2 / 2 - t ^ 3 / 6 ≤ Real.exp (-t) := by
  have hd_exp : ∀ y : ℝ, HasDerivAt (fun x : ℝ => Real.exp (-x)) (-Real.exp (-y)) y := by
    intro y
    have h := (Real.hasDerivAt_exp (-y)).comp y (hasDerivAt_id y).neg
    simpa [Function.comp_def] using h
  have h2 : ∀ x : ℝ, 0 ≤ x → Real.exp (-x) - (1 - x + x ^ 2 / 2) ≤ 0 := by
    intro x hx
    set g2 : ℝ → ℝ := fun y => (1 - y + y ^ 2 / 2) - Real.exp (-y)
    have hg2_deriv : ∀ y : ℝ, HasDerivAt g2 ((-1 + y) + Real.exp (-y)) y := by
      intro y
      have hp : HasDerivAt (fun y : ℝ => 1 - y + y ^ 2 / 2) (-1 + y) y := by
        have h1 : HasDerivAt (fun y : ℝ => (1 : ℝ) - y) (0 - 1) y :=
          (hasDerivAt_const y (1 : ℝ)).sub (hasDerivAt_id y)
        have h2 : HasDerivAt (fun y : ℝ => y ^ 2 / 2) ((2 : ℕ) * y ^ (2 - 1) / 2) y :=
          (hasDerivAt_pow 2 y).div_const 2
        convert h1.add h2 using 1; ring
      convert hp.sub (hd_exp y) using 1; ring
    have hg2_mono : MonotoneOn g2 (Set.Ici 0) := by
      apply monotoneOn_of_deriv_nonneg (convex_Ici 0)
      · exact ((continuous_const.sub continuous_id |>.add ((continuous_id.pow 2).div_const 2)).sub
          (Real.continuous_exp.comp continuous_neg)).continuousOn
      · intro y _; exact (hg2_deriv y).differentiableAt.differentiableWithinAt
      · intro y _; rw [(hg2_deriv y).deriv]; linarith [Real.add_one_le_exp (-y)]
    have h0 : g2 0 ≤ g2 x := hg2_mono (Set.mem_Ici.mpr (le_refl 0)) hx hx
    dsimp [g2] at h0; norm_num at h0; linarith
  set g3 : ℝ → ℝ := fun y => Real.exp (-y) - (1 - y + y ^ 2 / 2 - y ^ 3 / 6)
  have hg3_deriv : ∀ y : ℝ, HasDerivAt g3 ((1 - y + y ^ 2 / 2) - Real.exp (-y)) y := by
    intro y
    have hp : HasDerivAt (fun y : ℝ => 1 - y + y ^ 2 / 2 - y ^ 3 / 6) (-1 + y - y ^ 2 / 2) y := by
      have h1 : HasDerivAt (fun y : ℝ => (1 : ℝ) - y) (0 - 1) y :=
        (hasDerivAt_const y (1 : ℝ)).sub (hasDerivAt_id y)
      have h2 : HasDerivAt (fun y : ℝ => y ^ 2 / 2) ((2 : ℕ) * y ^ (2 - 1) / 2) y :=
        (hasDerivAt_pow 2 y).div_const 2
      have h3 : HasDerivAt (fun y : ℝ => y ^ 3 / 6) ((3 : ℕ) * y ^ (3 - 1) / 6) y :=
        (hasDerivAt_pow 3 y).div_const 6
      convert (h1.add h2).sub h3 using 1; ring
    convert (hd_exp y).sub hp using 1; ring
  have hg3_mono : MonotoneOn g3 (Set.Ici 0) := by
    apply monotoneOn_of_deriv_nonneg (convex_Ici 0)
    · exact ((Real.continuous_exp.comp continuous_neg).sub
        (((continuous_const.sub continuous_id).add ((continuous_id.pow 2).div_const 2)).sub
          ((continuous_id.pow 3).div_const 6))).continuousOn
    · intro y _; exact (hg3_deriv y).differentiableAt.differentiableWithinAt
    · intro y hy
      rw [(hg3_deriv y).deriv]
      have hy0 : 0 ≤ y := le_of_lt (by rw [interior_Ici] at hy; exact hy)
      linarith [h2 y hy0]
  have h0 : g3 0 ≤ g3 t := hg3_mono (Set.mem_Ici.mpr (le_refl 0)) ht ht
  dsimp [g3] at h0; norm_num at h0; linarith

/-- Elementary exponential upper bound: `exp (-3.58) ≤ 279 / 10000` and `exp (-3.92) ≤ 1 / 50`. -/
lemma exp_neg_358_le : Real.exp (-3.58) ≤ 279 / 10000 := by
  have hsum := Real.sum_le_exp_of_nonneg (by norm_num : (0 : ℝ) ≤ 3.58) 12
  have hval : (35.85 : ℝ) ≤ ∑ i ∈ Finset.range 12, (3.58 : ℝ) ^ i / (i.factorial : ℝ) := by
    norm_num [Finset.sum_range_succ, Nat.factorial]
  have hpos : (0 : ℝ) < Real.exp 3.58 := Real.exp_pos _
  rw [Real.exp_neg, inv_le_comm₀ hpos (by norm_num : (0 : ℝ) < 279 / 10000)]
  linarith

lemma exp_neg_392_le : Real.exp (-3.92) ≤ 1 / 50 := by
  have hsum := Real.sum_le_exp_of_nonneg (by norm_num : (0 : ℝ) ≤ 3.92) 11
  have hval : (50 : ℝ) ≤ ∑ i ∈ Finset.range 11, (3.92 : ℝ) ^ i / (i.factorial : ℝ) := by
    norm_num [Finset.sum_range_succ, Nat.factorial]
  have hpos : (0 : ℝ) < Real.exp 3.92 := Real.exp_pos _
  rw [Real.exp_neg, inv_le_comm₀ hpos (by norm_num : (0 : ℝ) < 1 / 50)]
  linarith

/-- Optimal clean radius `r_n` for Theorem 2:
    `r_2 = 1`, `r_3 = 1`, `r_4 = 3/4`, `r_5 = 4/5`, `r_n = 4/n` for `n ≥ 6`. -/
noncomputable def gwsRadius (n : ℕ) : ℝ :=
  if n = 2 then 1
  else if n = 3 then 1
  else if n = 4 then 3 / 4
  else if n = 5 then 4 / 5
  else 4 / (n : ℝ)

lemma gwsRadius_pos {n : ℕ} (hn : 2 ≤ n) : 0 < gwsRadius n := by
  unfold gwsRadius
  split_ifs <;> positivity

/-- `gwsRadius n < 2 * sin(π / n)` for all `n ≥ 2`! -/
lemma gwsRadius_lt_two_sin {n : ℕ} (hn : 2 ≤ n) :
    gwsRadius n < 2 * Real.sin (Real.pi / (n : ℝ)) := by
  unfold gwsRadius
  split_ifs with h2 h3 h4 h5
  · subst h2; norm_num [Real.sin_pi_div_two]
  · subst h3
    have h : Real.sin (Real.pi / 3) = Real.sqrt 3 / 2 := Real.sin_pi_div_three
    rw [show ((3 : ℕ) : ℝ) = 3 by norm_num, h]
    nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3), Real.sqrt_nonneg 3]
  · subst h4
    have h : Real.sin (Real.pi / 4) = Real.sqrt 2 / 2 := Real.sin_pi_div_four
    rw [show ((4 : ℕ) : ℝ) = 4 by norm_num, h]
    nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2), Real.sqrt_nonneg 2]
  · subst h5
    -- π / 5 > π / 6, and sin(π / 6) = 1 / 2? Wait 2*sin(π/6) = 1 > 4/5!
    have hmono : Real.sin (Real.pi / 6) ≤ Real.sin (Real.pi / 5) :=
      Real.sin_le_sin_of_le_of_le_pi_div_two (by linarith [Real.pi_pos]) (by linarith [Real.pi_pos])
        (by linarith [Real.pi_pos])
    rw [show ((5 : ℕ) : ℝ) = 5 by norm_num]
    rw [Real.sin_pi_div_six] at hmono
    linarith
  · -- n ≥ 6: sin(x) ≥ x - x^3 / 6 for x = π/n ∈ (0, π/6] => 2*sin(π/n) ≥ 2*(π/n)*(1 - π^2/216) > 5.9/n > 4/n!
    have hn6 : (6 : ℝ) ≤ (n : ℝ) := by exact_mod_cast (show 6 ≤ n by omega)
    set x : ℝ := Real.pi / (n : ℝ)
    have hx_pos : 0 < x := div_pos Real.pi_pos (by linarith)
    have hx_le : x ≤ Real.pi / 6 := div_le_div_of_nonneg_left (le_of_lt Real.pi_pos) (by norm_num) hn6
    have hsin_lb : x - x ^ 3 / 6 ≤ Real.sin x := le_of_lt (Real.sin_gt_sub_cube hx_pos)
    have hpi_gt : (3.1 : ℝ) < Real.pi := by linarith [Real.pi_gt_d2]
    have hpi_lt : Real.pi < 3.2 := by linarith [Real.pi_lt_d2]
    have hx2_le : x ^ 2 ≤ (3.2 / 6) ^ 2 := by
      have : x ≤ 3.2 / 6 := by linarith
      nlinarith
    have hfactor : 4 / (n : ℝ) < 2 * (x - x ^ 3 / 6) := by
      have hx_eq : x - x ^ 3 / 6 = x * (1 - x ^ 2 / 6) := by ring
      rw [hx_eq]
      have h1 : (0.95 : ℝ) ≤ 1 - x ^ 2 / 6 := by nlinarith
      have h2 : 2 * (x * 0.95) ≤ 2 * (x * (1 - x ^ 2 / 6)) := by nlinarith
      have h3 : 4 / (n : ℝ) < 2 * (x * 0.95) := by
        dsimp [x]; rw [show 2 * (Real.pi / (n : ℝ) * 0.95) = (1.9 * Real.pi) / (n : ℝ) by ring]
        exact div_lt_div_of_pos_right (by linarith) (by linarith)
      linarith
    linarith

/-- Key circle bound for `n ≥ 6` on `‖u‖ = 4 / n`: `49 / 50 ≤ ‖1 - (1 - u) ^ n‖`. -/
theorem circle_one_sub_pow_lower_bound_ge6 {n : ℕ} (hn6 : 6 ≤ n) {u : ℂ}
    (hu_r : ‖u‖ = 4 / (n : ℝ)) :
    49 / 50 ≤ ‖1 - (1 - u) ^ n‖ := by
  have hn6R : (6 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn6
  set r : ℝ := 4 / (n : ℝ)
  have hr_pos : 0 < r := by dsimp [r]; positivity
  have hr_le : r ≤ 2 / 3 := by
    dsimp [r]; rw [div_le_iff₀ (by linarith : (0 : ℝ) < (n : ℝ))]; linarith
  set w : ℂ := 1 - u
  set R : ℝ := ‖w‖
  have hR_pos : 0 < R := by
    have hlb : 1 - r ≤ R := by
      have h := norm_sub_le (1 - u) (-u)
      rw [show (1 - u) - (-u) = 1 by ring, norm_one, norm_neg, hu_r] at h
      linarith
    linarith
  have hR_sq : R ^ 2 = 1 - 2 * u.re + r ^ 2 := by
    dsimp [R, w]; rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
    simp only [Complex.sub_re, Complex.sub_im, Complex.one_re, Complex.one_im, zero_sub]
    have hns : u.re ^ 2 + u.im ^ 2 = r ^ 2 := by
      have := Complex.normSq_eq_norm_sq u; rw [hu_r, Complex.normSq_apply] at this; linarith
    linarith
  set φ : ℝ := w.arg
  have hw_polar : w = (R : ℂ) * Complex.exp (↑φ * Complex.I) := (Complex.norm_mul_exp_arg_mul_I w).symm
  have hnorm_sq : ‖1 - w ^ n‖ ^ 2 = 1 - 2 * R ^ n * Real.cos ((n : ℝ) * φ) + (R ^ n) ^ 2 := by
    have hwn : w ^ n = ((R ^ n : ℝ) : ℂ) * Complex.exp (↑((n : ℝ) * φ) * Complex.I) := by
      rw [hw_polar, mul_pow, ← Complex.exp_nat_mul]
      push_cast; congr 1; congr 1; ring
    rw [hwn, ← Complex.normSq_eq_norm_sq, Complex.normSq_apply, Complex.exp_mul_I]
    simp only [Complex.sub_re, Complex.sub_im, Complex.mul_re, Complex.mul_im, Complex.add_re,
      Complex.add_im, Complex.one_re, Complex.one_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.cos_ofReal_re, Complex.cos_ofReal_im, Complex.sin_ofReal_re, Complex.sin_ofReal_im,
      Complex.I_re, Complex.I_im, mul_zero, mul_one, zero_mul, sub_zero, zero_add, add_zero, zero_sub]
    have hcs := Real.cos_sq_add_sin_sq ((n : ℝ) * φ)
    nlinarith
  have hsin_phi : |Real.sin φ| = |u.im| / R := by
    have h1 := Complex.sin_arg w
    have hwim : w.im = -u.im := by simp [w]
    rw [hwim] at h1
    change |Real.sin w.arg| = |u.im| / R
    rw [h1, abs_div, abs_neg, abs_of_pos hR_pos]
  have hphi_lt_pi2 : |φ| < Real.pi / 2 := by
    have hre_pos : 0 < w.re := by
      have : |u.re| ≤ r := by rw [← hu_r]; exact Complex.abs_re_le_norm u
      have := (abs_le.mp this).2
      simp only [w, Complex.sub_re, Complex.one_re]; linarith
    exact Complex.abs_arg_lt_pi_div_two_iff.mpr (Or.inl hre_pos)
  have hsin_abs_eq : Real.sin |φ| = |Real.sin φ| := by
    have hphi_b := abs_lt.mp hphi_lt_pi2
    rcases le_or_gt 0 φ with h | h
    · rw [abs_of_nonneg h, abs_of_nonneg (Real.sin_nonneg_of_nonneg_of_le_pi h (by linarith only [hphi_b.2, Real.pi_pos]))]
    · rw [abs_of_neg h, Real.sin_neg, abs_of_neg (Real.sin_neg_of_neg_of_neg_pi_lt h (by linarith only [hphi_b.1, Real.pi_pos]))]
  have hsin_le_r : Real.sin |φ| ≤ r := by
    rw [hsin_abs_eq, hsin_phi, div_le_iff₀ hR_pos]
    have hns : u.re ^ 2 + u.im ^ 2 = r ^ 2 := by
      have := Complex.normSq_eq_norm_sq u; rw [hu_r, Complex.normSq_apply] at this; linarith only [this]
    have hsq : u.im ^ 2 ≤ (r * R) ^ 2 := by
      have hdiff : (r * R) ^ 2 - u.im ^ 2 = (u.re - r ^ 2) ^ 2 := by
        rw [mul_pow, hR_sq]
        linear_combination -hns
      nlinarith only [hdiff, sq_nonneg (u.re - r ^ 2)]
    nlinarith only [hsq, abs_nonneg u.im, sq_abs u.im, mul_nonneg (le_of_lt hr_pos) (le_of_lt hR_pos)]
  have hphi_le : |φ| ≤ (115 / 100 : ℝ) * r := by
    set y : ℝ := (115 / 100 : ℝ) * r
    have hy_pos : 0 < y := by dsimp [y]; positivity
    have hy_le : y ≤ (115 / 100 : ℝ) * (2 / 3) := by dsimp [y]; linarith only [hr_le]
    have hy_lt : y < Real.pi / 2 := by linarith only [hy_le, Real.pi_gt_three]
    have hsin_y : r ≤ Real.sin y := by
      have hlb := Real.sin_gt_sub_cube hy_pos
      have hy2 : y ^ 2 ≤ ((115 / 100 : ℝ) * (2 / 3)) ^ 2 := by nlinarith only [hy_pos, hy_le]
      have hcalc : r ≤ y - y ^ 3 / 6 := by
        have : y - y ^ 3 / 6 = r * ((115 / 100) * (1 - y ^ 2 / 6)) := by dsimp [y]; ring
        rw [this]; nlinarith only [hy2, hr_pos]
      linarith only [hlb, hcalc]
    by_contra hgt; push Not at hgt
    have hmono := Real.sin_lt_sin_of_lt_of_le_pi_div_two (by linarith only [hy_pos, Real.pi_pos])
      (le_of_lt hphi_lt_pi2) hgt
    linarith only [hmono, hsin_y, hsin_le_r]
  have hnphi_le : (n : ℝ) * |φ| ≤ 3 * Real.pi / 2 := by
    have h1 : (n : ℝ) * |φ| ≤ (n : ℝ) * ((115 / 100) * r) :=
      mul_le_mul_of_nonneg_left hphi_le (by linarith only [hn6R])
    have h2 : (n : ℝ) * ((115 / 100) * r) = 46 / 10 := by
      dsimp [r]; field_simp [ne_of_gt (by linarith only [hn6R] : (0 : ℝ) < (n : ℝ))]; ring
    linarith only [h1, h2, Real.pi_gt_d2]
  -- PIECE A: π / 2 ≤ n * |φ| ≤ 3 * π / 2 => cos(n * φ) ≤ 0 => ‖1 - w^n‖ ≥ 1 ≥ 49/50!
  by_cases hA : Real.pi / 2 ≤ (n : ℝ) * |φ|
  · have hcos_np : Real.cos ((n : ℝ) * φ) ≤ 0 := by
      have habs : |(n : ℝ) * φ| = (n : ℝ) * |φ| := by rw [abs_mul, abs_of_pos (by linarith only [hn6R])]
      rw [← Real.cos_abs ((n : ℝ) * φ), habs]
      exact Real.cos_nonpos_of_pi_div_two_le_of_le hA (by linarith only [hnphi_le])
    have hsq : (49 / 50 : ℝ) ^ 2 ≤ ‖1 - w ^ n‖ ^ 2 := by
      rw [hnorm_sq]
      have hRn_nn : 0 ≤ R ^ n := pow_nonneg (le_of_lt hR_pos) n
      nlinarith only [hcos_np, hRn_nn, sq_nonneg (R ^ n)]
    nlinarith only [hsq, norm_nonneg (1 - w ^ n)]
  push Not at hA
  have hsin_lt : |u.im| / R ≤ Real.pi / (2 * (n : ℝ)) := by
    have h1 : Real.sin |φ| ≤ |φ| := Real.sin_le (abs_nonneg φ)
    have h2 : |φ| ≤ Real.pi / (2 * (n : ℝ)) := by
      rw [le_div_iff₀ (by linarith : 0 < 2 * (n : ℝ))]; linarith
    linarith [hsin_phi, hsin_abs_eq]
  -- PIECE B: u.re ≤ 0 => R^n > 2 => ‖1 - w^n‖ ≥ R^n - 1 > 1 ≥ 49/50!
  by_cases hB : u.re ≤ 0
  · have hR_le : R ≤ 5 / 3 := by
      have h1 : R ≤ 1 + r := by
        have := norm_sub_le (1 : ℂ) u; rw [norm_one, hu_r] at this; exact this
      linarith
    have huim_le : |u.im| ≤ (7 / 10 : ℝ) * r := by
      have h1 : |u.im| ≤ (Real.pi / (2 * (n : ℝ))) * R := (div_le_iff₀ hR_pos).mp hsin_lt
      have h2 : (Real.pi / (2 * (n : ℝ))) * R = (Real.pi / 8) * R * r := by
        dsimp [r]; field_simp [ne_of_gt (by linarith : (0 : ℝ) < (n : ℝ))]; ring
      rw [h2] at h1
      have hpi : Real.pi ≤ 3.2 := by linarith [Real.pi_lt_d2]
      calc |u.im| ≤ (Real.pi / 8) * R * r := h1
        _ ≤ (3.2 / 8) * (5 / 3) * r := by gcongr
        _ ≤ (7 / 10) * r := by nlinarith only [hr_pos]
    have hure_le : u.re ≤ -(7 / 10 : ℝ) * r := by
      have hns : u.re ^ 2 + u.im ^ 2 = r ^ 2 := by
        have := Complex.normSq_eq_norm_sq u; rw [hu_r, Complex.normSq_apply] at this; linarith only [this]
      have huim2 : u.im ^ 2 ≤ ((7 / 10) * r) ^ 2 := by
        rw [← sq_abs u.im]; nlinarith only [huim_le, abs_nonneg u.im, hr_pos]
      nlinarith only [hns, huim2, hB, hr_pos]
    have hR2_ge : 1 + 5 / (n : ℝ) ≤ R ^ 2 := by
      rw [hR_sq]
      have h1 : (7 / 5 : ℝ) * r = 56 / (10 * (n : ℝ)) := by dsimp [r]; ring
      have h2 : 5 / (n : ℝ) ≤ 56 / (10 * (n : ℝ)) := by
        rw [div_le_div_iff₀ (by linarith) (by linarith)]; linarith
      nlinarith only [hure_le, h1, h2, sq_nonneg r]
    have hR2n_ge : 6 ≤ (R ^ 2) ^ n := by
      have h5n_nn : 0 ≤ 5 / (n : ℝ) := div_nonneg (by norm_num) (by linarith only [hn6R])
      have hber : 1 + (n : ℝ) * (5 / (n : ℝ)) ≤ (1 + 5 / (n : ℝ)) ^ n :=
        one_add_mul_le_pow (by linarith only [h5n_nn]) n
      have hcancel : (n : ℝ) * (5 / (n : ℝ)) = 5 := mul_div_cancel₀ 5 (ne_of_gt (by linarith only [hn6R]))
      have hpow : (1 + 5 / (n : ℝ)) ^ n ≤ (R ^ 2) ^ n :=
        pow_le_pow_left₀ (by linarith only [h5n_nn]) hR2_ge n
      linarith only [hber, hcancel, hpow]
    have hRn_gt2 : 2 < R ^ n := by
      have h1 : (R ^ n) ^ 2 = (R ^ 2) ^ n := by rw [← pow_mul, ← pow_mul, mul_comm]
      nlinarith only [h1, hR2n_ge, pow_nonneg (le_of_lt hR_pos) n]
    have hrev : R ^ n - 1 ≤ ‖1 - w ^ n‖ := by
      have h := norm_sub_le (1 - w ^ n) (1 : ℂ)
      rw [show (1 - w ^ n) - 1 = -(w ^ n) by ring, norm_neg, norm_pow, norm_one] at h
      linarith only [h]
    linarith only [hRn_gt2, hrev]
  push Not at hB
  have hR_le_121 : R ≤ 13 / 10 := by
    have h1 : R ^ 2 ≤ 1 + r ^ 2 := by rw [hR_sq]; linarith only [hB]
    nlinarith only [h1, hr_le, hr_pos, hR_pos]
  have huim_rough : |u.im| ≤ (52 / 100 : ℝ) * r := by
    have h1 : |u.im| ≤ (Real.pi / (2 * (n : ℝ))) * R := (div_le_iff₀ hR_pos).mp hsin_lt
    have h2 : (Real.pi / (2 * (n : ℝ))) * R = (Real.pi / 8) * R * r := by
      dsimp [r]; field_simp [ne_of_gt (by linarith : (0 : ℝ) < (n : ℝ))]; ring
    rw [h2] at h1
    have hpi : Real.pi ≤ 3.15 := by linarith [Real.pi_lt_d2]
    calc |u.im| ≤ (Real.pi / 8) * R * r := h1
      _ ≤ (3.15 / 8) * (13 / 10) * r := by gcongr
      _ ≤ (52 / 100) * r := by nlinarith only [hr_pos]
  have hure_rough : (85 / 100 : ℝ) * r ≤ u.re := by
    have hns : u.re ^ 2 + u.im ^ 2 = r ^ 2 := by
      have := Complex.normSq_eq_norm_sq u; rw [hu_r, Complex.normSq_apply] at this; linarith only [this]
    have huim2 : u.im ^ 2 ≤ ((52 / 100) * r) ^ 2 := by
      rw [← sq_abs u.im]; nlinarith only [huim_rough, abs_nonneg u.im, hr_pos]
    nlinarith only [hns, huim2, hB, hr_pos]
  have hR_le1 : R ≤ 1 := by
    have h1 : R ^ 2 ≤ 1 := by rw [hR_sq]; nlinarith only [hure_rough, hr_le, hr_pos]
    nlinarith only [h1, hR_pos]
  -- PIECE C: π/4 ≤ n*|φ| < π/2
  by_cases hC : Real.pi / 4 ≤ (n : ℝ) * |φ|
  · have huim_c : |u.im| ≤ (393 / 1000 : ℝ) * r := by
      have h1 : |u.im| ≤ (Real.pi / (2 * (n : ℝ))) * R := (div_le_iff₀ hR_pos).mp hsin_lt
      have h2 : (Real.pi / (2 * (n : ℝ))) * R = (Real.pi / 8) * R * r := by
        dsimp [r]; field_simp [ne_of_gt (by linarith : (0 : ℝ) < (n : ℝ))]; ring
      rw [h2] at h1
      have hpi : Real.pi ≤ 3.142 := by linarith [Real.pi_lt_d4]
      calc |u.im| ≤ (Real.pi / 8) * R * r := h1
        _ ≤ (3.142 / 8) * 1 * r := by gcongr
        _ ≤ (393 / 1000) * r := by nlinarith only [hr_pos]
    have hure_c : (919 / 1000 : ℝ) * r ≤ u.re := by
      have hns : u.re ^ 2 + u.im ^ 2 = r ^ 2 := by
        have := Complex.normSq_eq_norm_sq u; rw [hu_r, Complex.normSq_apply] at this; linarith only [this]
      have huim2 : u.im ^ 2 ≤ ((393 / 1000) * r) ^ 2 := by
        rw [← sq_abs u.im]; nlinarith only [huim_c, abs_nonneg u.im, hr_pos]
      nlinarith only [hns, huim2, hB, hr_pos]
    have hR2_exp : R ^ 2 ≤ Real.exp (-((179 / 100 : ℝ) * r)) := by
      have hpoly : R ^ 2 ≤ 1 - (179 / 100) * r + ((179 / 100) * r) ^ 2 / 2 - ((179 / 100) * r) ^ 3 / 6 := by
        rw [hR_sq]
        have hdiff : (1 - (179 / 100) * r + ((179 / 100) * r) ^ 2 / 2 - ((179 / 100) * r) ^ 3 / 6) -
            (1 - 2 * ((919 / 1000) * r) + r ^ 2) =
            r * (48 / 1000 + (60205 / 100000) * r - (5735339 / 6000000) * r ^ 2) := by ring
        have hquad : 0 ≤ 48 / 1000 + (60205 / 100000) * r - (5735339 / 6000000) * r ^ 2 := by
          nlinarith only [hr_pos, hr_le]
        nlinarith only [hdiff, hure_c, mul_nonneg (le_of_lt hr_pos) hquad]
      exact le_trans hpoly (one_sub_add_sq_sub_cube_le_exp_neg (by positivity))
    have hRn_le : R ^ n ≤ 279 / 10000 := by
      have hpow : (R ^ 2) ^ n ≤ (Real.exp (-((179 / 100 : ℝ) * r))) ^ n :=
        pow_le_pow_left₀ (by positivity) hR2_exp n
      rw [← Real.exp_nat_mul] at hpow
      have hmul : (n : ℝ) * -((179 / 100 : ℝ) * r) = ((2 : ℕ) : ℝ) * (-3.58 : ℝ) := by
        dsimp [r]; field_simp [ne_of_gt (by linarith : (0 : ℝ) < (n : ℝ))]; norm_num
      rw [hmul, Real.exp_nat_mul] at hpow
      have hR2n : (R ^ n) ^ 2 = (R ^ 2) ^ n := by rw [← pow_mul, ← pow_mul, mul_comm]
      have hRn_le_exp : R ^ n ≤ Real.exp (-3.58) := by
        nlinarith only [hpow, hR2n, pow_nonneg (le_of_lt hR_pos) n, Real.exp_pos (-3.58)]
      exact le_trans hRn_le_exp exp_neg_358_le
    have hcos_le : Real.cos ((n : ℝ) * φ) ≤ 708 / 1000 := by
      have habs : |(n : ℝ) * φ| = (n : ℝ) * |φ| := by rw [abs_mul, abs_of_pos (by linarith only [hn6R])]
      rw [← Real.cos_abs ((n : ℝ) * φ), habs]
      have hmono : Real.cos ((n : ℝ) * |φ|) ≤ Real.cos (Real.pi / 4) :=
        Real.cos_le_cos_of_nonneg_of_le_pi (by linarith only [Real.pi_pos]) (by linarith only [hA, Real.pi_pos]) hC
      rw [Real.cos_pi_div_four] at hmono
      have hsq2 : Real.sqrt 2 / 2 ≤ 708 / 1000 := by
        nlinarith only [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2), Real.sqrt_nonneg 2]
      linarith only [hmono, hsq2]
    have hsq : (49 / 50 : ℝ) ^ 2 ≤ ‖1 - w ^ n‖ ^ 2 := by
      rw [hnorm_sq]
      have hRn_nn : 0 ≤ R ^ n := pow_nonneg (le_of_lt hR_pos) n
      have hprod : 2 * R ^ n * Real.cos ((n : ℝ) * φ) ≤ 2 * (279 / 10000) * (708 / 1000) := by
        nlinarith only [hRn_le, hRn_nn, hcos_le]
      nlinarith only [hprod, sq_nonneg (R ^ n)]
    nlinarith only [hsq, norm_nonneg (1 - w ^ n)]
  -- PIECE D: n * |φ| < π / 4
  · push Not at hC
    have hsin_lt_d : |u.im| / R ≤ Real.pi / (4 * (n : ℝ)) := by
      have h1 : Real.sin |φ| ≤ |φ| := Real.sin_le (abs_nonneg φ)
      have h2 : |φ| ≤ Real.pi / (4 * (n : ℝ)) := by
        rw [le_div_iff₀ (by linarith only [hn6R] : 0 < 4 * (n : ℝ))]; linarith only [hC]
      linarith only [h1, h2, hsin_phi, hsin_abs_eq]
    have huim_d : |u.im| ≤ (197 / 1000 : ℝ) * r := by
      have h1 : |u.im| ≤ (Real.pi / (4 * (n : ℝ))) * R := (div_le_iff₀ hR_pos).mp hsin_lt_d
      have h2 : (Real.pi / (4 * (n : ℝ))) * R = (Real.pi / 16) * R * r := by
        dsimp [r]; field_simp [ne_of_gt (by linarith only [hn6R] : (0 : ℝ) < (n : ℝ))]; ring
      rw [h2] at h1
      have hpi : Real.pi ≤ 3.142 := by linarith [Real.pi_lt_d4]
      calc |u.im| ≤ (Real.pi / 16) * R * r := h1
        _ ≤ (3.142 / 16) * 1 * r := by gcongr
        _ ≤ (197 / 1000) * r := by nlinarith only [hr_pos]
    have hure_d : (98 / 100 : ℝ) * r ≤ u.re := by
      have hns : u.re ^ 2 + u.im ^ 2 = r ^ 2 := by
        have := Complex.normSq_eq_norm_sq u; rw [hu_r, Complex.normSq_apply] at this; linarith only [this]
      have huim2 : u.im ^ 2 ≤ ((197 / 1000) * r) ^ 2 := by
        rw [← sq_abs u.im]; nlinarith only [huim_d, abs_nonneg u.im, hr_pos]
      nlinarith only [hns, huim2, hB, hr_pos]
    have hR2_exp : R ^ 2 ≤ Real.exp (-((196 / 100 : ℝ) * r)) := by
      have hpoly : R ^ 2 ≤ 1 - (196 / 100) * r + ((196 / 100) * r) ^ 2 / 2 - ((196 / 100) * r) ^ 3 / 6 := by
        rw [hR_sq]
        have hdiff : (1 - (196 / 100) * r + ((196 / 100) * r) ^ 2 / 2 - ((196 / 100) * r) ^ 3 / 6) -
            (1 - 2 * ((98 / 100) * r) + r ^ 2) =
            r ^ 2 * ((9208 / 10000) - (7529536 / 6000000) * r) := by ring
        have hlin : 0 ≤ (9208 / 10000 : ℝ) - (7529536 / 6000000) * r := by nlinarith only [hr_le]
        nlinarith only [hdiff, hure_d, mul_nonneg (sq_nonneg r) hlin]
      exact le_trans hpoly (one_sub_add_sq_sub_cube_le_exp_neg (by positivity))
    have hRn_le : R ^ n ≤ 1 / 50 := by
      have hpow : (R ^ 2) ^ n ≤ (Real.exp (-((196 / 100 : ℝ) * r))) ^ n :=
        pow_le_pow_left₀ (by positivity) hR2_exp n
      rw [← Real.exp_nat_mul] at hpow
      have hmul : (n : ℝ) * -((196 / 100 : ℝ) * r) = ((2 : ℕ) : ℝ) * (-3.92 : ℝ) := by
        dsimp [r]; field_simp [ne_of_gt (by linarith only [hn6R] : (0 : ℝ) < (n : ℝ))]; norm_num
      rw [hmul, Real.exp_nat_mul] at hpow
      have hR2n : (R ^ n) ^ 2 = (R ^ 2) ^ n := by rw [← pow_mul, ← pow_mul, mul_comm]
      have hRn_le_exp : R ^ n ≤ Real.exp (-3.92) := by
        nlinarith only [hpow, hR2n, pow_nonneg (le_of_lt hR_pos) n, Real.exp_pos (-3.92)]
      exact le_trans hRn_le_exp exp_neg_392_le
    have hrev : 1 - R ^ n ≤ ‖1 - w ^ n‖ := by
      have h := norm_sub_le (1 - w ^ n) (-(w ^ n))
      rw [show (1 - w ^ n) - -(w ^ n) = 1 by ring, norm_one, norm_neg, norm_pow] at h
      linarith only [h]
    linarith only [hRn_le, hrev]

/-- **Key Circle Bound for ALL `n ≥ 2`**:
    For every `n ≥ 2` and every `u : ℂ` on the circle `‖u‖ = gwsRadius n`,
      `49 / 50 ≤ ‖1 - (1 - u) ^ n‖`
    (and `1 ≤ ‖1 - (1 - u) ^ n‖` for `n = 2, 3`). -/
theorem circle_one_sub_pow_lower_bound {n : ℕ} (hn : 2 ≤ n) {u : ℂ}
    (hu : ‖u‖ = gwsRadius n) :
    49 / 50 ≤ ‖1 - (1 - u) ^ n‖ := by
  by_cases hn2 : n = 2
  · subst hn2
    have hu1 : ‖u‖ = 1 := by simpa [gwsRadius] using hu
    have hid : 1 - (1 - u) ^ 2 = u * (2 - u) := by ring
    rw [hid, norm_mul, hu1, one_mul]
    have hrev : 2 - ‖u‖ ≤ ‖(2 : ℂ) - u‖ := by
      have h := norm_sub_le ((2 : ℂ) - u) (-u)
      have h2 : (2 : ℂ) - u - (-u) = 2 := by ring
      rw [h2, norm_neg] at h; norm_num at h; linarith
    linarith
  by_cases hn3 : n = 3
  · subst hn3
    have hu1 : ‖u‖ = 1 := by simpa [gwsRadius] using hu
    have hns : u.re ^ 2 + u.im ^ 2 = 1 := by
      have := Complex.normSq_eq_norm_sq u; rw [hu1, Complex.normSq_apply] at this; linarith
    set w : ℂ := 1 - u
    have hw_ns : Complex.normSq w = 2 - 2 * u.re := by
      dsimp [w]; rw [Complex.normSq_apply]
      simp only [Complex.sub_re, Complex.sub_im, Complex.one_re, Complex.one_im, zero_sub]
      linarith
    have hw3_re : (w ^ 3).re = (1 - u.re) ^ 3 - 3 * (1 - u.re) * u.im ^ 2 := by
      dsimp [w]
      simp only [pow_succ, pow_zero, one_mul, Complex.sub_re, Complex.sub_im, Complex.mul_re,
        Complex.mul_im, Complex.one_re, Complex.one_im, zero_sub]
      ring
    have hexp : ‖1 - w ^ 3‖ ^ 2 = 1 + 12 * (1 - u.re) ^ 2 := by
      have h1 : ‖1 - w ^ 3‖ ^ 2 = 1 - 2 * (w ^ 3).re + (Complex.normSq w) ^ 3 := by
        rw [← Complex.normSq_eq_norm_sq]
        have hns3 : Complex.normSq (w ^ 3) = (Complex.normSq w) ^ 3 := map_pow Complex.normSq w 3
        rw [Complex.normSq_apply]
        simp only [Complex.sub_re, Complex.sub_im, Complex.one_re, Complex.one_im, zero_sub]
        have h2 := Complex.normSq_apply (w ^ 3)
        linarith
      rw [h1, hw3_re, hw_ns]
      have him2 : u.im ^ 2 = 1 - u.re ^ 2 := by linarith
      rw [him2]; ring
    nlinarith only [hexp, sq_nonneg (1 - u.re), norm_nonneg (1 - w ^ 3)]
  by_cases hn4 : n = 4
  · subst hn4
    have hur : ‖u‖ = 3 / 4 := by simpa [gwsRadius] using hu
    have hns : u.re ^ 2 + u.im ^ 2 = 9 / 16 := by
      have := Complex.normSq_eq_norm_sq u; rw [hur, Complex.normSq_apply] at this; linarith
    set x := u.re
    have hx_le : x ≤ 3 / 4 := by
      have : |x| ≤ 3 / 4 := by rw [← hur]; exact Complex.abs_re_le_norm u
      exact (abs_le.mp this).2
    set w : ℂ := 1 - u
    have hw_ns : Complex.normSq w = 25 / 16 - 2 * x := by
      dsimp [w, x]; rw [Complex.normSq_apply]
      simp only [Complex.sub_re, Complex.sub_im, Complex.one_re, Complex.one_im, zero_sub]
      linarith
    have hw4_re : (w ^ 4).re = (1 - x) ^ 4 - 6 * (1 - x) ^ 2 * u.im ^ 2 + u.im ^ 4 := by
      dsimp [w, x]
      simp only [pow_succ, pow_zero, one_mul, Complex.sub_re, Complex.sub_im, Complex.mul_re,
        Complex.mul_im, Complex.one_re, Complex.one_im, zero_sub]
      ring
    have hexp : ‖1 - w ^ 4‖ ^ 2 =
        65025 / 65536 + (3 / 4 - x) * (6885 / 512 - (963 / 32) * x + 18 * x ^ 2) := by
      have h1 : ‖1 - w ^ 4‖ ^ 2 = 1 - 2 * (w ^ 4).re + (Complex.normSq w) ^ 4 := by
        rw [← Complex.normSq_eq_norm_sq]
        have hns4 : Complex.normSq (w ^ 4) = (Complex.normSq w) ^ 4 := map_pow Complex.normSq w 4
        rw [Complex.normSq_apply]
        simp only [Complex.sub_re, Complex.sub_im, Complex.one_re, Complex.one_im, zero_sub]
        have h2 := Complex.normSq_apply (w ^ 4)
        linarith
      rw [h1, hw4_re, hw_ns]
      have him2 : u.im ^ 2 = 9 / 16 - x ^ 2 := by dsimp [x]; linarith
      rw [show u.im ^ 4 = (u.im ^ 2) ^ 2 by ring, him2]
      ring
    have hq_pos : 0 ≤ 6885 / 512 - (963 / 32) * x + 18 * x ^ 2 := by
      nlinarith only [sq_nonneg (6 * x - 321 / 64)]
    have hsq : (49 / 50 : ℝ) ^ 2 ≤ ‖1 - w ^ 4‖ ^ 2 := by
      rw [hexp]
      have : 0 ≤ (3 / 4 - x) * (6885 / 512 - (963 / 32) * x + 18 * x ^ 2) :=
        mul_nonneg (by linarith) hq_pos
      linarith
    nlinarith only [hsq, norm_nonneg (1 - w ^ 4)]
  by_cases hn5 : n = 5
  · subst hn5
    have hur : ‖u‖ = 4 / 5 := by simpa [gwsRadius] using hu
    have hns : u.re ^ 2 + u.im ^ 2 = 16 / 25 := by
      have := Complex.normSq_eq_norm_sq u; rw [hur, Complex.normSq_apply] at this; linarith
    set x := u.re
    set t : ℝ := 4 / 5 - x
    have ht_nn : 0 ≤ t := by
      have : |x| ≤ 4 / 5 := by rw [← hur]; exact Complex.abs_re_le_norm u
      dsimp [t]; linarith [(abs_le.mp this).2]
    set w : ℂ := 1 - u
    have hw_ns : Complex.normSq w = 41 / 25 - 2 * x := by
      dsimp [w, x]; rw [Complex.normSq_apply]
      simp only [Complex.sub_re, Complex.sub_im, Complex.one_re, Complex.one_im, zero_sub]
      linarith
    have hw5_re : (w ^ 5).re = (1 - x) ^ 5 - 10 * (1 - x) ^ 3 * u.im ^ 2 + 5 * (1 - x) * u.im ^ 4 := by
      dsimp [w, x]
      simp only [pow_succ, pow_zero, one_mul, Complex.sub_re, Complex.sub_im, Complex.mul_re,
        Complex.mul_im, Complex.one_re, Complex.one_im, zero_sub]
      ring
    have hexp : ‖1 - w ^ 5‖ ^ 2 =
        9759376 / 9765625 + t * (18752 / 78125 - (4992 / 3125) * t - (384 / 125) * t ^ 2 + (256 / 5) * t ^ 3) := by
      have h1 : ‖1 - w ^ 5‖ ^ 2 = 1 - 2 * (w ^ 5).re + (Complex.normSq w) ^ 5 := by
        rw [← Complex.normSq_eq_norm_sq]
        have hns5 : Complex.normSq (w ^ 5) = (Complex.normSq w) ^ 5 := map_pow Complex.normSq w 5
        rw [Complex.normSq_apply]
        simp only [Complex.sub_re, Complex.sub_im, Complex.one_re, Complex.one_im, zero_sub]
        have h2 := Complex.normSq_apply (w ^ 5)
        linarith
      rw [h1, hw5_re, hw_ns]
      have him2 : u.im ^ 2 = 16 / 25 - x ^ 2 := by dsimp [x]; linarith
      rw [show u.im ^ 4 = (u.im ^ 2) ^ 2 by ring, him2]
      dsimp [t]; ring
    have hq_pos : 0 ≤ 18752 / 78125 - (4992 / 3125) * t - (384 / 125) * t ^ 2 + (256 / 5) * t ^ 3 := by
      have hA : 0 ≤ (256 / 5 : ℝ) * t ^ 2 - 20 * t + 2 := by
        nlinarith only [sq_nonneg (10 * t - 2)]
      have hB : 0 ≤ (16928 / 1000 : ℝ) * t ^ 2 - (4992 / 3125 + 2) * t + 18752 / 78125 := by
        nlinarith only [sq_nonneg (13 * t - 138 / 100)]
      have hdecomp : 18752 / 78125 - (4992 / 3125) * t - (384 / 125) * t ^ 2 + (256 / 5) * t ^ 3 =
          t * ((256 / 5) * t ^ 2 - 20 * t + 2) +
          ((16928 / 1000) * t ^ 2 - (4992 / 3125 + 2) * t + 18752 / 78125) := by ring
      rw [hdecomp]
      nlinarith only [mul_nonneg ht_nn hA, hB]
    have hsq : (49 / 50 : ℝ) ^ 2 ≤ ‖1 - w ^ 5‖ ^ 2 := by
      rw [hexp]
      nlinarith only [mul_nonneg ht_nn hq_pos]
    nlinarith only [hsq, norm_nonneg (1 - w ^ 5)]
  · have hn6 : 6 ≤ n := by omega
    have hr_eq : gwsRadius n = 4 / (n : ℝ) := by simp [gwsRadius, hn2, hn3, hn4, hn5]
    rw [hr_eq] at hu
    exact circle_one_sub_pow_lower_bound_ge6 hn6 hu

/-- Minimum Modulus Principle on `F_n(v) = (1 - (1 - v)^n) / (n * v)` over `‖v‖ ≤ gwsRadius n`:
    for every `n ≥ 2` and every `‖v‖ ≤ gwsRadius n`,
      `(49 / 50) / (n * gwsRadius n) ≤ ‖F_n(v)‖`. -/
theorem diag_polyFromInvCrits_disk_lower_bound {n : ℕ} (hn : 2 ≤ n) {v : ℂ}
    (hv : ‖v‖ ≤ gwsRadius n) :
    (49 / 50 : ℝ) / ((n : ℝ) * gwsRadius n) ≤
      ‖symMultiaffine (n - 1) (fun m => (-1 : ℂ) ^ m / ((m + 1 : ℕ) : ℂ)) (fun _ => v)‖ := by
  set r0 : ℝ := gwsRadius n
  have hr0_pos : 0 < r0 := gwsRadius_pos hn
  have hr0_lt : r0 < 2 * Real.sin (Real.pi / (n : ℝ)) := gwsRadius_lt_two_sin hn
  have hn_pos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast (show 0 < n by omega)
  set cF : ℕ → ℂ := fun m => (-1 : ℂ) ^ m / ((m + 1 : ℕ) : ℂ)
  set g : ℂ → ℂ := fun z => (diagPoly (n - 1) cF).eval z
  have hg_eq : ∀ z, g z = symMultiaffine (n - 1) cF (fun _ => z) := fun z => eval_diagPoly (n - 1) cF z
  have hg_ne : ∀ z ∈ Metric.closedBall (0 : ℂ) r0, g z ≠ 0 := by
    intro z hz
    rw [Metric.mem_closedBall, dist_zero_right] at hz
    rw [hg_eq]
    by_cases hz0 : z = 0
    · subst hz0
      unfold symMultiaffine
      obtain ⟨k, hk⟩ : ∃ k, n - 1 = k + 1 := ⟨n - 2, by omega⟩
      rw [hk, Finset.sum_range_succ']
      have hrest : ∑ x ∈ Finset.range (k + 1), cF (x + 1) * elemSym (k + 1) (fun _ => (0 : ℂ)) (x + 1) = 0 := by
        apply Finset.sum_eq_zero; intro x _
        rw [elemSym_const, zero_pow (Nat.succ_ne_zero x), mul_zero, mul_zero]
      rw [hrest, zero_add]
      have he0 : elemSym (k + 1) (fun _ => (0 : ℂ)) 0 = 1 := rfl
      rw [he0]; dsimp [cF]; norm_num
    · intro h0
      have hcf := diag_polyFromInvCrits_closed_form (by omega : 1 ≤ n) z
      rw [h0, mul_zero] at hcf
      have hlb := norm_ge_two_sin_pi_div_of_one_sub_pow_eq_one hn hz0 (by linear_combination hcf)
      linarith
  set C0 : ℝ := ((n : ℝ) * r0) / (49 / 50 : ℝ)
  have hC0_pos : 0 < C0 := by positivity
  set f : ℂ → ℂ := fun z => (g z)⁻¹
  have hf_diff : DiffContOnCl ℂ f (Metric.ball (0 : ℂ) r0) := by
    have hcl : closure (Metric.ball (0 : ℂ) r0) = Metric.closedBall (0 : ℂ) r0 :=
      closure_ball 0 (ne_of_gt hr0_pos)
    have hdiff_on : DifferentiableOn ℂ f (Metric.closedBall (0 : ℂ) r0) := fun z hz =>
      ((Polynomial.differentiable _ z).inv (hg_ne z hz)).differentiableWithinAt
    exact ⟨hdiff_on.mono Metric.ball_subset_closedBall, by rw [hcl]; exact hdiff_on.continuousOn⟩
  have hfront : ∀ z ∈ frontier (Metric.ball (0 : ℂ) r0), ‖f z‖ ≤ C0 := by
    intro z hz
    have hsp : z ∈ Metric.sphere (0 : ℂ) r0 := by
      rw [frontier_ball 0 (ne_of_gt hr0_pos)] at hz; exact hz
    rw [Metric.mem_sphere, dist_zero_right] at hsp
    have hcirc := circle_one_sub_pow_lower_bound hn hsp
    have hcf := diag_polyFromInvCrits_closed_form (by omega : 1 ≤ n) z
    have hnorm : (n : ℝ) * r0 * ‖g z‖ = ‖1 - (1 - z) ^ n‖ := by
      rw [← hcf, hg_eq, norm_mul, norm_mul, Complex.norm_natCast, hsp]
    have hgz_lb : (49 / 50 : ℝ) / ((n : ℝ) * r0) ≤ ‖g z‖ := by
      rw [div_le_iff₀ (by positivity)]; linarith
    dsimp [f, C0]; rw [norm_inv]
    rw [inv_le_iff_one_le_mul₀ (norm_pos_iff.mpr (hg_ne z (by rw [Metric.mem_closedBall, dist_zero_right, hsp])))]
    rw [mul_comm, ← div_le_iff₀ hC0_pos]
    calc 1 / (((n : ℝ) * r0) / (49 / 50)) = (49 / 50 : ℝ) / ((n : ℝ) * r0) := by ring
      _ ≤ ‖g z‖ := hgz_lb
  have hvcl : v ∈ closure (Metric.ball (0 : ℂ) r0) := by
    rw [closure_ball 0 (ne_of_gt hr0_pos), Metric.mem_closedBall, dist_zero_right]; exact hv
  have hfv : ‖f v‖ ≤ C0 :=
    Complex.norm_le_of_forall_mem_frontier_norm_le Metric.isBounded_ball hf_diff hfront hvcl
  dsimp [f, C0] at hfv; rw [norm_inv, hg_eq] at hfv
  have hgv_pos : 0 < ‖symMultiaffine (n - 1) cF (fun _ => v)‖ :=
    norm_pos_iff.mpr (by rw [← hg_eq]; exact hg_ne v (by rw [Metric.mem_closedBall, dist_zero_right]; exact hv))
  rw [inv_le_iff_one_le_mul₀ hgv_pos, mul_comm, ← div_le_iff₀ hC0_pos] at hfv
  calc (49 / 50 : ℝ) / ((n : ℝ) * r0) = 1 / (((n : ℝ) * r0) / (49 / 50)) := by ring
    _ ≤ ‖symMultiaffine (n - 1) cF (fun _ => v)‖ := hfv

/-- **THEOREM 2 (All-n Grace-Walsh-Szego Critical-Value Lower Bound — 98% of `r_min / n`)**:
    For EVERY degree `n ≥ 2` and EVERY vector of nonzero inverse critical points `w : Fin (n - 1) → ℂ`
    with `‖w k‖ ≤ 1 / r_min` (`r_min > 0`, i.e., all critical points satisfy `|ζ_k| ≥ r_min`),
    there exists a critical point `ζ = (w j)⁻¹` of `P = polyFromInvCrits n w` such that:
      `(49 / (50 * n)) * r_min ≤ ‖P.eval ζ‖`!! -/
theorem dual_smale_gws_critical_value_bound {n : ℕ} (hn : 2 ≤ n) (w : Fin (n - 1) → ℂ)
    (hw_ne : ∀ k : Fin (n - 1), w k ≠ 0)
    {r_min : ℝ} (hr : 0 < r_min) (hw : ∀ k : Fin (n - 1), ‖w k‖ ≤ 1 / r_min) :
    ∃ j : Fin (n - 1), (49 / (50 * (n : ℝ))) * r_min ≤ ‖(polyFromInvCrits n w).eval (w j)⁻¹‖ := by
  set P : ℂ[X] := polyFromInvCrits n w
  set r : ℝ := gwsRadius n * r_min
  have hr_pos : 0 < r := mul_pos (gwsRadius_pos hn) hr
  have hn_pos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast (show 0 < n by omega)
  set M : ℝ := (49 / (50 * (n : ℝ))) * r_min
  have hM_pos : 0 < M := by positivity
  -- Verify P has degree n ≥ 2 (leading coeff is (-1)^(n-1) / n * ∏ w_k ≠ 0!)
  have hprod_ne : elemSym (n - 1) w (n - 1) ≠ 0 := by
    have helem_top : ∀ (m : ℕ) (v : Fin m → ℂ), elemSym m v m = ∏ i : Fin m, v i := by
      intro m; induction m with
      | zero => intro v; simp [elemSym]
      | succ m ih =>
        intro v
        rw [Fin.prod_univ_castSucc]
        simp only [elemSym, elemSym_eq_zero_of_lt m _ (m + 1) (by omega), zero_add, ih]
        ring
    rw [helem_top]
    exact Finset.prod_ne_zero_iff.mpr (fun k _ => hw_ne k)
  have hP_deg : 2 ≤ P.natDegree := by
    have hcoeff_n : P.coeff n ≠ 0 := by
      dsimp [P, polyFromInvCrits]
      change (Polynomial.lcoeff ℂ n) (∑ m ∈ Finset.range n, _) ≠ 0
      rw [map_sum, Finset.sum_eq_single (n - 1)]
      · simp only [Polynomial.lcoeff_apply]
        rw [Nat.sub_add_cancel (by omega : 1 ≤ n), Polynomial.coeff_C_mul_X_pow]
        simp only [ite_true]
        apply mul_ne_zero _ hprod_ne
        exact div_ne_zero (pow_ne_zero _ (by norm_num)) (Nat.cast_ne_zero.mpr (by omega))
      · intro b hb hne
        simp only [Polynomial.lcoeff_apply]
        rw [Polynomial.coeff_C_mul_X_pow]
        have : b < n := Finset.mem_range.mp hb
        simp [show n ≠ b + 1 by omega]
      · intro hnot; exact absurd (Finset.mem_range.mpr (by omega)) hnot
    exact le_trans hn (Polynomial.le_natDegree_of_ne_zero hcoeff_n)
  -- (1) P has no zeros on 0 < ‖z‖ ≤ r (by Theorem 2A!)
  have hnozero : ∀ z : ℂ, 0 < ‖z‖ → ‖z‖ ≤ r → P.eval z ≠ 0 := by
    intro z hz0 hzr
    have hlt : ‖z‖ < 2 * Real.sin (Real.pi / (n : ℝ)) * r_min := by
      have h1 := gwsRadius_lt_two_sin hn
      nlinarith
    exact dual_smale_zero_free_disk hn w hr hw (norm_pos_iff.mp hz0) hlt
  -- (2) On ‖z‖ = r, ‖P.eval z‖ ≥ M (by GWS + diag_polyFromInvCrits_disk_lower_bound!)
  have hcircle : ∀ z : ℂ, ‖z‖ = r → M ≤ ‖P.eval z‖ := by
    intro z hzr
    rw [show P.eval z = z * symMultiaffine (n - 1) (fun m => (-1 : ℂ) ^ m / ((m + 1 : ℕ) : ℂ)) (fun k => w k * z)
        from polyFromInvCrits_eval_eq_mul_symMultiaffine (by omega) w z]
    have hbound : ∀ k : Fin (n - 1), ‖w k * z‖ ≤ gwsRadius n := by
      intro k
      rw [norm_mul, hzr]
      calc ‖w k‖ * (gwsRadius n * r_min)
          ≤ (1 / r_min) * (gwsRadius n * r_min) := mul_le_mul_of_nonneg_right (hw k) (le_of_lt hr_pos)
        _ = gwsRadius n := by field_simp [ne_of_gt hr]
    rcases grace_walsh_szego_disk (m := n - 1) (by omega) (gwsRadius_pos hn)
        (fun m => (-1 : ℂ) ^ m / ((m + 1 : ℕ) : ℂ)) (fun k => w k * z) hbound with ⟨v, hv_le, heq⟩
    rw [heq, norm_mul, hzr]
    have hlb := diag_polyFromInvCrits_disk_lower_bound hn hv_le
    calc M = (gwsRadius n * r_min) * ((49 / 50 : ℝ) / ((n : ℝ) * gwsRadius n)) := by
            dsimp [M]; field_simp [ne_of_gt hn_pos, ne_of_gt (gwsRadius_pos hn)]
      _ ≤ (gwsRadius n * r_min) * ‖symMultiaffine (n - 1) _ (fun _ => v)‖ :=
            mul_le_mul_of_nonneg_left hlb (le_of_lt hr_pos)
  -- (3) Apply Elementary Polynomial Mountain Pass Theorem!
  have hP0 : P.eval 0 = 0 := polyFromInvCrits_eval_zero n w
  have hP'0 : (derivative P).eval 0 ≠ 0 := by
    rw [derivative_polyFromInvCrits_eval_zero (by omega) w]; exact one_ne_zero
  obtain ⟨ζ, hζ_crit, hζ_ge⟩ := polynomial_mountain_pass P hP_deg hP0 hP'0 hr_pos hM_pos hnozero hcircle
  -- Identify ζ as (w j)⁻¹ for some j : Fin (n - 1)!
  have hprod0 : ∏ k : Fin (n - 1), (1 - w k * ζ) = 0 := by
    rw [prod_one_sub_eq_sum_elemSym]
    have h1 := hζ_crit
    rw [derivative_polyFromInvCrits] at h1
    have heval : (∑ m ∈ Finset.range n, C ((-1 : ℂ) ^ m * elemSym (n - 1) w m) * X ^ m).eval ζ =
        ∑ m ∈ Finset.range ((n - 1) + 1), (-1 : ℂ) ^ m * elemSym (n - 1) w m * ζ ^ m := by
      have hnn : (n - 1) + 1 = n := Nat.sub_add_cancel (by omega)
      rw [hnn]
      change (Polynomial.evalRingHom ζ) (∑ m ∈ Finset.range n, _) = _
      rw [map_sum]
      apply Finset.sum_congr rfl; intro m _; simp
    rw [← heval]; exact h1
  rcases Finset.prod_eq_zero_iff.mp hprod0 with ⟨j, _, hj⟩
  have hζ_eq : ζ = (w j)⁻¹ := by
    have h1 : w j * ζ = 1 := by linear_combination -hj
    exact eq_inv_of_mul_eq_one_right h1
  exact ⟨j, by rw [← hζ_eq]; exact hζ_ge⟩

/-- **COROLLARY 2.1 (Bounded-Spread Dual Smale Bound for ALL `n ≥ 2`)**:
    If all critical points satisfy `r_min ≤ |ζ_k| ≤ r_max` (i.e. `1 / r_max ≤ ‖w k‖ ≤ 1 / r_min`),
    with spread `κ = r_max / r_min ≥ 1`, then:
      `∃ j : Fin (n - 1), 49 / (50 * κ * n) ≤ ‖dualSmaleQuotient n w j‖`!
    In particular, for equal-modulus critical points (`r_min = r_max`, `κ = 1`):
      `∃ j : Fin (n - 1), 49 / (50 * n) ≤ ‖dualSmaleQuotient n w j‖` (98% of the full conjecture for ALL `n ≥ 2`)! -/
theorem dual_smale_bounded_spread {n : ℕ} (hn : 2 ≤ n) (w : Fin (n - 1) → ℂ)
    {r_min r_max : ℝ} (hr_min : 0 < r_min) (hr_max : 0 < r_max)
    (hw_ub : ∀ k : Fin (n - 1), ‖w k‖ ≤ 1 / r_min)
    (hw_lb : ∀ k : Fin (n - 1), 1 / r_max ≤ ‖w k‖) :
    ∃ j : Fin (n - 1),
      49 / (50 * (r_max / r_min) * (n : ℝ)) ≤ ‖dualSmaleQuotient n w j‖ := by
  have hw_ne : ∀ k : Fin (n - 1), w k ≠ 0 := fun k =>
    norm_pos_iff.mp (lt_of_lt_of_le (by positivity) (hw_lb k))
  rcases dual_smale_gws_critical_value_bound hn w hw_ne hr_min hw_ub with ⟨j, hj⟩
  refine ⟨j, ?_⟩
  rw [← eval_div_eq_dualSmaleQuotient w j (hw_ne j), norm_div, norm_inv]
  have hwj_pos : 0 < ‖w j‖ := norm_pos_iff.mpr (hw_ne j)
  have hζ_le : ‖w j‖⁻¹ ≤ r_max := by
    rw [inv_le_comm₀ hwj_pos hr_max]
    simpa [one_div] using hw_lb j
  have hn_pos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast (show 0 < n by omega)
  calc 49 / (50 * (r_max / r_min) * (n : ℝ))
      = ((49 / (50 * (n : ℝ))) * r_min) / r_max := by field_simp [ne_of_gt hr_min, ne_of_gt hr_max, ne_of_gt hn_pos]
    _ ≤ ‖(polyFromInvCrits n w).eval (w j)⁻¹‖ / ‖w j‖⁻¹ :=
        div_le_div₀ (by positivity) hj (inv_pos.mpr hwj_pos) hζ_le

/-- **COROLLARY 2.2 (Equal-Modulus Dual Smale to 98% for ALL `n ≥ 2`)**:
    If all critical points have equal modulus (`‖w k‖ = 1 / R` for all `k`, `R > 0`), then
    `∃ j : Fin (n - 1), 49 / (50 * n) ≤ ‖dualSmaleQuotient n w j‖`. -/
theorem dual_smale_equal_modulus {n : ℕ} (hn : 2 ≤ n) (w : Fin (n - 1) → ℂ)
    {R : ℝ} (hR : 0 < R) (heq : ∀ k : Fin (n - 1), ‖w k‖ = 1 / R) :
    ∃ j : Fin (n - 1), 49 / (50 * (n : ℝ)) ≤ ‖dualSmaleQuotient n w j‖ := by
  rcases dual_smale_bounded_spread hn w hR hR (fun k => le_of_eq (heq k)) (fun k => le_of_eq (heq k).symm) with ⟨j, hj⟩
  rw [div_self (ne_of_gt hR), mul_one] at hj
  exact ⟨j, hj⟩

end DualSmale
