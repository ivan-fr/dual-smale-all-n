/-
  DualSmale/IsolatedAndLocal.lean

  THEOREM 3 (All-n Isolated Minimal Critical Point Theorem):
    For EVERY degree n >= 2, if a critical point zeta_j satisfies |zeta_k| >= n * |zeta_j|
    for all k != j (equivalently, all normalized inverse ratios w_k = zeta_j / zeta_k satisfy
    ‖w_k‖ <= 1 / n), then:
      ‖P(zeta_j) / zeta_j‖ > 5 / 18   (constant lower bound > 0.2777 independent of n!)
    and in particular:
      ‖P(zeta_j) / zeta_j‖ >= 1 / n   (strictly > 1 / n for all n >= 3!).

  THEOREM 4 (Universal Strict Local Minimum Quadratic Form for ALL n >= 3):
    Around the unique extremal polynomial P_n(z) = (1 - (1 - z)^n) / n (all w_k = 1),
    for any perturbation w_k = 1 + x_k + i y_k inside the closed unit disk
    (so 2 x_k + x_k^2 + y_k^2 <= 0), the second variation of ‖n P(1)‖^2 is strictly
    positive definite with explicit eigenvalue n / ((n - 1)^2 (n - 2)) > 0.
-/

import DualSmale.PolynomialReduction

open scoped BigOperators
open Complex

namespace DualSmale

/-- Elementary factorial bound: `6 * 4^(m - 1) ≤ (m + 2)!` for all `m ≥ 1`. -/
lemma six_mul_four_pow_le_factorial : ∀ m : ℕ, 1 ≤ m → 6 * 4 ^ (m - 1) ≤ Nat.factorial (m + 2) := by
  intro m hm
  obtain ⟨k, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by omega⟩
  clear hm
  simp only [Nat.add_sub_cancel]
  induction k with
  | zero => norm_num [Nat.factorial]
  | succ k ih =>
    rw [pow_succ, show k + 1 + 1 + 2 = (k + 1 + 2) + 1 by omega, Nat.factorial_succ]
    have h4 : 4 ≤ k + 1 + 2 + 1 := by omega
    calc 6 * (4 ^ k * 4) = 4 * (6 * 4 ^ k) := by ring
      _ ≤ (k + 1 + 2 + 1) * Nat.factorial (k + 1 + 2) := Nat.mul_le_mul h4 ih

/-- Elementary binomial upper bound: `C(n - 2, m) * m! ≤ n^m`. -/
lemma choose_mul_factorial_le_pow (n m : ℕ) :
    Nat.choose (n - 2) m * Nat.factorial m ≤ n ^ m := by
  have h1 : Nat.choose (n - 2) m * Nat.factorial m = (n - 2).descFactorial m := by
    rw [mul_comm, ← Nat.descFactorial_eq_factorial_mul_choose]
  rw [h1]
  exact le_trans (Nat.descFactorial_le_pow (n - 2) m) (Nat.pow_le_pow_left (Nat.sub_le n 2) m)

/-- **Diagonal Bound for Theorem 3 (ALL `n ≥ 2`, `‖w‖ ≤ 1 / n`)**:
    `5 / 18 < ‖GnPoly n w‖` (and `1 / n ≤ ‖GnPoly n w‖`, strictly `1 / n < ‖GnPoly n w‖` for `n ≥ 3`). -/
theorem GnPoly_isolated_lower_bound {n : ℕ} (hn : 2 ≤ n) {w : ℂ} (hw : ‖w‖ ≤ 1 / (n : ℝ)) :
    5 / 18 < ‖GnPoly n w‖ ∧ 1 / (n : ℝ) ≤ ‖GnPoly n w‖ ∧ (3 ≤ n → 1 / (n : ℝ) < ‖GnPoly n w‖) := by
  have hn_pos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast (show 0 < n by omega)
  -- Case n = 2: G_2(w) = 1/2
  by_cases hn2 : n = 2
  · subst hn2
    have hg : GnPoly 2 w = 1 / 2 := by unfold GnPoly P1Form symMultiaffine; simp [elemSym]
    rw [hg]; norm_num
  -- Case n = 3: G_3(w) = 1/2 - w / 6, ‖w‖ ≤ 1/3 => ‖G_3(w)‖ ≥ 1/2 - 1/18 = 4/9
  by_cases hn3 : n = 3
  · subst hn3
    have hg : GnPoly 3 w = 1 / 2 - w / 6 := by
      unfold GnPoly P1Form symMultiaffine
      simp only [show 3 - 2 = 1 by rfl, Finset.sum_range_succ, Finset.range_zero, Finset.sum_empty,
        zero_add, elemSym_const]
      norm_num [Nat.choose]; ring
    rw [hg]
    have hrev : (1 / 2 : ℝ) - ‖w‖ / 6 ≤ ‖(1 / 2 : ℂ) - w / 6‖ := by
      have h1 := norm_sub_le ((1 / 2 : ℂ) - w / 6) (-(w / 6))
      have h2 : (1 / 2 : ℂ) - w / 6 - -(w / 6) = 1 / 2 := by ring
      rw [h2, norm_neg, norm_div] at h1
      norm_num at h1
      linarith
    have hw3 : ‖w‖ ≤ 1 / 3 := by simpa using hw
    refine ⟨by linarith, by linarith, fun _ => by linarith⟩
  -- General case n ≥ 4: power series bound with geometric majorant 1 / (6 * 4^(m - 1))!
  have hn4 : 4 ≤ n := by omega
  obtain ⟨k, hk⟩ : ∃ k, n - 2 = k + 1 := ⟨n - 3, by omega⟩
  -- Split GnPoly n w = 1/2 + tail
  have hsplit : GnPoly n w = (1 / 2 : ℂ) +
      ∑ m ∈ Finset.range (k + 1),
        ((-1 : ℂ) ^ (m + 1) / (((m + 2) * (m + 3) : ℕ) : ℂ)) *
          ((Nat.choose (k + 1) (m + 1) : ℂ) * w ^ (m + 1)) := by
    unfold GnPoly P1Form symMultiaffine
    rw [hk, Finset.sum_range_succ']
    have he0 : elemSym (k + 1) (fun _ => w) 0 = 1 := rfl
    rw [he0]
    simp only [pow_zero, zero_add, mul_one, one_mul, elemSym_const]
    have h12 : (((1 * 2 : ℕ) : ℂ)) = 2 := by norm_num
    rw [h12, add_comm]
  set tail : ℂ := ∑ m ∈ Finset.range (k + 1),
      ((-1 : ℂ) ^ (m + 1) / (((m + 2) * (m + 3) : ℕ) : ℂ)) *
        ((Nat.choose (k + 1) (m + 1) : ℂ) * w ^ (m + 1))
  -- Each term m ≥ 0 has norm ≤ (1 / 6) * (1 / 4)^m!
  have hterm : ∀ m ∈ Finset.range (k + 1),
      ‖((-1 : ℂ) ^ (m + 1) / (((m + 2) * (m + 3) : ℕ) : ℂ)) *
        ((Nat.choose (k + 1) (m + 1) : ℂ) * w ^ (m + 1))‖ ≤
        (1 / 6 : ℝ) * (1 / 4 : ℝ) ^ m := by
    intro m _
    rw [norm_mul, norm_div, norm_pow, norm_neg, norm_one, one_pow, Complex.norm_natCast,
      norm_mul, Complex.norm_natCast, norm_pow]
    have hw_pow : ‖w‖ ^ (m + 1) ≤ (1 / (n : ℝ)) ^ (m + 1) :=
      pow_le_pow_left₀ (norm_nonneg w) hw (m + 1)
    have hden_pos : (0 : ℝ) < (((m + 2) * (m + 3) : ℕ) : ℝ) := by positivity
    have hfac_pos : (0 : ℝ) < (Nat.factorial (m + 1) : ℝ) := by positivity
    have hfac_id : ((Nat.factorial (m + 1) : ℝ) * (((m + 2) * (m + 3) : ℕ) : ℝ)) =
        (Nat.factorial (m + 3) : ℝ) := by
      have hnat : Nat.factorial (m + 1) * ((m + 2) * (m + 3)) = Nat.factorial (m + 3) := by
        simp only [Nat.factorial_succ]; ring
      exact_mod_cast hnat
    have hch : (Nat.choose (k + 1) (m + 1) : ℝ) * (Nat.factorial (m + 1) : ℝ) ≤ (n : ℝ) ^ (m + 1) := by
      rw [← hk]
      exact_mod_cast choose_mul_factorial_le_pow n (m + 1)
    have h64 : (6 : ℝ) * (4 : ℝ) ^ m ≤ (Nat.factorial (m + 3) : ℝ) := by
      have h := six_mul_four_pow_le_factorial (m + 1) (by omega)
      simp only [Nat.add_sub_cancel, show m + 1 + 2 = m + 3 by omega] at h
      exact_mod_cast h
    have hn_pow_pos : (0 : ℝ) < (n : ℝ) ^ (m + 1) := pow_pos hn_pos (m + 1)
    calc 1 / (((m + 2) * (m + 3) : ℕ) : ℝ) * ((Nat.choose (k + 1) (m + 1) : ℝ) * ‖w‖ ^ (m + 1))
        ≤ 1 / (((m + 2) * (m + 3) : ℕ) : ℝ) * ((Nat.choose (k + 1) (m + 1) : ℝ) * (1 / (n : ℝ)) ^ (m + 1)) := by
          gcongr
      _ = ((Nat.choose (k + 1) (m + 1) : ℝ) * (Nat.factorial (m + 1) : ℝ)) /
            ((Nat.factorial (m + 3) : ℝ) * (n : ℝ) ^ (m + 1)) := by
          rw [← hfac_id, one_div_pow]
          field_simp [ne_of_gt hden_pos, ne_of_gt hfac_pos, ne_of_gt hn_pow_pos]
      _ ≤ (n : ℝ) ^ (m + 1) / ((Nat.factorial (m + 3) : ℝ) * (n : ℝ) ^ (m + 1)) := by
          gcongr
      _ = 1 / (Nat.factorial (m + 3) : ℝ) := by
          field_simp [ne_of_gt hn_pow_pos]
      _ ≤ 1 / ((6 : ℝ) * (4 : ℝ) ^ m) := by
          exact one_div_le_one_div_of_le (by positivity) h64
      _ = (1 / 6 : ℝ) * (1 / 4 : ℝ) ^ m := by
          rw [one_div_pow]; ring
  -- Geometric sum bound: ∑_{m=0}^k (1/6)*(1/4)^m < (1/6)/(3/4) = 2/9!
  have htail_lt : ‖tail‖ < 2 / 9 := by
    calc ‖tail‖
        ≤ ∑ m ∈ Finset.range (k + 1),
            ‖((-1 : ℂ) ^ (m + 1) / (((m + 2) * (m + 3) : ℕ) : ℂ)) *
              ((Nat.choose (k + 1) (m + 1) : ℂ) * w ^ (m + 1))‖ := norm_sum_le _ _
      _ ≤ ∑ m ∈ Finset.range (k + 1), (1 / 6 : ℝ) * (1 / 4 : ℝ) ^ m := Finset.sum_le_sum hterm
      _ = (1 / 6 : ℝ) * ∑ m ∈ Finset.range (k + 1), (1 / 4 : ℝ) ^ m := (Finset.mul_sum _ _ _).symm
      _ = (1 / 6 : ℝ) * (((1 / 4 : ℝ) ^ (k + 1) - 1) / ((1 / 4 : ℝ) - 1)) := by
          rw [geom_sum_eq (by norm_num)]
      _ = (2 / 9 : ℝ) * (1 - (1 / 4 : ℝ) ^ (k + 1)) := by ring
      _ < 2 / 9 := by
          have hpos : (0 : ℝ) < (1 / 4 : ℝ) ^ (k + 1) := by positivity
          linarith
  have hrev : (1 / 2 : ℝ) - ‖tail‖ ≤ ‖GnPoly n w‖ := by
    rw [hsplit]
    have h1 := norm_sub_le ((1 / 2 : ℂ) + tail) tail
    rw [add_sub_cancel_right] at h1
    norm_num at h1
    linarith
  have hgt : (5 / 18 : ℝ) < ‖GnPoly n w‖ := by linarith
  have h4 : 1 / (n : ℝ) ≤ 1 / 4 := by
    have : (4 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn4
    exact one_div_le_one_div_of_le (by norm_num) this
  exact ⟨hgt, by linarith, fun _ => by linarith⟩

/-- **THEOREM 3 (All-n Isolated Minimal Critical Point Theorem)**:
    For EVERY `n ≥ 2` and EVERY vector `w_rest : Fin (n - 2) → ℂ` with `‖w_rest i‖ ≤ 1 / n`
    (equivalently `|ζ_k| ≥ n * |ζ_j|` for all `k ≠ j`), we have:
      `5 / 18 < ‖P1Form n w_rest‖`,
    and in particular `1 / n ≤ ‖P1Form n w_rest‖` (strictly `1 / n < ‖P1Form n w_rest‖` for `n ≥ 3`). -/
theorem dual_smale_isolated_critical_point {n : ℕ} (hn : 2 ≤ n) (w_rest : Fin (n - 2) → ℂ)
    (hiso : ∀ i : Fin (n - 2), ‖w_rest i‖ ≤ 1 / (n : ℝ)) :
    5 / 18 < ‖P1Form n w_rest‖ ∧ 1 / (n : ℝ) ≤ ‖P1Form n w_rest‖ ∧
      (3 ≤ n → 1 / (n : ℝ) < ‖P1Form n w_rest‖) := by
  by_cases hn2 : n = 2
  · subst hn2
    have hp : P1Form 2 w_rest = 1 / 2 := by unfold P1Form symMultiaffine; simp [elemSym]
    rw [hp]; norm_num
  · have hm : 1 ≤ n - 2 := by omega
    have hr : (0 : ℝ) < 1 / (n : ℝ) := by positivity
    rcases grace_walsh_szego_disk hm hr GnCoeff w_rest hiso with ⟨ζ, hζ, heq⟩
    have hPeq : P1Form n w_rest = GnPoly n ζ := heq
    rw [hPeq]
    exact GnPoly_isolated_lower_bound hn hζ

/-- **Polynomial Form of Theorem 3**. -/
theorem dual_smale_isolated_critical_point_poly {n : ℕ} (hn : 2 ≤ n)
    (w : Fin (n - 1) → ℂ) (hlast : w ⟨n - 2, by omega⟩ = 1)
    (hiso : ∀ i : Fin (n - 2), ‖w ⟨i.val, by omega⟩‖ ≤ 1 / (n : ℝ)) :
    5 / 18 < ‖dualSmaleQuotient n w ⟨n - 2, by omega⟩‖ ∧
      1 / (n : ℝ) ≤ ‖dualSmaleQuotient n w ⟨n - 2, by omega⟩‖ ∧
      (3 ≤ n → 1 / (n : ℝ) < ‖dualSmaleQuotient n w ⟨n - 2, by omega⟩‖) := by
  rw [dualSmaleQuotient_at_one n hn w hlast]
  exact dual_smale_isolated_critical_point hn (fun i => w ⟨i.val, by omega⟩) hiso

/-- **THEOREM 4 (Universal Second-Order Strict Positivity Theorem — ALL degrees `n ≥ 3`)**:
    Around the extremal polynomial `P_n(z) = (1 - (1 - z)^n) / n` (all `w_k = 1`),
    for ANY perturbation `w_k = 1 + x_k + i y_k` in the closed unit disk (`2 x_k + x_k^2 + y_k^2 ≤ 0`),
    the second variation of `‖n * P(1)‖^2` is strictly positive definite with explicit constant
    `n / ((n - 1)^2 * (n - 2))`. -/
theorem universal_local_quadratic_lower_bound {n : ℕ} (hn : 3 ≤ n)
    (x y : Fin (n - 2) → ℝ)
    (hdisk : ∀ k, 2 * x k + (x k) ^ 2 + (y k) ^ 2 ≤ 0) :
    (2 / ((n - 1 : ℕ) : ℝ)) * (∑ k, (-x k)) -
      (2 / (((n - 1 : ℕ) : ℝ) * ((n - 2 : ℕ) : ℝ))) * ((∑ k, y k) ^ 2 - ∑ k, (y k) ^ 2) +
      (1 / ((n - 1 : ℕ) : ℝ) ^ 2) * (∑ k, y k) ^ 2
    ≥ ((n : ℝ) / (((n - 1 : ℕ) : ℝ) ^ 2 * ((n - 2 : ℕ) : ℝ))) * (∑ k, (y k) ^ 2) +
      (1 / ((n - 1 : ℕ) : ℝ)) * (∑ k, (x k) ^ 2) := by
  have h1_pos : (0 : ℝ) < ((n - 1 : ℕ) : ℝ) := by exact_mod_cast (show 0 < n - 1 by omega)
  have h2_pos : (0 : ℝ) < ((n - 2 : ℕ) : ℝ) := by exact_mod_cast (show 0 < n - 2 by omega)
  have hx_sum : ∑ k, ((x k) ^ 2 + (y k) ^ 2) / 2 ≤ ∑ k, (-x k) := by
    apply Finset.sum_le_sum; intro k _; linarith [hdisk k]
  have hcs : (∑ k : Fin (n - 2), y k) ^ 2 ≤ ((n - 2 : ℕ) : ℝ) * ∑ k : Fin (n - 2), (y k) ^ 2 := by
    have hnn : (0 : ℝ) ≤ ∑ i : Fin (n - 2), ∑ j : Fin (n - 2), (y i - y j) ^ 2 :=
      Finset.sum_nonneg (fun _ _ => Finset.sum_nonneg (fun _ _ => sq_nonneg _))
    have hexp : ∑ i : Fin (n - 2), ∑ j : Fin (n - 2), (y i - y j) ^ 2 =
        2 * (((n - 2 : ℕ) : ℝ) * ∑ k : Fin (n - 2), (y k) ^ 2 - (∑ k : Fin (n - 2), y k) ^ 2) := by
      have h2 : ∑ i : Fin (n - 2), ∑ j : Fin (n - 2), 2 * y i * y j = 2 * (∑ i : Fin (n - 2), y i) ^ 2 := by
        simp_rw [mul_assoc, ← Finset.mul_sum, ← Finset.sum_mul]; ring
      simp_rw [sub_sq, Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.sum_const,
        Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, h2, ← Finset.mul_sum]
      ring
    linarith
  set Sx2 : ℝ := ∑ k, (x k) ^ 2
  set Sy2 : ℝ := ∑ k, (y k) ^ 2
  set Sy : ℝ := ∑ k, y k
  set m1 : ℝ := ((n - 1 : ℕ) : ℝ)
  set m2 : ℝ := ((n - 2 : ℕ) : ℝ)
  have hn_cast : (n : ℝ) = m1 + 1 := by dsimp [m1]; exact_mod_cast (show n = (n - 1) + 1 by omega)
  have hm1_m2 : m1 = m2 + 1 := by dsimp [m1, m2]; exact_mod_cast (show n - 1 = (n - 2) + 1 by omega)
  have hsum_split : ∑ k, ((x k) ^ 2 + (y k) ^ 2) / 2 = (Sx2 + Sy2) / 2 := by
    rw [← Finset.sum_div, Finset.sum_add_distrib]
  rw [hsum_split] at hx_sum
  have hstep1 : (2 / m1) * ((Sx2 + Sy2) / 2) ≤ (2 / m1) * (∑ k, (-x k)) :=
    mul_le_mul_of_nonneg_left hx_sum (div_nonneg (by norm_num) (le_of_lt h1_pos))
  have hden : 0 < m1 ^ 2 * m2 := mul_pos (sq_pos_of_pos h1_pos) h2_pos
  have hkey : (2 / m1) * ((Sx2 + Sy2) / 2) - (2 / (m1 * m2)) * (Sy ^ 2 - Sy2) + (1 / m1 ^ 2) * Sy ^ 2
      - ((n : ℝ) / (m1 ^ 2 * m2)) * Sy2 - (1 / m1) * Sx2 =
      ((m1 + 1) / (m1 ^ 2 * m2)) * (m2 * Sy2 - Sy ^ 2) := by
    rw [hn_cast, hm1_m2]
    field_simp [ne_of_gt h1_pos, ne_of_gt h2_pos]
    ring
  have hnonneg : 0 ≤ ((m1 + 1) / (m1 ^ 2 * m2)) * (m2 * Sy2 - Sy ^ 2) :=
    mul_nonneg (div_nonneg (by linarith) (le_of_lt hden)) (by linarith [hcs])
  linarith

end DualSmale
