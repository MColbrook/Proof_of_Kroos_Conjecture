module

public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Ring

/-!
# The exponential rescaling inequality

This module concerns the scalar estimate used near the centre in Section 4
of `bandlimited_proof.tex`. It proves no geometric or approximation theorem.

It reuses Mathlib's `Real.le_log_one_add_of_nonneg`,
`Real.log_le_sub_one_of_pos`, and logarithm/exponential identities
(Apache 2.0; the Log/Basic file credits Chris Hughes, Abhimanyu Pallavi
Sudhir, Jean Lo, and Calle Sönne).

The main theorem has a natural degree `N > 0` and a real parameter `q ≥ 0`.
The paper assumes the stronger condition `N ≥ 2`. Its negative integer power
is expressed as a natural power of the reciprocal of the positive base.
-/

@[expose] public section

namespace Bandlimited.Rescaling

theorem log_one_add_lower_quadratic {t : ℝ} (ht : 0 ≤ t) :
    t - t ^ 2 / 2 ≤ Real.log (1 + t) := by
  apply le_trans ?_ (Real.le_log_one_add_of_nonneg ht)
  apply (le_div_iff₀ (by linarith : (0 : ℝ) < t + 2)).2
  have hc : (0 : ℝ) ≤ t ^ 3 := pow_nonneg ht 3
  nlinarith

theorem log_one_add_upper {t : ℝ} (ht : 0 ≤ t) :
    Real.log (1 + t) ≤ t := by
  have hb : (0 : ℝ) < 1 + t := by linarith
  linarith [Real.log_le_sub_one_of_pos hb]

/-- Bounds for the logarithm of the rescaling ratio, allowing real `n > 0`. -/
theorem exponent_bounds {q n : ℝ} (hq : 0 ≤ q) (hn : 0 < n) :
    0 ≤ q - n * Real.log (1 + q / n) ∧
      q - n * Real.log (1 + q / n) ≤ q ^ 2 / (2 * n) := by
  have ht : 0 ≤ q / n := div_nonneg hq hn.le
  have hu := mul_le_mul_of_nonneg_left (log_one_add_upper ht) hn.le
  have hl := mul_le_mul_of_nonneg_left (log_one_add_lower_quadratic ht) hn.le
  have hc : n * (q / n) = q := by field_simp
  have hs : n * ((q / n) ^ 2 / 2) = q ^ 2 / (2 * n) := by
    field_simp
  rw [hc] at hu
  rw [mul_sub, hc, hs] at hl
  constructor <;> linarith

/-- The full scalar ratio estimate from the manuscript, for natural degree. -/
theorem rescaling_ratio_bounds {q : ℝ} {N : ℕ} (hq : 0 ≤ q) (hN : 0 < N) :
    1 ≤ ((1 + q / (N : ℝ))⁻¹) ^ N * Real.exp q ∧
      ((1 + q / (N : ℝ))⁻¹) ^ N * Real.exp q ≤
        Real.exp (q ^ 2 / (2 * (N : ℝ))) := by
  have hn : (0 : ℝ) < N := by exact_mod_cast hN
  have hb : (0 : ℝ) < 1 + q / (N : ℝ) := by positivity
  have hr : (0 : ℝ) < ((1 + q / (N : ℝ))⁻¹) ^ N * Real.exp q :=
    mul_pos (pow_pos (inv_pos.mpr hb) N) (Real.exp_pos q)
  have hlog : Real.log (((1 + q / (N : ℝ))⁻¹) ^ N * Real.exp q) =
      q - (N : ℝ) * Real.log (1 + q / (N : ℝ)) := by
    rw [Real.log_mul (pow_ne_zero N (inv_ne_zero hb.ne')) (Real.exp_ne_zero q),
      Real.log_pow, Real.log_inv, Real.log_exp]
    ring
  have heq : ((1 + q / (N : ℝ))⁻¹) ^ N * Real.exp q =
      Real.exp (q - (N : ℝ) * Real.log (1 + q / (N : ℝ))) := by
    rw [← hlog, Real.exp_log hr]
  have hbounds := exponent_bounds hq hn
  rw [heq]
  constructor
  · simpa using Real.exp_le_exp.mpr hbounds.1
  · exact Real.exp_le_exp.mpr hbounds.2

end Bandlimited.Rescaling

#print axioms Bandlimited.Rescaling.log_one_add_lower_quadratic
#print axioms Bandlimited.Rescaling.log_one_add_upper
#print axioms Bandlimited.Rescaling.exponent_bounds
#print axioms Bandlimited.Rescaling.rescaling_ratio_bounds
