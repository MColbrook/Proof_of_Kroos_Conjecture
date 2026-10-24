module

public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Ring

/-!
# Exact bounds for the constants in the homogeneous Gaussian construction

The statements below concern only the scalar constants in the Taylor and
supporting-hyperplane estimates of `bandlimited_proof.tex`. They do not assert
the analytic approximation lemmas or the main approximation theorem.

The proofs reuse Mathlib's `Real.add_one_le_exp`,
`Real.one_sub_inv_le_log_of_pos`, `Real.log_mul`, and `Real.log_pow`.
Mathlib is licensed under Apache 2.0. All numerical arithmetic here produces
proof terms checked by Lean's kernel; no native evaluation is used.
-/

@[expose] public section

namespace Bandlimited.Numerics

/-- The bandwidth chosen in the manuscript, with `e = Real.exp 1`. -/
noncomputable def bandwidth (D : ℝ) : ℝ := 1 / (64 * Real.exp 1 * D)

theorem exp_one_ge_one : (1 : ℝ) ≤ Real.exp 1 := by
  linarith [Real.add_one_le_exp (1 : ℝ)]

theorem bandwidth_pos {D : ℝ} (hD : 0 < D) : 0 < bandwidth D := by
  unfold bandwidth
  positivity

/-- The identity `σ₀ T = 1 / (32e)` for `T = 2D`. -/
theorem bandwidth_times_chart_radius {D : ℝ} (hD : 0 < D) :
    bandwidth D * (2 * D) = 1 / (32 * Real.exp 1) := by
  unfold bandwidth
  field_simp
  ring

/-- The geometric factor in the factorial estimate is exactly `1/16`. -/
theorem taylor_geometric_factor {D : ℝ} (hD : 0 < D) :
    2 * Real.exp 1 * bandwidth D * (2 * D) = (1 : ℝ) / 16 := by
  unfold bandwidth
  field_simp
  ring

/-- The constant in the hyperplane-region exponent is independent of `D`. -/
theorem bandwidth_times_D {D : ℝ} (hD : 0 < D) :
    bandwidth D * D = 1 / (64 * Real.exp 1) := by
  unfold bandwidth
  field_simp

/-- A deliberately coarse exact lower bound suffices for both logarithms. -/
theorem log_two_lower : (7 : ℝ) / 12 ≤ Real.log 2 := by
  have h₁ := Real.one_sub_inv_le_log_of_pos (by norm_num : (0 : ℝ) < 4 / 3)
  have h₂ := Real.one_sub_inv_le_log_of_pos (by norm_num : (0 : ℝ) < 3 / 2)
  have hprod : Real.log (2 : ℝ) = Real.log (4 / 3) + Real.log (3 / 2) := by
    rw [← Real.log_mul (by norm_num : (4 / 3 : ℝ) ≠ 0)
      (by norm_num : (3 / 2 : ℝ) ≠ 0)]
    norm_num
  norm_num at h₁ h₂
  linarith

theorem inv_thirty_two_exp_one_le : 1 / (32 * Real.exp 1) ≤ (1 : ℝ) / 32 := by
  apply (div_le_iff₀ (by positivity : (0 : ℝ) < 32 * Real.exp 1)).2
  nlinarith [exp_one_ge_one]

theorem inv_sixty_four_exp_one_le : 1 / (64 * Real.exp 1) ≤ (1 : ℝ) / 64 := by
  apply (div_le_iff₀ (by positivity : (0 : ℝ) < 64 * Real.exp 1)).2
  nlinarith [exp_one_ge_one]

/-- The strict margin needed to dominate the Taylor remainder by `exp (-N)`. -/
theorem taylor_log_margin :
    1 < Real.log 4 - 1 / (32 * Real.exp 1) := by
  have hlog : Real.log (4 : ℝ) = 2 * Real.log 2 := by
    have h := Real.log_pow (2 : ℝ) 2
    norm_num at h
    exact h
  nlinarith [log_two_lower, inv_thirty_two_exp_one_le]

/-- The strict margin needed for the `exp (-N/4)` hyperplane-region bound. -/
theorem hyperplane_log_margin :
    (1 : ℝ) / 4 < Real.log 2 / 2 - 1 / (64 * Real.exp 1) := by
  nlinarith [log_two_lower, inv_sixty_four_exp_one_le]

end Bandlimited.Numerics

#print axioms Bandlimited.Numerics.exp_one_ge_one
#print axioms Bandlimited.Numerics.bandwidth_pos
#print axioms Bandlimited.Numerics.bandwidth_times_chart_radius
#print axioms Bandlimited.Numerics.taylor_geometric_factor
#print axioms Bandlimited.Numerics.bandwidth_times_D
#print axioms Bandlimited.Numerics.log_two_lower
#print axioms Bandlimited.Numerics.inv_thirty_two_exp_one_le
#print axioms Bandlimited.Numerics.inv_sixty_four_exp_one_le
#print axioms Bandlimited.Numerics.taylor_log_margin
#print axioms Bandlimited.Numerics.hyperplane_log_margin
