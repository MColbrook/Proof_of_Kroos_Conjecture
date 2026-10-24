module

public import Bandlimited.SupportingChart

/-! Exact projective chord identities and comparison with the orthogonal
residual. Coarse constants suffice for the principal uniform kernel theorem. -/

@[expose] public section
noncomputable section
open scoped RealInnerProductSpace
namespace Bandlimited

@[simp] theorem sphere_norm {d : ℕ} (u : Sphere d) : ‖(u : E d)‖ = 1 := by
  simpa only [Metric.mem_sphere, dist_zero_right] using u.property

theorem rho_nonnegative {d : ℕ} (u v : Sphere d) : 0 ≤ rho u v :=
  le_min (norm_nonneg _) (norm_nonneg _)

theorem rho_le_two {d : ℕ} (u v : Sphere d) : rho u v ≤ 2 := by
  calc
    rho u v ≤ ‖(u : E d) - (v : E d)‖ := min_le_left _ _
    _ ≤ ‖(u : E d)‖ + ‖(v : E d)‖ := norm_sub_le _ _
    _ = 2 := by rw [sphere_norm, sphere_norm]; norm_num

theorem rho_sq_inner {d : ℕ} (u v : Sphere d) :
    (rho u v) ^ 2 = 2 - 2 * |inner ℝ (v : E d) (u : E d)| := by
  have hm := norm_sub_sq_real (u : E d) (v : E d)
  have hp := norm_add_sq_real (u : E d) (v : E d)
  rw [sphere_norm, sphere_norm, real_inner_comm (v : E d) (u : E d)] at hm hp
  by_cases hi : 0 ≤ inner ℝ (v : E d) (u : E d)
  · have hn : ‖(u : E d) - (v : E d)‖ ≤ ‖(u : E d) + (v : E d)‖ := by
      nlinarith [norm_nonneg ((u : E d) - (v : E d)),
        norm_nonneg ((u : E d) + (v : E d))]
    rw [rho, min_eq_left hn, abs_of_nonneg hi]
    nlinarith
  · have hn : ‖(u : E d) + (v : E d)‖ ≤ ‖(u : E d) - (v : E d)‖ := by
      nlinarith [norm_nonneg ((u : E d) - (v : E d)),
        norm_nonneg ((u : E d) + (v : E d))]
    rw [rho, min_eq_right hn, abs_of_neg (lt_of_not_ge hi)]
    nlinarith

theorem residual_sq_inner {d : ℕ} (u v : Sphere d) :
    ‖orthogonalResidual (v : E d) (u : E d)‖ ^ 2 =
      1 - (inner ℝ (v : E d) (u : E d)) ^ 2 := by
  rw [orthogonalResidual, norm_sub_sq_real, inner_smul_right,
    real_inner_comm (u : E d) (v : E d), norm_smul, Real.norm_eq_abs,
    sphere_norm, sphere_norm, mul_one, sq_abs]
  ring

theorem residual_le_rho {d : ℕ} (u v : Sphere d) :
    ‖orthogonalResidual (v : E d) (u : E d)‖ ≤ rho u v := by
  have hr := rho_sq_inner u v
  have hp := residual_sq_inner u v
  have hinner : |inner ℝ (v : E d) (u : E d)| ≤ 1 := by
    simpa only [sphere_norm, one_mul] using abs_real_inner_le_norm (v : E d) (u : E d)
  have habs := sq_abs (inner ℝ (v : E d) (u : E d))
  nlinarith [sq_nonneg (1 - |inner ℝ (v : E d) (u : E d)|),
    norm_nonneg (orthogonalResidual (v : E d) (u : E d)), rho_nonnegative u v]

theorem rho_le_two_residual {d : ℕ} (u v : Sphere d) :
    rho u v ≤ 2 * ‖orthogonalResidual (v : E d) (u : E d)‖ := by
  have hr := rho_sq_inner u v
  have hp := residual_sq_inner u v
  have hinner : |inner ℝ (v : E d) (u : E d)| ≤ 1 := by
    simpa only [sphere_norm, one_mul] using abs_real_inner_le_norm (v : E d) (u : E d)
  have habs := sq_abs (inner ℝ (v : E d) (u : E d))
  have habs0 := abs_nonneg (inner ℝ (v : E d) (u : E d))
  have hprod : 0 ≤ (1 - |inner ℝ (v : E d) (u : E d)|) *
      |inner ℝ (v : E d) (u : E d)| := mul_nonneg (by linarith) habs0
  nlinarith [norm_nonneg (orthogonalResidual (v : E d) (u : E d)), rho_nonnegative u v]

theorem rho_le_sqrt_two {d : ℕ} (u v : Sphere d) : rho u v ≤ Real.sqrt 2 := by
  have hr := rho_sq_inner u v
  have hs : (Real.sqrt 2) ^ 2 = (2 : ℝ) := Real.sq_sqrt (by norm_num)
  nlinarith [rho_nonnegative u v, Real.sqrt_nonneg (2 : ℝ),
    abs_nonneg (inner ℝ (v : E d) (u : E d))]

theorem rho_le_sqrt_two_residual {d : ℕ} (u v : Sphere d) :
    rho u v ≤ Real.sqrt 2 * ‖orthogonalResidual (v : E d) (u : E d)‖ := by
  have hr := rho_sq_inner u v
  have hp := residual_sq_inner u v
  have hinner : |inner ℝ (v : E d) (u : E d)| ≤ 1 := by
    simpa only [sphere_norm, one_mul] using abs_real_inner_le_norm (v : E d) (u : E d)
  have hprod : 0 ≤ (1 - |inner ℝ (v : E d) (u : E d)|) *
      |inner ℝ (v : E d) (u : E d)| :=
    mul_nonneg (by linarith) (abs_nonneg _)
  have hs : (Real.sqrt 2 * ‖orthogonalResidual (v : E d) (u : E d)‖) ^ 2 =
      2 * ‖orthogonalResidual (v : E d) (u : E d)‖ ^ 2 := by
    rw [mul_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
  have hq : (rho u v) ^ 2 ≤ 2 * ‖orthogonalResidual (v : E d) (u : E d)‖ ^ 2 := by
    nlinarith [sq_abs (inner ℝ (v : E d) (u : E d))]
  nlinarith [rho_nonnegative u v,
    mul_nonneg (Real.sqrt_nonneg (2 : ℝ)) (norm_nonneg (orthogonalResidual (v : E d) (u : E d)))]

#print axioms rho_le_sqrt_two
#print axioms rho_le_sqrt_two_residual
#print axioms rho_sq_inner
#print axioms residual_sq_inner
#print axioms residual_le_rho
#print axioms rho_le_two_residual

end Bandlimited
end
