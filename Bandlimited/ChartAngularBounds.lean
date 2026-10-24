module

public import Bandlimited.ChartBoundary

/-! Comparison of the chart radius and antipodal chord distance.
The constant 2D is used in both directions; it suffices for the intended
uniform theorem and avoids unnecessary square-root constants. -/

@[expose] public section
noncomputable section
open scoped RealInnerProductSpace
namespace Bandlimited

theorem orthogonalResidual_smul {d : ℕ} (v x : E d) (c : ℝ) :
    orthogonalResidual v (c • x) = c • orthogonalResidual v x := by
  simp only [orthogonalResidual, inner_smul_right, smul_sub, smul_smul]

theorem supportingChart_radial {d : ℕ} (ν : BodyNorm d)
    (ℓ : E d →L[ℝ] ℝ) {α β a₀ : ℝ} (hα : 0 < α)
    (hν : NormBounds α β ν) (v u : Sphere d) (hu : ℓ (u : E d) ≠ 0) :
    supportingChart (v : E d) (radial ν u) ℓ a₀ =
      (a₀ / ℓ (u : E d)) • orthogonalResidual (v : E d) (u : E d) := by
  have hnu := ν.sphere_value_pos hα hν u
  simp only [supportingChart, radial, map_smul, smul_eq_mul,
    orthogonalResidual_smul, smul_smul]
  congr 1
  field_simp [hu, hnu.ne']

 theorem supportingChart_angular_bounds {d : ℕ} (ν : BodyNorm d)
    (ℓ : E d →L[ℝ] ℝ) {α β : ℝ} (hα : 0 < α) (hαβ : α ≤ β)
    (hν : NormBounds α β ν) (hℓ : ∀ x, |ℓ x| ≤ ν.toFun x)
    (u v : Sphere d) (ha : 1 / 2 ≤ ℓ (radial ν u)) :
    let t := supportingChart (v : E d) (radial ν u) ℓ (ν.toFun (v : E d))
    ‖t‖ / (2 * (β / α)) ≤ rho u v ∧ rho u v ≤ (2 * (β / α)) * ‖t‖ := by
  let t := supportingChart (v : E d) (radial ν u) ℓ (ν.toFun (v : E d))
  let q := ‖orthogonalResidual (v : E d) (u : E d)‖
  have hβ : 0 < β := hα.trans_le hαβ
  have hnu := ν.sphere_value_pos hα hν u
  have hnv := ν.sphere_value_pos hα hν v
  have hαu : α ≤ ν.toFun (u : E d) := by simpa only [sphere_norm, mul_one] using (hν (u : E d)).1
  have hαv : α ≤ ν.toFun (v : E d) := by simpa only [sphere_norm, mul_one] using (hν (v : E d)).1
  have hβu : ν.toFun (u : E d) ≤ β := by simpa only [sphere_norm, mul_one] using (hν (u : E d)).2
  have hβv : ν.toFun (v : E d) ≤ β := by simpa only [sphere_norm, mul_one] using (hν (v : E d)).2
  have hαℓ : α / 2 ≤ ℓ (u : E d) := by
    rw [supportingHeight_radial, supportingHeight] at ha
    have h := (le_div_iff₀ hnu).1 ha
    linarith
  have huℓ : 0 < ℓ (u : E d) := by linarith
  have hβℓ : ℓ (u : E d) ≤ β := (le_abs_self _).trans ((hℓ _).trans hβu)
  have ht : ‖t‖ = ν.toFun (v : E d) / ℓ (u : E d) * q := by
    change ‖supportingChart (v : E d) (radial ν u) ℓ (ν.toFun (v : E d))‖ = _
    rw [supportingChart_radial ν ℓ hα hν v u huℓ.ne', norm_smul,
      Real.norm_eq_abs, abs_of_pos (div_pos hnv huℓ)]
  have hT : ‖t‖ ≤ (2 * (β / α)) * q := by
    rw [ht]
    apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
    apply (div_le_iff₀ huℓ).2
    have h := mul_le_mul_of_nonneg_left hαℓ (show 0 ≤ 2 * (β / α) by positivity)
    have hEq : 2 * (β / α) * (α / 2) = β := by field_simp
    rw [hEq] at h
    exact hβv.trans h
  have hq : q ≤ (β / α) * ‖t‖ := by
    rw [ht]
    have hfactor : 1 ≤ (β / α) * (ν.toFun (v : E d) / ℓ (u : E d)) := by
      rw [← mul_div_assoc]
      apply (le_div_iff₀ huℓ).2
      have h := mul_le_mul_of_nonneg_left hαv (show 0 ≤ β / α by positivity)
      have hEq : (β / α) * α = β := by field_simp
      rw [hEq] at h
      convert hβℓ.trans h using 1 <;> ring
    have h := mul_le_mul_of_nonneg_right hfactor (norm_nonneg (orthogonalResidual (v : E d) (u : E d)))
    nlinarith
  constructor
  · apply (div_le_iff₀ (by positivity : (0 : ℝ) < 2 * (β / α))).2
    have h := hT.trans (mul_le_mul_of_nonneg_left (residual_le_rho u v) (by positivity))
    nlinarith
  · have h := rho_le_two_residual u v
    change rho u v ≤ 2 * q at h
    nlinarith

#print axioms supportingChart_radial
#print axioms supportingChart_angular_bounds

end Bandlimited
end
