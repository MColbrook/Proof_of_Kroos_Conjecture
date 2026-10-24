module

public import Bandlimited.SupportingHeight

/-! Radial boundary identities for supporting coordinates. All denominators
are justified by the positive lower norm bound or positive chart height. -/

@[expose] public section
noncomputable section
open scoped RealInnerProductSpace
namespace Bandlimited

theorem BodyNorm.sphere_value_pos {d : ℕ} (ν : BodyNorm d)
    {α β : ℝ} (hα : 0 < α) (hν : NormBounds α β ν) (u : Sphere d) :
    0 < ν.toFun (u : E d) :=
  hα.trans_le (by simpa only [sphere_norm, mul_one] using (hν (u : E d)).1)

@[simp] theorem supportingHeight_radial {d : ℕ} (ν : BodyNorm d)
    (ℓ : E d →L[ℝ] ℝ) (u : Sphere d) :
    ℓ (radial ν u) = supportingHeight ν ℓ u := by
  simp only [radial, map_smul, smul_eq_mul, supportingHeight, div_eq_inv_mul]

theorem BodyNorm.radial_value {d : ℕ} (ν : BodyNorm d)
    {α β : ℝ} (hα : 0 < α) (hν : NormBounds α β ν) (u : Sphere d) :
    ν.toFun (radial ν u) = 1 := by
  have hpos := ν.sphere_value_pos hα hν u
  simp only [radial, ν.smul, abs_of_pos (inv_pos.mpr hpos), inv_mul_cancel₀ hpos.ne']

theorem BodyNorm.radial_norm_bound {d : ℕ} (ν : BodyNorm d)
    {α β : ℝ} (hα : 0 < α) (hν : NormBounds α β ν) (u : Sphere d) :
    ‖radial ν u‖ ≤ α⁻¹ := by
  have hpos := ν.sphere_value_pos hα hν u
  have hlow : α ≤ ν.toFun (u : E d) := by
    simpa only [sphere_norm, mul_one] using (hν (u : E d)).1
  rw [radial, norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hpos), sphere_norm, mul_one]
  exact inv_anti₀ hα hlow

theorem supportingChart_norm_bound {d : ℕ} (ν : BodyNorm d)
    (ℓ : E d →L[ℝ] ℝ) {α β : ℝ} (hα : 0 < α) (hαβ : α ≤ β)
    (hν : NormBounds α β ν) (u v : Sphere d)
    (ha : 1 / 2 ≤ ℓ (radial ν u)) :
    ‖supportingChart (v : E d) (radial ν u) ℓ (ν.toFun (v : E d))‖ ≤ 2 * (β / α) := by
  have ha0 : 0 < ℓ (radial ν u) := by linarith
  have hv0 := ν.sphere_value_pos hα hν v
  have hvβ : ν.toFun (v : E d) ≤ β := by
    simpa only [sphere_norm, mul_one] using (hν (v : E d)).2
  have hβ : 0 ≤ β := (hα.trans_le hαβ).le
  rw [supportingChart, norm_smul, Real.norm_eq_abs, abs_of_pos (div_pos hv0 ha0)]
  calc
    ν.toFun (v : E d) / ℓ (radial ν u) *
        ‖orthogonalResidual (v : E d) (radial ν u)‖ ≤
      (2 * β) * α⁻¹ := by
      apply mul_le_mul _ _ (norm_nonneg _) (by positivity)
      · apply (div_le_iff₀ ha0).2
        nlinarith
      · exact (orthogonalResidual_norm _ _ (sphere_norm v)).trans (ν.radial_norm_bound hα hν u)
    _ = 2 * (β / α) := by ring

theorem supportingChart_radial_identity {d : ℕ} (ν : BodyNorm d)
    (ℓ : E d →L[ℝ] ℝ) {α β N : ℝ} (hα : 0 < α)
    (hν : NormBounds α β ν) (u v : Sphere d)
    (hv : ℓ (v : E d) = ν.toFun (v : E d))
    (ha : 0 < ℓ (radial ν u)) (hN : N ≠ 0) :
    ℓ (radial ν u) =
      (1 + supportingProfile ν (v : E d) ℓ (ν.toFun (v : E d)) N
        (N • supportingChart (v : E d) (radial ν u) ℓ (ν.toFun (v : E d))) / N)⁻¹ := by
  let a₀ := ν.toFun (v : E d)
  let a := ℓ (radial ν u)
  let t := supportingChart (v : E d) (radial ν u) ℓ a₀
  have ha₀ : 0 < a₀ := ν.sphere_value_pos hα hν v
  have hid := supportingChart_identity (v : E d) (radial ν u) ℓ ha₀.ne' ha.ne' hv
  have hn : (a / a₀) * ν.toFun ((v : E d) + supportProjection (v : E d) ℓ a₀ t) = 1 := by
    have h := ν.radial_value hα hν u
    rw [hid, ν.smul, abs_of_pos (div_pos ha ha₀)] at h
    exact h
  have ha' : a ≠ 0 := ha.ne'
  have hV : ν.toFun ((v : E d) + supportProjection (v : E d) ℓ a₀ t) = a₀ / a := by
    apply (eq_div_iff ha').2
    have hm := hn
    field_simp [ha₀.ne'] at hm
    nlinarith [hm]
  have hq : 1 + supportingProfile ν (v : E d) ℓ a₀ N (N • t) / N = a⁻¹ := by
    simp only [supportingProfile, map_smul, smul_smul, inv_mul_cancel₀ hN, one_smul]
    rw [hV]
    field_simp [hN, ha', ha₀.ne']
    <;> ring
  change a = (1 + supportingProfile ν (v : E d) ℓ a₀ N (N • t) / N)⁻¹
  rw [hq, inv_inv]

#print axioms BodyNorm.radial_value
#print axioms BodyNorm.radial_norm_bound
#print axioms supportingChart_norm_bound
#print axioms supportingChart_radial_identity

end Bandlimited
end
