module

public import Bandlimited.SupportingFunctional
public import Mathlib.Analysis.InnerProductSpace.Basic

/-! Supporting-hyperplane coordinates in the ambient Euclidean space.
Using the ambient space for T12 avoids a choice of coordinates on v-perp;
the profile is constant in the v direction, and chart points lie in v-perp. -/

@[expose] public section
noncomputable section
open Set
open scoped RealInnerProductSpace
namespace Bandlimited

def supportProjection {d : ℕ} (v : E d) (ℓ : E d →L[ℝ] ℝ) (a₀ : ℝ) :
    E d →L[ℝ] E d :=
  ContinuousLinearMap.id ℝ (E d) - a₀⁻¹ • ℓ.smulRight v

@[simp] theorem supportProjection_apply {d : ℕ}
    (v : E d) (ℓ : E d →L[ℝ] ℝ) (a₀ : ℝ) (x : E d) :
    supportProjection v ℓ a₀ x = x - (ℓ x / a₀) • v := by
  simp [supportProjection, div_eq_inv_mul, smul_smul]

theorem supportProjection_functional {d : ℕ}
    (v : E d) (ℓ : E d →L[ℝ] ℝ) {a₀ : ℝ} (ha₀ : a₀ ≠ 0)
    (hv : ℓ v = a₀) (x : E d) : ℓ (supportProjection v ℓ a₀ x) = 0 := by
  rw [supportProjection_apply, map_sub, map_smul, hv]
  simp only [smul_eq_mul]
  field_simp
  <;> ring

@[simp] theorem supportProjection_self {d : ℕ}
    (v : E d) (ℓ : E d →L[ℝ] ℝ) {a₀ : ℝ} (ha₀ : a₀ ≠ 0)
    (hv : ℓ v = a₀) : supportProjection v ℓ a₀ v = 0 := by
  simp [hv, ha₀]

theorem supportProjection_norm {d : ℕ}
    (v : E d) (hv : ‖v‖ = 1) (ℓ : E d →L[ℝ] ℝ)
    {a₀ β : ℝ} (ha₀ : 0 < a₀) (hℓ : ‖ℓ‖ ≤ β) (x : E d) :
    ‖supportProjection v ℓ a₀ x‖ ≤ (1 + β / a₀) * ‖x‖ := by
  rw [supportProjection_apply]
  calc
    ‖x - (ℓ x / a₀) • v‖ ≤ ‖x‖ + ‖(ℓ x / a₀) • v‖ := norm_sub_le _ _
    _ = ‖x‖ + |ℓ x| / a₀ := by
      rw [norm_smul, Real.norm_eq_abs, abs_div, abs_of_pos ha₀, hv, mul_one]
    _ ≤ ‖x‖ + (β * ‖x‖) / a₀ := by
      gcongr
      exact (show |ℓ x| ≤ ‖ℓ‖ * ‖x‖ by simpa only [Real.norm_eq_abs] using ℓ.le_opNorm x).trans
        (mul_le_mul_of_nonneg_right hℓ (norm_nonneg x))
    _ = (1 + β / a₀) * ‖x‖ := by ring

def supportingProfile {d : ℕ} (ν : BodyNorm d) (v : E d)
    (ℓ : E d →L[ℝ] ℝ) (a₀ N : ℝ) (x : E d) : ℝ :=
  N * (ν.toFun (v + N⁻¹ • supportProjection v ℓ a₀ x) / a₀ - 1)

theorem supportingProfile_nonneg {d : ℕ} (ν : BodyNorm d) (v : E d)
    (ℓ : E d →L[ℝ] ℝ) {a₀ N : ℝ} (ha₀ : 0 < a₀) (hN : 0 ≤ N)
    (hv : ℓ v = a₀) (hℓ : ∀ x, |ℓ x| ≤ ν.toFun x) (x : E d) :
    0 ≤ supportingProfile ν v ℓ a₀ N x := by
  have hval : ℓ (v + N⁻¹ • supportProjection v ℓ a₀ x) = a₀ := by
    rw [map_add, map_smul, supportProjection_functional v ℓ ha₀.ne' hv, hv]
    simp
  have hbound := hℓ (v + N⁻¹ • supportProjection v ℓ a₀ x)
  rw [hval, abs_of_pos ha₀] at hbound
  exact mul_nonneg hN (sub_nonneg.mpr ((le_div_iff₀ ha₀).2 (by simpa using hbound)))

@[simp] theorem supportingProfile_zero {d : ℕ} (ν : BodyNorm d) (v : E d)
    (ℓ : E d →L[ℝ] ℝ) {a₀ N : ℝ} (ha₀ : a₀ ≠ 0)
    (hv : ν.toFun v = a₀) : supportingProfile ν v ℓ a₀ N 0 = 0 := by
  simp [supportingProfile, hv, ha₀]

theorem supportingProfile_convex {d : ℕ} (ν : BodyNorm d) (v : E d)
    (ℓ : E d →L[ℝ] ℝ) {a₀ N : ℝ} (ha₀ : 0 < a₀) (hN : 0 ≤ N) :
    ConvexOn ℝ univ (supportingProfile ν v ℓ a₀ N) := by
  let g : E d →ᵃ[ℝ] E d := AffineMap.const ℝ (E d) v +
    (N⁻¹ • (supportProjection v ℓ a₀).toLinearMap).toAffineMap
  have hg : ConvexOn ℝ univ (fun x => ν.toFun (v + N⁻¹ • supportProjection v ℓ a₀ x)) := by
    simpa only [Set.preimage_univ, Function.comp_def, g, AffineMap.coe_add, Pi.add_apply,
      AffineMap.const_apply, LinearMap.coe_toAffineMap, LinearMap.smul_apply, ContinuousLinearMap.coe_coe] using
      ν.convexOn.comp_affineMap g
  have hc := (ConvexOn.smul (div_nonneg hN ha₀.le) hg).add_const (-N)
  convert hc using 1
  funext x
  simp only [supportingProfile, smul_eq_mul, Pi.add_apply]
  ring

theorem supportingProfile_lipschitz {d : ℕ} (ν : BodyNorm d) (v : E d)
    (hv : ‖v‖ = 1) (ℓ : E d →L[ℝ] ℝ) {a₀ N α β : ℝ}
    (ha₀ : 0 < a₀) (hN : 0 < N) (hβ : 0 ≤ β)
    (hℓ : ‖ℓ‖ ≤ β) (hν : NormBounds α β ν) (x y : E d) :
    |supportingProfile ν v ℓ a₀ N x - supportingProfile ν v ℓ a₀ N y| ≤
      (β / a₀ * (1 + β / a₀)) * ‖x - y‖ := by
  let B := supportProjection v ℓ a₀
  let z := fun t : E d => v + N⁻¹ • B t
  have hdiff : z x - z y = N⁻¹ • B (x - y) := by
    simp only [z, map_sub, smul_sub]
    abel
  have halg : supportingProfile ν v ℓ a₀ N x - supportingProfile ν v ℓ a₀ N y =
      (N / a₀) * (ν.toFun (z x) - ν.toFun (z y)) := by
    simp only [supportingProfile, z, B]
    ring
  rw [halg, abs_mul, abs_of_pos (div_pos hN ha₀)]
  calc
    N / a₀ * |ν.toFun (z x) - ν.toFun (z y)| ≤
        N / a₀ * (β * ‖z x - z y‖) := by
      apply mul_le_mul_of_nonneg_left _ (div_nonneg hN.le ha₀.le)
      exact (ν.abs_sub_le _ _).trans (hν _).2
    _ = (β / a₀) * ‖B (x - y)‖ := by
      rw [hdiff, norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hN)]
      field_simp
      <;> ring
    _ ≤ (β / a₀) * ((1 + β / a₀) * ‖x - y‖) :=
      mul_le_mul_of_nonneg_left (supportProjection_norm v hv ℓ ha₀ hℓ _)
        (div_nonneg hβ ha₀.le)
    _ = _ := by ring

theorem supportingProfile_common_bound {d : ℕ} (ν : BodyNorm d)
    (v : E d) (hv : ‖v‖ = 1) (ℓ : E d →L[ℝ] ℝ)
    {α β N : ℝ} (hα : 0 < α) (hαβ : α ≤ β) (hN : 0 < N)
    (hν : NormBounds α β ν) (hvℓ : ℓ v = ν.toFun v)
    (hℓ : ∀ x, |ℓ x| ≤ ν.toFun x) (hnℓ : ‖ℓ‖ ≤ β) :
    HasProfileLipschitzBound (β / α * (1 + β / α))
      (supportingProfile ν v ℓ (ν.toFun v) N) := by
  have hβ : 0 ≤ β := (hα.trans_le hαβ).le
  have hαv : α ≤ ν.toFun v := by simpa only [hv, mul_one] using (hν v).1
  have ha₀ : 0 < ν.toFun v := hα.trans_le hαv
  have hratio : β / ν.toFun v ≤ β / α :=
    div_le_div_of_nonneg_left hβ hα hαv
  have hc : β / ν.toFun v * (1 + β / ν.toFun v) ≤ β / α * (1 + β / α) := by
    exact mul_le_mul hratio (by linarith) (by positivity) (by positivity)
  have hLip (x y : E d) :
      |supportingProfile ν v ℓ (ν.toFun v) N x -
        supportingProfile ν v ℓ (ν.toFun v) N y| ≤
          (β / α * (1 + β / α)) * ‖x - y‖ :=
    (supportingProfile_lipschitz ν v hv ℓ ha₀ hN hβ hnℓ hν x y).trans
      (mul_le_mul_of_nonneg_right hc (norm_nonneg _))
  refine ⟨⟨supportingProfile_convex ν v ℓ ha₀ hN.le,
    supportingProfile_nonneg ν v ℓ ha₀ hN.le hvℓ hℓ,
    supportingProfile_zero ν v ℓ ha₀.ne' rfl,
    ⟨β / α * (1 + β / α), by positivity, hLip⟩⟩, hLip⟩

def orthogonalResidual {d : ℕ} (v x : E d) : E d := x - inner ℝ v x • v

theorem orthogonalResidual_norm {d : ℕ} (v x : E d) (hv : ‖v‖ = 1) :
    ‖orthogonalResidual v x‖ ≤ ‖x‖ := by
  have hs := norm_sub_sq_real x (inner ℝ v x • v)
  rw [inner_smul_right, real_inner_comm x v, norm_smul, Real.norm_eq_abs,
    hv, mul_one, sq_abs] at hs
  change ‖x - inner ℝ v x • v‖ ≤ ‖x‖
  rw [real_inner_comm x v]
  nlinarith [sq_nonneg (inner ℝ x v), norm_nonneg x,
    norm_nonneg (x - inner ℝ x v • v)]

theorem supportProjection_residual {d : ℕ} (v z : E d)
    (ℓ : E d →L[ℝ] ℝ) {a₀ : ℝ} (ha₀ : a₀ ≠ 0) (hv : ℓ v = a₀) :
    supportProjection v ℓ a₀ (orthogonalResidual v z) = supportProjection v ℓ a₀ z := by
  simp only [orthogonalResidual, map_sub, map_smul,
    supportProjection_self v ℓ ha₀ hv, smul_zero, sub_zero]

def supportingChart {d : ℕ} (v z : E d) (ℓ : E d →L[ℝ] ℝ) (a₀ : ℝ) : E d :=
  (a₀ / ℓ z) • orthogonalResidual v z

theorem supportingChart_identity {d : ℕ} (v z : E d)
    (ℓ : E d →L[ℝ] ℝ) {a₀ : ℝ} (ha₀ : a₀ ≠ 0) (hz : ℓ z ≠ 0)
    (hv : ℓ v = a₀) :
    z = (ℓ z / a₀) • (v + supportProjection v ℓ a₀ (supportingChart v z ℓ a₀)) := by
  rw [supportingChart, map_smul, supportProjection_residual v z ℓ ha₀ hv,
    supportProjection_apply]
  ext i
  simp only [PiLp.smul_apply, PiLp.add_apply, PiLp.sub_apply, smul_eq_mul]
  field_simp
  <;> ring

#print axioms supportProjection_functional
#print axioms supportProjection_norm
#print axioms supportingProfile_nonneg
#print axioms orthogonalResidual_norm
#print axioms supportingChart_identity

end Bandlimited
end
