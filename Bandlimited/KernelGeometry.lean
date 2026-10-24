module

public import Bandlimited.LocalAngularError
public import Bandlimited.PolynomialLifting

/-! Linear chart maps, antipodal identities, and the three-region reduction
for the homogeneous Gaussian kernel. -/

@[expose] public section
noncomputable section
open scoped RealInnerProductSpace
namespace Bandlimited

def orthogonalResidualLinear {d : ℕ} (v : E d) : E d →ₗ[ℝ] E d where
  toFun := orthogonalResidual v
  map_add' x y := by
    simp only [orthogonalResidual, inner_add_right, add_smul]
    abel
  map_smul' a x := by
    simp only [orthogonalResidual, inner_smul_right, smul_sub, smul_smul, RingHom.id_apply]

@[simp] theorem orthogonalResidualLinear_apply {d : ℕ} (v x : E d) :
    orthogonalResidualLinear v x = orthogonalResidual v x := rfl

@[simp] theorem supportingHeight_sphereNeg {d : ℕ} (ν : BodyNorm d)
    (ℓ : E d →L[ℝ] ℝ) (u : Sphere d) :
    supportingHeight ν ℓ (sphereNeg u) = -supportingHeight ν ℓ u := by
  simp only [supportingHeight, sphereNeg, map_neg, ν.map_neg, neg_div]

@[simp] theorem radial_sphereNeg {d : ℕ} (ν : BodyNorm d) (u : Sphere d) :
    radial ν (sphereNeg u) = -radial ν u := by
  simp only [radial, sphereNeg, ν.map_neg, smul_neg]

@[simp] theorem rho_sphereNeg_left {d : ℕ} (u v : Sphere d) :
    rho (sphereNeg u) v = rho u v := by
  have hsub : -(u : E d) - (v : E d) = -((u : E d) + (v : E d)) := by abel
  have hadd : -(u : E d) + (v : E d) = -((u : E d) - (v : E d)) := by abel
  simp only [rho, sphereNeg, hsub, hadd, norm_neg, min_comm]

def angularKernelError {d : ℕ} (ν : BodyNorm d) (v : Sphere d)
    (N : ℕ) (A L : ℝ) (p : Polynomial d) (u : Sphere d) : ℝ :=
  (1 + (N : ℝ) / A * rho u v) ^ L *
    |evalPolynomial p (radial ν u) -
      Real.exp (-((N : ℝ) ^ 2 / A ^ 2) * (rho u v) ^ 2)|

theorem angularKernelError_even {d N : ℕ} (ν : BodyNorm d) (v : Sphere d)
    (A L : ℝ) (p : Polynomial d) (hp : p.IsHomogeneous N) (hN : Even N)
    (u : Sphere d) :
    angularKernelError ν v N A L p (sphereNeg u) = angularKernelError ν v N A L p u := by
  simp only [angularKernelError, rho_sphereNeg_left, radial_sphereNeg,
    eval_homogeneous_neg hp, hN.neg_one_pow, one_mul]

theorem kernel_error_of_three_regions {d N : ℕ} (ν : BodyNorm d) (v : Sphere d)
    (ℓ : E d →L[ℝ] ℝ) (A L b : ℝ) (p : Polynomial d)
    (hp : p.IsHomogeneous N) (hN : Even N)
    (hsmall : ∀ u : Sphere d, |supportingHeight ν ℓ u| ≤ 1 / 2 →
      angularKernelError ν v N A L p u ≤ b)
    (hpositive : ∀ u : Sphere d, 1 / 2 ≤ supportingHeight ν ℓ u →
      angularKernelError ν v N A L p u ≤ b) :
    ∀ u : Sphere d, angularKernelError ν v N A L p u ≤ b := by
  intro u
  by_cases hu : |supportingHeight ν ℓ u| ≤ 1 / 2
  · exact hsmall u hu
  · by_cases hpos : 1 / 2 ≤ supportingHeight ν ℓ u
    · exact hpositive u hpos
    · have hneg : 1 / 2 ≤ supportingHeight ν ℓ (sphereNeg u) := by
        rw [supportingHeight_sphereNeg]
        have habs : 1 / 2 < |supportingHeight ν ℓ u| := lt_of_not_ge hu
        rcases lt_or_ge (supportingHeight ν ℓ u) 0 with h | h
        · rw [abs_of_neg h] at habs
          linarith
        · rw [abs_of_nonneg h] at habs
          linarith
      have h := hpositive (sphereNeg u) hneg
      rwa [angularKernelError_even ν v A L p hp hN u] at h

#print axioms rho_sphereNeg_left
#print axioms angularKernelError_even
#print axioms kernel_error_of_three_regions

end Bandlimited
end
