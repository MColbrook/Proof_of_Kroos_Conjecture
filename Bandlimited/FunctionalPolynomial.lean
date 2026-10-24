module

public import Bandlimited.PolynomialTransport

/-! The exact real linear polynomial associated with a continuous linear
functional, used for fraction-free homogenization. -/

@[expose] public section
noncomputable section
namespace Bandlimited

def scalarEmbeddingLinear : ℝ →ₗ[ℝ] E 1 :=
  (LinearMap.id : ℝ →ₗ[ℝ] ℝ).smulRight (PiLp.single 2 (0 : Fin 1) 1)

@[simp] theorem scalarEmbeddingLinear_zero_coordinate (t : ℝ) :
    scalarEmbeddingLinear t (0 : Fin 1) = t := by
  simp [scalarEmbeddingLinear, PiLp.smul_apply, smul_eq_mul]

def functionalPolynomial {d : ℕ} (ℓ : E d →ₗ[ℝ] ℝ) : Polynomial d :=
  linearSubstitution (scalarEmbeddingLinear.comp ℓ) (0 : Fin 1)

theorem functionalPolynomial_homogeneous {d : ℕ} (ℓ : E d →ₗ[ℝ] ℝ) :
    (functionalPolynomial ℓ).IsHomogeneous 1 :=
  linearSubstitution_homogeneous _ _

@[simp] theorem functionalPolynomial_eval {d : ℕ} (ℓ : E d →ₗ[ℝ] ℝ) (x : E d) :
    evalPolynomial (functionalPolynomial ℓ) x = ℓ x := by
  rw [functionalPolynomial, linearSubstitution_eval]
  change scalarEmbeddingLinear (ℓ x) (0 : Fin 1) = ℓ x
  exact scalarEmbeddingLinear_zero_coordinate _

#print axioms functionalPolynomial_homogeneous
#print axioms functionalPolynomial_eval

end Bandlimited
end
