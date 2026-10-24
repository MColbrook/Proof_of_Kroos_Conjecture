module

public import Bandlimited.SphericalEstimates
public import Bandlimited.SphericalGaussian

/-!
# Full positive spherical quadrature theorem (T13)

All assertions use the exact canonical sphere measure from the independently
specified principal statement. Constants for the Gaussian estimates depend only
on dimension and are fixed before the arbitrary real tail exponent.
-/
@[expose] public section
open scoped BigOperators
open MeasureTheory Set
noncomputable section
namespace Bandlimited
namespace SphereQuadrature

theorem tailIntegralConstant_pos (s : ℕ) (L : ℝ) (hL : (s : ℝ) < L) :
    0 < tailIntegralConstant s L := by
  have hLp : 0 < L := lt_of_le_of_lt (Nat.cast_nonneg s) hL
  have hquot : (s : ℝ) / L < 1 := (div_lt_one hLp).mpr hL
  unfold tailIntegralConstant
  exact div_pos (mul_pos (by norm_num) (capUpperConstant_pos s)) (sub_pos.mpr hquot)

def gaussianUpperConstant (s : ℕ) : ℝ :=
  gaussianPolynomialConstant (s + 1) * tailIntegralConstant s ((s + 1 : ℕ) : ℝ)

theorem gaussianUpperConstant_pos (s : ℕ) : 0 < gaussianUpperConstant s := by
  unfold gaussianUpperConstant
  apply mul_pos (gaussianPolynomialConstant_pos (s + 1))
  apply tailIntegralConstant_pos
  exact_mod_cast Nat.lt_succ_self s

theorem gaussianKernel_le_tail (n : ℕ) (lam : ℝ) (hlam : 0 ≤ lam)
    {d : ℕ} (u v : Sphere d) :
    gaussianKernel lam u v ≤ gaussianPolynomialConstant n * tailKernel lam (n : ℝ) u v := by
  have h := gaussian_polynomial_domination n (mul_nonneg hlam (rho_nonneg u v))
  have heq : -(lam * rho u v) ^ 2 = -lam ^ 2 * (rho u v) ^ 2 := by ring
  change Real.exp (-lam ^ 2 * (rho u v) ^ 2) ≤
    gaussianPolynomialConstant n * (1 + lam * rho u v) ^ (-(n : ℝ))
  rw [← heq]
  exact h

theorem sphericalGaussianIntegral_upper (s : ℕ) (lam : ℝ) (hlam : 1 ≤ lam)
    (u : Sphere (s + 1)) :
    sphericalGaussianIntegral s lam u ≤ gaussianUpperConstant s * (lam ^ s)⁻¹ := by
  have hl0 : 0 ≤ lam := by linarith
  have hsn : (s : ℝ) < ((s + 1 : ℕ) : ℝ) := by exact_mod_cast Nat.lt_succ_self s
  let G : C(Sphere (s + 1) × Sphere (s + 1), ℝ) :=
    ⟨fun p => gaussianKernel lam p.1 p.2, continuous_gaussianKernel lam⟩
  let H : C(Sphere (s + 1) × Sphere (s + 1), ℝ) :=
    ⟨fun p => tailKernel lam ((s + 1 : ℕ) : ℝ) p.1 p.2,
      continuous_tailKernel lam ((s + 1 : ℕ) : ℝ) hl0⟩
  have hGint : Integrable (gaussianKernel lam u) (surfaceMeasure s) :=
    (G.curry u).continuous.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hHint : Integrable (tailKernel lam ((s + 1 : ℕ) : ℝ) u) (surfaceMeasure s) :=
    (H.curry u).continuous.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hmono := integral_mono hGint (hHint.const_mul (gaussianPolynomialConstant (s + 1)))
    (gaussianKernel_le_tail (s + 1) lam hl0 u)
  rw [integral_const_mul] at hmono
  calc
    sphericalGaussianIntegral s lam u ≤ gaussianPolynomialConstant (s + 1) *
        sphericalTailIntegral s lam ((s + 1 : ℕ) : ℝ) u := hmono
    _ ≤ gaussianPolynomialConstant (s + 1) *
        (tailIntegralConstant s ((s + 1 : ℕ) : ℝ) * (lam ^ s)⁻¹) :=
      mul_le_mul_of_nonneg_left (sphericalTailIntegral_upper s _ hsn lam hlam u)
        (gaussianPolynomialConstant_pos (s + 1)).le
    _ = gaussianUpperConstant s * (lam ^ s)⁻¹ := by unfold gaussianUpperConstant; ring

end SphereQuadrature
open SphereQuadrature

/-- Manuscript Lemma 5.1, with all thirteen-principal-result specification
quantifiers and the actual surface measure preserved. -/
theorem positive_spherical_quadrature : PositiveSphericalQuadratureStatement := by
  intro s _hs
  refine ⟨gaussianLowerConstant s, gaussianUpperConstant s,
    gaussianLowerConstant_pos s, gaussianUpperConstant_pos s, ?_⟩
  intro L hL
  refine ⟨tailIntegralConstant s L, tailIntegralConstant_pos s L hL, ?_⟩
  intro lam hlam
  refine ⟨(fun u v => sphericalIntegrals_independent s lam L u v), ?_, ?_⟩
  · intro u
    exact ⟨sphericalGaussianIntegral_lower s lam hlam u,
      sphericalGaussianIntegral_upper s lam hlam u,
      sphericalTailIntegral_upper s L hL lam hlam u⟩
  · intro ζ hζ
    have hL0 : 0 ≤ L := (Nat.cast_nonneg s).trans hL.le
    exact positive_spherical_quadrature_rule s lam L hlam hL0 ζ hζ

#print axioms positive_spherical_quadrature
end Bandlimited
end
