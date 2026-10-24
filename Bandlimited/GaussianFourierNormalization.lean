module

public import Bandlimited.FourierConvention
public import Mathlib.Analysis.SpecialFunctions.Gaussian.FourierTransform

/- Exact Gaussian normalization for the manuscript's Fourier convention. -/

@[expose] public section
noncomputable section
open MeasureTheory
open scoped BigOperators RealInnerProductSpace

namespace Bandlimited
namespace GaussianNormalization

def frequency (d : ℕ) (ξ : E d) : ℂ :=
  ((Real.pi ^ ((d : ℝ) / 2) * Real.exp (-‖ξ‖ ^ 2 / 4) : ℝ) : ℂ)

theorem normalization (d : ℕ) :
    ((2 * Real.pi) ^ d)⁻¹ * Real.pi ^ ((d : ℝ) / 2) *
      (4 * Real.pi) ^ ((d : ℝ) / 2) = 1 := by
  have hprod : Real.pi ^ ((d : ℝ) / 2) * (4 * Real.pi) ^ ((d : ℝ) / 2) =
      (2 * Real.pi) ^ d := by
    rw [← Real.mul_rpow (by positivity : 0 ≤ Real.pi) (by positivity : 0 ≤ 4 * Real.pi)]
    have hb : Real.pi * (4 * Real.pi) = (2 * Real.pi) ^ 2 := by ring
    rw [hb, ← Real.rpow_natCast (2 * Real.pi) 2,
      ← Real.rpow_mul (by positivity : 0 ≤ 2 * Real.pi)]
    norm_num only [Nat.cast_ofNat]
    have he : (2 : ℝ) * ((d : ℝ) / 2) = (d : ℝ) := by ring
    rw [he, Real.rpow_natCast]
  rw [mul_assoc, hprod, inv_mul_cancel₀ (by positivity : (2 * Real.pi) ^ d ≠ 0)]

end GaussianNormalization

 theorem inverseFourier_gaussianFrequency (d : ℕ) (x : E d) :
    inverseFourier (GaussianNormalization.frequency d) x = (Real.exp (-‖x‖ ^ 2) : ℂ) := by
  have hinner (ξ : E d) : (∑ i : Fin d, x i * ξ i : ℝ) = ⟪x, ξ⟫ := by
    simp only [EuclideanSpace.inner_eq_star_dotProduct, dotProduct, star_trivial, mul_comm]
  have hint :
      (∫ ξ : E d, GaussianNormalization.frequency d ξ *
        Complex.exp (Complex.I * ((∑ i : Fin d, x i * ξ i : ℝ) : ℂ))) =
      ((Real.pi ^ ((d : ℝ) / 2) : ℝ) : ℂ) *
        ∫ ξ : E d, Complex.exp (-(1 / 4 : ℂ) * ‖ξ‖ ^ 2 + Complex.I * ⟪x, ξ⟫) := by
    rw [← integral_const_mul]
    apply integral_congr_ae
    filter_upwards [] with ξ
    rw [hinner]
    simp only [GaussianNormalization.frequency, Complex.ofReal_mul, Complex.ofReal_exp]
    rw [mul_assoc, ← Complex.exp_add]
    congr 2
    push_cast
    ring
  have hg := GaussianFourier.integral_cexp_neg_mul_sq_norm_add_of_euclideanSpace
    (b := (1 / 4 : ℂ)) (by norm_num : 0 < (1 / 4 : ℂ).re) Complex.I x
  simp only [Fintype.card_fin] at hg
  have hb : (Real.pi : ℂ) / (1 / 4 : ℂ) = ((4 * Real.pi : ℝ) : ℂ) := by push_cast; ring
  have he : Complex.I ^ 2 * (‖x‖ : ℂ) ^ 2 / (4 * (1 / 4 : ℂ)) = ((-‖x‖ ^ 2 : ℝ) : ℂ) := by
    rw [Complex.I_sq]
    push_cast
    ring
  rw [hb, he] at hg
  have hp : ((4 * Real.pi : ℝ) : ℂ) ^ ((d : ℂ) / 2) =
      (((4 * Real.pi) ^ ((d : ℝ) / 2) : ℝ) : ℂ) := by
    rw [Complex.ofReal_cpow (by positivity : 0 ≤ 4 * Real.pi)]
    push_cast
    rfl
  rw [hp] at hg
  unfold inverseFourier
  rw [hint, hg]
  have hn := congrArg (fun t : ℝ => (t : ℂ)) (GaussianNormalization.normalization d)
  push_cast at hn
  push_cast
  rw [← mul_assoc, ← mul_assoc, hn, one_mul]

#print axioms inverseFourier_gaussianFrequency

end Bandlimited
end
