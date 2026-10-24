module

public import Bandlimited.Definitions
public import Mathlib.Analysis.Fourier.FourierTransform
public import Mathlib.Analysis.Distribution.SchwartzSpace.Fourier
public import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
public import Mathlib.MeasureTheory.Measure.Haar.NormedSpace

/-!
# The manuscript's inverse Fourier convention

Mathlib uses `exp (2π i ⟪ξ,x⟫)`. The manuscript uses `exp (i ⟪x,ξ⟫)`
and the prefactor `(2π)^(-d)`. This module proves the exact conversion.
Mathlib reuse is under Apache 2.0.
-/

@[expose] public section

noncomputable section
open MeasureTheory
open scoped FourierTransform RealInnerProductSpace BigOperators Topology

namespace Bandlimited

theorem inverseFourier_eq_mathlib_inverse {d : ℕ} (φ : E d → ℂ) (x : E d) :
    inverseFourier φ x = (((2 * Real.pi) ^ d : ℝ)⁻¹ : ℂ) *
      (𝓕⁻ φ) ((2 * Real.pi)⁻¹ • x) := by
  unfold inverseFourier
  rw [Real.fourierInv_eq']
  congr 1
  apply integral_congr_ae
  filter_upwards [] with ξ
  have hinner : 2 * Real.pi * ⟪ξ, (2 * Real.pi)⁻¹ • x⟫ =
      ∑ i : Fin d, x i * ξ i := by
    rw [real_inner_smul_right, ← mul_assoc,
      mul_inv_cancel₀ (by positivity : 2 * Real.pi ≠ 0), one_mul]
    simp only [EuclideanSpace.inner_eq_star_dotProduct, dotProduct,
      star_trivial]
  rw [hinner, smul_eq_mul, mul_comm (φ ξ)]
  congr 1
  congr 1
  ring

/-- Even real frequency data have a real-valued inverse transform. The proof
uses exact integral invariance under ξ ↦ -ξ, with no evaluation oracle. -/
theorem inverseFourier_real_of_even {d : ℕ} (φ : E d → ℂ)
    (hreal : IsRealValued φ) (heven : ∀ ξ, φ (-ξ) = φ ξ) :
    IsRealValued (inverseFourier φ) := by
  intro x
  apply Complex.conj_eq_iff_im.mp
  rw [inverseFourier_eq_mathlib_inverse]
  simp only [map_mul, map_inv₀, Complex.conj_ofReal]
  congr 1
  rw [Real.fourierInv_eq', ← integral_conj]
  have hφ : ∀ ξ, (starRingEnd ℂ) (φ ξ) = φ ξ :=
    fun ξ => Complex.conj_eq_iff_im.mpr (hreal ξ)
  calc
    (∫ ξ : E d, (starRingEnd ℂ)
      (Complex.exp ((↑(2 * Real.pi * ⟪ξ, (2 * Real.pi)⁻¹ • x⟫) * Complex.I)) • φ ξ)) =
        ∫ ξ : E d, Complex.exp
          ((↑(2 * Real.pi * ⟪-ξ, (2 * Real.pi)⁻¹ • x⟫) * Complex.I)) • φ (-ξ) := by
      apply integral_congr_ae
      filter_upwards [] with ξ
      simp only [smul_eq_mul, map_mul, ← Complex.exp_conj,
        Complex.conj_ofReal, Complex.conj_I, hφ, heven, inner_neg_left,
        mul_neg, Complex.ofReal_neg, neg_mul]
    _ = _ := by
      simpa only [neg_one_smul, abs_inv, abs_pow, abs_neg, abs_one,
        one_pow, inv_one, one_smul] using
        (MeasureTheory.Measure.integral_comp_smul volume
          (fun ξ : E d => Complex.exp
            ((↑(2 * Real.pi * ⟪ξ, (2 * Real.pi)⁻¹ • x⟫) * Complex.I)) • φ ξ) (-1))

/-- The scalar change required by the two Fourier conventions. -/
def inverseFourierScale (d : ℕ) : E d ≃L[ℝ] E d :=
  ContinuousLinearEquiv.smulLeft (R₁ := ℝ) (M₁ := E d)
    (Units.mk0 ((2 * Real.pi)⁻¹) (by positivity))

/-- The manuscript's inverse Fourier transform as an actual Schwartz map. -/
def inverseFourierSchwartz {d : ℕ} (φ : SchwartzMap (E d) ℂ) :
    SchwartzMap (E d) ℂ :=
  (((2 * Real.pi) ^ d : ℝ)⁻¹ : ℂ) •
    (SchwartzMap.compCLMOfContinuousLinearEquiv ℂ (inverseFourierScale d)) (𝓕⁻ φ)

theorem inverseFourierSchwartz_apply {d : ℕ} (φ : SchwartzMap (E d) ℂ) (x : E d) :
    inverseFourierSchwartz φ x = inverseFourier φ x := by
  rw [inverseFourier_eq_mathlib_inverse]
  change (((2 * Real.pi) ^ d : ℝ)⁻¹ : ℂ) *
    (𝓕⁻ φ) (inverseFourierScale d x) = _
  rw [SchwartzMap.fourierInv_coe]
  rfl

theorem SmoothFrequency.inverse_schwartz {d : ℕ} {σ : ℝ} {φ : E d → ℂ}
    (hφ : SmoothFrequency σ φ) :
    ∃ F : SchwartzMap (E d) ℂ, ∀ x, F x = inverseFourier φ x := by
  let φS := hφ.2.1.toSchwartzMap hφ.1
  exact ⟨inverseFourierSchwartz φS, inverseFourierSchwartz_apply φS⟩

theorem inverseFourierSchwartz_continuous {d : ℕ} :
    Continuous (inverseFourierSchwartz : SchwartzMap (E d) ℂ → SchwartzMap (E d) ℂ) := by
  unfold inverseFourierSchwartz
  exact ((SchwartzMap.compCLMOfContinuousLinearEquiv ℂ (inverseFourierScale d)).continuous.comp
    (FourierTransform.continuous_fourierInv : Continuous
      (𝓕⁻ : SchwartzMap (E d) ℂ → SchwartzMap (E d) ℂ))).const_smul
        ((((2 * Real.pi) ^ d : ℝ)⁻¹ : ℂ))

theorem schwartz_rescale {d : ℕ} (f : SchwartzMap (E d) ℂ) (A : ℝ) (hA : A ≠ 0) :
    ∃ F : SchwartzMap (E d) ℂ, ∀ x, F x = f (A⁻¹ • x) := by
  let S : E d ≃L[ℝ] E d := ContinuousLinearEquiv.smulLeft (R₁ := ℝ) (M₁ := E d)
    (Units.mk0 A⁻¹ (inv_ne_zero hA))
  exact ⟨SchwartzMap.compCLMOfContinuousLinearEquiv ℂ S f, fun _ => rfl⟩

theorem inverseFourier_rescale {d : ℕ} (φ : E d → ℂ) (A : ℝ) (hA : 0 < A)
    (x : E d) :
    inverseFourier (fun ξ => ((A ^ d : ℝ) : ℂ) * φ (A • ξ)) x =
      inverseFourier φ (A⁻¹ • x) := by
  let H : E d → ℂ := fun ξ => φ ξ * Complex.exp
    (Complex.I * ((∑ i : Fin d, (A⁻¹ • x) i * ξ i : ℝ) : ℂ))
  have hdot (ξ : E d) : (∑ i : Fin d, (A⁻¹ • x) i * (A • ξ) i : ℝ) =
      ∑ i : Fin d, x i * ξ i := by
    apply Finset.sum_congr rfl
    intro i hi
    simp only [PiLp.smul_apply, smul_eq_mul]
    field_simp
  have hphase (ξ : E d) : φ (A • ξ) * Complex.exp
      (Complex.I * ((∑ i : Fin d, x i * ξ i : ℝ) : ℂ)) = H (A • ξ) := by
    change φ (A • ξ) * Complex.exp
      (Complex.I * ((∑ i : Fin d, x i * ξ i : ℝ) : ℂ)) =
        φ (A • ξ) * Complex.exp
          (Complex.I * ((∑ i : Fin d, (A⁻¹ • x) i * (A • ξ) i : ℝ) : ℂ))
    rw [hdot]
  unfold inverseFourier
  congr 1
  calc
    (∫ ξ : E d, ((A ^ d : ℝ) : ℂ) * φ (A • ξ) *
        Complex.exp (Complex.I * ((∑ i : Fin d, x i * ξ i : ℝ) : ℂ))) =
        ((A ^ d : ℝ) : ℂ) * ∫ ξ : E d, H (A • ξ) := by
      rw [← integral_const_mul]
      apply integral_congr_ae
      filter_upwards [] with ξ
      rw [mul_assoc, hphase]
    _ = ((A ^ d : ℝ) : ℂ) * ((A ^ d)⁻¹ • ∫ ξ : E d, H ξ) := by
      rw [MeasureTheory.Measure.integral_comp_smul_of_nonneg volume H A
        (hR := hA.le), finrank_euclideanSpace_fin]
    _ = ∫ ξ : E d, H ξ := by
      rw [Complex.real_smul, ← mul_assoc, ← Complex.ofReal_mul,
        mul_inv_cancel₀ (pow_ne_zero _ hA.ne'), Complex.ofReal_one, one_mul]

#print axioms inverseFourier_rescale
#print axioms inverseFourierSchwartz_continuous
#print axioms schwartz_rescale
#print axioms inverseFourier_eq_mathlib_inverse
#print axioms inverseFourierSchwartz_apply
#print axioms SmoothFrequency.inverse_schwartz
#print axioms inverseFourier_real_of_even

end Bandlimited
