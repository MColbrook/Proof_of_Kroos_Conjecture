module

public import Bandlimited.SphericalCaps

/-! Gaussian spherical integrals: lower cap bound and kernel-proved polynomial domination. -/
@[expose] public section
open scoped BigOperators
open MeasureTheory Set
noncomputable section
namespace Bandlimited.SphereQuadrature

def gaussianLowerConstant (s : ℕ) : ℝ := Real.exp (-1) * capLowerConstant s

theorem gaussianLowerConstant_pos (s : ℕ) : 0 < gaussianLowerConstant s :=
  mul_pos (Real.exp_pos _) (capLowerConstant_pos s)

theorem sphericalGaussianIntegral_lower (s : ℕ) (lam : ℝ) (hlam : 1 ≤ lam)
    (u : Sphere (s + 1)) :
    gaussianLowerConstant s * (lam ^ s)⁻¹ ≤ sphericalGaussianIntegral s lam u := by
  classical
  have hlp : 0 < lam := by linarith
  let G : C(Sphere (s + 1) × Sphere (s + 1), ℝ) :=
    ⟨fun p => gaussianKernel lam p.1 p.2, continuous_gaussianKernel lam⟩
  have hint : Integrable (gaussianKernel lam u) (surfaceMeasure s) :=
    (G.curry u).continuous.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  let S : Set (Sphere (s + 1)) := projectiveBall u (1 / lam)
  let Rho : C(Sphere (s + 1) × Sphere (s + 1), ℝ) :=
    ⟨fun p => rho p.1 p.2, continuous_rho⟩
  have hS : MeasurableSet S := measurableSet_lt (Rho.curry u).continuous.measurable measurable_const
  have hpoint (v : Sphere (s + 1)) :
      S.indicator (fun _ => Real.exp (-1)) v ≤ gaussianKernel lam u v := by
    by_cases hv : v ∈ S
    · rw [indicator_of_mem hv]
      have hsmall : rho u v * lam < 1 := (lt_div_iff₀ hlp).mp hv
      have hnonneg : 0 ≤ lam * rho u v := mul_nonneg hlp.le (rho_nonneg u v)
      have hsq : (lam * rho u v) ^ 2 ≤ 1 := by nlinarith
      apply Real.exp_le_exp.mpr
      nlinarith
    · rw [indicator_of_notMem hv]
      exact (Real.exp_pos _).le
  have hmono := integral_mono ((integrable_const (Real.exp (-1))).indicator hS) hint hpoint
  rw [integral_indicator hS, integral_const] at hmono
  simp only [measureReal_restrict_apply_univ, smul_eq_mul] at hmono
  have hr : 0 < 1 / lam := div_pos zero_lt_one hlp
  have hr1 : 1 / lam ≤ 1 := (div_le_iff₀ hlp).mpr (by linarith)
  have hcap := mul_le_mul_of_nonneg_left (projectiveBall_lower s u hr hr1) (Real.exp_pos (-1)).le
  calc
    gaussianLowerConstant s * (lam ^ s)⁻¹ =
        Real.exp (-1) * (capLowerConstant s * (1 / lam) ^ s) := by
      unfold gaussianLowerConstant
      simp only [one_div, inv_pow]
      ring
    _ ≤ Real.exp (-1) * (surfaceMeasure s).real S := hcap
    _ ≤ sphericalGaussianIntegral s lam u := by
      unfold sphericalGaussianIntegral
      convert hmono using 1; ring

def gaussianPolynomialConstant (n : ℕ) : ℝ := (2 : ℝ) ^ n * (n.factorial : ℝ)

theorem gaussianPolynomialConstant_pos (n : ℕ) : 0 < gaussianPolynomialConstant n := by
  unfold gaussianPolynomialConstant
  positivity

/-- Polynomial domination uses the kernel-proved exponential series bound. -/
theorem gaussian_polynomial_domination (n : ℕ) {t : ℝ} (ht : 0 ≤ t) :
    Real.exp (-t ^ 2) ≤ gaussianPolynomialConstant n * (1 + t) ^ (-(n : ℝ)) := by
  have hbase : 0 < 1 + t := by linarith
  have hfact : (0 : ℝ) < (n.factorial : ℝ) := by positivity
  have hfact1 : (1 : ℝ) ≤ (n.factorial : ℝ) := by
    have hn : 1 ≤ n.factorial := Nat.succ_le_iff.mpr (Nat.factorial_pos n)
    exact_mod_cast hn
  have hbound : Real.exp (-t ^ 2) * (1 + t) ^ n ≤ gaussianPolynomialConstant n := by
    by_cases ht1 : t ≤ 1
    · have hp : (1 + t) ^ n ≤ (2 : ℝ) ^ n := pow_le_pow_left₀ (by positivity) (by linarith) n
      have he : Real.exp (-t ^ 2) ≤ 1 := Real.exp_le_one_iff.mpr (by nlinarith [sq_nonneg t])
      calc
        Real.exp (-t ^ 2) * (1 + t) ^ n ≤ 1 * (2 : ℝ) ^ n :=
          mul_le_mul he hp (pow_nonneg hbase.le _) (by norm_num)
        _ ≤ gaussianPolynomialConstant n := by
          unfold gaussianPolynomialConstant
          nlinarith [pow_nonneg (by norm_num : (0 : ℝ) ≤ 2) n]
    · have ht1 : 1 ≤ t := le_of_not_ge ht1
      have hp : t ^ n ≤ Real.exp t * (n.factorial : ℝ) :=
        (div_le_iff₀ hfact).mp (Real.pow_div_factorial_le_exp t ht n)
      have he : Real.exp t ≤ Real.exp (t ^ 2) := Real.exp_le_exp.mpr (by nlinarith)
      have hp' : t ^ n ≤ (n.factorial : ℝ) * Real.exp (t ^ 2) := by
        have hm := mul_le_mul_of_nonneg_right he hfact.le
        nlinarith
      have htwo : (1 + t) ^ n ≤ (2 : ℝ) ^ n * t ^ n := by
        rw [← mul_pow]
        exact pow_le_pow_left₀ (by positivity) (by linarith) n
      have hdom : (1 + t) ^ n ≤ gaussianPolynomialConstant n * Real.exp (t ^ 2) := by
        apply htwo.trans
        unfold gaussianPolynomialConstant
        have hm := mul_le_mul_of_nonneg_left hp' (pow_nonneg (by norm_num : (0 : ℝ) ≤ 2) n)
        nlinarith
      calc
        Real.exp (-t ^ 2) * (1 + t) ^ n ≤
            Real.exp (-t ^ 2) * (gaussianPolynomialConstant n * Real.exp (t ^ 2)) :=
          mul_le_mul_of_nonneg_left hdom (Real.exp_pos _).le
        _ = gaussianPolynomialConstant n := by
          rw [mul_left_comm, ← Real.exp_add]
          simp
  rw [Real.rpow_neg hbase.le, Real.rpow_natCast, ← div_eq_mul_inv]
  exact (le_div_iff₀ (pow_pos hbase n)).mpr hbound

#print axioms sphericalGaussianIntegral_lower
#print axioms gaussian_polynomial_domination
end Bandlimited.SphereQuadrature
end
