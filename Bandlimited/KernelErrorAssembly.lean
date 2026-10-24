module
public import Bandlimited.KernelScalarEstimates
public import Bandlimited.KernelWeights
public import Bandlimited.ConvexGaussianErrors
@[expose] public section
noncomputable section
namespace Bandlimited
namespace KernelEstimates

 theorem central_real_error (w w₀ B τ G₀ δ a q R G H T J : ℝ) (F : ℂ) (N : ℕ)
    (hw : 0 ≤ w) (hw₀ : 0 ≤ w₀) (hB : 0 ≤ B) (hτ : 0 ≤ τ) (hG₀ : 0 ≤ G₀)
    (hwbound : w ≤ B * w₀) (hr : 1 ≤ a ^ N * Real.exp q)
    (hrδ : a ^ N * Real.exp q - 1 ≤ δ)
    (herr : w₀ * ‖(Real.exp (-q) : ℂ) * F - (G : ℂ)‖ ≤ τ)
    (hG : w₀ * ‖(G : ℂ)‖ ≤ G₀)
    (hTaylor : w * |R - a ^ N * F.re| ≤ T)
    (hangle : w * |G - H| ≤ J) :
    w * |R - H| ≤ T + B * (τ + δ * (G₀ + τ)) + J := by
  let r := a ^ N * Real.exp q
  have heq : (r : ℂ) * ((Real.exp (-q) : ℂ) * F) = (a ^ N : ℝ) * F := by
    rw [← mul_assoc, ← Complex.ofReal_mul]
    have hc : r * Real.exp (-q) = a ^ N := by
      dsimp [r]
      rw [mul_assoc, ← Real.exp_add, add_neg_cancel, Real.exp_zero, mul_one]
    rw [hc]
  have hc := central_ratio_weighted_error w₀ τ G₀ r
    ((Real.exp (-q) : ℂ) * F) (G : ℂ) hw₀ hτ hG₀ hr herr hG
  rw [heq] at hc
  have hRe : |a ^ N * F.re - G| ≤ ‖(a ^ N : ℝ) * F - (G : ℂ)‖ := by
    simpa only [Complex.sub_re, Complex.mul_re, Complex.ofReal_re,
      Complex.ofReal_im, zero_mul, sub_zero] using
      Complex.abs_re_le_norm ((a ^ N : ℝ) * F - (G : ℂ))
  have hc' : w₀ * |a ^ N * F.re - G| ≤ τ + δ * (G₀ + τ) :=
    (mul_le_mul_of_nonneg_left hRe hw₀).trans
      (hc.trans (by dsimp [r] at *; nlinarith [mul_le_mul_of_nonneg_right hrδ (by linarith : 0 ≤ G₀ + τ)]))
  have hm := mul_le_mul_of_nonneg_left hc' hB
  have hm' := mul_le_mul_of_nonneg_right hwbound (abs_nonneg (a ^ N * F.re - G))
  have ht : |R - H| ≤ |R - a ^ N * F.re| + |a ^ N * F.re - G| + |G - H| := by
    have h₁ := norm_add_le (R - a ^ N * F.re) (a ^ N * F.re - G)
    have h₂ := norm_add_le (R - G) (G - H)
    simp only [Real.norm_eq_abs] at h₁ h₂
    have heq₁ : R - a ^ N * F.re + (a ^ N * F.re - G) = R - G := by ring
    have heq₂ : R - G + (G - H) = R - H := by ring
    rw [heq₁] at h₁
    rw [heq₂] at h₂
    linarith
  have ht' := mul_le_mul_of_nonneg_left ht hw
  nlinarith

 theorem outer_real_error (w w₀ B a R H T J : ℝ) (F : ℂ) (N : ℕ)
    (hw : 0 ≤ w) (hw₀ : 0 ≤ w₀) (hB : 0 ≤ B) (ha : 0 ≤ a ^ N)
    (ha1 : a ^ N ≤ 1) (hH : 0 ≤ H) (hwbound : w ≤ B * w₀)
    (hTaylor : w * |R - a ^ N * F.re| ≤ T)
    (htail : w₀ * (‖F‖ + H) ≤ J) :
    w * |R - H| ≤ T + B * J := by
  have hR : |a ^ N * F.re| ≤ ‖F‖ := by
    rw [abs_mul, abs_of_nonneg ha]
    exact (mul_le_mul_of_nonneg_left (Complex.abs_re_le_norm F) ha).trans
      (by nlinarith [norm_nonneg F])
  have ht : |R - H| ≤ |R - a ^ N * F.re| + ‖F‖ + H := by
    have h := abs_add_le (R - a ^ N * F.re) (a ^ N * F.re - H)
    have h' := norm_sub_le (a ^ N * F.re) H
    simp only [Real.norm_eq_abs, abs_of_nonneg hH] at h'
    have heq : R - a ^ N * F.re + (a ^ N * F.re - H) = R - H := by ring
    rw [heq] at h
    linarith
  have h₁ := mul_le_mul_of_nonneg_left ht hw
  have h₂ := mul_le_mul_of_nonneg_right hwbound (by positivity : 0 ≤ ‖F‖ + H)
  have h₃ := mul_le_mul_of_nonneg_left htail hB
  nlinarith

#print axioms central_real_error
#print axioms outer_real_error
end KernelEstimates
end Bandlimited
end
