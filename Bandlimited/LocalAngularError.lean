module

public import Bandlimited.LocalAngularGaussian

/-! A quantitative local angular comparison. All geometric inputs below are
exact identities or norm bounds proved from the supporting chart; the error
constant is uniform over norms and centres. -/

@[expose] public section
noncomputable section
open scoped RealInnerProductSpace
namespace Bandlimited

theorem local_angular_gaussian_error {d : ℕ} (u v : Sphere d) (t : E d)
    (ℓ : E d →L[ℝ] ℝ) (a₀ D M N A : ℝ)
    (hD : 0 ≤ D) (hM : 0 ≤ M) (hN : 0 < N) (hA : 0 < A)
    (ht : inner ℝ (v : E d) t = 0)
    (hB : ‖supportProjection (v : E d) ℓ a₀ t‖ ≤ (1 + D) * ‖t‖)
    (hℓ : |ℓ t / a₀| ≤ D * ‖t‖)
    (hcentral : ‖N • t‖ ≤ M) (hlarge : 2 * (1 + D) * M ≤ N)
    (hu : (u : E d) = ‖(v : E d) + supportProjection (v : E d) ℓ a₀ t‖⁻¹ •
      ((v : E d) + supportProjection (v : E d) ℓ a₀ t)) :
    |Real.exp (-((N ^ 2 / A ^ 2) * (rho u v) ^ 2)) - gaussian A (N • t)| ≤
      12 * (1 + D) * M ^ 3 / (N * A ^ 2) := by
  let w := (v : E d) + supportProjection (v : E d) ℓ a₀ t
  let c := 1 - ℓ t / a₀
  let den := ‖w‖ * (‖w‖ + c)
  have hNt : ‖N • t‖ = N * ‖t‖ := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos hN]
  have htM : ‖t‖ ≤ M / N := by
    apply (le_div_iff₀ hN).2
    rw [hNt] at hcentral
    nlinarith
  have hsmall : (1 + D) * ‖t‖ ≤ 1 / 2 := by
    have h := mul_le_mul_of_nonneg_left htM (show 0 ≤ 1 + D by linarith)
    have hfrac : (1 + D) * (M / N) ≤ 1 / 2 := by
      rw [← mul_div_assoc]
      apply (div_le_iff₀ hN).2
      nlinarith
    exact h.trans hfrac
  have hcabs : |c - 1| ≤ D * ‖t‖ := by
    simpa only [c, sub_sub_cancel_left, abs_neg] using hℓ
  have hwabs : |‖w‖ - 1| ≤ (1 + D) * ‖t‖ := by
    have hnorm := abs_norm_sub_norm_le w (v : E d)
    rw [sphere_norm] at hnorm
    have hsub : w - (v : E d) = supportProjection (v : E d) ℓ a₀ t := by
      dsimp [w]
      abel
    rw [hsub] at hnorm
    exact hnorm.trans hB
  have hden := chart_denominator_ratio_bound hD (norm_nonneg t) hsmall hwabs hcabs
  have hden0 : 0 < den := hden.1
  have hratio : |2 / den - 1| ≤ 12 * (1 + D) * ‖t‖ := hden.2
  have hc : 0 < c := by
    have h := abs_le.mp hcabs
    have hdr : D * ‖t‖ ≤ (1 + D) * ‖t‖ := by nlinarith [norm_nonneg t]
    linarith
  have hgeo := projective_chart_denominator u v t ℓ a₀ ht hc hu
  change (rho u v) ^ 2 * den = 2 * ‖t‖ ^ 2 at hgeo
  have hsq : ‖N • t‖ ^ 2 = N ^ 2 * ‖t‖ ^ 2 := by rw [hNt, mul_pow]
  have hfactor : N ^ 2 * (rho u v) ^ 2 - ‖N • t‖ ^ 2 =
      ‖N • t‖ ^ 2 * (2 / den - 1) := by
    have hfrac : (rho u v) ^ 2 = (2 * ‖t‖ ^ 2) / den :=
      (eq_div_iff hden0.ne').2 hgeo
    rw [hfrac, hsq]
    ring
  have hquad : |N ^ 2 * (rho u v) ^ 2 - ‖N • t‖ ^ 2| ≤
      12 * (1 + D) * M ^ 3 / N := by
    rw [hfactor, abs_mul, abs_of_nonneg (sq_nonneg _)]
    calc
      ‖N • t‖ ^ 2 * |2 / den - 1| ≤
          M ^ 2 * (12 * (1 + D) * (M / N)) := by
        apply mul_le_mul (pow_le_pow_left₀ (norm_nonneg _) hcentral 2)
          (hratio.trans (mul_le_mul_of_nonneg_left htM (by positivity)))
          (abs_nonneg _) (sq_nonneg M)
      _ = 12 * (1 + D) * M ^ 3 / N := by ring
  have hexp := exp_neg_arguments_lipschitz
    (show 0 ≤ (N ^ 2 / A ^ 2) * (rho u v) ^ 2 by positivity)
    (show 0 ≤ ‖N • t‖ ^ 2 / A ^ 2 by positivity)
  unfold gaussian
  rw [neg_div]
  apply hexp.trans
  have hid : (N ^ 2 / A ^ 2) * (rho u v) ^ 2 - ‖N • t‖ ^ 2 / A ^ 2 =
      (N ^ 2 * (rho u v) ^ 2 - ‖N • t‖ ^ 2) / A ^ 2 := by ring
  rw [hid, abs_div, abs_of_pos (sq_pos_of_pos hA)]
  calc
    |N ^ 2 * (rho u v) ^ 2 - ‖N • t‖ ^ 2| / A ^ 2 ≤
        (12 * (1 + D) * M ^ 3 / N) / A ^ 2 :=
      div_le_div_of_nonneg_right hquad (sq_nonneg A)
    _ = 12 * (1 + D) * M ^ 3 / (N * A ^ 2) := by ring

#print axioms local_angular_gaussian_error

end Bandlimited
end
