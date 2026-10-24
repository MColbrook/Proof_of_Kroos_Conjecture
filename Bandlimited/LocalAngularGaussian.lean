module

public import Bandlimited.ChartAngularBounds

/-! Local angular Gaussian comparison. The scalar exponential estimate is
proved from its ordered power-series lower bound; no numerical execution
or unproved Taylor estimate is used. -/

@[expose] public section
noncomputable section
namespace Bandlimited
open scoped RealInnerProductSpace

theorem exp_neg_arguments_lipschitz {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    |Real.exp (-a) - Real.exp (-b)| ≤ |a - b| := by
  have hord (a b : ℝ) (ha : 0 ≤ a) (hab : a ≤ b) :
      Real.exp (-a) - Real.exp (-b) ≤ b - a := by
    have hid : Real.exp (-a) - Real.exp (-b) =
        Real.exp (-a) * (1 - Real.exp (a - b)) := by
      have hexp : Real.exp (-b) = Real.exp (-a) * Real.exp (a - b) := by
        rw [← Real.exp_add]
        congr 1
        ring
      rw [hexp]
      ring
    rw [hid]
    have he : Real.exp (-a) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
    have hs : 1 - Real.exp (a - b) ≤ b - a := by
      linarith [Real.add_one_le_exp (a - b)]
    calc
      Real.exp (-a) * (1 - Real.exp (a - b)) ≤ Real.exp (-a) * (b - a) :=
        mul_le_mul_of_nonneg_left hs (Real.exp_pos _).le
      _ ≤ 1 * (b - a) := mul_le_mul_of_nonneg_right he (sub_nonneg.mpr hab)
      _ = b - a := one_mul _
  rcases le_total a b with hab | hba
  · have he : Real.exp (-b) ≤ Real.exp (-a) := Real.exp_le_exp.mpr (by linarith)
    rw [abs_of_nonneg (sub_nonneg.mpr he), abs_of_nonpos (sub_nonpos.mpr hab)]
    linarith [hord a b ha hab]
  · have he : Real.exp (-a) ≤ Real.exp (-b) := Real.exp_le_exp.mpr (by linarith)
    rw [abs_of_nonpos (sub_nonpos.mpr he), abs_of_nonneg (sub_nonneg.mpr hba)]
    linarith [hord b a hb hba]

theorem orthogonalResidual_inner {d : ℕ} (v z : E d) (hv : ‖v‖ = 1) :
    inner ℝ v (orthogonalResidual v z) = 0 := by
  simp only [orthogonalResidual, inner_sub_right, inner_smul_right,
    real_inner_self_eq_norm_sq, hv]
  ring

theorem supportingChart_orthogonal {d : ℕ} (v z : E d)
    (ℓ : E d →L[ℝ] ℝ) (a₀ : ℝ) (hv : ‖v‖ = 1) :
    inner ℝ v (supportingChart v z ℓ a₀) = 0 := by
  rw [supportingChart, inner_smul_right, orthogonalResidual_inner v z hv, mul_zero]

theorem supportingChart_direction {d : ℕ} (ν : BodyNorm d)
    (ℓ : E d →L[ℝ] ℝ) {α β : ℝ} (hα : 0 < α) (hν : NormBounds α β ν)
    (u v : Sphere d) (hv : ℓ (v : E d) = ν.toFun (v : E d))
    (ha : 0 < ℓ (radial ν u)) :
    let t := supportingChart (v : E d) (radial ν u) ℓ (ν.toFun (v : E d))
    let w := (v : E d) + supportProjection (v : E d) ℓ (ν.toFun (v : E d)) t
    (u : E d) = ‖w‖⁻¹ • w := by
  let a₀ := ν.toFun (v : E d)
  let a := ℓ (radial ν u)
  let t := supportingChart (v : E d) (radial ν u) ℓ a₀
  let w := (v : E d) + supportProjection (v : E d) ℓ a₀ t
  let c := ν.toFun (u : E d) * (a / a₀)
  have ha₀ : 0 < a₀ := ν.sphere_value_pos hα hν v
  have hnu := ν.sphere_value_pos hα hν u
  have hc : 0 < c := mul_pos hnu (div_pos ha ha₀)
  have hu : (u : E d) = c • w := by
    have hrad := supportingChart_identity (v : E d) (radial ν u) ℓ ha₀.ne' ha.ne' hv
    calc
      (u : E d) = ν.toFun (u : E d) • radial ν u := by
        simp only [radial, smul_smul, mul_inv_cancel₀ hnu.ne', one_smul]
      _ = ν.toFun (u : E d) • ((a / a₀) • w) := congrArg (fun z => ν.toFun (u : E d) • z) hrad
      _ = c • w := by rw [smul_smul]
  have hnorm : c * ‖w‖ = 1 := by
    have h := congrArg norm hu
    rw [sphere_norm, norm_smul, Real.norm_eq_abs, abs_of_pos hc] at h
    exact h.symm
  have hw : ‖w‖ ≠ 0 := by intro hz; rw [hz, mul_zero] at hnorm; norm_num at hnorm
  have hc' : c = ‖w‖⁻¹ := by
    apply mul_left_cancel₀ hw
    rw [mul_inv_cancel₀ hw]
    nlinarith [hnorm]
  change (u : E d) = ‖w‖⁻¹ • w
  simpa only [hc'] using hu

/-- Rationalizing the projective chord formula gives an exact quadratic
identity. The positivity of the longitudinal coefficient is explicit. -/
theorem projective_chart_denominator {d : ℕ} (u v : Sphere d) (t : E d)
    (ℓ : E d →L[ℝ] ℝ) (a₀ : ℝ)
    (ht : inner ℝ (v : E d) t = 0)
    (hc : 0 < 1 - ℓ t / a₀)
    (hu : (u : E d) = ‖(v : E d) + supportProjection (v : E d) ℓ a₀ t‖⁻¹ •
      ((v : E d) + supportProjection (v : E d) ℓ a₀ t)) :
    let w := (v : E d) + supportProjection (v : E d) ℓ a₀ t
    (rho u v) ^ 2 * (‖w‖ * (‖w‖ + (1 - ℓ t / a₀))) = 2 * ‖t‖ ^ 2 := by
  let c := 1 - ℓ t / a₀
  let w := (v : E d) + supportProjection (v : E d) ℓ a₀ t
  change 0 < c at hc
  have hwrep : w = c • (v : E d) + t := by
    dsimp [w, c]
    rw [supportProjection_apply, sub_smul, one_smul]
    abel
  have hinner : inner ℝ (v : E d) w = c := by
    rw [hwrep, inner_add_right, inner_smul_right, ht, real_inner_self_eq_norm_sq, sphere_norm]
    ring
  have hsq : ‖w‖ ^ 2 = c ^ 2 + ‖t‖ ^ 2 := by
    rw [hwrep, norm_add_sq_real, real_inner_smul_left, ht, norm_smul,
      Real.norm_eq_abs, sphere_norm, mul_one, sq_abs]
    ring
  have hw : 0 < ‖w‖ := by
    have hn := norm_nonneg w
    nlinarith [sq_nonneg ‖t‖]
  have hui : inner ℝ (v : E d) (u : E d) = c / ‖w‖ := by
    rw [hu, inner_smul_right, hinner]
    ring
  have hr := rho_sq_inner u v
  rw [hui, abs_of_pos (div_pos hc hw)] at hr
  change (rho u v) ^ 2 * (‖w‖ * (‖w‖ + c)) = 2 * ‖t‖ ^ 2
  have hmul : (rho u v) ^ 2 * ‖w‖ = 2 * ‖w‖ - 2 * c := by
    have h := hr
    field_simp [hw.ne'] at h
    nlinarith [h]
  calc
    (rho u v) ^ 2 * (‖w‖ * (‖w‖ + c)) =
        ((rho u v) ^ 2 * ‖w‖) * (‖w‖ + c) := by ring
    _ = (2 * ‖w‖ - 2 * c) * (‖w‖ + c) := by rw [hmul]
    _ = 2 * ‖t‖ ^ 2 := by nlinarith [hsq]

/-- A denominator near its unit-chart value gives a uniform relative error.
All constants are explicit and independent of the norm and centre. -/
theorem chart_denominator_ratio_bound {D r w c : ℝ} (hD : 0 ≤ D) (hr : 0 ≤ r)
    (hsmall : (1 + D) * r ≤ 1 / 2)
    (hw : |w - 1| ≤ (1 + D) * r) (hc : |c - 1| ≤ D * r) :
    0 < w * (w + c) ∧ |2 / (w * (w + c)) - 1| ≤ 12 * (1 + D) * r := by
  have hw' := abs_le.mp hw
  have hc' := abs_le.mp hc
  have hdr : D * r ≤ (1 + D) * r := by nlinarith
  have hwlow : 1 / 2 ≤ w := by linarith
  have hclow : 1 / 2 ≤ c := by linarith
  have hwhigh : w ≤ 3 / 2 := by linarith
  have hchigh : c ≤ 3 / 2 := by linarith
  have hden : 1 / 2 ≤ w * (w + c) := by
    have h := mul_le_mul hwlow (show (1 : ℝ) ≤ w + c by linarith)
      (by norm_num : (0 : ℝ) ≤ 1) (by linarith : 0 ≤ w)
    nlinarith
  have hden0 : 0 < w * (w + c) := by linarith
  have hwabs : |w| ≤ 2 := by rw [abs_of_nonneg (by linarith)]; linarith
  have hwpabs : |w + 1| ≤ 3 := by rw [abs_of_nonneg (by linarith)]; linarith
  have hpoly : |w * (w + c) - 2| ≤ 6 * (1 + D) * r := by
    calc
      |w * (w + c) - 2| = |((w - 1) * (w + 1) + w * (c - 1)) + (w - 1)| := by
        congr 1
        ring
      _ ≤ |(w - 1) * (w + 1) + w * (c - 1)| + |w - 1| := abs_add_le _ _
      _ ≤ |w - 1| * |w + 1| + |w| * |c - 1| + |w - 1| := by
        have h := abs_add_le ((w - 1) * (w + 1)) (w * (c - 1))
        simp only [abs_mul] at h
        linarith
      _ ≤ ((1 + D) * r) * 3 + 2 * (D * r) + (1 + D) * r := by
        gcongr
      _ ≤ 6 * (1 + D) * r := by nlinarith
  refine ⟨hden0, ?_⟩
  have hid : 2 / (w * (w + c)) - 1 = (2 - w * (w + c)) / (w * (w + c)) := by
    field_simp [hden0.ne']
    <;> ring
  rw [hid, abs_div, abs_of_pos hden0, abs_sub_comm]
  calc
    |w * (w + c) - 2| / (w * (w + c)) ≤
      (6 * (1 + D) * r) / (w * (w + c)) :=
        div_le_div_of_nonneg_right hpoly hden0.le
    _ ≤ 12 * (1 + D) * r := by
      apply (div_le_iff₀ hden0).2
      have h := mul_le_mul_of_nonneg_left hden (show 0 ≤ 12 * (1 + D) * r by positivity)
      nlinarith

#print axioms chart_denominator_ratio_bound
#print axioms supportingChart_direction
#print axioms projective_chart_denominator
#print axioms exp_neg_arguments_lipschitz

end Bandlimited
end
