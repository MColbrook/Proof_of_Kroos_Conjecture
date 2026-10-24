module

public import Bandlimited.AngularGeometry

/-! Uniform height and angular separation estimates for a supporting
functional on a norm sphere. These are the geometric hypotheses used in
the small-height part of the Gaussian-kernel construction. -/

@[expose] public section
noncomputable section
open Set
namespace Bandlimited

def supportingHeight {d : ℕ} (ν : BodyNorm d) (ℓ : E d →L[ℝ] ℝ)
    (u : Sphere d) : ℝ := ℓ (u : E d) / ν.toFun (u : E d)

theorem supportingHeight_abs_le {d : ℕ} (ν : BodyNorm d)
    (ℓ : E d →L[ℝ] ℝ) {α β : ℝ} (hα : 0 < α)
    (hν : NormBounds α β ν) (hℓ : ∀ x, |ℓ x| ≤ ν.toFun x)
    (u : Sphere d) : |supportingHeight ν ℓ u| ≤ 1 := by
  have hnu : 0 < ν.toFun (u : E d) :=
    hα.trans_le (by simpa only [sphere_norm, mul_one] using (hν (u : E d)).1)
  rw [supportingHeight, abs_div, abs_of_pos hnu]
  exact (div_le_one hnu).2 (hℓ _)

theorem supportingHeight_lipschitz {d : ℕ} (ν : BodyNorm d)
    (ℓ : E d →L[ℝ] ℝ) {α β : ℝ} (hα : 0 < α) (hαβ : α ≤ β)
    (hν : NormBounds α β ν) (hℓ : ∀ x, |ℓ x| ≤ ν.toFun x)
    (hnℓ : ‖ℓ‖ ≤ β) (u w : Sphere d) :
    |supportingHeight ν ℓ u - supportingHeight ν ℓ w| ≤
      (2 * (β / α)) * ‖(u : E d) - (w : E d)‖ := by
  have hβ : 0 ≤ β := (hα.trans_le hαβ).le
  have hnu : α ≤ ν.toFun (u : E d) := by simpa only [sphere_norm, mul_one] using (hν (u : E d)).1
  have hnw : α ≤ ν.toFun (w : E d) := by simpa only [sphere_norm, mul_one] using (hν (w : E d)).1
  have hnu0 : 0 < ν.toFun (u : E d) := hα.trans_le hnu
  have hnw0 : 0 < ν.toFun (w : E d) := hα.trans_le hnw
  have halg : supportingHeight ν ℓ u - supportingHeight ν ℓ w =
      (ℓ ((u : E d) - (w : E d)) + supportingHeight ν ℓ w *
        (ν.toFun (w : E d) - ν.toFun (u : E d))) / ν.toFun (u : E d) := by
    simp only [supportingHeight, map_sub]
    field_simp
    <;> ring
  have hell : |ℓ ((u : E d) - (w : E d))| ≤ β * ‖(u : E d) - (w : E d)‖ := by
    exact (show |ℓ ((u : E d) - (w : E d))| ≤ ‖ℓ‖ * ‖(u : E d) - (w : E d)‖ by
      simpa only [Real.norm_eq_abs] using ℓ.le_opNorm ((u : E d) - (w : E d))).trans
      (mul_le_mul_of_nonneg_right hnℓ (norm_nonneg _))
  have hnorm : |ν.toFun (w : E d) - ν.toFun (u : E d)| ≤
      β * ‖(u : E d) - (w : E d)‖ := by
    rw [abs_sub_comm]
    exact (ν.abs_sub_le _ _).trans (hν _).2
  rw [halg, abs_div, abs_of_pos hnu0]
  calc
    |ℓ ((u : E d) - (w : E d)) + supportingHeight ν ℓ w *
        (ν.toFun (w : E d) - ν.toFun (u : E d))| / ν.toFun (u : E d) ≤
      (|ℓ ((u : E d) - (w : E d))| + |supportingHeight ν ℓ w| *
        |ν.toFun (w : E d) - ν.toFun (u : E d)|) / ν.toFun (u : E d) := by
      gcongr
      simpa only [abs_mul] using abs_add_le (ℓ ((u : E d) - (w : E d)))
        (supportingHeight ν ℓ w * (ν.toFun (w : E d) - ν.toFun (u : E d)))
    _ ≤ (β * ‖(u : E d) - (w : E d)‖ + β * ‖(u : E d) - (w : E d)‖) /
        ν.toFun (u : E d) := by
      apply div_le_div_of_nonneg_right _ hnu0.le
      exact add_le_add hell (by
        calc
          |supportingHeight ν ℓ w| * |ν.toFun (w : E d) - ν.toFun (u : E d)| ≤
              1 * |ν.toFun (w : E d) - ν.toFun (u : E d)| :=
            mul_le_mul_of_nonneg_right (supportingHeight_abs_le ν ℓ hα hν hℓ w) (abs_nonneg _)
          _ ≤ β * ‖(u : E d) - (w : E d)‖ := by simpa only [one_mul] using hnorm)
    _ ≤ (β * ‖(u : E d) - (w : E d)‖ + β * ‖(u : E d) - (w : E d)‖) / α :=
      div_le_div_of_nonneg_left (by positivity) hα hnu
    _ = _ := by ring

def sphereNeg {d : ℕ} (v : Sphere d) : Sphere d :=
  ⟨-(v : E d), by simpa only [Metric.mem_sphere, dist_zero_right, norm_neg] using v.property⟩

theorem supportingHeight_separation {d : ℕ} (ν : BodyNorm d)
    (ℓ : E d →L[ℝ] ℝ) {α β : ℝ} (hα : 0 < α) (hαβ : α ≤ β)
    (hν : NormBounds α β ν) (hℓ : ∀ x, |ℓ x| ≤ ν.toFun x)
    (hnℓ : ‖ℓ‖ ≤ β) (v u : Sphere d)
    (hv : ℓ (v : E d) = ν.toFun (v : E d))
    (hu : |supportingHeight ν ℓ u| ≤ 1 / 2) :
    (4 * (β / α))⁻¹ ≤ rho u v := by
  have hβ : 0 < β := hα.trans_le hαβ
  have hD : 0 < β / α := div_pos hβ hα
  have hv0 : 0 < ν.toFun (v : E d) :=
    hα.trans_le (by simpa only [sphere_norm, mul_one] using (hν (v : E d)).1)
  have hhv : supportingHeight ν ℓ v = 1 := by
    simp only [supportingHeight, hv, div_self hv0.ne']
  have hhnv : supportingHeight ν ℓ (sphereNeg v) = -1 := by
    simp only [supportingHeight, sphereNeg, map_neg, ν.map_neg, hv, neg_div,
      div_self hv0.ne']
  have hu' := abs_le.mp hu
  have hplus := supportingHeight_lipschitz ν ℓ hα hαβ hν hℓ hnℓ u v
  have hminus := supportingHeight_lipschitz ν ℓ hα hαβ hν hℓ hnℓ u (sphereNeg v)
  rw [hhv] at hplus
  rw [hhnv] at hminus
  have hp : 1 / 2 ≤ (2 * (β / α)) * ‖(u : E d) - (v : E d)‖ := by
    have := neg_le_abs (supportingHeight ν ℓ u - 1)
    linarith
  have hm : 1 / 2 ≤ (2 * (β / α)) * ‖(u : E d) + (v : E d)‖ := by
    change |supportingHeight ν ℓ u - -1| ≤
      (2 * (β / α)) * ‖(u : E d) - -(v : E d)‖ at hminus
    simp only [sub_neg_eq_add] at hminus
    have := le_abs_self (supportingHeight ν ℓ u + 1)
    linarith
  apply le_min
  · rw [← one_div]
    apply (div_le_iff₀ (by positivity : (0 : ℝ) < 4 * (β / α))).2
    nlinarith
  · rw [← one_div]
    apply (div_le_iff₀ (by positivity : (0 : ℝ) < 4 * (β / α))).2
    nlinarith

#print axioms supportingHeight_separation
#print axioms supportingHeight_abs_le
#print axioms supportingHeight_lipschitz

end Bandlimited
end
