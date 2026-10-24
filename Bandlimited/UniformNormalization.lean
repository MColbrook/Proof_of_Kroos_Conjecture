module

public import Bandlimited.MaximalFrame
public import Bandlimited.BodyGeometry

/-! Uniform normalization by a maximal determinant frame. The coarse
dimension-only bounds 1/d and d suffice for the all-bodies theorem; no
regularity of the original boundary is assumed. -/

@[expose] public section
noncomputable section
open Set
open scoped BigOperators
namespace Bandlimited

def frameLinearEquiv {d : ℕ} (v : Fin d → E d)
    (hv : (frameMatrix v).det ≠ 0) : E d ≃ₗ[ℝ] E d :=
  (WithLp.linearEquiv 2 ℝ (Fin d → ℝ)).trans
    ((Matrix.toLinearEquiv (Pi.basisFun ℝ (Fin d)) (frameMatrix v)
      (isUnit_iff_ne_zero.mpr hv)).trans
        (WithLp.linearEquiv 2 ℝ (Fin d → ℝ)).symm)

theorem frameLinearEquiv_apply {d : ℕ} (v : Fin d → E d)
    (hv : (frameMatrix v).det ≠ 0) (x : E d) (i : Fin d) :
    frameLinearEquiv v hv x i = ∑ j : Fin d, v j i * x j := by
  change (Matrix.toLin (Pi.basisFun ℝ (Fin d)) (Pi.basisFun ℝ (Fin d))
    (frameMatrix v) (fun j => x j)) i = _
  rw [Matrix.toLin_eq_toLin', Matrix.toLin'_apply]
  rfl

theorem frameLinearEquiv_sum {d : ℕ} (v : Fin d → E d)
    (hv : (frameMatrix v).det ≠ 0) (x : E d) :
    frameLinearEquiv v hv x = ∑ j : Fin d, x j • v j := by
  ext i
  rw [frameLinearEquiv_apply]
  simp only [WithLp.ofLp_sum, Finset.sum_apply, PiLp.smul_apply, smul_eq_mul]
  apply Finset.sum_congr rfl
  intro j hj
  exact mul_comm _ _

theorem frameLinearEquiv_single {d : ℕ} (v : Fin d → E d)
    (hv : (frameMatrix v).det ≠ 0) (i : Fin d) :
    frameLinearEquiv v hv (PiLp.single 2 i 1) = v i := by
  rw [frameLinearEquiv_sum]
  simp [PiLp.single_apply]

def BodyNorm.compLinearEquiv {d : ℕ} (ν : BodyNorm d) (f : E d ≃ₗ[ℝ] E d) :
    BodyNorm d where
  toFun x := ν.toFun (f x)
  nonneg x := ν.nonneg (f x)
  zero_iff x := by
    rw [ν.zero_iff]
    exact f.map_eq_zero_iff
  smul a x := by rw [f.map_smul, ν.smul]
  add_le x y := by rw [f.map_add]; exact ν.add_le _ _

theorem BodyNorm.finite_sum_le {d : ℕ} (ν : BodyNorm d) {ι : Type*}
    (s : Finset ι) (x : ι → E d) :
    ν.toFun (∑ i ∈ s, x i) ≤ ∑ i ∈ s, ν.toFun (x i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [ν.map_zero]
  | @insert i s hi ih =>
    rw [Finset.sum_insert hi, Finset.sum_insert hi]
    exact (ν.add_le _ _).trans (add_le_add le_rfl ih)

theorem coordinate_norm_le_sum_abs {d : ℕ} (x : E d) :
    ‖x‖ ≤ ∑ i : Fin d, |x i| := by
  have hx : (∑ i : Fin d, PiLp.single 2 i (x i)) = x := by
    ext j
    simp
  calc
    ‖x‖ = ‖∑ i : Fin d, PiLp.single 2 i (x i)‖ := congrArg norm hx.symm
    _ ≤ ∑ i : Fin d, ‖(PiLp.single 2 i (x i) : E d)‖ := norm_sum_le _ _
    _ = ∑ i : Fin d, |x i| := by simp [PiLp.norm_single, Real.norm_eq_abs]

theorem maximal_frame_norm_bounds {d : ℕ} (hd : 1 ≤ d)
    {K : Set (E d)} (ν : BodyNorm d) (hball : normBall ν = K)
    (v : Fin d → E d) (hv : ∀ j, v j ∈ K) (hvd : (frameMatrix v).det ≠ 0)
    (hmax : ∀ w : Fin d → E d, (∀ j, w j ∈ K) →
      |(frameMatrix w).det| ≤ |(frameMatrix v).det|) :
    NormBounds (d : ℝ)⁻¹ (d : ℝ) (ν.compLinearEquiv (frameLinearEquiv v hvd)) := by
  classical
  let f := frameLinearEquiv v hvd
  have hdpos : 0 < (d : ℝ) := by exact_mod_cast (show 0 < d by omega)
  have hvi (i : Fin d) : ν.toFun (v i) ≤ 1 := by
    change v i ∈ normBall ν
    rw [hball]
    exact hv i
  intro z
  constructor
  · change (d : ℝ)⁻¹ * ‖z‖ ≤ ν.toFun (f z)
    by_cases hz : z = 0
    · simp only [hz, map_zero, ν.map_zero, norm_zero, mul_zero, le_refl]
    · let a : ℝ := ν.toFun (f z)
      have hfz : f z ≠ 0 := by
        intro h
        apply hz
        exact f.injective (by simpa only [map_zero] using h)
      have ha0 : a ≠ 0 := (ν.zero_iff _).not.mpr hfz
      have ha : 0 < a := lt_of_le_of_ne (ν.nonneg _) ha0.symm
      have hunit : ν.toFun (a⁻¹ • f z) = 1 := by
        rw [ν.smul, abs_of_pos (inv_pos.mpr ha)]
        exact inv_mul_cancel₀ ha0
      have hxK : a⁻¹ • f z ∈ K := by
        rw [← hball]
        change ν.toFun (a⁻¹ • f z) ≤ 1
        rw [hunit]
      have hrep : a⁻¹ • f z = ∑ j : Fin d, (a⁻¹ * z j) • v j := by
        rw [frameLinearEquiv_sum, Finset.smul_sum]
        simp only [smul_smul]
      have hzi (i : Fin d) : |z i| ≤ a := by
        have h := maximal_frame_coefficient_bound v hv hvd hmax
          (fun j => a⁻¹ * z j) (a⁻¹ • f z) hxK hrep i
        have hdiv : |z i| / a ≤ 1 := by
          simpa only [abs_mul, abs_inv, abs_of_pos ha, div_eq_inv_mul] using h
        simpa only [one_mul] using (div_le_iff₀ ha).mp hdiv
      have hnorm : ‖z‖ ≤ (d : ℝ) * a := by
        calc
          ‖z‖ ≤ ∑ i : Fin d, |z i| := coordinate_norm_le_sum_abs z
          _ ≤ ∑ _i : Fin d, a := Finset.sum_le_sum fun i _ => hzi i
          _ = (d : ℝ) * a := by simp
      rw [← div_eq_inv_mul]
      apply (div_le_iff₀ hdpos).2
      simpa only [mul_comm] using hnorm
  · change ν.toFun (f z) ≤ (d : ℝ) * ‖z‖
    rw [frameLinearEquiv_sum]
    calc
      ν.toFun (∑ i : Fin d, z i • v i) ≤ ∑ i : Fin d, ν.toFun (z i • v i) :=
        ν.finite_sum_le Finset.univ _
      _ ≤ ∑ i : Fin d, |z i| := by
        apply Finset.sum_le_sum
        intro i hi
        rw [ν.smul]
        simpa only [mul_one] using mul_le_mul_of_nonneg_left (hvi i) (abs_nonneg (z i))
      _ ≤ ∑ _i : Fin d, ‖z‖ := Finset.sum_le_sum fun i _ => by
        simpa only [Real.norm_eq_abs] using PiLp.norm_apply_le (p := 2) z i
      _ = (d : ℝ) * ‖z‖ := by simp

theorem symmetric_body_uniform_normalization {d : ℕ} (hd : 1 ≤ d)
    {K : Set (E d)} (hK : IsSymmetricConvexBody K) :
    ∃ f : E d ≃ₗ[ℝ] E d, ∃ ν : BodyNorm d,
      NormBounds (d : ℝ)⁻¹ (d : ℝ) ν ∧ normBall ν = f ⁻¹' K := by
  obtain ⟨ν, α, β, hα, hαβ, hν, hball⟩ := symmetric_body_as_norm_ball hK
  obtain ⟨v, hv, hvd, hmax⟩ := maximal_frame_exists hK
  refine ⟨frameLinearEquiv v hvd, ν.compLinearEquiv (frameLinearEquiv v hvd),
    maximal_frame_norm_bounds hd ν hball v hv hvd hmax, ?_⟩
  ext x
  change ν.toFun (frameLinearEquiv v hvd x) ≤ 1 ↔ frameLinearEquiv v hvd x ∈ K
  change frameLinearEquiv v hvd x ∈ normBall ν ↔ _
  rw [hball]

#print axioms frameLinearEquiv_apply
#print axioms maximal_frame_norm_bounds
#print axioms symmetric_body_uniform_normalization

end Bandlimited
end
