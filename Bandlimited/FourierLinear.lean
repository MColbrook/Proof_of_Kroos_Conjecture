module

public import Bandlimited.FourierTransport
public import Mathlib.Analysis.InnerProductSpace.Adjoint
public import Mathlib.MeasureTheory.Measure.Haar.MulEquivHaarChar

/-!
# Invertible linear transport with a strict bandwidth bound

The frequency map is the adjoint of the spatial map. The positive Haar
character supplies the exact Jacobian; no numerical integration or external
execution supports the change of variables.
-/

@[expose] public section
noncomputable section
open MeasureTheory Set
open scoped RealInnerProductSpace InnerProduct BigOperators Topology

namespace Bandlimited
namespace FourierLinear

 def adjointEquiv {d : ℕ} (U : E d ≃L[ℝ] E d) : E d ≃L[ℝ] E d :=
  ContinuousLinearEquiv.equivOfInverse' (ContinuousLinearMap.adjoint (U : E d →L[ℝ] E d))
    (ContinuousLinearMap.adjoint (U.symm : E d →L[ℝ] E d))
    (by rw [← ContinuousLinearMap.adjoint_comp,
      ContinuousLinearEquiv.coe_symm_comp_coe, ContinuousLinearMap.adjoint_id])
    (by rw [← ContinuousLinearMap.adjoint_comp,
      ContinuousLinearEquiv.coe_comp_coe_symm, ContinuousLinearMap.adjoint_id])

 theorem adjointEquiv_norm_bound {d : ℕ} (U : E d ≃L[ℝ] E d) (η : E d) :
    ‖adjointEquiv U η‖ ≤ ‖(U : E d →L[ℝ] E d)‖ * ‖η‖ := by
  change ‖(ContinuousLinearMap.adjoint (U : E d →L[ℝ] E d)) η‖ ≤ _
  have h := ((ContinuousLinearMap.adjoint (U : E d →L[ℝ] E d))).le_opNorm η
  simpa only [ContinuousLinearMap.adjoint.norm_map] using h

 theorem adjointEquiv_dot {d : ℕ} (U : E d ≃L[ℝ] E d) (x η : E d) :
    (∑ i : Fin d, x i * (adjointEquiv U η) i : ℝ) =
      ∑ i : Fin d, (U x) i * η i := by
  change (∑ i : Fin d, x i * ((ContinuousLinearMap.adjoint (U : E d →L[ℝ] E d)) η) i : ℝ) = _
  simpa only [EuclideanSpace.inner_eq_star_dotProduct, dotProduct, star_trivial,
    mul_comm, ContinuousLinearEquiv.coe_coe] using
    (U : E d →L[ℝ] E d).adjoint_inner_right x η

 def jacobian {d : ℕ} (V : E d ≃L[ℝ] E d) : NNReal :=
  addEquivAddHaarChar V.toContinuousAddEquiv

 theorem jacobian_pos {d : ℕ} (V : E d ≃L[ℝ] E d) :
    0 < (jacobian V : ℝ) := by
  exact_mod_cast addEquivAddHaarChar_pos V.toContinuousAddEquiv

 theorem integral_change {d : ℕ} (V : E d ≃L[ℝ] E d) (H : E d → ℂ) :
    (∫ ξ : E d, H ξ) = jacobian V • ∫ η : E d, H (V η) := by
  calc
    _ = ∫ ξ : E d, H ξ ∂(jacobian V • volume.map V) := by
      have hmap : jacobian V • volume.map V = (volume : Measure (E d)) := by
        simpa only [jacobian, ContinuousLinearEquiv.toContinuousAddEquiv_coe] using
          addEquivAddHaarChar_smul_map (volume : Measure (E d)) V.toContinuousAddEquiv
      rw [hmap]
    _ = jacobian V • ∫ η : E d, H (V η) := by
      rw [integral_smul_nnreal_measure]
      congr 1
      simpa only [Homeomorph.toMeasurableEquiv_coe, ContinuousLinearEquiv.coe_toHomeomorph] using
        integral_map_equiv V.toHomeomorph.toMeasurableEquiv H

 def transportedFrequency {d : ℕ} (U : E d ≃L[ℝ] E d) (φ : E d → ℂ)
    (ξ : E d) : ℂ :=
  (((jacobian (adjointEquiv U) : ℝ)⁻¹ : ℂ)) * φ ((adjointEquiv U).symm ξ)

 theorem inverseFourier_transportedFrequency {d : ℕ}
    (U : E d ≃L[ℝ] E d) (φ : E d → ℂ) (x : E d) :
    inverseFourier (transportedFrequency U φ) x = inverseFourier φ (U x) := by
  let V := adjointEquiv U
  let c : ℝ := jacobian V
  have hc : c ≠ 0 := (jacobian_pos V).ne'
  unfold inverseFourier
  congr 1
  calc
    _ = jacobian V • ∫ η : E d, transportedFrequency U φ (V η) *
        Complex.exp (Complex.I * ((∑ i : Fin d, x i * (V η) i : ℝ) : ℂ)) :=
      integral_change V _
    _ = jacobian V • (((c⁻¹ : ℝ) : ℂ) *
        ∫ η : E d, φ η * Complex.exp
          (Complex.I * ((∑ i : Fin d, (U x) i * η i : ℝ) : ℂ))) := by
      congr 1
      simp only [transportedFrequency, V, ContinuousLinearEquiv.symm_apply_apply,
        adjointEquiv_dot, mul_assoc]
      rw [integral_const_mul]
      simp only [c, V, Complex.ofReal_inv]
    _ = _ := by
      rw [NNReal.smul_def, Complex.real_smul, ← mul_assoc]
      change (c : ℂ) * ((c⁻¹ : ℝ) : ℂ) * _ = _
      rw [← Complex.ofReal_mul, mul_inv_cancel₀ hc, Complex.ofReal_one, one_mul]

 theorem transportedFrequency_smooth_of_support_image {d : ℕ} {σ : ℝ}
    (U : E d ≃L[ℝ] E d) (φ : E d → ℂ)
    (hsmooth : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) φ)
    (hcompact : HasCompactSupport φ)
    (himage : ∀ η ∈ tsupport φ, ‖adjointEquiv U η‖ < σ) :
    SmoothFrequency σ (transportedFrequency U φ) := by
  let V := adjointEquiv U
  have hcomp : HasCompactSupport (fun ξ => φ (V.symm ξ)) :=
    hcompact.comp_homeomorph V.symm.toHomeomorph
  refine ⟨contDiff_const.mul (hsmooth.comp V.symm.contDiff), hcomp.mul_left, ?_⟩
  intro ξ hξ
  have hs : ξ ∈ tsupport (fun ξ => φ (V.symm ξ)) :=
    tsupport_mul_subset_right hξ
  have hη : V.symm ξ ∈ tsupport φ :=
    tsupport_comp_subset_preimage φ V.symm.continuous hs
  have h := himage (V.symm ξ) hη
  simpa only [Metric.mem_ball, dist_zero_right, V, ContinuousLinearEquiv.apply_symm_apply] using h

 theorem SmoothFrequency.transported {d : ℕ} {δ σ : ℝ} {φ : E d → ℂ}
    (hφ : SmoothFrequency δ φ) (U : E d ≃L[ℝ] E d)
    (hbound : ‖(U : E d →L[ℝ] E d)‖ * δ < σ) :
    SmoothFrequency σ (transportedFrequency U φ) := by
  let V := adjointEquiv U
  have hcomp : HasCompactSupport (fun ξ => φ (V.symm ξ)) :=
    hφ.2.1.comp_homeomorph V.symm.toHomeomorph
  refine ⟨contDiff_const.mul (hφ.1.comp V.symm.contDiff), hcomp.mul_left, ?_⟩
  intro ξ hξ
  have hs : ξ ∈ tsupport (fun ξ => φ (V.symm ξ)) :=
    tsupport_mul_subset_right hξ
  have hη : V.symm ξ ∈ tsupport φ :=
    tsupport_comp_subset_preimage φ V.symm.continuous hs
  have hsmall : ‖V.symm ξ‖ < δ := by
    simpa only [Metric.mem_ball, dist_zero_right] using hφ.2.2 hη
  simp only [Metric.mem_ball, dist_zero_right]
  calc
    ‖ξ‖ = ‖V (V.symm ξ)‖ := by rw [V.apply_symm_apply]
    _ ≤ ‖(U : E d →L[ℝ] E d)‖ * ‖V.symm ξ‖ := adjointEquiv_norm_bound U _
    _ ≤ ‖(U : E d →L[ℝ] E d)‖ * δ :=
      mul_le_mul_of_nonneg_left hsmall.le (norm_nonneg _)
    _ < σ := hbound

end FourierLinear

 theorem InBandlimitedSpace.comp_linearEquiv {d : ℕ} {δ σ : ℝ} {F : E d → ℂ}
    (hF : InBandlimitedSpace d δ F) (U : E d ≃L[ℝ] E d)
    (hbound : ‖(U : E d →L[ℝ] E d)‖ * δ < σ) :
    InBandlimitedSpace d σ (fun x => F (U x)) := by
  by_cases hd : d = 0
  · simp only [InBandlimitedSpace, hd, ↓reduceIte] at hF ⊢
    obtain ⟨c, hc⟩ := hF
    exact ⟨c, fun x => hc (U x)⟩
  · simp only [InBandlimitedSpace, hd, ↓reduceIte] at hF ⊢
    obtain ⟨φ, hφ, rfl⟩ := hF
    refine ⟨FourierLinear.transportedFrequency U φ, FourierLinear.SmoothFrequency.transported hφ U hbound, ?_⟩
    exact funext fun x => (FourierLinear.inverseFourier_transportedFrequency U φ x).symm

#print axioms InBandlimitedSpace.comp_linearEquiv
#print axioms FourierLinear.integral_change
#print axioms FourierLinear.inverseFourier_transportedFrequency

end Bandlimited
