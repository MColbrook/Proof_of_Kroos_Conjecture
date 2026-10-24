module

public import Bandlimited.TensorDensity
public import Mathlib.Analysis.Distribution.SchwartzSpace.Basic
public import Mathlib.Topology.CompactOpen
public import Bandlimited.BoundaryUniqueness
public import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

/- Norm continuity of C₀-valued families with a common tail. -/

@[expose] public section
noncomputable section
open Set Metric
open scoped Topology ZeroAtInfty BigOperators

namespace Bandlimited
namespace C0Families

def evalLinear {d : ℕ} (x : E d) : C₀(E d, ℂ) →ₗ[ℂ] ℂ where
  toFun f := f x
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

def evalCLM {d : ℕ} (x : E d) : C₀(E d, ℂ) →L[ℂ] ℂ :=
  (evalLinear x).mkContinuous 1 (fun f => by
    change ‖f.toBCF x‖ ≤ 1 * ‖f.toBCF‖
    simpa only [one_mul] using BoundedContinuousFunction.norm_coe_le_norm f.toBCF x)

@[simp] theorem evalCLM_apply {d : ℕ} (x : E d) (f : C₀(E d, ℂ)) :
    evalCLM x f = f x := rfl

@[simp] theorem sum_apply {d : ℕ} {ι : Type*} (s : Finset ι)
    (f : ι → C₀(E d, ℂ)) (x : E d) : (∑ i ∈ s, f i) x = ∑ i ∈ s, f i x := by
  simpa only [evalCLM_apply] using map_sum (evalCLM x) f s

/-- Joint continuity and a uniform vanishing tail imply continuity in the
supremum norm. The parameter space can be arbitrary. -/
theorem continuous_of_joint_continuous_uniform_tail
    {Z : Type*} [TopologicalSpace Z] {d : ℕ}
    (F : Z → C₀(E d, ℂ))
    (hjoint : Continuous (fun p : Z × E d => F p.1 p.2))
    (htail : ∀ ε : ℝ, 0 < ε → ∃ R : ℝ, 0 ≤ R ∧
      ∀ z x, R ≤ ‖x‖ → ‖F z x‖ < ε) : Continuous F := by
  apply continuous_iff_continuousAt.mpr
  intro z₀
  show Filter.Tendsto F (𝓝 z₀) (𝓝 (F z₀))
  rw [ZeroAtInftyContinuousMap.tendsto_iff_tendstoUniformly]
  apply Metric.tendstoUniformly_iff.mpr
  intro ε hε
  obtain ⟨R, hR, htailR⟩ := htail (ε / 3) (by positivity)
  let K : Set (E d) := closedBall 0 R
  letI : CompactSpace K := isCompact_iff_compactSpace.mp (isCompact_closedBall (0 : E d) R)
  let FK (z : Z) : C(K, ℂ) :=
    ⟨fun x => F z x, (F z).continuous.comp continuous_subtype_val⟩
  have hFK : Continuous FK := by
    apply ContinuousMap.continuous_of_continuous_uncurry
    exact hjoint.comp (continuous_fst.prodMk (continuous_subtype_val.comp continuous_snd))
  have hnear := Metric.tendsto_nhds.mp (hFK.tendsto z₀) (ε / 3) (by positivity)
  filter_upwards [hnear] with z hz
  intro x
  rw [dist_comm]
  by_cases hx : ‖x‖ ≤ R
  · let xK : K := ⟨x, by simpa only [K, mem_closedBall, dist_zero_right] using hx⟩
    have hpoint := ContinuousMap.norm_coe_le_norm (FK z - FK z₀) xK
    have hpoint' : dist (F z x) (F z₀ x) ≤ dist (FK z) (FK z₀) := by
      simpa only [dist_eq_norm, FK, ContinuousMap.sub_apply, ContinuousMap.coe_mk, xK] using hpoint
    have hdist : dist (F z x) (F z₀ x) < ε / 3 := hpoint'.trans_lt hz
    linarith
  · have hxR : R ≤ ‖x‖ := (lt_of_not_ge hx).le
    calc
      dist (F z x) (F z₀ x) = ‖F z x - F z₀ x‖ := dist_eq_norm _ _
      _ ≤ ‖F z x‖ + ‖F z₀ x‖ := norm_sub_le _ _
      _ < ε / 3 + ε / 3 := add_lt_add (htailR z x hxR) (htailR z₀ x hxR)
      _ < ε := by linarith

/-- Morera upgrades pointwise holomorphy to holomorphy in the C₀ norm,
provided that norm continuity is already known. -/
theorem differentiableOn_of_evaluation {d : ℕ} (F : ℂ → C₀(E d, ℂ))
    (hF : Continuous F) (U : Set ℂ) (hU : IsOpen U)
    (hpoint : ∀ x : E d, DifferentiableOn ℂ (fun z => F z x) U) :
    DifferentiableOn ℂ F U := by
  apply (Complex.isConservativeOn_and_continuousOn_iff_isDifferentiableOn hU).mp
  refine ⟨?_, hF.continuousOn⟩
  intro z w hrect
  rw [← add_eq_zero_iff_eq_neg, Complex.wedgeIntegral_add_wedgeIntegral_eq]
  have hzlow : IntervalIntegrable (fun t : ℝ => F (t + z.im * Complex.I))
      MeasureTheory.volume z.re w.re := (hF.comp (by fun_prop)).intervalIntegrable _ _
  have hwhigh : IntervalIntegrable (fun t : ℝ => F (t + w.im * Complex.I))
      MeasureTheory.volume z.re w.re := (hF.comp (by fun_prop)).intervalIntegrable _ _
  have hwright : IntervalIntegrable (fun t : ℝ => F (w.re + t * Complex.I))
      MeasureTheory.volume z.im w.im := (hF.comp (by fun_prop)).intervalIntegrable _ _
  have hzleft : IntervalIntegrable (fun t : ℝ => F (z.re + t * Complex.I))
      MeasureTheory.volume z.im w.im := (hF.comp (by fun_prop)).intervalIntegrable _ _
  apply ZeroAtInftyContinuousMap.ext
  intro x
  change evalCLM x
    ((∫ t : ℝ in z.re..w.re, F (t + z.im * Complex.I)) -
      (∫ t : ℝ in z.re..w.re, F (t + w.im * Complex.I)) +
      Complex.I • (∫ t : ℝ in z.im..w.im, F (w.re + t * Complex.I)) -
      Complex.I • (∫ t : ℝ in z.im..w.im, F (z.re + t * Complex.I))) = 0
  simp only [map_sub, map_add, map_smul]
  rw [← (evalCLM x).intervalIntegral_comp_comm hzlow,
    ← (evalCLM x).intervalIntegral_comp_comm hwhigh,
    ← (evalCLM x).intervalIntegral_comp_comm hwright,
    ← (evalCLM x).intervalIntegral_comp_comm hzleft]
  exact Complex.integral_boundary_rect_eq_zero_of_differentiableOn
    (fun z => F z x) z w ((hpoint x).mono hrect)

#print axioms differentiableOn_of_evaluation
#print axioms continuous_of_joint_continuous_uniform_tail

end C0Families
end Bandlimited
end
