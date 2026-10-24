module

public import Bandlimited.Definitions
public import Mathlib.Analysis.Complex.HasPrimitives
public import Mathlib.Analysis.Complex.ReImTopology
public import Mathlib.Analysis.Analytic.IsolatedZeros
public import Mathlib.Tactic.LinearCombination

/-!
Boundary uniqueness prerequisites for one-sided weighted density.
The gluing argument uses the rectangle Cauchy theorem and Morera's theorem.
-/

@[expose] public section
noncomputable section
open Complex Set MeasureTheory Metric
open scoped Topology Interval

namespace Bandlimited
namespace BoundaryUniqueness

def rectangleIntegral (f : ℂ → ℂ) (z w : ℂ) : ℂ :=
  (∫ t : ℝ in z.re..w.re, f (t + z.im * I)) -
  (∫ t : ℝ in z.re..w.re, f (t + w.im * I)) +
  I * (∫ t : ℝ in z.im..w.im, f (w.re + t * I)) -
  I * (∫ t : ℝ in z.im..w.im, f (z.re + t * I))

theorem rectangleIntegral_zero_off_axis (f : ℂ → ℂ) (U : Set ℂ)
    (hc : ContinuousOn f U)
    (hd : ∀ q ∈ U, q.im ≠ 0 → DifferentiableAt ℂ f q)
    (z w : ℂ) (hrect : Rectangle z w ⊆ U)
    (hnocross : ¬ (min z.im w.im < 0 ∧ 0 < max z.im w.im)) :
    rectangleIntegral f z w = 0 := by
  apply integral_boundary_rect_eq_zero_of_continuousOn_of_differentiableOn f z w
    (hc.mono hrect)
  intro q hq
  have hqrect : q ∈ Rectangle z w :=
    ⟨⟨hq.1.1.le, hq.1.2.le⟩, ⟨hq.2.1.le, hq.2.2.le⟩⟩
  apply (hd q (hrect hqrect) ?_).differentiableWithinAt
  intro hzero
  apply hnocross
  have hqi : min z.im w.im < q.im ∧ q.im < max z.im w.im := hq.2
  rwa [hzero] at hqi

theorem rectangleIntegral_symm (f : ℂ → ℂ) (z w : ℂ) :
    rectangleIntegral f z w = rectangleIntegral f w z := by
  simp only [rectangleIntegral, intervalIntegral.integral_symm w.re z.re,
    intervalIntegral.integral_symm w.im z.im]
  ring

theorem vertical_intervalIntegrable (f : ℂ → ℂ) (U : Set ℂ)
    (hc : ContinuousOn f U) (z w : ℂ) (hrect : Rectangle z w ⊆ U)
    (k : ℝ) (hk : k ∈ [[z.re, w.re]]) :
    IntervalIntegrable (fun y : ℝ => f (k + y * I)) volume z.im w.im := by
  have hp : ContinuousOn (fun y : ℝ => f (k + y * I)) [[z.im, w.im]] := by
    apply (hc.mono hrect).comp (by fun_prop)
    intro y hy
    change ((k : ℂ) + y * I) ∈ Rectangle z w
    change ((k : ℂ) + y * I).re ∈ [[z.re, w.re]] ∧
      ((k : ℂ) + y * I).im ∈ [[z.im, w.im]]
    simpa using And.intro hk hy
  exact hp.intervalIntegrable

theorem rectangleIntegral_split_horizontal (f : ℂ → ℂ) (z w : ℂ)
    (hzero : 0 ∈ [[z.im, w.im]])
    (hz : IntervalIntegrable (fun y : ℝ => f (z.re + y * I)) volume z.im w.im)
    (hw : IntervalIntegrable (fun y : ℝ => f (w.re + y * I)) volume z.im w.im) :
    rectangleIntegral f z w =
      rectangleIntegral f z (w.re : ℂ) + rectangleIntegral f (z.re : ℂ) w := by
  have hzw := intervalIntegral.integral_add_adjacent_intervals
    (hz.mono_set (uIcc_subset_uIcc_left hzero))
    (hz.mono_set (uIcc_subset_uIcc_right hzero))
  have hww := intervalIntegral.integral_add_adjacent_intervals
    (hw.mono_set (uIcc_subset_uIcc_left hzero))
    (hw.mono_set (uIcc_subset_uIcc_right hzero))
  simp only [rectangleIntegral, Complex.ofReal_re, Complex.ofReal_im]
  rw [← hzw, ← hww]
  ring

theorem rectangleIntegral_zero_cross (f : ℂ → ℂ) (U : Set ℂ)
    (hc : ContinuousOn f U)
    (hd : ∀ q ∈ U, q.im ≠ 0 → DifferentiableAt ℂ f q)
    (z w : ℂ) (hrect : Rectangle z w ⊆ U) (hz : z.im < 0) (hw : 0 < w.im) :
    rectangleIntegral f z w = 0 := by
  have hzw : z.im ≤ w.im := by linarith
  have hzero : 0 ∈ [[z.im, w.im]] := by rw [uIcc_of_le hzw]; exact ⟨hz.le, hw.le⟩
  have hlow : Rectangle z (w.re : ℂ) ⊆ Rectangle z w := by
    intro q hq
    refine ⟨by simpa only [Complex.ofReal_re] using hq.1, ?_⟩
    apply uIcc_subset_uIcc_left hzero
    simpa only [Complex.ofReal_im, Set.mem_preimage] using hq.2
  have hupp : Rectangle (z.re : ℂ) w ⊆ Rectangle z w := by
    intro q hq
    refine ⟨by simpa only [Complex.ofReal_re] using hq.1, ?_⟩
    apply uIcc_subset_uIcc_right hzero
    simpa only [Complex.ofReal_im, Set.mem_preimage] using hq.2
  have hl := rectangleIntegral_zero_off_axis f U hc hd z (w.re : ℂ)
    (hlow.trans hrect) (by simp [max_eq_right hz.le])
  have hu := rectangleIntegral_zero_off_axis f U hc hd (z.re : ℂ) w
    (hupp.trans hrect) (by simp [min_eq_left hw.le])
  rw [rectangleIntegral_split_horizontal f z w hzero
    (vertical_intervalIntegrable f U hc z w hrect z.re left_mem_uIcc)
    (vertical_intervalIntegrable f U hc z w hrect w.re right_mem_uIcc), hl, hu, add_zero]

theorem differentiableOn_of_continuousOn_off_real (f : ℂ → ℂ) (U : Set ℂ)
    (hU : IsOpen U) (hc : ContinuousOn f U)
    (hd : ∀ q ∈ U, q.im ≠ 0 → DifferentiableAt ℂ f q) :
    DifferentiableOn ℂ f U := by
  apply (Complex.isConservativeOn_and_continuousOn_iff_isDifferentiableOn hU).mp
  refine ⟨?_, hc⟩
  intro z w hrect
  rw [← add_eq_zero_iff_eq_neg, Complex.wedgeIntegral_add_wedgeIntegral_eq]
  change rectangleIntegral f z w = 0
  by_cases hcross : min z.im w.im < 0 ∧ 0 < max z.im w.im
  · by_cases hzw : z.im ≤ w.im
    · exact rectangleIntegral_zero_cross f U hc hd z w hrect
        (by simpa only [min_eq_left hzw] using hcross.1)
        (by simpa only [max_eq_right hzw] using hcross.2)
    · rw [rectangleIntegral_symm]
      have hle : w.im ≤ z.im := le_of_not_ge hzw
      apply rectangleIntegral_zero_cross f U hc hd w z
      · simpa only [Rectangle, uIcc_comm] using hrect
      · simpa only [min_eq_right hle] using hcross.1
      · simpa only [max_eq_left hle] using hcross.2
  · exact rectangleIntegral_zero_off_axis f U hc hd z w hrect hcross

def zeroExtension (H : ℂ → ℂ) (z : ℂ) : ℂ := if 0 ≤ z.im then H z else 0

theorem zeroExtension_continuousOn_ball
    (H : ℂ → ℂ) (a c r : ℝ) (hra : r ≤ a) (hrc : r ≤ c)
    (hc : ContinuousOn H {z : ℂ | 0 ≤ z.im ∧ z.im < c})
    (hz : ∀ t : ℝ, |t| < a → H (t : ℂ) = 0) :
    ContinuousOn (zeroExtension H) (ball 0 r) := by
  classical
  have hclosed : IsClosed {z : ℂ | 0 ≤ z.im} := isClosed_le continuous_const continuous_im
  change ContinuousOn (fun z : ℂ => if 0 ≤ z.im then H z else 0) (ball 0 r)
  apply ContinuousOn.if
  · intro z hzb
    have him : 0 = z.im := frontier_le_subset_eq continuous_const continuous_im hzb.2
    have hreal : (z.re : ℂ) = z := Complex.ext (by simp) (by simpa using him)
    have hnorm : ‖z‖ < r := by simpa only [mem_ball, dist_zero_right] using hzb.1
    have habs : |z.re| < a := (Complex.abs_re_le_norm z).trans_lt (hnorm.trans_le hra)
    simpa only [hreal] using hz z.re habs
  · apply hc.mono
    intro z hzb
    have hpos : 0 ≤ z.im := by simpa only [hclosed.closure_eq, Set.mem_ofPred_eq] using hzb.2
    have hnorm : ‖z‖ < r := by simpa only [mem_ball, dist_zero_right] using hzb.1
    refine ⟨hpos, ?_⟩
    exact (le_abs_self z.im).trans_lt ((Complex.abs_im_le_norm z).trans_lt (hnorm.trans_le hrc))
  · exact continuousOn_const

theorem zeroExtension_zero_ball
    (H : ℂ → ℂ) (a c r : ℝ) (hr : 0 < r) (hra : r ≤ a) (hrc : r ≤ c)
    (hc : ContinuousOn H {z : ℂ | 0 ≤ z.im ∧ z.im < c})
    (hd : DifferentiableOn ℂ H {z : ℂ | 0 < z.im ∧ z.im < c})
    (hz : ∀ t : ℝ, |t| < a → H (t : ℂ) = 0) :
    EqOn (zeroExtension H) 0 (ball 0 r) := by
  have hcG := zeroExtension_continuousOn_ball H a c r hra hrc hc hz
  have hopen : IsOpen {z : ℂ | 0 < z.im ∧ z.im < c} :=
    (isOpen_lt continuous_const continuous_im).inter (isOpen_lt continuous_im continuous_const)
  have hdiff : DifferentiableOn ℂ (zeroExtension H) (ball 0 r) := by
    apply differentiableOn_of_continuousOn_off_real _ _ isOpen_ball hcG
    intro z hzb hzne
    have hnorm : ‖z‖ < r := by simpa only [mem_ball, dist_zero_right] using hzb
    rcases lt_or_gt_of_ne hzne with hneg | hpos
    · have heq : zeroExtension H =ᶠ[𝓝 z] (fun _ => (0 : ℂ)) := by
        filter_upwards [(isOpen_lt continuous_im continuous_const).mem_nhds hneg] with w hw
        simp only [zeroExtension, ite_eq_right hw.not_ge]
      exact heq.differentiableAt_iff.mpr (differentiableAt_const 0)
    · have heq : zeroExtension H =ᶠ[𝓝 z] H := by
        filter_upwards [(isOpen_lt continuous_const continuous_im).mem_nhds hpos] with w hw
        simp only [zeroExtension, ite_eq_left hw.le]
      have hzs : z ∈ {z : ℂ | 0 < z.im ∧ z.im < c} :=
        ⟨hpos, (le_abs_self z.im).trans_lt
          ((Complex.abs_im_le_norm z).trans_lt (hnorm.trans_le hrc))⟩
      exact heq.differentiableAt_iff.mpr (hd.differentiableAt (hopen.mem_nhds hzs))
  let z₀ : ℂ := (-(r / 2) : ℝ) • I
  have hz₀im : z₀.im = -(r / 2) := by simp [z₀]
  have hz₀norm : ‖z₀‖ = r / 2 := by
    dsimp [z₀]
    rw [norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs, abs_neg,
      abs_of_pos (by positivity : 0 < r / 2)]
  have hz₀ball : z₀ ∈ ball 0 r := by
    rw [mem_ball, dist_zero_right, hz₀norm]
    linarith
  have hz₀neg : z₀.im < 0 := by rw [hz₀im]; linarith
  have hevent : zeroExtension H =ᶠ[𝓝 z₀] 0 := by
    filter_upwards [(isOpen_lt continuous_im continuous_const).mem_nhds hz₀neg] with z hzneg
    simp only [zeroExtension, ite_eq_right hzneg.not_ge, Pi.zero_apply]
  exact (hdiff.analyticOnNhd isOpen_ball).eqOn_zero_of_preconnected_of_eventuallyEq_zero
    (convex_ball (0 : ℂ) r).isPreconnected hz₀ball hevent

theorem strip_zero_of_zero_boundary_interval
    (H : ℂ → ℂ) (a c : ℝ) (ha : 0 < a) (hcpos : 0 < c)
    (hc : ContinuousOn H {z : ℂ | 0 ≤ z.im ∧ z.im < c})
    (hd : DifferentiableOn ℂ H {z : ℂ | 0 < z.im ∧ z.im < c})
    (hz : ∀ t : ℝ, |t| < a → H (t : ℂ) = 0) :
    EqOn H 0 {z : ℂ | 0 < z.im ∧ z.im < c} := by
  let r : ℝ := min a c
  have hr : 0 < r := lt_min ha hcpos
  have hra : r ≤ a := min_le_left _ _
  have hrc : r ≤ c := min_le_right _ _
  have hball := zeroExtension_zero_ball H a c r hr hra hrc hc hd hz
  let z₁ : ℂ := (r / 2 : ℝ) • I
  have hz₁im : z₁.im = r / 2 := by simp [z₁]
  have hz₁norm : ‖z₁‖ = r / 2 := by
    dsimp [z₁]
    rw [norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (by positivity : 0 < r / 2)]
  have hz₁ball : z₁ ∈ ball 0 r := by
    rw [mem_ball, dist_zero_right, hz₁norm]
    linarith
  have hz₁s : z₁ ∈ {z : ℂ | 0 < z.im ∧ z.im < c} := by
    rw [mem_ofPred_eq, hz₁im]
    constructor <;> linarith
  have hopen : IsOpen {z : ℂ | 0 < z.im ∧ z.im < c} :=
    (isOpen_lt continuous_const continuous_im).inter (isOpen_lt continuous_im continuous_const)
  have hconv : Convex ℝ {z : ℂ | 0 < z.im ∧ z.im < c} := by
    change Convex ℝ (Complex.imCLM ⁻¹' Ioo (0 : ℝ) c)
    exact (convex_Ioo (0 : ℝ) c).linear_preimage Complex.imCLM.toLinearMap
  have hevent : H =ᶠ[𝓝 z₁] 0 := by
    filter_upwards [isOpen_ball.mem_nhds hz₁ball, hopen.mem_nhds hz₁s] with z hzb hzs
    have hg := hball hzb
    simpa only [zeroExtension, ite_eq_left hzs.1.le] using hg
  exact (hd.analyticOnNhd hopen).eqOn_zero_of_preconnected_of_eventuallyEq_zero
    hconv.isPreconnected hz₁s hevent

theorem real_zero_of_zero_boundary_interval
    (H : ℂ → ℂ) (a c : ℝ) (ha : 0 < a) (hcpos : 0 < c)
    (hc : ContinuousOn H {z : ℂ | 0 ≤ z.im ∧ z.im < c})
    (hd : DifferentiableOn ℂ H {z : ℂ | 0 < z.im ∧ z.im < c})
    (hz : ∀ t : ℝ, |t| < a → H (t : ℂ) = 0) :
    ∀ t : ℝ, H (t : ℂ) = 0 := by
  have heq := strip_zero_of_zero_boundary_interval H a c ha hcpos hc hd hz
  let S : Set ℂ := {z : ℂ | 0 < z.im ∧ z.im < c}
  intro t
  have htcl : (t : ℂ) ∈ closure S := by
    change (t : ℂ) ∈ closure (Complex.im ⁻¹' Ioo (0 : ℝ) c)
    rw [Complex.closure_preimage_im, closure_Ioo (ne_of_lt hcpos)]
    simpa only [mem_preimage, Complex.ofReal_im, mem_Icc, le_refl, true_and] using hcpos.le
  have hcont : ContinuousOn H (insert (t : ℂ) S) := by
    apply hc.mono
    intro z hzmem
    rcases mem_insert_iff.mp hzmem with rfl | hzs
    · simp only [mem_ofPred_eq, Complex.ofReal_im, le_refl, true_and]
      exact hcpos
    · exact ⟨hzs.1.le, hzs.2⟩
  have hsub : insert (t : ℂ) S ⊆ closure S := by
    intro z hzmem
    rcases mem_insert_iff.mp hzmem with rfl | hzs
    · exact htcl
    · exact subset_closure hzs
  have hboundary := heq.of_subset_closure hcont continuousOn_const
    (subset_insert (t : ℂ) S) hsub
  exact hboundary (mem_insert (t : ℂ) S)

#print axioms differentiableOn_of_continuousOn_off_real
#print axioms zeroExtension_zero_ball
#print axioms strip_zero_of_zero_boundary_interval
#print axioms real_zero_of_zero_boundary_interval

end BoundaryUniqueness
end Bandlimited
end
