module

public import Bandlimited.WeightedSchwartz
public import Bandlimited.WeightedDensityDual
public import Bandlimited.C0Families

/- Weighted Fourier–Laplace families in the actual C₀ supremum norm. -/

@[expose] public section
noncomputable section
open Set
open scoped Topology ZeroAtInfty

namespace Bandlimited
namespace WeightedDensity

def clippedParameter (c : ℝ) (z : ℂ) : ℂ :=
  (z.re : ℂ) + Complex.I * ((max 0 (min c z.im) : ℝ) : ℂ)

theorem clippedParameter_continuous (c : ℝ) : Continuous (clippedParameter c) := by
  unfold clippedParameter
  fun_prop

theorem clippedParameter_im (c : ℝ) (z : ℂ) :
    (clippedParameter c z).im = max 0 (min c z.im) := by
  simp [clippedParameter]

theorem clippedParameter_eq (c : ℝ) (z : ℂ) (h0 : 0 ≤ z.im) (hc : z.im ≤ c) :
    clippedParameter c z = z := by
  simp only [clippedParameter, min_eq_right hc, max_eq_right h0]
  exact Complex.ext (by simp) (by simp)

theorem clippedParameter_height (c : ℝ) (hc : 0 < c) (z : ℂ) :
    0 ≤ (clippedParameter c z).im ∧ (clippedParameter c z).im ≤ c := by
  rw [clippedParameter_im]
  exact ⟨le_max_left _ _, max_le hc.le (min_le_left _ _)⟩

def laplaceFunction (q : SchwartzMap (E 1) ℂ) (c M : ℝ) (z : ℂ) (x : E 1) : ℂ :=
  (oneSidedWeight c M (x 0) : ℂ) * q x *
    Complex.exp (-Complex.I * clippedParameter c z * (x 0 : ℂ))

theorem laplaceFunction_norm_le (q : SchwartzMap (E 1) ℂ)
    (c M : ℝ) (hc : 0 < c) (z : ℂ) (x : E 1) :
    ‖laplaceFunction q c M z x‖ ≤ gaussianWeight 1 M x * ‖q x‖ := by
  have hy := clippedParameter_height c hc z
  have hexponent : (clippedParameter c z).im * x 0 - c * max (x 0) 0 ≤ 0 := by
    by_cases hx : 0 ≤ x 0
    · rw [max_eq_left hx]
      nlinarith [mul_le_mul_of_nonneg_right hy.2 hx]
    · rw [max_eq_right (le_of_not_ge hx)]
      nlinarith [mul_nonpos_of_nonneg_of_nonpos hy.1 (le_of_not_ge hx)]
  have hreal : (-Complex.I * clippedParameter c z * (x 0 : ℂ)).re =
      (clippedParameter c z).im * x 0 := by simp [Complex.mul_re, Complex.mul_im]
  rw [laplaceFunction, norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (oneSidedWeight_positive c M (x 0)), Complex.norm_exp, hreal]
  calc
    oneSidedWeight c M (x 0) * ‖q x‖ *
        Real.exp ((clippedParameter c z).im * x 0) =
      (1 + |x 0|) ^ M * ‖q x‖ *
        Real.exp ((clippedParameter c z).im * x 0 - c * max (x 0) 0) := by
      rw [sub_eq_add_neg, Real.exp_add]
      unfold oneSidedWeight
      ring
    _ ≤ (1 + |x 0|) ^ M * ‖q x‖ * 1 := by
      apply mul_le_mul_of_nonneg_left (Real.exp_le_one_iff.mpr hexponent)
      positivity
    _ = gaussianWeight 1 M x * ‖q x‖ := by
      simp only [mul_one, gaussianWeight, div_one, norm_one_dimensional]

theorem laplaceFunction_joint_continuous (q : SchwartzMap (E 1) ℂ) (c M : ℝ) :
    Continuous (fun p : ℂ × E 1 => laplaceFunction q c M p.1 p.2) := by
  unfold laplaceFunction
  have hc : Continuous (clippedParameter c) := clippedParameter_continuous c
  have hW := oneSidedWeight_continuous c M
  have hx : Continuous (fun p : ℂ × E 1 => p.2 0) :=
    (PiLp.continuous_apply 2 (fun _ : Fin 1 => ℝ) 0).comp continuous_snd
  have hweight := Complex.continuous_ofReal.comp (hW.comp hx)
  have hq : Continuous (fun p : ℂ × E 1 => q p.2) :=
    q.continuous.comp continuous_snd
  have hz : Continuous (fun p : ℂ × E 1 => clippedParameter c p.1) :=
    hc.comp continuous_fst
  have ht := Complex.continuous_ofReal.comp hx
  exact (hweight.mul hq).mul (Complex.continuous_exp.comp ((continuous_const.mul hz).mul ht))

def laplaceC0 (q : SchwartzMap (E 1) ℂ) (c M : ℝ) (hc : 0 < c)
    (hM : 0 ≤ M) (z : ℂ) : C₀(E 1, ℂ) where
  toFun := laplaceFunction q c M z
  continuous_toFun := (laplaceFunction_joint_continuous q c M).comp
    (continuous_const.prodMk continuous_id)
  zero_at_infty' := TensorDensity.vanishesAtInfinity_tendsto ⟨
    (laplaceFunction_joint_continuous q c M).comp (continuous_const.prodMk continuous_id),
    fun ε hε => by
      obtain ⟨R, hR, ht⟩ := schwartz_real_weight_tail q M hM ε hε
      exact ⟨R, (by linarith), fun x hx =>
        (laplaceFunction_norm_le q c M hc z x).trans_lt (ht x hx)⟩⟩

@[simp] theorem laplaceC0_apply (q : SchwartzMap (E 1) ℂ) (c M : ℝ)
    (hc : 0 < c) (hM : 0 ≤ M) (z : ℂ) (x : E 1) :
    laplaceC0 q c M hc hM z x = laplaceFunction q c M z x := rfl

theorem laplaceC0_continuous (q : SchwartzMap (E 1) ℂ) (c M : ℝ)
    (hc : 0 < c) (hM : 0 ≤ M) : Continuous (laplaceC0 q c M hc hM) := by
  apply C0Families.continuous_of_joint_continuous_uniform_tail
  · exact laplaceFunction_joint_continuous q c M
  · intro ε hε
    obtain ⟨R, hR, ht⟩ := schwartz_real_weight_tail q M hM ε hε
    exact ⟨R, (by linarith), fun z x hx =>
      (laplaceFunction_norm_le q c M hc z x).trans_lt (ht x hx)⟩

theorem laplaceC0_differentiableOn (q : SchwartzMap (E 1) ℂ) (c M : ℝ)
    (hc : 0 < c) (hM : 0 ≤ M) :
    DifferentiableOn ℂ (laplaceC0 q c M hc hM) {z : ℂ | 0 < z.im ∧ z.im < c} := by
  have hU : IsOpen {z : ℂ | 0 < z.im ∧ z.im < c} :=
    (isOpen_lt continuous_const Complex.continuous_im).inter
      (isOpen_lt Complex.continuous_im continuous_const)
  apply C0Families.differentiableOn_of_evaluation _ (laplaceC0_continuous q c M hc hM) _ hU
  intro x
  have hfun : Set.EqOn (fun z => laplaceC0 q c M hc hM z x)
      (fun z => (oneSidedWeight c M (x 0) : ℂ) * q x *
        Complex.exp (-Complex.I * z * (x 0 : ℂ))) {z : ℂ | 0 < z.im ∧ z.im < c} := by
    intro z hz
    simp only [laplaceC0_apply, laplaceFunction, clippedParameter_eq c z hz.1.le hz.2.le]
  exact (by fun_prop : Differentiable ℂ (fun z : ℂ =>
    (oneSidedWeight c M (x 0) : ℂ) * q x * Complex.exp (-Complex.I * z * (x 0 : ℂ)))).differentiableOn.congr hfun

/-- A vanishing interval of real modulations determines every real modulation
for each continuous functional on the weighted C₀ family. -/
theorem laplaceC0_real_zero (q : SchwartzMap (E 1) ℂ) (c M a : ℝ)
    (hc : 0 < c) (hM : 0 ≤ M) (ha : 0 < a)
    (ℓ : C₀(E 1, ℂ) →L[ℂ] ℂ)
    (hz : ∀ t : ℝ, |t| < a → ℓ (laplaceC0 q c M hc hM (t : ℂ)) = 0) :
    ∀ t : ℝ, ℓ (laplaceC0 q c M hc hM (t : ℂ)) = 0 := by
  apply BoundaryUniqueness.real_zero_of_zero_boundary_interval
    (fun z => ℓ (laplaceC0 q c M hc hM z)) a c ha hc
  · exact (ℓ.continuous.comp (laplaceC0_continuous q c M hc hM)).continuousOn
  · exact ℓ.differentiable.comp_differentiableOn (laplaceC0_differentiableOn q c M hc hM)
  · exact hz

#print axioms laplaceC0_continuous
#print axioms laplaceC0_differentiableOn
#print axioms laplaceC0_real_zero

end WeightedDensity
end Bandlimited
end
