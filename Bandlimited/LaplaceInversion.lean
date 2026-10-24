module

public import Bandlimited.LaplaceC0
public import Mathlib.Analysis.Distribution.SchwartzSpace.Fourier
public import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

/- Fourier inversion for the C₀-valued Laplace family. -/

@[expose] public section
noncomputable section
open Set MeasureTheory
open scoped Topology ZeroAtInfty FourierTransform RealInnerProductSpace

namespace Bandlimited
namespace WeightedDensity

set_option maxHeartbeats 80000

 theorem laplaceC0_uniform_bound (q : SchwartzMap (E 1) ℂ) (c M : ℝ)
    (hc : 0 < c) (hM : 0 ≤ M) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ z : ℂ, ‖laplaceC0 q c M hc hM z‖ ≤ C := by
  let m : ℕ := ⌈M⌉₊
  let C : ℝ := (2 : ℝ) ^ m * ((Finset.Iic (m, 0)).sup
    (fun i => SchwartzMap.seminorm ℂ i.1 i.2)) q
  have hC : 0 ≤ C := by dsimp [C]; positivity
  refine ⟨C, hC, fun z => ?_⟩
  change ‖(laplaceC0 q c M hc hM z).toBCF‖ ≤ C
  apply (BoundedContinuousFunction.norm_le hC).mpr
  intro x
  exact (laplaceFunction_norm_le q c M hc z x).trans
    (gaussian_weight_schwartz_bound (by norm_num) hM (Nat.le_ceil M) q x)

 def weightedSchwartzProduct (q h : SchwartzMap (E 1) ℂ) (c M : ℝ)
    (hc : 0 < c) (hM : 0 ≤ M) : C₀(E 1, ℂ) :=
  weightedC0Map (schwartz_oneSided_weightedC0
    (SchwartzMap.pairing (.mul ℂ ℂ) q h) c M hc hM)

 @[simp] theorem weightedSchwartzProduct_apply (q h : SchwartzMap (E 1) ℂ)
    (c M : ℝ) (hc : 0 < c) (hM : 0 ≤ M) (x : E 1) :
    weightedSchwartzProduct q h c M hc hM x =
      (oneSidedWeight c M (x 0) : ℂ) * (q x * h x) := rfl

 def inversionIntegrand (q h : SchwartzMap (E 1) ℂ) (c M : ℝ)
    (hc : 0 < c) (hM : 0 ≤ M) (ξ : E 1) : C₀(E 1, ℂ) :=
  (𝓕 h) ξ • laplaceC0 q c M hc hM ((-(2 * Real.pi) * ξ 0 : ℝ) : ℂ)

 theorem inversionIntegrand_integrable (q h : SchwartzMap (E 1) ℂ) (c M : ℝ)
    (hc : 0 < c) (hM : 0 ≤ M) :
    Integrable (inversionIntegrand q h c M hc hM) := by
  obtain ⟨C, hC, hbound⟩ := laplaceC0_uniform_bound q c M hc hM
  have hcont : Continuous (inversionIntegrand q h c M hc hM) := by
    unfold inversionIntegrand
    have hcoord : Continuous (fun ξ : E 1 => ξ 0) :=
      PiLp.continuous_apply 2 (fun _ : Fin 1 => ℝ) 0
    exact (𝓕 h).continuous.smul ((laplaceC0_continuous q c M hc hM).comp
      (Complex.continuous_ofReal.comp (continuous_const.mul hcoord)))
  apply (((𝓕 h).integrable (μ := volume)).norm.mul_const C).mono' hcont.aestronglyMeasurable
  filter_upwards [] with ξ
  unfold inversionIntegrand
  rw [norm_smul]
  exact mul_le_mul_of_nonneg_left (hbound _) (norm_nonneg _)

 theorem inversionIntegrand_apply (q h : SchwartzMap (E 1) ℂ) (c M : ℝ)
    (hc : 0 < c) (hM : 0 ≤ M) (ξ x : E 1) :
    inversionIntegrand q h c M hc hM ξ x =
      ((oneSidedWeight c M (x 0) : ℂ) * q x) *
      (Complex.exp ((↑(2 * Real.pi * ⟪ξ, x⟫) : ℂ) * Complex.I) * (𝓕 h) ξ) := by
  have hclip : clippedParameter c ((-(2 * Real.pi) * ξ 0 : ℝ) : ℂ) =
      ((-(2 * Real.pi) * ξ 0 : ℝ) : ℂ) :=
    clippedParameter_eq c _ (by simp) (by simpa using hc.le)
  simp only [inversionIntegrand, ZeroAtInftyContinuousMap.smul_apply, smul_eq_mul,
    laplaceC0_apply, laplaceFunction, hclip]
  have hphase : -Complex.I * ((-(2 * Real.pi) * ξ 0 : ℝ) : ℂ) * (x 0 : ℂ) =
      (↑(2 * Real.pi * ⟪ξ, x⟫) : ℂ) * Complex.I := by
    simp only [EuclideanSpace.inner_eq_star_dotProduct, dotProduct, Fin.sum_univ_one,
      star_trivial, Complex.ofReal_mul, Complex.ofReal_neg]
    ring
  rw [hphase]
  ring

 theorem weightedSchwartzProduct_eq_integral (q h : SchwartzMap (E 1) ℂ) (c M : ℝ)
    (hc : 0 < c) (hM : 0 ≤ M) :
    weightedSchwartzProduct q h c M hc hM =
      ∫ ξ : E 1, inversionIntegrand q h c M hc hM ξ := by
  apply ZeroAtInftyContinuousMap.ext
  intro x
  have hi := (C0Families.evalCLM x).integral_comp_comm
    (inversionIntegrand_integrable q h c M hc hM)
  change weightedSchwartzProduct q h c M hc hM x =
    (C0Families.evalCLM x) (∫ ξ : E 1, inversionIntegrand q h c M hc hM ξ)
  rw [← hi]
  simp only [C0Families.evalCLM_apply, inversionIntegrand_apply]
  rw [integral_const_mul]
  have hInv : (∫ ξ : E 1,
      Complex.exp ((↑(2 * Real.pi * ⟪ξ, x⟫) : ℂ) * Complex.I) * (𝓕 h) ξ) = h x := by
    have h := congrArg (fun f : SchwartzMap (E 1) ℂ => f x)
      (FourierTransform.fourierInv_fourier_eq (F := SchwartzMap (E 1) ℂ) h)
    rw [SchwartzMap.fourierInv_coe, Real.fourierInv_eq'] at h
    simpa only [smul_eq_mul] using h
  rw [hInv, weightedSchwartzProduct_apply]
  ring

 theorem functional_zero_weightedSchwartzProduct
    (q h : SchwartzMap (E 1) ℂ) (c M : ℝ) (hc : 0 < c) (hM : 0 ≤ M)
    (ℓ : C₀(E 1, ℂ) →L[ℂ] ℂ)
    (hz : ∀ t : ℝ, ℓ (laplaceC0 q c M hc hM (t : ℂ)) = 0) :
    ℓ (weightedSchwartzProduct q h c M hc hM) = 0 := by
  rw [weightedSchwartzProduct_eq_integral, ← ℓ.integral_comp_comm
    (inversionIntegrand_integrable q h c M hc hM)]
  have heq : (fun ξ : E 1 => ℓ (inversionIntegrand q h c M hc hM ξ)) = 0 := by
    funext ξ
    simp only [inversionIntegrand, map_smul, hz, smul_zero, Pi.zero_apply]
  rw [heq]
  exact integral_zero' (E 1) ℂ

#print axioms inversionIntegrand_integrable
#print axioms weightedSchwartzProduct_eq_integral
#print axioms functional_zero_weightedSchwartzProduct

end WeightedDensity
end Bandlimited
end
