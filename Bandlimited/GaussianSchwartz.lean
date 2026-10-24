module

public import Bandlimited.Definitions
public import Mathlib.Analysis.Distribution.SchwartzSpace.Basic
public import Mathlib.Analysis.SpecialFunctions.SmoothTransition
public import Mathlib.Analysis.SpecialFunctions.ExpDeriv
public import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas

/-!
Gaussian membership in Schwartz space. A scalar smooth extension of exp(-bt)
from the nonnegative half-line is a Schwartz function; proper polynomial
composition with the squared Euclidean norm gives the multivariate Gaussian.
-/

@[expose] public section
noncomputable section
open Set Filter
open scoped Topology ContDiff

namespace Bandlimited
namespace GaussianSchwartz

def expExtension (b t : ℝ) : ℝ :=
  Real.smoothTransition (t + 1) * Real.exp (-b * t)

theorem expExtension_smooth (b : ℝ) : ContDiff ℝ ∞ (expExtension b) := by
  unfold expExtension
  fun_prop

theorem expExtension_nonneg_argument (b t : ℝ) (ht : 0 ≤ t) :
    expExtension b t = Real.exp (-b * t) := by
  rw [expExtension, Real.smoothTransition.one_of_one_le (by linarith), one_mul]

theorem iteratedDeriv_expExtension_pos (b t : ℝ) (ht : 0 < t) (n : ℕ) :
    iteratedDeriv n (expExtension b) t = (-b) ^ n * Real.exp (-b * t) := by
  have heq : expExtension b =ᶠ[nhds t] (fun s => Real.exp (-b * s)) := by
    filter_upwards [eventually_gt_nhds ht] with s hs
    exact expExtension_nonneg_argument b s hs.le
  rw [EventuallyEq.iteratedDeriv_eq n heq, iteratedDeriv_exp_const_mul]

theorem iteratedDeriv_expExtension_neg (b t : ℝ) (ht : t < -1) (n : ℕ) :
    iteratedDeriv n (expExtension b) t = 0 := by
  have heq : expExtension b =ᶠ[nhds t] (fun _ => (0 : ℝ)) := by
    filter_upwards [eventually_lt_nhds ht] with s hs
    rw [expExtension, Real.smoothTransition.zero_of_nonpos (by linarith), zero_mul]
  rw [EventuallyEq.iteratedDeriv_eq n heq]
  simp

theorem pow_mul_exp_bound (b : ℝ) (hb : 0 < b) (k : ℕ) (t : ℝ) (ht : 0 ≤ t) :
    t ^ k * Real.exp (-b * t) ≤ (k.factorial : ℝ) / b ^ k := by
  have hfac : (0 : ℝ) < k.factorial := by positivity
  have h := Real.pow_div_factorial_le_exp (b * t) (mul_nonneg hb.le ht) k
  have h' := (div_le_iff₀ hfac).mp h
  rw [mul_pow] at h'
  rw [neg_mul, Real.exp_neg, ← div_eq_mul_inv]
  apply (div_le_div_iff₀ (Real.exp_pos (b * t)) (pow_pos hb k)).mpr
  nlinarith

def scalarSchwartz (b : ℝ) (hb : 0 < b) : SchwartzMap ℝ ℝ where
  toFun := expExtension b
  smooth' := expExtension_smooth b
  decay' k n := by
    let ψ : ℝ → ℝ := fun t => ‖t‖ ^ k * ‖iteratedFDeriv ℝ n (expExtension b) t‖
    have hψ : Continuous ψ := by
      apply Continuous.mul (by fun_prop)
      exact ((expExtension_smooth b).of_le (mod_cast le_top)).continuous_iteratedFDeriv'.norm
    obtain ⟨C, hC⟩ := (isCompact_Icc.image hψ).bddAbove
    let C₂ : ℝ := b ^ n * ((k.factorial : ℝ) / b ^ k)
    have hC₂ : 0 ≤ C₂ := by dsimp [C₂]; positivity
    refine ⟨max C C₂, ?_⟩
    intro t
    rcases lt_or_ge t (-1) with ht | ht
    · rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv, iteratedDeriv_expExtension_neg b t ht,
        norm_zero, mul_zero]
      exact hC₂.trans (le_max_right _ _)
    · rcases le_or_gt t 0 with ht0 | ht0
      · exact (hC (mem_image_of_mem ψ (show t ∈ Icc (-1) 0 from ⟨ht, ht0⟩))).trans
          (le_max_left _ _)
      · rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv,
          iteratedDeriv_expExtension_pos b t ht0]
        simp only [Real.norm_eq_abs, abs_of_pos ht0, abs_mul, abs_pow,
          abs_neg, abs_of_pos hb, abs_of_pos (Real.exp_pos _)]
        calc
          t ^ k * (b ^ n * Real.exp (-b * t)) = b ^ n * (t ^ k * Real.exp (-b * t)) := by ring
          _ ≤ C₂ := mul_le_mul_of_nonneg_left (pow_mul_exp_bound b hb k t ht0.le) (by positivity)
          _ ≤ max C C₂ := le_max_right _ _

@[simp] theorem scalarSchwartz_apply (b : ℝ) (hb : 0 < b) (t : ℝ) :
    scalarSchwartz b hb t = expExtension b t := rfl

end GaussianSchwartz

open GaussianSchwartz in
 theorem gaussian_schwartz (d : ℕ) (b : ℝ) (hb : 0 < b) :
    ∃ F : SchwartzMap (E d) ℂ, ∀ x, F x = (Real.exp (-b * ‖x‖ ^ 2) : ℂ) := by
  have hproper : ∃ (k : ℕ) (C : ℝ), ∀ x : E d, ‖x‖ ≤ C * (1 + ‖‖x‖ ^ 2‖) ^ k := by
    refine ⟨1, 1, ?_⟩
    intro x
    simp only [pow_one, one_mul, Real.norm_of_nonneg (sq_nonneg _)]
    nlinarith [sq_nonneg (‖x‖ - 1 / 2)]
  let S : SchwartzMap (E d) ℝ :=
    SchwartzMap.compCLM ℝ (Function.hasTemperateGrowth_norm_sq (E d)) hproper
      (scalarSchwartz b hb)
  refine ⟨S.postcompCLM Complex.ofRealCLM, ?_⟩
  intro x
  simp only [SchwartzMap.postcompCLM_apply, Complex.ofRealCLM_apply, S,
    SchwartzMap.compCLM_apply, Function.comp_apply, scalarSchwartz_apply,
    expExtension_nonneg_argument b (‖x‖ ^ 2) (sq_nonneg _)]

#print axioms gaussian_schwartz

end Bandlimited
end
