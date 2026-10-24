module

public import Bandlimited.ConvexGaussianActive
public import Bandlimited.ConvexGaussianGeometry
public import Bandlimited.ConvexGaussianErrors
public import Bandlimited.FourierTensor

/- Actual class membership of the finite active tensor sums. -/
@[expose] public section
noncomputable section
open Set
open scoped BigOperators
namespace Bandlimited
namespace ConvexGaussian

theorem tensor_sum_bandlimited {r m : ℕ} {δ : ℝ}
    (F : Fin m → Fin r → ℝ → ℂ)
    (hF : ∀ j i, F j i ∈ scalarBandlimited δ) :
    InBandlimitedSpace r ((r : ℝ) * δ)
      (fun x => ∑ j : Fin m, ∏ i : Fin r, F j i (x i)) := by
  have hterm : ∀ j : Fin m, InBandlimitedSpace r ((r : ℝ) * δ)
      (fun x => ∏ i : Fin r, F j i (x i)) := by
    intro j
    have h := InBandlimitedSpace.tensor_product
      (fun i : Fin r => fun x : E 1 => F j i (x 0)) (fun i => hF j i)
    simpa only [TensorDensity.scalarLine_apply] using h
  simpa only using InBandlimitedSpace.finset_sum Finset.univ
    (fun j : Fin m => fun x : E r => ∏ i : Fin r, F j i (x i))
    (fun j _ => hterm j)

theorem real_part_error_le (a t : ℝ) (z : ℂ) :
    ‖(a : ℂ) * (z.re : ℂ) - (t : ℂ)‖ ≤ ‖(a : ℂ) * z - (t : ℂ)‖ := by
  have h := Complex.abs_re_le_norm ((a : ℂ) * z - (t : ℂ))
  simpa only [Complex.sub_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
    zero_mul, sub_zero, ← Complex.ofReal_mul, ← Complex.ofReal_sub,
    Complex.norm_real, Real.norm_eq_abs] using h

#print axioms tensor_sum_bandlimited
#print axioms real_part_error_le
end ConvexGaussian
end Bandlimited
end
