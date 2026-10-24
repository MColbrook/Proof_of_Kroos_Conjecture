module

public import Bandlimited.ConvexGaussianScalar
public import Bandlimited.ConvexGaussianTarget

/- Tensor approximation on the active subspace. The factors retain their actual
one-dimensional compact-frequency witnesses for subsequent Fourier transport. -/
@[expose] public section
noncomputable section
open Set
open scoped BigOperators RealInnerProductSpace
namespace Bandlimited
namespace ConvexGaussian

/-- T08 and T09 approximate the active Gaussian with arbitrarily small weighted
error. This theorem retains every factor's actual bandlimited-space membership. -/
theorem active_tensor_approximation (hone : OneSidedDensityStatement)
    {d : ℕ} {f : E d → ℝ} (hf : IsConvexProfile f)
    (v : Fin (Module.finrank ℝ (activeSubspace f)) → E d)
    (C : Fin (Module.finrank ℝ (activeSubspace f)) → ℝ)
    (hspan : Submodule.span ℝ (range v) = activeSubspace f)
    (hC : ∀ i, 0 ≤ C i) (hsupport : ∀ i x, ⟪v i, x⟫ - C i ≤ f x)
    (A L δ ε : ℝ) (hA : 1 ≤ A) (hL : 0 ≤ L) (hδ : 0 < δ) (hε : 0 < ε)
    (hr : 1 ≤ Module.finrank ℝ (activeSubspace f)) :
    ∃ m : ℕ, ∃ F : Fin m → Fin (Module.finrank ℝ (activeSubspace f)) → ℝ → ℂ,
        (∀ j i, F j i ∈ scalarBandlimited δ) ∧
          ∀ y : activeSubspace f,
            gaussianWeight A L (y : E d) *
              ‖(Real.exp (-f y) : ℂ) *
                (∑ j : Fin m, ∏ i, F j i (slopeCoordinateEquiv (activeSubspace f) v hspan y i)) -
                  (gaussian A (y : E d) : ℂ)‖ < ε := by
  classical
  let r := Module.finrank ℝ (activeSubspace f)
  let T := slopeCoordinateEquiv (activeSubspace f) v hspan
  let c : ℝ := ((r : ℝ) + 1)⁻¹
  have hc : 0 < c := by dsimp [c]; positivity
  obtain ⟨B, hB, hcomparison⟩ := supporting_weight_comparison hf L hL v C hspan hC hsupport
  let H : E r → ℂ := fun t =>
    (Real.exp (f (T.symm t)) * gaussian A ((T.symm t : activeSubspace f) : E d) : ℂ)
  have hH : WeightedC0 (fun t : E r => ∏ i : Fin r, oneSidedWeight c L (t i)) H :=
    active_target_weightedC0 hf (activeSubspace f) T A c L
      (lt_of_lt_of_le zero_lt_one hA) hc hL
  obtain ⟨m, F, hF, b, hb, herr⟩ := tensor_density r hr
    (fun _ => oneSidedWeight c L)
    (fun _ => WeightedDensity.oneSidedWeight_continuous c L)
    (fun _ t => WeightedDensity.oneSidedWeight_positive c L t)
    (fun _ => scalarBandlimited δ)
    (fun _ => oneSided_scalar_dense hone c L δ hc hL hδ)
    H hH (ε / B) (div_pos hε hB)
  refine ⟨m, F, hF, ?_⟩
  intro y
  let P : ℂ := ∑ j : Fin m, ∏ i : Fin r, F j i (T y i)
  have hcancel : (Real.exp (-f y) : ℂ) * (Real.exp (f y) : ℂ) = 1 := by
    rw [← Complex.ofReal_mul, ← Real.exp_add]
    simp
  have heq : (Real.exp (-f y) : ℂ) * (P - H (T y)) =
      (Real.exp (-f y) : ℂ) * P - (gaussian A (y : E d) : ℂ) := by
    dsimp [H]
    simp only [ContinuousLinearEquiv.symm_apply_apply, Complex.ofReal_mul]
    calc
      (Real.exp (-f y) : ℂ) * (P - (Real.exp (f y) : ℂ) *
          (gaussian A (y : E d) : ℂ)) =
          (Real.exp (-f y) : ℂ) * P -
            ((Real.exp (-f y) : ℂ) * (Real.exp (f y) : ℂ)) *
              (gaussian A (y : E d) : ℂ) := by ring
      _ = _ := by rw [hcancel, one_mul]
  have hnorm : ‖(Real.exp (-f y) : ℂ) * P - (gaussian A (y : E d) : ℂ)‖ =
      Real.exp (-f y) * ‖P - H (T y)‖ := by
    rw [← heq, norm_mul, Complex.norm_real, Real.norm_of_nonneg (Real.exp_pos _).le]
  have hpoint := herr (T y)
  have hcompare := hcomparison A hA y
  change gaussianWeight A L (y : E d) *
    ‖(Real.exp (-f y) : ℂ) * P - (gaussian A (y : E d) : ℂ)‖ < ε
  rw [hnorm]
  calc
    gaussianWeight A L (y : E d) * (Real.exp (-f y) * ‖P - H (T y)‖) =
        (gaussianWeight A L (y : E d) * Real.exp (-f y)) * ‖P - H (T y)‖ := by ring
    _ ≤ (B * ∏ i : Fin r, oneSidedWeight c L (T y i)) * ‖P - H (T y)‖ :=
      mul_le_mul_of_nonneg_right hcompare (norm_nonneg _)
    _ = B * ((∏ i : Fin r, oneSidedWeight c L (T y i)) * ‖P - H (T y)‖) := by ring
    _ ≤ B * b := mul_le_mul_of_nonneg_left hpoint hB.le
    _ < ε := by simpa only [mul_comm] using (lt_div_iff₀ hB).mp hb

#print axioms active_tensor_approximation
end ConvexGaussian
end Bandlimited
end
