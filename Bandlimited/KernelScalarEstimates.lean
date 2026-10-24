module

public import Bandlimited.Rescaling
public import Bandlimited.Definitions

/- Scalar/error assembly for the central part of T07. The exact logarithm and
rescaling-ratio estimates are reused from the checked Rescaling development. -/
@[expose] public section
noncomputable section
namespace Bandlimited
namespace KernelEstimates

/-- The manuscript's ratio estimate is uniform on a fixed central interval. -/
theorem compact_rescaling_ratio_bound {q C M : ℝ} {N : ℕ}
    (hq : 0 ≤ q) (hC : 0 ≤ C) (hM : 0 ≤ M) (hqbound : q ≤ C * M) (hN : 0 < N) :
    1 ≤ ((1 + q / (N : ℝ))⁻¹) ^ N * Real.exp q ∧
      ((1 + q / (N : ℝ))⁻¹) ^ N * Real.exp q ≤
        Real.exp (C ^ 2 * M ^ 2 / (2 * (N : ℝ))) := by
  have h := Rescaling.rescaling_ratio_bounds hq hN
  refine ⟨h.1, h.2.trans (Real.exp_le_exp.mpr ?_)⟩
  apply div_le_div_of_nonneg_right _ (by positivity : 0 ≤ 2 * (N : ℝ))
  have hs : q ^ 2 ≤ (C * M) ^ 2 :=
    pow_le_pow_left₀ hq hqbound 2
  simpa only [mul_pow] using hs

/-- Quantitative scalar convergence, with all numerical reasoning checked in
the kernel and a natural threshold independent of the central parameter. -/
theorem central_exponential_error_tends_to_zero (C M : ℝ) (ε : ℝ) (hε : 0 < ε) :
    ∃ N₀ : ℕ, 1 ≤ N₀ ∧ ∀ N : ℕ, N₀ ≤ N →
      Real.exp (C ^ 2 * M ^ 2 / (2 * (N : ℝ))) - 1 < ε := by
  let b : ℝ := Real.log (1 + ε)
  have hb : 0 < b := Real.log_pos (by linarith)
  let R : ℝ := C ^ 2 * M ^ 2 / (2 * b)
  refine ⟨⌈R⌉₊ + 1, by omega, ?_⟩
  intro N hN
  have hNp : 0 < (N : ℝ) := by exact_mod_cast (show 0 < N by omega)
  have hR : R < (N : ℝ) := by
    have hceil : R ≤ (⌈R⌉₊ : ℝ) := Nat.le_ceil R
    have hcast : (⌈R⌉₊ : ℝ) + 1 ≤ N := by exact_mod_cast hN
    linarith
  have hratio : C ^ 2 * M ^ 2 / (2 * (N : ℝ)) < b := by
    apply (div_lt_iff₀ (by positivity : 0 < 2 * (N : ℝ))).mpr
    have h := (div_lt_iff₀ (by positivity : 0 < 2 * b)).mp hR
    nlinarith
  have hexp := Real.exp_lt_exp.mpr hratio
  have hlog : Real.exp b = 1 + ε := Real.exp_log (by linarith)
  linarith

/-- Multiplying an approximate target by a ratio near one produces precisely
the central error expression in the manuscript. -/
theorem central_ratio_weighted_error (w τ B r : ℝ) (Z G : ℂ)
    (hw : 0 ≤ w) (hτ : 0 ≤ τ) (hB : 0 ≤ B) (hr : 1 ≤ r)
    (herr : w * ‖Z - G‖ ≤ τ) (hG : w * ‖G‖ ≤ B) :
    w * ‖(r : ℂ) * Z - G‖ ≤ τ + (r - 1) * (B + τ) := by
  have hr0 : 0 ≤ r - 1 := by linarith
  have hZ : w * ‖Z‖ ≤ B + τ := by
    have hnorm : ‖Z‖ ≤ ‖Z - G‖ + ‖G‖ := by
      calc
        ‖Z‖ = ‖(Z - G) + G‖ := by rw [sub_add_cancel]
        _ ≤ ‖Z - G‖ + ‖G‖ := norm_add_le _ _
    have h := mul_le_mul_of_nonneg_left hnorm hw
    nlinarith
  have hnorm : ‖(r : ℂ) * Z - G‖ ≤ ‖Z - G‖ + (r - 1) * ‖Z‖ := by
    calc
      ‖(r : ℂ) * Z - G‖ = ‖(Z - G) + ((r - 1 : ℝ) : ℂ) * Z‖ := by
        congr 1
        simp only [Complex.ofReal_sub, Complex.ofReal_one]
        ring
      _ ≤ ‖Z - G‖ + ‖((r - 1 : ℝ) : ℂ) * Z‖ := norm_add_le _ _
      _ = ‖Z - G‖ + (r - 1) * ‖Z‖ := by
        rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hr0]
  have h := mul_le_mul_of_nonneg_left hnorm hw
  have hmul := mul_le_mul_of_nonneg_left hZ hr0
  nlinarith

#print axioms compact_rescaling_ratio_bound
#print axioms central_exponential_error_tends_to_zero
#print axioms central_ratio_weighted_error
end KernelEstimates
end Bandlimited
end
