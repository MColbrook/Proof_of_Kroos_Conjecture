module

public import Bandlimited.GaussianCutoff
public import Bandlimited.TensorDensity
public import Bandlimited.BandlimitedOperations

/- Polynomial weights and the exact one-sided weight preserve Schwartz C₀ decay. -/

@[expose] public section
noncomputable section
open Set
open scoped Topology

namespace Bandlimited
namespace WeightedDensity

theorem schwartz_real_weight_tail {d : ℕ} (f : SchwartzMap (E d) ℂ)
    (M : ℝ) (hM : 0 ≤ M) :
    ∀ ε : ℝ, 0 < ε → ∃ R : ℝ, 1 ≤ R ∧ ∀ x : E d, R ≤ ‖x‖ →
      gaussianWeight 1 M x * ‖f x‖ < ε := by
  intro ε hε
  let m : ℕ := ⌈M⌉₊
  have hm : M ≤ (m : ℝ) := Nat.le_ceil M
  let C : ℝ := (2 : ℝ) ^ m * SchwartzMap.seminorm ℂ (m + 1) 0 f
  have hC : 0 ≤ C := by dsimp [C]; positivity
  let R : ℝ := 1 + C / ε
  have hR : 1 ≤ R := by dsimp [R]; linarith [div_nonneg hC hε.le]
  have hRp : 0 < R := by linarith
  have hsmall : C / R < ε := by
    apply (div_lt_iff₀ hRp).mpr
    dsimp [R]
    have hcancel : ε * (C / ε) = C := by field_simp [hε.ne']
    nlinarith
  refine ⟨R, hR, ?_⟩
  intro x hx
  have hx1 : 1 ≤ ‖x‖ := hR.trans hx
  have hpoly : (1 + ‖x‖) ^ m ≤ (2 : ℝ) ^ m * ‖x‖ ^ m := by
    rw [← mul_pow]
    exact pow_le_pow_left₀ (by positivity) (by linarith) m
  calc
    gaussianWeight 1 M x * ‖f x‖ ≤ (1 + ‖x‖) ^ m * ‖f x‖ :=
      mul_le_mul_of_nonneg_right (gaussian_weight_le_integer_weight (by norm_num) hM hm x)
        (norm_nonneg _)
    _ ≤ ((2 : ℝ) ^ m * ‖x‖ ^ m) * ‖f x‖ :=
      mul_le_mul_of_nonneg_right hpoly (norm_nonneg _)
    _ = (2 : ℝ) ^ m * (‖x‖ ^ m * ‖f x‖) := by ring
    _ ≤ (2 : ℝ) ^ m * (SchwartzMap.seminorm ℂ (m + 1) 0 f / R) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      simpa only [norm_iteratedFDeriv_zero] using schwartz_weighted_derivative_tail f m 0 hRp x hx
    _ = C / R := by dsimp [C]; ring
    _ < ε := hsmall

theorem oneSidedWeight_positive (c M t : ℝ) : 0 < oneSidedWeight c M t := by
  unfold oneSidedWeight
  positivity

theorem oneSidedWeight_continuous (c M : ℝ) : Continuous (oneSidedWeight c M) := by
  have hb : Continuous (fun t : ℝ => 1 + |t|) := continuous_const.add continuous_abs
  have hp (t : ℝ) : 0 < 1 + |t| := by positivity
  have heq : (fun t : ℝ => (1 + |t|) ^ M) =
      fun t => Real.exp (Real.log (1 + |t|) * M) := by
    funext t
    exact Real.rpow_def_of_pos (hp t) M
  have hpoly : Continuous (fun t : ℝ => (1 + |t|) ^ M) := by
    rw [heq]
    exact Real.continuous_exp.comp ((hb.log (fun t => (hp t).ne')).mul continuous_const)
  unfold oneSidedWeight
  exact hpoly.mul (Real.continuous_exp.comp
    (continuous_const.mul (continuous_id.max continuous_const)))

theorem oneSidedWeight_le_polynomial (c M t : ℝ) (hc : 0 < c) :
    oneSidedWeight c M t ≤ (1 + |t|) ^ M := by
  unfold oneSidedWeight
  have hexp : Real.exp (-c * max t 0) ≤ 1 := Real.exp_le_one_iff.mpr (by
    have ht : 0 ≤ max t 0 := le_max_right _ _
    nlinarith)
  simpa only [mul_one] using mul_le_mul_of_nonneg_left hexp
    (Real.rpow_nonneg (by positivity : 0 ≤ 1 + |t|) M)

theorem norm_one_dimensional (x : E 1) : ‖x‖ = |x 0| := by
  have h := congrArg norm (TensorDensity.scalarLine_coord x)
  simpa only [TensorDensity.norm_scalarLine] using h.symm

theorem schwartz_oneSided_weightedC0 (f : SchwartzMap (E 1) ℂ)
    (c M : ℝ) (hc : 0 < c) (hM : 0 ≤ M) :
    WeightedC0 (fun x => oneSidedWeight c M (x 0)) f := by
  have hW : Continuous (fun x : E 1 => oneSidedWeight c M (x 0)) :=
    (oneSidedWeight_continuous c M).comp (PiLp.continuous_apply 2 (fun _ : Fin 1 => ℝ) 0)
  have hcont : Continuous (fun x : E 1 => (oneSidedWeight c M (x 0) : ℂ) * f x) :=
    (Complex.continuous_ofReal.comp hW).mul f.continuous
  refine ⟨f.continuous, hcont, ?_⟩
  intro ε hε
  obtain ⟨R, hR, htail⟩ := schwartz_real_weight_tail f M hM ε hε
  refine ⟨R, (by linarith : 0 ≤ R), ?_⟩
  intro x hx
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (oneSidedWeight_positive c M (x 0))]
  calc
    oneSidedWeight c M (x 0) * ‖f x‖ ≤ gaussianWeight 1 M x * ‖f x‖ := by
      apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
      simpa only [gaussianWeight, div_one, norm_one_dimensional] using
        oneSidedWeight_le_polynomial c M (x 0) hc
    _ < ε := htail x hx

theorem bandlimited_oneSided_weightedC0 {δ : ℝ} {F : E 1 → ℂ}
    (hF : InBandlimitedSpace 1 δ F) (c M : ℝ) (hc : 0 < c) (hM : 0 ≤ M) :
    WeightedC0 (fun x => oneSidedWeight c M (x 0)) F := by
  obtain ⟨f, hf⟩ := hF.exists_schwartz (by omega)
  have heq : (f : E 1 → ℂ) = F := funext hf
  rw [← heq]
  exact schwartz_oneSided_weightedC0 f c M hc hM

#print axioms bandlimited_oneSided_weightedC0
#print axioms schwartz_real_weight_tail
#print axioms schwartz_oneSided_weightedC0

end WeightedDensity
end Bandlimited
end
