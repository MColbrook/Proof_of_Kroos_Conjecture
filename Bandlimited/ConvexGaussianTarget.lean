module

public import Bandlimited.ConvexWeightedGaussian
public import Bandlimited.WeightedSchwartz

/- The convex profile multiplied by a Gaussian belongs to the tensor weighted
C₀ space after the active coordinate change. -/
@[expose] public section
noncomputable section
open Set
open scoped BigOperators RealInnerProductSpace
namespace Bandlimited
namespace ConvexGaussian

set_option maxHeartbeats 80000

/-- Global Lipschitz continuity and f(0)=0 imply at most linear growth. -/
theorem profile_linear_growth {d : ℕ} {f : E d → ℝ} (hf : IsConvexProfile f) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x, f x ≤ C * ‖x‖ := by
  obtain ⟨C, hC, hbound⟩ := hf.2.2.2
  refine ⟨C, hC, ?_⟩
  intro x
  have h := hbound x 0
  simp only [hf.2.2.1, sub_zero] at h
  exact (le_abs_self _).trans h

/-- Outside an explicitly chosen radius, the profile is absorbed by half of
the Gaussian exponent. The radius may depend on the profile. -/
theorem profile_gaussian_tail_domination {d : ℕ} {f : E d → ℝ}
    (hf : IsConvexProfile f) (A : ℝ) (hA : 0 < A) :
    ∃ R : ℝ, 0 ≤ R ∧ ∀ x : E d, R ≤ ‖x‖ →
      Real.exp (f x) * gaussian A x ≤ Real.exp (-‖x‖ ^ 2 / (2 * A ^ 2)) := by
  obtain ⟨C, hC, hlin⟩ := profile_linear_growth hf
  refine ⟨2 * C * A ^ 2, by positivity, ?_⟩
  intro x hx
  have hden : 0 < 2 * A ^ 2 := by positivity
  have hhalf : f x ≤ ‖x‖ ^ 2 / (2 * A ^ 2) := by
    apply (hlin x).trans
    apply (le_div_iff₀ hden).mpr
    nlinarith [mul_nonneg (norm_nonneg x) (sub_nonneg.mpr hx)]
  rw [gaussian, ← Real.exp_add]
  apply Real.exp_le_exp.mpr
  have hsplit : ‖x‖ ^ 2 / A ^ 2 = 2 * (‖x‖ ^ 2 / (2 * A ^ 2)) := by
    field_simp
    <;> ring
  simp only [neg_div] at *
  linarith

/-- A tensor product of the one-sided weights has polynomial growth under any
linear coordinate map; the exponential factors are at most one. -/
theorem tensor_weight_polynomial_bound {d r : ℕ} (S : Submodule ℝ (E d))
    (T : S ≃L[ℝ] E r) (c L : ℝ) (hc : 0 < c) (hL : 0 ≤ L) :
    ∃ N : ℕ, ∃ B : ℝ, 0 < B ∧ ∀ y : S,
      (∏ i : Fin r, oneSidedWeight c L (T y i)) ≤
        B * gaussianWeight 1 (N : ℝ) (y : E d) := by
  let m : ℕ := ⌈L⌉₊
  let K : ℝ := 1 + ‖T.toContinuousLinearMap‖
  let N : ℕ := m * r
  have hm : L ≤ (m : ℝ) := Nat.le_ceil L
  have hK : 1 ≤ K := by dsimp [K]; linarith [norm_nonneg T.toContinuousLinearMap]
  refine ⟨N, K ^ N, by positivity, ?_⟩
  intro y
  have hcoord : ∀ i : Fin r, 1 + |T y i| ≤ K * (1 + ‖(y : E d)‖) := by
    intro i
    have hi : |T y i| ≤ ‖T y‖ := by
      simpa only [Real.norm_eq_abs] using PiLp.norm_apply_le (T y) i
    have hn := ContinuousLinearMap.le_opNorm T.toContinuousLinearMap y
    change ‖T y‖ ≤ ‖T.toContinuousLinearMap‖ * ‖y‖ at hn
    change ‖T y‖ ≤ ‖T.toContinuousLinearMap‖ * ‖(y : E d)‖ at hn
    change 1 + |T y i| ≤ K * (1 + ‖y‖)
    dsimp [K]
    nlinarith [norm_nonneg T.toContinuousLinearMap, norm_nonneg (y : E d)]
  have hfactor : ∀ i : Fin r, oneSidedWeight c L (T y i) ≤
      (K * (1 + ‖(y : E d)‖)) ^ m := by
    intro i
    calc
      oneSidedWeight c L (T y i) ≤ (1 + |T y i|) ^ L :=
        WeightedDensity.oneSidedWeight_le_polynomial c L (T y i) hc
      _ ≤ (1 + |T y i|) ^ (m : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le (by linarith [abs_nonneg (T y i)]) hm
      _ = (1 + |T y i|) ^ m := Real.rpow_natCast _ _
      _ ≤ (K * (1 + ‖(y : E d)‖)) ^ m :=
        pow_le_pow_left₀ (by positivity) (hcoord i) m
  calc
    (∏ i : Fin r, oneSidedWeight c L (T y i)) ≤
        ∏ i : Fin r, (K * (1 + ‖(y : E d)‖)) ^ m :=
      Finset.prod_le_prod₀ (fun i _ => (WeightedDensity.oneSidedWeight_positive c L (T y i)).le)
        (fun i _ => hfactor i)
    _ = (K * (1 + ‖(y : E d)‖)) ^ N := by simp [N, ← pow_mul]
    _ = K ^ N * gaussianWeight 1 (N : ℝ) (y : E d) := by
      simp only [mul_pow, gaussianWeight, div_one, Real.rpow_natCast]

/-- The target for tensor density is in the required weighted C₀ space. The
proof permits every globally Lipschitz convex profile, with no common Lipschitz bound. -/
theorem active_target_weightedC0 {d r : ℕ} {f : E d → ℝ}
    (hf : IsConvexProfile f) (S : Submodule ℝ (E d)) (T : S ≃L[ℝ] E r)
    (A c L : ℝ) (hA : 0 < A) (hc : 0 < c) (hL : 0 ≤ L) :
    WeightedC0 (fun t : E r => ∏ i : Fin r, oneSidedWeight c L (t i))
      (fun t : E r => (Real.exp (f (T.symm t)) * gaussian A ((T.symm t : S) : E d) : ℂ)) := by
  let J : E r →L[ℝ] E d := S.subtypeL.comp T.symm.toContinuousLinearMap
  let H : E r → ℂ := fun t => (Real.exp (f (J t)) * gaussian A (J t) : ℂ)
  let W : E r → ℝ := fun t => ∏ i : Fin r, oneSidedWeight c L (t i)
  have hH : Continuous H := by
    dsimp [H, gaussian]
    simp only [← Complex.ofReal_mul]
    exact Complex.continuous_ofReal.comp
      (((profile_continuous hf).comp J.continuous).rexp.mul
        (((J.continuous.norm.pow 2).neg.div_const (A ^ 2)).rexp))
  have hW : Continuous W := by
    dsimp [W]
    exact continuous_finset_prod _ fun i _ =>
      (WeightedDensity.oneSidedWeight_continuous c L).comp (PiLp.continuous_apply 2 (fun _ : Fin r => ℝ) i)
  refine ⟨hH, (Complex.continuous_ofReal.comp hW).mul hH, ?_⟩
  obtain ⟨N, B, hB, hpoly⟩ := tensor_weight_polynomial_bound S T c L hc hL
  obtain ⟨R₀, hR₀, hdom⟩ := profile_gaussian_tail_domination hf A hA
  obtain ⟨G, hG⟩ := gaussian_schwartz d ((2 * A ^ 2)⁻¹) (by positivity)
  intro ε hε
  obtain ⟨R₁, hR₁, htail⟩ := WeightedDensity.schwartz_real_weight_tail G (N : ℝ)
    (Nat.cast_nonneg _) (ε / B) (div_pos hε hB)
  let K : ℝ := 1 + ‖T.toContinuousLinearMap‖
  have hK : 0 < K := by dsimp [K]; positivity
  let R : ℝ := max R₀ R₁
  have hR : 0 ≤ R := (by linarith : 0 ≤ R₁).trans (le_max_right _ _)
  refine ⟨K * R, mul_nonneg hK.le hR, ?_⟩
  intro t ht
  let y : S := T.symm t
  have hnorm : ‖t‖ ≤ K * ‖(y : E d)‖ := by
    have h := ContinuousLinearMap.le_opNorm T.toContinuousLinearMap (T.symm t)
    change ‖T (T.symm t)‖ ≤ ‖T.toContinuousLinearMap‖ * ‖((T.symm t : S) : E d)‖ at h
    rw [T.apply_symm_apply] at h
    exact h.trans (mul_le_mul_of_nonneg_right (by dsimp [K]; linarith)
      (norm_nonneg y))
  have hy : R ≤ ‖(y : E d)‖ := (mul_le_mul_iff_right₀ hK).mp (ht.trans hnorm)
  have htarget : ‖H t‖ ≤ ‖G (y : E d)‖ := by
    dsimp [H]
    rw [← Complex.ofReal_mul, Complex.norm_real, Real.norm_of_nonneg (by unfold gaussian; positivity), hG,
      Complex.norm_real, Real.norm_of_nonneg (Real.exp_pos _).le]
    have hJy : J t = (y : E d) := rfl
    rw [hJy]
    have heq : -(2 * A ^ 2)⁻¹ * ‖(y : E d)‖ ^ 2 =
        -‖(y : E d)‖ ^ 2 / (2 * A ^ 2) := by ring
    rw [heq]
    exact hdom (y : E d) ((le_max_left _ _).trans hy)
  have hWnon : 0 ≤ W t := Finset.prod_nonneg fun i _ =>
    (WeightedDensity.oneSidedWeight_positive c L (t i)).le
  rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hWnon]
  calc
    W t * ‖H t‖ ≤ W t * ‖G (y : E d)‖ :=
      mul_le_mul_of_nonneg_left htarget hWnon
    _ ≤ (B * gaussianWeight 1 (N : ℝ) (y : E d)) * ‖G (y : E d)‖ := by
      apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
      simpa only [W, y, ContinuousLinearEquiv.apply_symm_apply] using hpoly y
    _ = B * (gaussianWeight 1 (N : ℝ) (y : E d) * ‖G (y : E d)‖) := by ring
    _ < B * (ε / B) := mul_lt_mul_of_pos_left
      (htail (y : E d) ((le_max_right _ _).trans hy)) hB
    _ = ε := by field_simp

#print axioms profile_gaussian_tail_domination
#print axioms active_target_weightedC0
end ConvexGaussian
end Bandlimited
end
