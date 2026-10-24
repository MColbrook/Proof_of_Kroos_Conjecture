module

public import Bandlimited.Definitions
public import Mathlib.Analysis.Distribution.SchwartzSpace.Basic
public import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct
public import Mathlib.Analysis.Calculus.ContDiff.Bounds

/-!
# Expanding compact cutoffs in Schwartz space

The estimates in this module use Mathlib's iterated Frechet derivative product
and composition inequalities (Apache 2.0). The parameter of expansion is real.
-/

@[expose] public section
noncomputable section
open scoped BigOperators Topology
open Set Filter

namespace Bandlimited

/-- Rescaling a Schwartz function by a contraction cannot increase the
unweighted bound on any fixed iterated derivative. -/
theorem scaled_schwartz_derivative_bound {d : ℕ}
    (f : SchwartzMap (E d) ℂ) {R : ℝ} (hR : 1 ≤ R) (n : ℕ) (x : E d) :
    ‖iteratedFDeriv ℝ n (fun y : E d => f (R⁻¹ • y)) x‖ ≤
      SchwartzMap.seminorm ℂ 0 n f := by
  let T : E d →L[ℝ] E d := R⁻¹ • ContinuousLinearMap.id ℝ (E d)
  have hRpos : 0 < R := lt_of_lt_of_le zero_lt_one hR
  have hRi : |R⁻¹| ≤ 1 := by
    rw [abs_of_nonneg (inv_nonneg.mpr hRpos.le)]
    exact inv_le_one_of_one_le₀ hR
  have hT : ‖T‖ ≤ 1 := by
    apply ContinuousLinearMap.opNorm_le_bound T zero_le_one
    intro y
    change ‖R⁻¹ • y‖ ≤ 1 * ‖y‖
    simpa only [norm_smul, Real.norm_eq_abs] using
      mul_le_mul_of_nonneg_right hRi (norm_nonneg y)
  have hder := T.iteratedFDeriv_comp_right (f.smooth ⊤) x (i := n) (by exact_mod_cast (le_top : (n : ℕ∞) ≤ ⊤))
  change ‖iteratedFDeriv ℝ n (f ∘ T) x‖ ≤ _
  rw [hder]
  calc
    ‖(iteratedFDeriv ℝ n f (T x)).compContinuousLinearMap (fun _ => T)‖ ≤
        ‖iteratedFDeriv ℝ n f (T x)‖ * ∏ _ : Fin n, ‖T‖ :=
      ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _
    _ ≤ ‖iteratedFDeriv ℝ n f (T x)‖ * 1 := by
      apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
      exact Finset.prod_le_one₀ (fun _ _ => norm_nonneg _) (fun _ _ => hT)
    _ ≤ SchwartzMap.seminorm ℂ 0 n f := by
      simpa only [mul_one] using f.norm_iteratedFDeriv_le_seminorm ℂ n (T x)

/-- One additional power in a Schwartz seminorm yields a uniform tail bound. -/
theorem schwartz_weighted_derivative_tail {d : ℕ} (f : SchwartzMap (E d) ℂ)
    (k n : ℕ) {R : ℝ} (hR : 0 < R) (x : E d) (hx : R ≤ ‖x‖) :
    ‖x‖ ^ k * ‖iteratedFDeriv ℝ n f x‖ ≤
      SchwartzMap.seminorm ℂ (k + 1) n f / R := by
  apply (le_div_iff₀ hR).mpr
  calc
    (‖x‖ ^ k * ‖iteratedFDeriv ℝ n f x‖) * R ≤
        (‖x‖ ^ k * ‖iteratedFDeriv ℝ n f x‖) * ‖x‖ :=
      mul_le_mul_of_nonneg_left hx (by positivity)
    _ = ‖x‖ ^ (k + 1) * ‖iteratedFDeriv ℝ n f x‖ := by rw [pow_succ]; ring
    _ ≤ SchwartzMap.seminorm ℂ (k + 1) n f := f.le_seminorm ℂ (k + 1) n x

def unitCutoffBump (d : ℕ) : ContDiffBump (0 : E d) where
  rIn := 1
  rOut := 2
  rIn_pos := zero_lt_one
  rIn_lt_rOut := one_lt_two

def unitCutoffSchwartz (d : ℕ) : SchwartzMap (E d) ℂ :=
  ((unitCutoffBump d).hasCompactSupport.comp_left
    (by simp : ((0 : ℝ) : ℂ) = 0)).toSchwartzMap
      (Complex.ofRealCLM.contDiff.comp (unitCutoffBump d).contDiff)

theorem unitCutoffSchwartz_apply (d : ℕ) (x : E d) :
    unitCutoffSchwartz d x = (unitCutoffBump d x : ℂ) := rfl

theorem unitCutoffSchwartz_one (d : ℕ) (x : E d) (hx : ‖x‖ ≤ 1) :
    unitCutoffSchwartz d x = 1 := by
  rw [unitCutoffSchwartz_apply, (unitCutoffBump d).one_of_mem_closedBall]
  · rfl
  · simpa only [Metric.mem_closedBall, dist_zero_right, unitCutoffBump] using hx

def cutoffScale (d : ℕ) (R : ℝ) : E d ≃L[ℝ] E d :=
  ContinuousLinearEquiv.smulLeft (R₁ := ℝ) (M₁ := E d)
    (Units.mk0 ((max 1 R)⁻¹) (by positivity))

def scaledUnitCutoff (d : ℕ) (R : ℝ) : SchwartzMap (E d) ℂ :=
  (SchwartzMap.compCLMOfContinuousLinearEquiv ℂ (cutoffScale d R))
    (unitCutoffSchwartz d)

theorem scaledUnitCutoff_apply (d : ℕ) (R : ℝ) (x : E d) :
    scaledUnitCutoff d R x = unitCutoffSchwartz d ((max 1 R)⁻¹ • x) := rfl

def compactCutoff {d : ℕ} (f : SchwartzMap (E d) ℂ) (R : ℝ) : SchwartzMap (E d) ℂ :=
  SchwartzMap.smulLeftCLM ℂ (scaledUnitCutoff d R) f

theorem compactCutoff_apply {d : ℕ} (f : SchwartzMap (E d) ℂ) (R : ℝ) (x : E d) :
    compactCutoff f R x = scaledUnitCutoff d R x * f x := by
  unfold compactCutoff
  rw [SchwartzMap.smulLeftCLM_apply_apply (scaledUnitCutoff d R).hasTemperateGrowth]
  rfl

theorem scaledUnitCutoff_one {d : ℕ} {R : ℝ} (hR : 1 ≤ R) (x : E d)
    (hx : ‖x‖ ≤ R) : scaledUnitCutoff d R x = 1 := by
  rw [scaledUnitCutoff_apply, max_eq_right hR]
  apply unitCutoffSchwartz_one
  rw [norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos (lt_of_lt_of_le zero_lt_one hR)]
  rw [← div_eq_inv_mul]
  exact (div_le_one (lt_of_lt_of_le zero_lt_one hR)).mpr hx

theorem compactCutoff_eventuallyEq {d : ℕ} (f : SchwartzMap (E d) ℂ)
    {R : ℝ} (hR : 1 ≤ R) (x : E d) (hx : ‖x‖ < R) :
    (compactCutoff f R : E d → ℂ) =ᶠ[𝓝 x] f := by
  have hball : {y : E d | ‖y‖ < R} ∈ 𝓝 x :=
    (isOpen_lt continuous_norm continuous_const).mem_nhds hx
  filter_upwards [hball] with y hy
  rw [compactCutoff_apply, scaledUnitCutoff_one hR y hy.le, one_mul]

theorem compactCutoff_derivative_eq {d : ℕ} (f : SchwartzMap (E d) ℂ)
    {R : ℝ} (hR : 1 ≤ R) (n : ℕ) (x : E d) (hx : ‖x‖ < R) :
    iteratedFDeriv ℝ n (compactCutoff f R) x = iteratedFDeriv ℝ n f x :=
  ((compactCutoff_eventuallyEq f hR x hx).iteratedFDeriv ℝ n).eq_of_nhds

theorem scaledUnitCutoff_derivative_bound (d : ℕ) {R : ℝ} (hR : 1 ≤ R)
    (n : ℕ) (x : E d) :
    ‖iteratedFDeriv ℝ n (scaledUnitCutoff d R) x‖ ≤
      SchwartzMap.seminorm ℂ 0 n (unitCutoffSchwartz d) := by
  have heq : (scaledUnitCutoff d R : E d → ℂ) =
      fun y : E d => unitCutoffSchwartz d (R⁻¹ • y) := by
    funext y
    rw [scaledUnitCutoff_apply, max_eq_right hR]
  rw [heq]
  exact scaled_schwartz_derivative_bound (unitCutoffSchwartz d) hR n x

def cutoffErrorConstant {d : ℕ} (f : SchwartzMap (E d) ℂ) (k n : ℕ) : ℝ :=
  (∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ) *
    SchwartzMap.seminorm ℂ 0 i (unitCutoffSchwartz d) *
    SchwartzMap.seminorm ℂ (k + 1) (n - i) f) +
      SchwartzMap.seminorm ℂ (k + 1) n f

theorem cutoffErrorConstant_nonneg {d : ℕ} (f : SchwartzMap (E d) ℂ) (k n : ℕ) :
    0 ≤ cutoffErrorConstant f k n := by
  unfold cutoffErrorConstant
  positivity

theorem compactCutoff_product_derivative_bound {d : ℕ} (f : SchwartzMap (E d) ℂ)
    {R : ℝ} (hR : 1 ≤ R) (n : ℕ) (x : E d) :
    ‖iteratedFDeriv ℝ n (compactCutoff f R) x‖ ≤
      ∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ) *
        SchwartzMap.seminorm ℂ 0 i (unitCutoffSchwartz d) *
        ‖iteratedFDeriv ℝ (n - i) f x‖ := by
  have heq : (compactCutoff f R : E d → ℂ) =
      fun y : E d => scaledUnitCutoff d R y * f y := funext (compactCutoff_apply f R)
  rw [heq]
  have hp := norm_iteratedFDeriv_mul_le ((scaledUnitCutoff d R).smooth ⊤)
    (f.smooth ⊤) x (n := n) (by exact_mod_cast (le_top : (n : ℕ∞) ≤ ⊤))
  apply hp.trans
  apply Finset.sum_le_sum
  intro i hi
  exact mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left (scaledUnitCutoff_derivative_bound d hR i x)
      (Nat.cast_nonneg _)) (norm_nonneg _)

theorem compactCutoff_error_derivative_bound {d : ℕ} (f : SchwartzMap (E d) ℂ)
    {R : ℝ} (hR : 1 ≤ R) (k n : ℕ) (x : E d) (hx : R ≤ ‖x‖) :
    ‖x‖ ^ k * ‖iteratedFDeriv ℝ n (compactCutoff f R - f) x‖ ≤
      cutoffErrorConstant f k n / R := by
  have hRpos : 0 < R := lt_of_lt_of_le zero_lt_one hR
  have hsub : iteratedFDeriv ℝ n (compactCutoff f R - f) x =
      iteratedFDeriv ℝ n (compactCutoff f R) x - iteratedFDeriv ℝ n f x := by
    change iteratedFDeriv ℝ n ((compactCutoff f R : E d → ℂ) - (f : E d → ℂ)) x = _
    exact iteratedFDeriv_sub_apply ((compactCutoff f R).smooth n).contDiffAt
      (f.smooth n).contDiffAt
  rw [hsub]
  calc
    ‖x‖ ^ k * ‖iteratedFDeriv ℝ n (compactCutoff f R) x - iteratedFDeriv ℝ n f x‖ ≤
        ‖x‖ ^ k * (‖iteratedFDeriv ℝ n (compactCutoff f R) x‖ +
          ‖iteratedFDeriv ℝ n f x‖) :=
      mul_le_mul_of_nonneg_left (norm_sub_le _ _) (by positivity)
    _ ≤ ‖x‖ ^ k * ((∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ) *
          SchwartzMap.seminorm ℂ 0 i (unitCutoffSchwartz d) *
          ‖iteratedFDeriv ℝ (n - i) f x‖) + ‖iteratedFDeriv ℝ n f x‖) :=
      mul_le_mul_of_nonneg_left
        (add_le_add (compactCutoff_product_derivative_bound f hR n x) le_rfl) (by positivity)
    _ = (∑ i ∈ Finset.range (n + 1), ((n.choose i : ℝ) *
          SchwartzMap.seminorm ℂ 0 i (unitCutoffSchwartz d)) *
          (‖x‖ ^ k * ‖iteratedFDeriv ℝ (n - i) f x‖)) +
          ‖x‖ ^ k * ‖iteratedFDeriv ℝ n f x‖ := by
      rw [mul_add, Finset.mul_sum]
      congr 1
      apply Finset.sum_congr rfl
      intro i hi
      ring
    _ ≤ (∑ i ∈ Finset.range (n + 1), ((n.choose i : ℝ) *
          SchwartzMap.seminorm ℂ 0 i (unitCutoffSchwartz d)) *
          (SchwartzMap.seminorm ℂ (k + 1) (n - i) f / R)) +
          SchwartzMap.seminorm ℂ (k + 1) n f / R := by
      apply add_le_add _ (schwartz_weighted_derivative_tail f k n hRpos x hx)
      apply Finset.sum_le_sum
      intro i hi
      exact mul_le_mul_of_nonneg_left
        (schwartz_weighted_derivative_tail f k (n - i) hRpos x hx) (by positivity)
    _ = cutoffErrorConstant f k n / R := by
      unfold cutoffErrorConstant
      rw [add_div, Finset.sum_div]
      congr 1
      apply Finset.sum_congr rfl
      intro i hi
      ring

theorem compactCutoff_error_seminorm_bound {d : ℕ} (f : SchwartzMap (E d) ℂ)
    {R : ℝ} (hR : 1 ≤ R) (k n : ℕ) :
    SchwartzMap.seminorm ℂ k n (compactCutoff f R - f) ≤
      cutoffErrorConstant f k n / R := by
  have hRpos : 0 < R := lt_of_lt_of_le zero_lt_one hR
  apply SchwartzMap.seminorm_le_bound ℂ k n (compactCutoff f R - f)
    (div_nonneg (cutoffErrorConstant_nonneg f k n) hRpos.le)
  intro x
  by_cases hx : ‖x‖ < R
  · have heq : iteratedFDeriv ℝ n (compactCutoff f R - f) x = 0 := by
      change iteratedFDeriv ℝ n ((compactCutoff f R : E d → ℂ) - (f : E d → ℂ)) x = 0
      rw [iteratedFDeriv_sub_apply ((compactCutoff f R).smooth n).contDiffAt
        (f.smooth n).contDiffAt, compactCutoff_derivative_eq f hR n x hx, sub_self]
    rw [heq, norm_zero, mul_zero]
    exact div_nonneg (cutoffErrorConstant_nonneg f k n) hRpos.le
  · exact compactCutoff_error_derivative_bound f hR k n x (le_of_not_gt hx)

theorem compactCutoff_tendsto {d : ℕ} (f : SchwartzMap (E d) ℂ) :
    Tendsto (compactCutoff f) atTop (𝓝 f) := by
  apply ((schwartz_withSeminorms ℂ (E d) ℂ).tendsto_nhds_atTop (compactCutoff f) f).mpr
  intro ⟨k, n⟩ ε hε
  refine ⟨max 1 (cutoffErrorConstant f k n / ε + 1), ?_⟩
  intro R hR
  have hR1 : 1 ≤ R := le_trans (le_max_left _ _) hR
  have hRpos : 0 < R := lt_of_lt_of_le zero_lt_one hR1
  have hRε : cutoffErrorConstant f k n / ε < R := by
    have := le_trans (le_max_right _ _) hR
    linarith
  have hlt : cutoffErrorConstant f k n / R < ε := by
    apply (div_lt_iff₀ hRpos).mpr
    have hm := mul_lt_mul_of_pos_right hRε hε
    rw [div_mul_cancel₀ _ (ne_of_gt hε)] at hm
    simpa only [mul_comm R ε] using hm
  exact lt_of_le_of_lt (compactCutoff_error_seminorm_bound f hR1 k n) hlt

theorem scaledUnitCutoff_zero {d : ℕ} (R : ℝ) (x : E d)
    (hx : 2 * max 1 R ≤ ‖x‖) : scaledUnitCutoff d R x = 0 := by
  rw [scaledUnitCutoff_apply, unitCutoffSchwartz_apply]
  have hRp : 0 < max 1 R := lt_of_lt_of_le zero_lt_one (le_max_left _ _)
  have hdist : 2 ≤ dist ((max 1 R)⁻¹ • x) 0 := by
    rw [dist_zero_right, norm_smul, Real.norm_eq_abs,
      abs_inv, abs_of_pos hRp, ← div_eq_inv_mul]
    exact (le_div_iff₀ hRp).mpr hx
  rw [(unitCutoffBump d).zero_of_le_dist hdist]
  rfl

theorem compactCutoff_support {d : ℕ} (f : SchwartzMap (E d) ℂ) (R : ℝ) :
    tsupport (compactCutoff f R) ⊆ Metric.closedBall (0 : E d) (2 * max 1 R) := by
  change closure (Function.support (compactCutoff f R)) ⊆ _
  apply closure_minimal _ Metric.isClosed_closedBall
  intro x hx
  by_contra hnot
  have hnorm : 2 * max 1 R ≤ ‖x‖ := by
    have : ¬ ‖x‖ ≤ 2 * max 1 R := by
      simpa only [Metric.mem_closedBall, dist_zero_right] using hnot
    exact le_of_lt (lt_of_not_ge this)
  have hz : compactCutoff f R x = 0 := by
    rw [compactCutoff_apply, scaledUnitCutoff_zero R x hnorm, zero_mul]
  exact hx hz

theorem compactCutoff_hasCompactSupport {d : ℕ} (f : SchwartzMap (E d) ℂ) (R : ℝ) :
    HasCompactSupport (compactCutoff f R) :=
  (isCompact_closedBall (0 : E d) (2 * max 1 R)).of_isClosed_subset
    (isClosed_tsupport _) (compactCutoff_support f R)

theorem scaledUnitCutoff_real (d : ℕ) (R : ℝ) :
    IsRealValued (scaledUnitCutoff d R) := by
  intro x
  simp only [scaledUnitCutoff_apply, unitCutoffSchwartz_apply, Complex.ofReal_im]

theorem scaledUnitCutoff_even (d : ℕ) (R : ℝ) (x : E d) :
    scaledUnitCutoff d R (-x) = scaledUnitCutoff d R x := by
  simp only [scaledUnitCutoff_apply, unitCutoffSchwartz_apply, smul_neg,
    (unitCutoffBump d).neg]

theorem compactCutoff_real {d : ℕ} (f : SchwartzMap (E d) ℂ)
    (hf : IsRealValued f) (R : ℝ) : IsRealValued (compactCutoff f R) := by
  intro x
  rw [compactCutoff_apply, Complex.mul_im, hf x, scaledUnitCutoff_real d R x]
  simp

theorem compactCutoff_even {d : ℕ} (f : SchwartzMap (E d) ℂ)
    (hf : ∀ x, f (-x) = f x) (R : ℝ) (x : E d) :
    compactCutoff f R (-x) = compactCutoff f R x := by
  simp only [compactCutoff_apply, scaledUnitCutoff_even, hf]

#print axioms compactCutoff_support
#print axioms compactCutoff_hasCompactSupport
#print axioms compactCutoff_real
#print axioms compactCutoff_even
#print axioms compactCutoff_tendsto
#print axioms cutoffErrorConstant_nonneg
#print axioms compactCutoff_product_derivative_bound
#print axioms compactCutoff_error_derivative_bound
#print axioms compactCutoff_error_seminorm_bound
#print axioms scaled_schwartz_derivative_bound
#print axioms scaledUnitCutoff_apply
#print axioms compactCutoff_apply
#print axioms scaledUnitCutoff_one
#print axioms compactCutoff_eventuallyEq
#print axioms compactCutoff_derivative_eq
#print axioms scaledUnitCutoff_derivative_bound
#print axioms schwartz_weighted_derivative_tail
#print axioms unitCutoffSchwartz_apply
#print axioms unitCutoffSchwartz_one

end Bandlimited
