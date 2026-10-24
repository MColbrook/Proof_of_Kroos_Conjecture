module

public import Bandlimited.SphericalCaps
public import Mathlib.MeasureTheory.Integral.Layercake
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-! Quantitative spherical kernel integrals from sharp cap growth. -/
@[expose] public section
open scoped BigOperators
open MeasureTheory Set
noncomputable section
namespace Bandlimited.SphereQuadrature

def tailIntegralConstant (s : ℕ) (L : ℝ) : ℝ :=
  (2 * capUpperConstant s) / (1 - (s : ℝ) / L)

set_option maxHeartbeats 300000 in
theorem sphericalTailIntegral_upper (s : ℕ) (L : ℝ) (hL : (s : ℝ) < L)
    (lam : ℝ) (hlam : 1 ≤ lam) (u : Sphere (s + 1)) :
    sphericalTailIntegral s lam L u ≤ tailIntegralConstant s L * (lam ^ s)⁻¹ := by
  have hLp : 0 < L := lt_of_le_of_lt (Nat.cast_nonneg s) hL
  have hlp : 0 < lam := by linarith
  let H : C(Sphere (s + 1) × Sphere (s + 1), ℝ) :=
    ⟨fun p => tailKernel lam L p.1 p.2, continuous_tailKernel lam L hlp.le⟩
  have hint : Integrable (tailKernel lam L u) (surfaceMeasure s) :=
    (H.curry u).continuous.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hnn (v : Sphere (s + 1)) : 0 ≤ tailKernel lam L u v :=
    Real.rpow_nonneg (by have h := rho_nonneg u v; positivity) _
  have hle (v : Sphere (s + 1)) : tailKernel lam L u v ≤ 1 := by
    have hb : 1 ≤ 1 + lam * rho u v := by nlinarith [rho_nonneg u v]
    simpa only [tailKernel, Real.one_rpow] using
      Real.rpow_le_rpow_of_nonpos zero_lt_one hb (neg_nonpos.mpr hLp.le)
  let a : ℝ := -1 / L
  let b : ℝ := -(s : ℝ) / L
  let K : ℝ := (2 * capUpperConstant s) * (lam ^ s)⁻¹
  have ha : a ≤ 0 := by dsimp [a]; exact div_nonpos_of_nonpos_of_nonneg (by norm_num) hLp.le
  have hb : -1 < b := by
    dsimp [b]
    apply (lt_div_iff₀ hLp).mpr
    linarith
  have hlevel (t : ℝ) (ht : t ∈ Ioc (0 : ℝ) 1) :
      (surfaceMeasure s).real {v | t ≤ tailKernel lam L u v} ≤ K * t ^ b := by
    have hsubset : {v | t ≤ tailKernel lam L u v} ⊆ projectiveBall u (t ^ a / lam) := by
      intro v hv
      have hbase : 0 < 1 + lam * rho u v := by have h := rho_nonneg u v; positivity
      have hp := Real.rpow_le_rpow_of_nonpos ht.1 hv ha
      have hab : (-L) * a = 1 := by dsimp [a]; field_simp
      have hpow : (tailKernel lam L u v) ^ a = 1 + lam * rho u v := by
        unfold tailKernel
        rw [← Real.rpow_mul hbase.le, hab, Real.rpow_one]
      rw [hpow] at hp
      apply (lt_div_iff₀ hlp).mpr
      linarith
    have hrad : 0 < t ^ a / lam := div_pos (Real.rpow_pos_of_pos ht.1 _) hlp
    have hpow : (t ^ a) ^ s = t ^ b := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul ht.1.le]
      congr 1
      dsimp [a, b]
      ring
    calc
      _ ≤ (surfaceMeasure s).real (projectiveBall u (t ^ a / lam)) := measureReal_mono hsubset
      _ ≤ (2 * capUpperConstant s) * (t ^ a / lam) ^ s := projectiveBall_upper s u hrad
      _ = K * t ^ b := by rw [div_pow, hpow]; dsimp [K]; ring
  have hmajor : IntegrableOn (fun t : ℝ => K * t ^ b) (Ioc (0 : ℝ) 1) :=
    ((intervalIntegral.intervalIntegrable_rpow' hb (a := 0) (b := 1)).1).const_mul K
  have hbound := integral_mono_of_nonneg
    (μ := (volume : Measure ℝ).restrict (Ioc 0 1))
    (Filter.Eventually.of_forall fun t => ENNReal.toReal_nonneg)
    hmajor (by filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht; exact hlevel t ht)
  have hvalue : (∫ t : ℝ in Ioc 0 1, t ^ b) = 1 / (b + 1) := by
    rw [← intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1),
      integral_rpow (Or.inl hb)]
    simp [Real.zero_rpow (by linarith : b + 1 ≠ 0)]
  unfold sphericalTailIntegral
  rw [hint.integral_eq_integral_Ioc_meas_le
    (Filter.Eventually.of_forall hnn) (Filter.Eventually.of_forall hle)]
  calc
    _ ≤ ∫ t : ℝ in Ioc 0 1, K * t ^ b := hbound
    _ = K * (1 / (b + 1)) := by rw [integral_const_mul, hvalue]
    _ = tailIntegralConstant s L * (lam ^ s)⁻¹ := by
      dsimp [K, b, tailIntegralConstant]
      ring

#print axioms sphericalTailIntegral_upper
end Bandlimited.SphereQuadrature
end
