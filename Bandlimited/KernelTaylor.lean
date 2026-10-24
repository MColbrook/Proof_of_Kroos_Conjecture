module

public import Bandlimited.PolynomialTransport
public import Bandlimited.FourierTransport
public import NumericalBounds
public import Mathlib.Analysis.Complex.Exponential
public import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Taylor polynomials and fraction-free homogeneous extension

This module develops the actual algebraic homogeneous extension in the
ambient Euclidean space. The Fourier Taylor estimates are developed with
the exact bandwidth constants; no analytic bound is introduced as an axiom.
-/

@[expose] public section
noncomputable section
open Set MeasureTheory
open scoped BigOperators
namespace Bandlimited
namespace KernelTaylor

 theorem homogeneous_eval_smul {d k : ℕ} {p : Polynomial d}
    (hp : p.IsHomogeneous k) (a : ℝ) (x : E d) :
    evalPolynomial p (a • x) = a ^ k * evalPolynomial p x := by
  classical
  simp only [evalPolynomial, MvPolynomial.eval_eq, PiLp.smul_apply, smul_eq_mul,
    mul_pow, Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro u hu
  have hdegree := hp.degree_eq_sum_deg_support hu
  rw [← hdegree]
  ring

 theorem sum_components_up_to {d m : ℕ} (p : Polynomial d) (hp : p.totalDegree ≤ m) :
    (∑ k ∈ Finset.range (m + 1), MvPolynomial.homogeneousComponent k p) = p := by
  have hsub : Finset.range (p.totalDegree + 1) ⊆ Finset.range (m + 1) :=
    Finset.range_mono (Nat.add_le_add_right hp 1)
  calc
    _ = ∑ k ∈ Finset.range (p.totalDegree + 1), MvPolynomial.homogeneousComponent k p := by
      symm
      apply Finset.sum_subset hsub
      intro k hk hnot
      exact MvPolynomial.homogeneousComponent_eq_zero k p (by
        simp only [Finset.mem_range] at hk hnot
        omega)
    _ = p := MvPolynomial.sum_homogeneousComponent p

 def homogenized {d e : ℕ} (m N : ℕ) (p : Polynomial e) (ell : Polynomial d)
    (b : E d →ₗ[ℝ] E e) : Polynomial d :=
  ∑ k ∈ Finset.range (m + 1), ell ^ (N - k) *
    polynomialPullback b (MvPolynomial.homogeneousComponent k p)

 theorem homogenized_homogeneous {d e m N : ℕ} (hmN : m ≤ N)
    (p : Polynomial e) (ell : Polynomial d) (hell : ell.IsHomogeneous 1)
    (b : E d →ₗ[ℝ] E e) :
    (homogenized m N p ell b).IsHomogeneous N := by
  classical
  apply MvPolynomial.IsHomogeneous.sum
  intro k hk
  have hkN : k ≤ N := by
    simp only [Finset.mem_range] at hk
    omega
  have hpow : (ell ^ (N - k)).IsHomogeneous (N - k) := by
    simpa only [one_mul] using hell.pow (N - k)
  have hcomp : (polynomialPullback b (MvPolynomial.homogeneousComponent k p)).IsHomogeneous k :=
    polynomialPullback_homogeneous b (MvPolynomial.homogeneousComponent_isHomogeneous k p)
  simpa only [Nat.sub_add_cancel hkN] using hpow.mul hcomp

 theorem homogenized_eval {d e m N : ℕ} (hmN : m ≤ N)
    (p : Polynomial e) (hp : p.totalDegree ≤ m) (ell : Polynomial d)
    (b : E d →ₗ[ℝ] E e) (x : E d) (hx : evalPolynomial ell x ≠ 0) :
    evalPolynomial (homogenized m N p ell b) x =
      (evalPolynomial ell x) ^ N *
        evalPolynomial p ((evalPolynomial ell x)⁻¹ • b x) := by
  classical
  have hleft : evalPolynomial (homogenized m N p ell b) x =
      ∑ k ∈ Finset.range (m + 1), (evalPolynomial ell x) ^ (N - k) *
        evalPolynomial (polynomialPullback b (MvPolynomial.homogeneousComponent k p)) x := by
    simp only [homogenized, evalPolynomial, map_sum, map_mul, map_pow]
  have heval : evalPolynomial p ((evalPolynomial ell x)⁻¹ • b x) =
      ∑ k ∈ Finset.range (m + 1),
        evalPolynomial (MvPolynomial.homogeneousComponent k p)
          ((evalPolynomial ell x)⁻¹ • b x) := by
    conv_lhs => rw [← sum_components_up_to p hp]
    simp only [evalPolynomial, map_sum]
  rw [hleft, heval, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k hk
  have hkN : k ≤ N := by
    simp only [Finset.mem_range] at hk
    omega
  rw [polynomialPullback_eval, homogeneous_eval_smul
    (MvPolynomial.homogeneousComponent_isHomogeneous k p)]
  rw [pow_sub₀ (evalPolynomial ell x) hx hkN, inv_pow]
  ring

 theorem homogenized_even {d e m N : ℕ} (hmN : m ≤ N) (hN : Even N)
    (p : Polynomial e) (ell : Polynomial d) (hell : ell.IsHomogeneous 1)
    (b : E d →ₗ[ℝ] E e) (x : E d) :
    evalPolynomial (homogenized m N p ell b) (-x) =
      evalPolynomial (homogenized m N p ell b) x := by
  have h := homogeneous_eval_smul (homogenized_homogeneous hmN p ell hell b) (-1) x
  simpa only [neg_one_smul, hN.neg_one_pow, one_mul] using h

 theorem homogenized_degree {d e m N : ℕ} (hmN : m ≤ N)
    (p : Polynomial e) (ell : Polynomial d) (hell : ell.IsHomogeneous 1)
    (b : E d →ₗ[ℝ] E e) (x : E d)
    (hvalue : evalPolynomial (homogenized m N p ell b) x ≠ 0) :
    (homogenized m N p ell b).totalDegree = N := by
  apply (homogenized_homogeneous hmN p ell hell b).totalDegree
  intro hzero
  apply hvalue
  rw [hzero]
  simp [evalPolynomial]

 def hermitianFrequency {d : ℕ} (φ : E d → ℂ) (ξ : E d) : ℂ :=
  ((1 : ℂ) / 2) * (φ ξ + starRingEnd ℂ (φ (-ξ)))

 theorem hermitianFrequency_symmetry {d : ℕ} (φ : E d → ℂ) (ξ : E d) :
    starRingEnd ℂ (hermitianFrequency φ (-ξ)) = hermitianFrequency φ ξ := by
  simp only [hermitianFrequency, map_mul, map_add, map_div₀, map_one, map_ofNat,
    neg_neg, Complex.conj_conj]
  ring

 theorem hermitianFrequency_smooth {d : ℕ} {σ : ℝ} {φ : E d → ℂ}
    (hφ : SmoothFrequency σ φ) : SmoothFrequency σ (hermitianFrequency φ) :=
  (hφ.add_same_bandwidth hφ.conj_reflect).const_mul ((1 : ℂ) / 2)

 theorem inverseFourier_hermitianFrequency {d : ℕ} {σ : ℝ} {φ : E d → ℂ}
    (hφ : SmoothFrequency σ φ) (hreal : IsRealValued (inverseFourier φ)) :
    inverseFourier (hermitianFrequency φ) = inverseFourier φ := by
  funext x
  change inverseFourier (fun ξ => ((1 : ℂ) / 2) *
    (φ ξ + starRingEnd ℂ (φ (-ξ)))) x = _
  rw [inverseFourier_const_mul, inverseFourier_add hφ hφ.conj_reflect,
    inverseFourier_conj_reflect]
  rw [Complex.conj_eq_iff_im.mpr (hreal x)]
  ring

 theorem complex_linear_power_expansion {d k : ℕ} (N : ℝ) (ξ t : E d) :
    (Complex.I * (N : ℂ) * ((∑ i : Fin d, ξ i * t i : ℝ) : ℂ)) ^ k =
      ∑ j : Fin k → Fin d,
        (∏ i : Fin k, Complex.I * (N : ℂ) * (ξ (j i) : ℂ)) *
          ((∏ i : Fin k, t (j i) : ℝ) : ℂ) := by
  classical
  have hbase : Complex.I * (N : ℂ) * ((∑ i : Fin d, ξ i * t i : ℝ) : ℂ) =
      ∑ i : Fin d, (Complex.I * (N : ℂ) * (ξ i : ℂ)) * (t i : ℂ) := by
    push_cast
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    ring
  rw [hbase]
  calc
    _ = ∏ _i : Fin k, ∑ j : Fin d,
        (Complex.I * (N : ℂ) * (ξ j : ℂ)) * (t j : ℂ) := by simp
    _ = ∑ j : Fin k → Fin d,
        ∏ i : Fin k, (Complex.I * (N : ℂ) * (ξ (j i) : ℂ)) * (t (j i) : ℂ) := by
      rw [Fintype.prod_sum]
    _ = _ := by
      apply Finset.sum_congr rfl
      intro j hj
      rw [Finset.prod_mul_distrib]
      push_cast
      rfl

 def fourierMoment {d k : ℕ} (N : ℝ) (φ : E d → ℂ)
    (j : Fin k → Fin d) : ℂ :=
  ∫ ξ : E d, φ ξ *
    (∏ i : Fin k, Complex.I * (N : ℂ) * (ξ (j i) : ℂ)) / (k.factorial : ℂ)

 theorem fourierMoment_real {d k : ℕ} (N : ℝ) (φ : E d → ℂ)
    (hφ : ∀ ξ, starRingEnd ℂ (φ (-ξ)) = φ ξ) (j : Fin k → Fin d) :
    (fourierMoment N φ j).im = 0 := by
  apply Complex.conj_eq_iff_im.mp
  change starRingEnd ℂ (∫ ξ : E d, φ ξ *
      (∏ i : Fin k, Complex.I * (N : ℂ) * (ξ (j i) : ℂ)) / (k.factorial : ℂ)) = _
  rw [← integral_conj]
  let H : E d → ℂ := fun ξ => φ ξ *
    (∏ i : Fin k, Complex.I * (N : ℂ) * (ξ (j i) : ℂ)) / (k.factorial : ℂ)
  have hconj (ξ : E d) : starRingEnd ℂ (φ ξ) = φ (-ξ) := by
    simpa only [neg_neg] using hφ (-ξ)
  have hpoint (ξ : E d) : starRingEnd ℂ (H ξ) = H (-ξ) := by
    simp only [H, map_div₀, map_mul, map_prod, hconj, Complex.conj_I,
      Complex.conj_ofReal, map_natCast, PiLp.neg_apply, Complex.ofReal_neg, mul_neg, neg_mul]
  calc
    _ = ∫ ξ : E d, H (-ξ) := integral_congr_ae (Filter.Eventually.of_forall hpoint)
    _ = ∫ ξ : E d, H ξ := by
      simpa only [neg_one_smul, abs_inv, abs_pow, abs_neg, abs_one,
        one_pow, inv_one, one_smul] using
        (MeasureTheory.Measure.integral_comp_smul volume H (-1))

 def momentPolynomial {d : ℕ} (N : ℝ) (φ : E d → ℂ) (k : ℕ) : Polynomial d :=
  ∑ j : Fin k → Fin d, MvPolynomial.C (fourierMoment N φ j).re *
    ∏ i : Fin k, MvPolynomial.X (j i)

 theorem momentPolynomial_homogeneous {d : ℕ} (N : ℝ) (φ : E d → ℂ) (k : ℕ) :
    (momentPolynomial N φ k).IsHomogeneous k := by
  classical
  apply MvPolynomial.IsHomogeneous.sum
  intro j hj
  apply MvPolynomial.IsHomogeneous.C_mul
  have h := MvPolynomial.IsHomogeneous.prod Finset.univ
    (fun i : Fin k => (MvPolynomial.X (j i) : Polynomial d)) (fun _ => 1)
    (fun i _ => MvPolynomial.isHomogeneous_X ℝ (j i))
  simpa only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul,
    mul_one, nsmul_eq_mul] using h

 def fourierTaylorPolynomial {d : ℕ} (N : ℝ) (φ : E d → ℂ) (m : ℕ) : Polynomial d :=
  ∑ k ∈ Finset.range (m + 1), momentPolynomial N φ k


 theorem integrable_frequency_times {d : ℕ} {σ : ℝ} {φ : E d → ℂ}
    (hφ : SmoothFrequency σ φ) (g : E d → ℂ) (hg : Continuous g) :
    Integrable (fun ξ => φ ξ * g ξ) := by
  have hs : HasCompactSupport (fun ξ => φ ξ * g ξ) := hφ.2.1.mul_right
  exact (hφ.1.continuous.mul hg).integrable_of_hasCompactSupport hs

 theorem moment_integrand_integrable {d k : ℕ} {σ : ℝ} {φ : E d → ℂ}
    (hφ : SmoothFrequency σ φ) (N : ℝ) (j : Fin k → Fin d) :
    Integrable (fun ξ : E d => φ ξ *
      (∏ i : Fin k, Complex.I * (N : ℂ) * (ξ (j i) : ℂ)) / (k.factorial : ℂ)) := by
  have hg : Continuous (fun ξ : E d =>
      (∏ i : Fin k, Complex.I * (N : ℂ) * (ξ (j i) : ℂ)) / (k.factorial : ℂ)) := by
    fun_prop
  simpa only [mul_div_assoc] using integrable_frequency_times hφ _ hg

 theorem power_integrand_integrable {d k : ℕ} {σ : ℝ} {φ : E d → ℂ}
    (hφ : SmoothFrequency σ φ) (N : ℝ) (t : E d) :
    Integrable (fun ξ : E d => φ ξ *
      (Complex.I * (N : ℂ) * ((∑ i : Fin d, ξ i * t i : ℝ) : ℂ)) ^ k /
        (k.factorial : ℂ)) := by
  have hg : Continuous (fun ξ : E d =>
      (Complex.I * (N : ℂ) * ((∑ i : Fin d, ξ i * t i : ℝ) : ℂ)) ^ k /
        (k.factorial : ℂ)) := by
    fun_prop
  simpa only [mul_div_assoc] using integrable_frequency_times hφ _ hg

 theorem momentPolynomial_eval_integral {d : ℕ} {σ : ℝ} {φ : E d → ℂ}
    (hφ : SmoothFrequency σ φ) (N : ℝ) (k : ℕ) (t : E d) :
    evalPolynomial (momentPolynomial N φ k) t =
      (∫ ξ : E d, φ ξ *
        (Complex.I * (N : ℂ) * ((∑ i : Fin d, ξ i * t i : ℝ) : ℂ)) ^ k /
          (k.factorial : ℂ)).re := by
  classical
  have hpoint (ξ : E d) : φ ξ *
      (Complex.I * (N : ℂ) * ((∑ i : Fin d, ξ i * t i : ℝ) : ℂ)) ^ k /
        (k.factorial : ℂ) =
      ∑ j : Fin k → Fin d, (φ ξ *
        (∏ i : Fin k, Complex.I * (N : ℂ) * (ξ (j i) : ℂ)) / (k.factorial : ℂ)) *
          ((∏ i : Fin k, t (j i) : ℝ) : ℂ) := by
    rw [complex_linear_power_expansion, Finset.mul_sum, Finset.sum_div]
    apply Finset.sum_congr rfl
    intro j hj
    ring
  have heq : (fun ξ : E d => φ ξ *
      (Complex.I * (N : ℂ) * ((∑ i : Fin d, ξ i * t i : ℝ) : ℂ)) ^ k /
        (k.factorial : ℂ)) =
      (fun ξ : E d => ∑ j : Fin k → Fin d, (φ ξ *
        (∏ i : Fin k, Complex.I * (N : ℂ) * (ξ (j i) : ℂ)) / (k.factorial : ℂ)) *
          ((∏ i : Fin k, t (j i) : ℝ) : ℂ)) := funext hpoint
  rw [heq, integral_finsetSum Finset.univ (fun j _ =>
    (moment_integrand_integrable hφ N j).mul_const _)]
  simp only [integral_mul_const, fourierMoment, Complex.re_sum,
    momentPolynomial, evalPolynomial, map_sum, map_mul, MvPolynomial.eval_C,
    map_prod, MvPolynomial.eval_X, Complex.mul_re, Complex.ofReal_re,
    Complex.ofReal_im, mul_zero, sub_zero]

 theorem fourierTaylorPolynomial_eval_integral {d : ℕ} {σ : ℝ} {φ : E d → ℂ}
    (hφ : SmoothFrequency σ φ) (N : ℝ) (m : ℕ) (t : E d) :
    evalPolynomial (fourierTaylorPolynomial N φ m) t =
      (∫ ξ : E d, φ ξ * ∑ k ∈ Finset.range (m + 1),
        (Complex.I * (N : ℂ) * ((∑ i : Fin d, ξ i * t i : ℝ) : ℂ)) ^ k /
          (k.factorial : ℂ)).re := by
  classical
  have heq : (fun ξ : E d => φ ξ * ∑ k ∈ Finset.range (m + 1),
      (Complex.I * (N : ℂ) * ((∑ i : Fin d, ξ i * t i : ℝ) : ℂ)) ^ k /
        (k.factorial : ℂ)) =
      (fun ξ : E d => ∑ k ∈ Finset.range (m + 1), φ ξ *
        (Complex.I * (N : ℂ) * ((∑ i : Fin d, ξ i * t i : ℝ) : ℂ)) ^ k /
          (k.factorial : ℂ)) := by
    funext ξ
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k hk
    ring
  rw [heq, integral_finsetSum _ (fun k _ => power_integrand_integrable hφ N t)]
  simp only [fourierTaylorPolynomial, evalPolynomial, map_sum, Complex.re_sum]
  apply Finset.sum_congr rfl
  intro k hk
  exact momentPolynomial_eval_integral hφ N k t

 theorem fourierTaylorPolynomial_degree_le {d : ℕ} (N : ℝ) (φ : E d → ℂ) (m : ℕ) :
    (fourierTaylorPolynomial N φ m).totalDegree ≤ m := by
  classical
  apply MvPolynomial.totalDegree_finsetSum_le
  intro k hk
  apply (momentPolynomial_homogeneous N φ k).totalDegree_le.trans
  simp only [Finset.mem_range] at hk
  omega

 theorem fourierTaylor_homogenized {d N : ℕ} (φ : E d → ℂ)
    (ell : Polynomial d) (hell : ell.IsHomogeneous 1) (b : E d →ₗ[ℝ] E d) :
    (homogenized (N / 2) N (fourierTaylorPolynomial (N : ℝ) φ (N / 2)) ell b).IsHomogeneous N :=
  homogenized_homogeneous (Nat.div_le_self N 2) _ ell hell b

#print axioms fourierTaylorPolynomial_degree_le
#print axioms fourierTaylor_homogenized

 theorem one_div_sixteen_le_exp_neg_two : (1 : ℝ) / 16 ≤ Real.exp (-2) := by
  have hlog : 1 ≤ Real.log 4 := by
    have h := Numerics.taylor_log_margin
    have hpos : 0 ≤ 1 / (32 * Real.exp 1) := by positivity
    linarith
  have hquarter : (1 : ℝ) / 4 ≤ Real.exp (-1) := by
    calc
      (1 : ℝ) / 4 = Real.exp (-Real.log 4) := by
        rw [Real.exp_neg, Real.exp_log (by norm_num : (0 : ℝ) < 4)]
        norm_num
      _ ≤ Real.exp (-1) := Real.exp_le_exp.mpr (neg_le_neg hlog)
  calc
    (1 : ℝ) / 16 = ((1 : ℝ) / 4) ^ 2 := by norm_num
    _ ≤ Real.exp (-1) ^ 2 := pow_le_pow_left₀ (by norm_num) hquarter 2
    _ = Real.exp (-2) := by
      rw [pow_two, ← Real.exp_add]
      norm_num

 theorem complex_taylor_remainder {m : ℕ} (hm : 1 ≤ m) (z : ℂ)
    (hz : ‖z‖ ≤ (m : ℝ) / (16 * Real.exp 1)) :
    ‖Complex.exp z - ∑ k ∈ Finset.range (m + 1), z ^ k / k.factorial‖ ≤
      Real.exp (-(2 * (m : ℝ))) := by
  let c : ℝ := 1 / (16 * Real.exp 1)
  have hc : 0 < c := by dsimp [c]; positivity
  have hc16 : c ≤ (1 : ℝ) / 16 := by
    apply (div_le_iff₀ (by positivity : (0 : ℝ) < 16 * Real.exp 1)).2
    nlinarith [Numerics.exp_one_ge_one]
  have hce : c * Real.exp 1 = (1 : ℝ) / 16 := by
    dsimp [c]
    field_simp
  have hzm : ‖z‖ ≤ c * (m : ℝ) := by
    simpa only [c, div_eq_mul_inv, one_mul, mul_comm] using hz
  have hm0 : 0 ≤ (m : ℝ) := Nat.cast_nonneg _
  have hcond : ‖z‖ / ((m + 1).succ : ℝ) ≤ 1 / 2 := by
    apply (div_le_iff₀ (by positivity : (0 : ℝ) < ((m + 1).succ : ℝ))).2
    have hprod := mul_le_mul_of_nonneg_right hc16 hm0
    push_cast
    nlinarith
  calc
    _ ≤ ‖z‖ ^ (m + 1) / ((m + 1).factorial : ℝ) * 2 := Complex.exp_bound' hcond
    _ ≤ (c * (m : ℝ)) ^ (m + 1) / ((m + 1).factorial : ℝ) * 2 := by
      apply mul_le_mul_of_nonneg_right _ (by norm_num)
      apply div_le_div_of_nonneg_right _ (by positivity)
      exact pow_le_pow_left₀ (norm_nonneg _) hzm (m + 1)
    _ = 2 * c ^ (m + 1) * ((m : ℝ) ^ (m + 1) / ((m + 1).factorial : ℝ)) := by
      rw [mul_pow]
      ring
    _ ≤ 2 * c ^ (m + 1) * Real.exp (m : ℝ) :=
      mul_le_mul_of_nonneg_left (Real.pow_div_factorial_le_exp (m : ℝ) hm0 (m + 1)) (by positivity)
    _ = 2 * c * (c * Real.exp 1) ^ m := by
      have he : Real.exp (m : ℝ) = Real.exp 1 ^ m := by
        simpa only [mul_one] using Real.exp_nat_mul (1 : ℝ) m
      rw [he, pow_succ, mul_pow]
      ring
    _ = 2 * c * ((1 : ℝ) / 16) ^ m := by rw [hce]
    _ ≤ ((1 : ℝ) / 16) ^ m := by
      have hp : 0 ≤ ((1 : ℝ) / 16) ^ m := by positivity
      simpa only [one_mul] using
        mul_le_mul_of_nonneg_right (by linarith : 2 * c ≤ 1) hp
    _ ≤ Real.exp (-2) ^ m :=
      pow_le_pow_left₀ (by positivity) one_div_sixteen_le_exp_neg_two m
    _ = Real.exp (-(2 * (m : ℝ))) := by
      rw [← Real.exp_nat_mul]
      congr 1
      ring


 theorem phase_norm_le {d : ℕ} (N : ℝ) (ξ t : E d) :
    ‖Complex.I * (N : ℂ) * ((∑ i : Fin d, ξ i * t i : ℝ) : ℂ)‖ ≤
      |N| * (‖ξ‖ * ‖t‖) := by
  have hdot : |∑ i : Fin d, ξ i * t i| ≤ ‖ξ‖ * ‖t‖ := by
    have h := abs_real_inner_le_norm t ξ
    rw [mul_comm ‖t‖ ‖ξ‖] at h
    simpa only [EuclideanSpace.inner_eq_star_dotProduct, dotProduct, star_trivial,
      Real.norm_eq_abs] using h
  simpa only [norm_mul, Complex.norm_I, Complex.norm_real, Real.norm_eq_abs, one_mul]
    using mul_le_mul_of_nonneg_left hdot (abs_nonneg N)

 theorem phase_norm_on_support {d m : ℕ} {σ D : ℝ} {φ : E d → ℂ}
    (hφ : SmoothFrequency σ φ) (hD : 1 ≤ D)
    (hσ : σ ≤ 1 / (64 * Real.exp 1 * D)) (t : E d) (ht : ‖t‖ ≤ 2 * D)
    (ξ : E d) (hξ : φ ξ ≠ 0) :
    ‖Complex.I * ((2 * (m : ℝ)) : ℂ) *
      ((∑ i : Fin d, ξ i * t i : ℝ) : ℂ)‖ ≤ (m : ℝ) / (16 * Real.exp 1) := by
  have hD0 : 0 < D := by linarith
  have hsmall : ‖ξ‖ < σ := by
    simpa only [Metric.mem_ball, dist_zero_right] using
      hφ.2.2 (show ξ ∈ tsupport φ from subset_closure hξ)
  have hσ0 : 0 ≤ σ := (norm_nonneg ξ).trans hsmall.le
  have hprod : ‖ξ‖ * ‖t‖ ≤ σ * (2 * D) :=
    mul_le_mul hsmall.le ht (norm_nonneg _) hσ0
  have hsigma : σ * (2 * D) ≤ 1 / (32 * Real.exp 1) := by
    have hh := (le_div_iff₀ (by positivity : (0 : ℝ) < 64 * Real.exp 1 * D)).mp hσ
    apply (le_div_iff₀ (by positivity : (0 : ℝ) < 32 * Real.exp 1)).2
    nlinarith
  have hp := phase_norm_le (2 * (m : ℝ)) ξ t
  simp only [Complex.ofReal_mul, Complex.ofReal_ofNat] at hp
  calc
    _ ≤ |2 * (m : ℝ)| * (‖ξ‖ * ‖t‖) := hp
    _ ≤ (2 * (m : ℝ)) * (1 / (32 * Real.exp 1)) := by
      rw [abs_of_nonneg (by positivity)]
      exact mul_le_mul_of_nonneg_left (hprod.trans hsigma) (by positivity)
    _ = _ := by ring

 theorem fourierTaylor_integral_error {d m : ℕ} {σ D : ℝ} {φ : E d → ℂ}
    (hφ : SmoothFrequency σ φ) (hm : 1 ≤ m) (hD : 1 ≤ D)
    (hσ : σ ≤ 1 / (64 * Real.exp 1 * D)) (t : E d) (ht : ‖t‖ ≤ 2 * D) :
    |evalPolynomial (fourierTaylorPolynomial (2 * (m : ℝ)) φ m) t -
      (∫ ξ : E d, φ ξ * Complex.exp (Complex.I * ((2 * (m : ℝ)) : ℂ) *
        ((∑ i : Fin d, ξ i * t i : ℝ) : ℂ))).re| ≤
      (∫ ξ : E d, ‖φ ξ‖) * Real.exp (-(2 * (m : ℝ))) := by
  classical
  let z : E d → ℂ := fun ξ => Complex.I * ((2 * (m : ℝ)) : ℂ) *
    ((∑ i : Fin d, ξ i * t i : ℝ) : ℂ)
  let T : E d → ℂ := fun ξ => ∑ k ∈ Finset.range (m + 1), z ξ ^ k / (k.factorial : ℂ)
  have hz : Continuous z := by fun_prop
  have hT : Continuous T := by fun_prop
  have hiT := integrable_frequency_times hφ T hT
  have hie := integrable_frequency_times hφ (fun ξ => Complex.exp (z ξ))
    (Complex.continuous_exp.comp hz)
  have hierr : Integrable (fun ξ => φ ξ * (T ξ - Complex.exp (z ξ))) :=
    integrable_frequency_times hφ _ (hT.sub (Complex.continuous_exp.comp hz))
  have hinorm : Integrable (fun ξ : E d => ‖φ ξ‖) :=
    hφ.1.continuous.integrable_of_hasCompactSupport hφ.2.1 |>.norm
  have hbound (ξ : E d) : ‖φ ξ * (T ξ - Complex.exp (z ξ))‖ ≤
      ‖φ ξ‖ * Real.exp (-(2 * (m : ℝ))) := by
    by_cases hξ : φ ξ = 0
    · simp only [hξ, zero_mul, norm_zero, le_refl]
    · rw [norm_mul]
      apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
      rw [norm_sub_rev]
      exact complex_taylor_remainder hm (z ξ) (phase_norm_on_support hφ hD hσ t ht ξ hξ)
  rw [fourierTaylorPolynomial_eval_integral hφ]
  simp only [Complex.ofReal_mul, Complex.ofReal_ofNat]
  change |(∫ ξ : E d, φ ξ * T ξ).re -
    (∫ ξ : E d, φ ξ * Complex.exp (z ξ)).re| ≤ _
  rw [← Complex.sub_re, ← integral_sub hiT hie]
  have hrewrite : (fun ξ : E d => φ ξ * T ξ - φ ξ * Complex.exp (z ξ)) =
      (fun ξ : E d => φ ξ * (T ξ - Complex.exp (z ξ))) := by
    funext ξ
    ring
  rw [hrewrite]
  calc
    _ ≤ ‖∫ ξ : E d, φ ξ * (T ξ - Complex.exp (z ξ))‖ := Complex.abs_re_le_norm _
    _ ≤ ∫ ξ : E d, ‖φ ξ * (T ξ - Complex.exp (z ξ))‖ := norm_integral_le_integral_norm _
    _ ≤ ∫ ξ : E d, ‖φ ξ‖ * Real.exp (-(2 * (m : ℝ))) :=
      integral_mono hierr.norm (hinorm.mul_const _) hbound
    _ = _ := integral_mul_const _ _

#print axioms fourierTaylor_integral_error


 def fourierMass {d : ℕ} (φ : E d → ℂ) : ℝ :=
  ((2 * Real.pi) ^ d : ℝ)⁻¹ * ∫ ξ : E d, ‖φ ξ‖

 def normalizedFrequency {d : ℕ} (φ : E d → ℂ) (ξ : E d) : ℂ :=
  (((2 * Real.pi) ^ d : ℝ)⁻¹ : ℂ) * φ ξ

 theorem normalizedFrequency_smooth {d : ℕ} {σ : ℝ} {φ : E d → ℂ}
    (hφ : SmoothFrequency σ φ) : SmoothFrequency σ (normalizedFrequency φ) :=
  hφ.const_mul _

 theorem fourierMass_nonneg {d : ℕ} (φ : E d → ℂ) : 0 ≤ fourierMass φ := by
  unfold fourierMass
  exact mul_nonneg (by positivity) (integral_nonneg fun ξ => norm_nonneg (φ ξ))

 theorem integral_norm_normalizedFrequency {d : ℕ} (φ : E d → ℂ) :
    (∫ ξ : E d, ‖normalizedFrequency φ ξ‖) = fourierMass φ := by
  have hc : 0 ≤ ((2 * Real.pi) ^ d : ℝ)⁻¹ := by positivity
  simp only [normalizedFrequency, norm_mul, ← Complex.ofReal_inv, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg hc, fourierMass, integral_const_mul]

 theorem inverseFourier_scaled_integral {d : ℕ} (φ : E d → ℂ) (N : ℝ) (t : E d) :
    inverseFourier φ (N • t) = ∫ ξ : E d, normalizedFrequency φ ξ *
      Complex.exp (Complex.I * (N : ℂ) * ((∑ i : Fin d, ξ i * t i : ℝ) : ℂ)) := by
  unfold inverseFourier
  rw [← integral_const_mul]
  apply integral_congr_ae
  filter_upwards [] with ξ
  simp only [normalizedFrequency, PiLp.smul_apply, smul_eq_mul]
  rw [mul_assoc]
  congr 2
  push_cast
  simp only [Finset.mul_sum]
  apply congrArg Complex.exp
  apply Finset.sum_congr rfl
  intro i hi
  push_cast
  ring

 def approximatingPolynomial {d : ℕ} (N : ℕ) (φ : E d → ℂ) : Polynomial d :=
  fourierTaylorPolynomial (N : ℝ) (normalizedFrequency φ) (N / 2)

 theorem approximatingPolynomial_degree {d : ℕ} (N : ℕ) (φ : E d → ℂ) :
    (approximatingPolynomial N φ).totalDegree ≤ N / 2 :=
  fourierTaylorPolynomial_degree_le _ _ _

 theorem approximatingPolynomial_chart_error {d N : ℕ} {σ D : ℝ} {φ : E d → ℂ}
    (hφ : SmoothFrequency σ φ) (hN : Even N) (hN2 : 2 ≤ N) (hD : 1 ≤ D)
    (hσ : σ ≤ 1 / (64 * Real.exp 1 * D)) (t : E d) (ht : ‖t‖ ≤ 2 * D) :
    |evalPolynomial (approximatingPolynomial N φ) t - (inverseFourier φ ((N : ℝ) • t)).re| ≤
      fourierMass φ * Real.exp (-(N : ℝ)) := by
  have hNm : N = 2 * (N / 2) := by
    have hmod := Nat.mod_eq_zero_of_dvd hN.two_dvd
    omega
  have hm : 1 ≤ N / 2 := by omega
  have hcast : (N : ℝ) = 2 * ((N / 2 : ℕ) : ℝ) := by exact_mod_cast hNm
  have h := fourierTaylor_integral_error (normalizedFrequency_smooth hφ) hm hD hσ t ht
  rw [integral_norm_normalizedFrequency] at h
  rw [inverseFourier_scaled_integral]
  simpa only [approximatingPolynomial, hcast, Complex.ofReal_mul, Complex.ofReal_ofNat] using h

#print axioms approximatingPolynomial_degree
#print axioms approximatingPolynomial_chart_error

 theorem small_height_exponential_bound (m : ℕ) :
    ((1 : ℝ) / 2) ^ m * Real.exp ((2 * (m : ℝ)) / (64 * Real.exp 1)) ≤
      Real.exp (-(2 * (m : ℝ)) / 4) := by
  have hhalf : (1 : ℝ) / 2 = Real.exp (-Real.log 2) := by
    rw [Real.exp_neg, Real.exp_log (by norm_num : (0 : ℝ) < 2)]
    norm_num
  rw [hhalf, ← Real.exp_nat_mul, ← Real.exp_add]
  apply Real.exp_le_exp.mpr
  have h := mul_le_mul_of_nonneg_left Numerics.hyperplane_log_margin.le
    (by positivity : 0 ≤ 2 * (m : ℝ))
  ring_nf at h ⊢
  linarith


 def homogeneousApproximation {d e : ℕ} (N : ℕ) (φ : E e → ℂ)
    (ell : Polynomial d) (b : E d →ₗ[ℝ] E e) : Polynomial d :=
  ∑ k ∈ Finset.range (N / 2 + 1), ell ^ (N - k) *
    polynomialPullback b (momentPolynomial (N : ℝ) (normalizedFrequency φ) k)

 theorem homogeneousApproximation_homogeneous {d e : ℕ} (N : ℕ) (φ : E e → ℂ)
    (ell : Polynomial d) (hell : ell.IsHomogeneous 1) (b : E d →ₗ[ℝ] E e) :
    (homogeneousApproximation N φ ell b).IsHomogeneous N := by
  classical
  apply MvPolynomial.IsHomogeneous.sum
  intro k hk
  have hkN : k ≤ N := by
    simp only [Finset.mem_range] at hk
    have hdiv := Nat.div_le_self N 2
    omega
  have hpow : (ell ^ (N - k)).IsHomogeneous (N - k) := by
    simpa only [one_mul] using hell.pow (N - k)
  have hcomp := polynomialPullback_homogeneous b
    (momentPolynomial_homogeneous (N : ℝ) (normalizedFrequency φ) k)
  simpa only [Nat.sub_add_cancel hkN] using hpow.mul hcomp

 theorem homogeneousApproximation_eval {d e : ℕ} (N : ℕ) (φ : E e → ℂ)
    (ell : Polynomial d) (b : E d →ₗ[ℝ] E e) (x : E d)
    (hx : evalPolynomial ell x ≠ 0) :
    evalPolynomial (homogeneousApproximation N φ ell b) x =
      (evalPolynomial ell x) ^ N *
        evalPolynomial (approximatingPolynomial N φ) ((evalPolynomial ell x)⁻¹ • b x) := by
  classical
  have hleft : evalPolynomial (homogeneousApproximation N φ ell b) x =
      ∑ k ∈ Finset.range (N / 2 + 1), (evalPolynomial ell x) ^ (N - k) *
        evalPolynomial (polynomialPullback b
          (momentPolynomial (N : ℝ) (normalizedFrequency φ) k)) x := by
    simp only [homogeneousApproximation, evalPolynomial, map_sum, map_mul, map_pow]
  have heval : evalPolynomial (approximatingPolynomial N φ)
      ((evalPolynomial ell x)⁻¹ • b x) =
      ∑ k ∈ Finset.range (N / 2 + 1),
        evalPolynomial (momentPolynomial (N : ℝ) (normalizedFrequency φ) k)
          ((evalPolynomial ell x)⁻¹ • b x) := by
    simp only [approximatingPolynomial, fourierTaylorPolynomial, evalPolynomial, map_sum]
  rw [hleft, heval, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k hk
  have hkN : k ≤ N := by
    simp only [Finset.mem_range] at hk
    have hdiv := Nat.div_le_self N 2
    omega
  rw [polynomialPullback_eval, homogeneous_eval_smul
    (momentPolynomial_homogeneous (N : ℝ) (normalizedFrequency φ) k)]
  rw [pow_sub₀ (evalPolynomial ell x) hx hkN, inv_pow]
  ring

 theorem phase_norm_small_height {d : ℕ} {σ D : ℝ} {φ : E d → ℂ}
    (hφ : SmoothFrequency σ φ) (N : ℝ) (hN : 0 ≤ N) (hD : 1 ≤ D)
    (hσ : σ ≤ 1 / (64 * Real.exp 1 * D)) (y : E d) (hy : ‖y‖ ≤ D)
    (ξ : E d) (hξ : φ ξ ≠ 0) :
    ‖Complex.I * (N : ℂ) * ((∑ i : Fin d, ξ i * y i : ℝ) : ℂ)‖ ≤
      N / (64 * Real.exp 1) := by
  have hD0 : 0 < D := by linarith
  have hsmall : ‖ξ‖ < σ := by
    simpa only [Metric.mem_ball, dist_zero_right] using
      hφ.2.2 (show ξ ∈ tsupport φ from subset_closure hξ)
  have hσ0 : 0 ≤ σ := (norm_nonneg ξ).trans hsmall.le
  have hprod : ‖ξ‖ * ‖y‖ ≤ σ * D :=
    mul_le_mul hsmall.le hy (norm_nonneg _) hσ0
  have hsigma : σ * D ≤ 1 / (64 * Real.exp 1) := by
    have hh := (le_div_iff₀ (by positivity : (0 : ℝ) < 64 * Real.exp 1 * D)).mp hσ
    apply (le_div_iff₀ (by positivity : (0 : ℝ) < 64 * Real.exp 1)).2
    nlinarith
  calc
    _ ≤ |N| * (‖ξ‖ * ‖y‖) := phase_norm_le N ξ y
    _ ≤ N * (1 / (64 * Real.exp 1)) := by
      rw [abs_of_nonneg hN]
      exact mul_le_mul_of_nonneg_left (hprod.trans hsigma) hN
    _ = _ := by ring

 theorem momentPolynomial_eval_bound {d : ℕ} {σ D : ℝ} {φ : E d → ℂ}
    (hφ : SmoothFrequency σ φ) (N : ℝ) (hN : 0 ≤ N) (k : ℕ) (hD : 1 ≤ D)
    (hσ : σ ≤ 1 / (64 * Real.exp 1 * D)) (y : E d) (hy : ‖y‖ ≤ D) :
    |evalPolynomial (momentPolynomial N φ k) y| ≤
      (∫ ξ : E d, ‖φ ξ‖) * (N / (64 * Real.exp 1)) ^ k / (k.factorial : ℝ) := by
  rw [momentPolynomial_eval_integral hφ]
  let H : E d → ℂ := fun ξ => φ ξ *
    (Complex.I * (N : ℂ) * ((∑ i : Fin d, ξ i * y i : ℝ) : ℂ)) ^ k /
      (k.factorial : ℂ)
  have hH : Integrable H := power_integrand_integrable hφ N y
  have hφi : Integrable (fun ξ : E d => ‖φ ξ‖) :=
    hφ.1.continuous.integrable_of_hasCompactSupport hφ.2.1 |>.norm
  have hbound (ξ : E d) : ‖H ξ‖ ≤
      ‖φ ξ‖ * ((N / (64 * Real.exp 1)) ^ k / (k.factorial : ℝ)) := by
    by_cases hξ : φ ξ = 0
    · simp only [H, hξ, zero_mul, zero_div, norm_zero, le_refl]
    · rw [show ‖H ξ‖ = ‖φ ξ‖ *
          ‖Complex.I * (N : ℂ) * ((∑ i : Fin d, ξ i * y i : ℝ) : ℂ)‖ ^ k /
          (k.factorial : ℝ) by
          simp only [H, norm_div, norm_mul, norm_pow, Complex.norm_natCast]]
      rw [mul_div_assoc]
      apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
      apply div_le_div_of_nonneg_right _ (by positivity)
      exact pow_le_pow_left₀ (norm_nonneg _)
        (phase_norm_small_height hφ N hN hD hσ y hy ξ hξ) k
  calc
    _ ≤ ‖∫ ξ : E d, H ξ‖ := Complex.abs_re_le_norm _
    _ ≤ ∫ ξ : E d, ‖H ξ‖ := norm_integral_le_integral_norm _
    _ ≤ ∫ ξ : E d, ‖φ ξ‖ * ((N / (64 * Real.exp 1)) ^ k / (k.factorial : ℝ)) :=
      integral_mono hH.norm (hφi.mul_const _) hbound
    _ = _ := by rw [integral_mul_const]; ring

 theorem homogeneousApproximation_small_height {d e N : ℕ} {σ D : ℝ} {φ : E e → ℂ}
    (hφ : SmoothFrequency σ φ) (hN : Even N) (hD : 1 ≤ D)
    (hσ : σ ≤ 1 / (64 * Real.exp 1 * D)) (ell : Polynomial d)
    (b : E d →ₗ[ℝ] E e) (x : E d)
    (hell : |evalPolynomial ell x| ≤ 1 / 2) (hb : ‖b x‖ ≤ D) :
    |evalPolynomial (homogeneousApproximation N φ ell b) x| ≤
      fourierMass φ * Real.exp (-(N : ℝ) / 4) := by
  classical
  let m := N / 2
  let B : ℝ := (N : ℝ) / (64 * Real.exp 1)
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hmass := fourierMass_nonneg φ
  have hNm : N = 2 * m := by
    have hmod := Nat.mod_eq_zero_of_dvd hN.two_dvd
    dsimp [m]
    omega
  have hcast : (N : ℝ) = 2 * (m : ℝ) := by exact_mod_cast hNm
  have heval : evalPolynomial (homogeneousApproximation N φ ell b) x =
      ∑ k ∈ Finset.range (m + 1), (evalPolynomial ell x) ^ (N - k) *
        evalPolynomial (momentPolynomial (N : ℝ) (normalizedFrequency φ) k) (b x) := by
    simp only [homogeneousApproximation, evalPolynomial, map_sum, map_mul, map_pow, m]
    apply Finset.sum_congr rfl
    intro k hk
    congr 1
    exact polynomialPullback_eval b _ x
  have hterm (k : ℕ) (hk : k ∈ Finset.range (m + 1)) :
      |(evalPolynomial ell x) ^ (N - k) *
        evalPolynomial (momentPolynomial (N : ℝ) (normalizedFrequency φ) k) (b x)| ≤
      ((1 : ℝ) / 2) ^ m * (fourierMass φ * B ^ k / (k.factorial : ℝ)) := by
    have hkN : m ≤ N - k := by
      simp only [Finset.mem_range] at hk
      omega
    have ha : |evalPolynomial ell x| ^ (N - k) ≤ ((1 : ℝ) / 2) ^ m := by
      calc
        _ ≤ ((1 : ℝ) / 2) ^ (N - k) := pow_le_pow_left₀ (abs_nonneg _) hell _
        _ ≤ ((1 : ℝ) / 2) ^ m := pow_le_pow_of_le_one (by norm_num) (by norm_num) hkN
    have hq := momentPolynomial_eval_bound (normalizedFrequency_smooth hφ)
      (N : ℝ) (by positivity) k hD hσ (b x) hb
    rw [integral_norm_normalizedFrequency] at hq
    rw [abs_mul, abs_pow]
    exact mul_le_mul ha hq (abs_nonneg _) (by positivity)
  calc
    _ = |∑ k ∈ Finset.range (m + 1), (evalPolynomial ell x) ^ (N - k) *
        evalPolynomial (momentPolynomial (N : ℝ) (normalizedFrequency φ) k) (b x)| := by rw [heval]
    _ ≤ ∑ k ∈ Finset.range (m + 1), |(evalPolynomial ell x) ^ (N - k) *
        evalPolynomial (momentPolynomial (N : ℝ) (normalizedFrequency φ) k) (b x)| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ k ∈ Finset.range (m + 1), ((1 : ℝ) / 2) ^ m *
        (fourierMass φ * B ^ k / (k.factorial : ℝ)) := Finset.sum_le_sum hterm
    _ = fourierMass φ * (((1 : ℝ) / 2) ^ m *
        ∑ k ∈ Finset.range (m + 1), B ^ k / (k.factorial : ℝ)) := by
      rw [Finset.mul_sum, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro k hk
      ring
    _ ≤ fourierMass φ * (((1 : ℝ) / 2) ^ m * Real.exp B) :=
      mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left (Real.sum_le_exp_of_nonneg hB _) (by positivity))
        (fourierMass_nonneg φ)
    _ ≤ fourierMass φ * Real.exp (-(N : ℝ) / 4) := by
      apply mul_le_mul_of_nonneg_left _ (fourierMass_nonneg φ)
      simpa only [B, hcast] using small_height_exponential_bound m

#print axioms homogeneousApproximation_homogeneous
#print axioms homogeneousApproximation_eval
#print axioms homogeneousApproximation_small_height


 theorem approximation_specification {e N : ℕ} {σ D : ℝ} {φ : E e → ℂ}
    (hφ : SmoothFrequency σ φ) (hN : Even N) (hN2 : 2 ≤ N) (hD : 1 ≤ D)
    (hσ : σ ≤ 1 / (64 * Real.exp 1 * D)) :
    ∃ P : Polynomial e, P.totalDegree ≤ N / 2 ∧
      (∀ t : E e, ‖t‖ ≤ 2 * D →
        |evalPolynomial P t - (inverseFourier φ ((N : ℝ) • t)).re| ≤
          fourierMass φ * Real.exp (-(N : ℝ))) ∧
      ∀ (d : ℕ) (ell : Polynomial d), ell.IsHomogeneous 1 →
        ∀ b : E d →ₗ[ℝ] E e, ∃ R : Polynomial d,
          R.IsHomogeneous N ∧
          (∀ x : E d, evalPolynomial ell x ≠ 0 →
            evalPolynomial R x = (evalPolynomial ell x) ^ N *
              evalPolynomial P ((evalPolynomial ell x)⁻¹ • b x)) ∧
          (∀ x : E d, |evalPolynomial ell x| ≤ 1 / 2 → ‖b x‖ ≤ D →
            |evalPolynomial R x| ≤ fourierMass φ * Real.exp (-(N : ℝ) / 4)) := by
  refine ⟨approximatingPolynomial N φ, approximatingPolynomial_degree N φ,
    fun t ht => approximatingPolynomial_chart_error hφ hN hN2 hD hσ t ht, ?_⟩
  intro d ell hell b
  exact ⟨homogeneousApproximation N φ ell b,
    homogeneousApproximation_homogeneous N φ ell hell b,
    fun x hx => homogeneousApproximation_eval N φ ell b x hx,
    fun x ha hb => homogeneousApproximation_small_height hφ hN hD hσ ell b x ha hb⟩

#print axioms approximation_specification

#print axioms complex_taylor_remainder
#print axioms small_height_exponential_bound

#print axioms homogenized_homogeneous
#print axioms homogenized_eval
#print axioms homogenized_even
#print axioms homogenized_degree

end KernelTaylor
end Bandlimited
