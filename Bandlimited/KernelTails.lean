module

public import Bandlimited.WeightedSchwartz
public import Bandlimited.BandlimitedOperations
public import Bandlimited.GaussianSchwartz

/- Uniform tails needed by T07. All exponential estimates use kernel-checked
factorial bounds from the GaussianSchwartz development. -/
@[expose] public section
noncomputable section
open Set
open scoped BigOperators
namespace Bandlimited
namespace KernelEstimates

/-- Polynomial growth is dominated by an exponential, with a real threshold
uniform over the entire real half-line. -/
theorem polynomial_exponential_tail (a L b : ℝ) (ha : 0 ≤ a) (hL : 0 ≤ L)
    (hb : 0 < b) : ∀ ε : ℝ, 0 < ε → ∃ R : ℝ, 1 ≤ R ∧ ∀ x : ℝ, R ≤ x →
      (1 + a * x) ^ L * Real.exp (-b * x) < ε := by
  intro ε hε
  let m : ℕ := ⌈L⌉₊
  let F : ℝ := ((m + 1).factorial : ℝ) / b ^ (m + 1)
  let K : ℝ := (1 + a) ^ m * F
  have hF : 0 ≤ F := by dsimp [F]; positivity
  have hK : 0 ≤ K := by dsimp [K]; positivity
  let R : ℝ := 1 + K / ε
  have hR : 1 ≤ R := by dsimp [R]; linarith [div_nonneg hK hε.le]
  have hRp : 0 < R := by linarith
  have hsmall : K / R < ε := by
    apply (div_lt_iff₀ hRp).mpr
    have hc : ε * (K / ε) = K := by field_simp
    dsimp [R]
    nlinarith
  refine ⟨R, hR, ?_⟩
  intro x hx
  have hxone : 1 ≤ x := hR.trans hx
  have hxp : 0 < x := by linarith
  have hpoly : (1 + a * x) ^ L ≤ ((1 + a) * x) ^ m := by
    calc
      (1 + a * x) ^ L ≤ (1 + a * x) ^ (m : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le (by nlinarith) (Nat.le_ceil L)
      _ = (1 + a * x) ^ m := Real.rpow_natCast _ _
      _ ≤ ((1 + a) * x) ^ m := pow_le_pow_left₀ (by positivity) (by nlinarith) m
  have hpower : x ^ m * Real.exp (-b * x) ≤ F / x := by
    apply (le_div_iff₀ hxp).mpr
    have h := GaussianSchwartz.pow_mul_exp_bound b hb (m + 1) x hxp.le
    simpa only [F, pow_succ, mul_assoc, mul_comm, mul_left_comm] using h
  calc
    (1 + a * x) ^ L * Real.exp (-b * x) ≤
        ((1 + a) * x) ^ m * Real.exp (-b * x) :=
      mul_le_mul_of_nonneg_right hpoly (Real.exp_pos _).le
    _ = (1 + a) ^ m * (x ^ m * Real.exp (-b * x)) := by rw [mul_pow]; ring
    _ ≤ (1 + a) ^ m * (F / x) := mul_le_mul_of_nonneg_left hpower (by positivity)
    _ = K / x := by dsimp [K]; ring
    _ ≤ K / R := div_le_div_of_nonneg_left hK hRp hx
    _ < ε := hsmall

/-- A single polynomial tail radius works for every member of a finite
Schwartz family. Empty families are allowed. -/
theorem finite_schwartz_polynomial_tail {d m : ℕ} (F : Fin m → SchwartzMap (E d) ℂ)
    (L : ℝ) (hL : 0 ≤ L) : ∀ ε : ℝ, 0 < ε → ∃ R : ℝ, 1 ≤ R ∧
      ∀ j : Fin m, ∀ x : E d, R ≤ ‖x‖ → gaussianWeight 1 L x * ‖F j x‖ < ε := by
  intro ε hε
  have heach := fun j : Fin m => WeightedDensity.schwartz_real_weight_tail (F j) L hL ε hε
  choose R hR htail using heach
  obtain ⟨B, hB⟩ := (Set.finite_range R).bddAbove
  refine ⟨max 1 B, le_max_left _ _, ?_⟩
  intro j x hx
  apply htail j x
  exact (hB (Set.mem_range_self j)).trans ((le_max_right _ _).trans hx)

/-- The actual bandlimited functions supplied by T12 have simultaneous
polynomial tails; their Schwartz representatives are obtained from their
compact smooth frequency witnesses. -/
theorem finite_bandlimited_polynomial_tail {d m : ℕ} (hd : d ≠ 0) (σ L : ℝ)
    (hL : 0 ≤ L) (F : Fin m → E d → ℂ)
    (hF : ∀ j, InBandlimitedSpace d σ (F j)) :
    ∀ ε : ℝ, 0 < ε → ∃ R : ℝ, 1 ≤ R ∧ ∀ j : Fin m, ∀ x : E d,
      R ≤ ‖x‖ → gaussianWeight 1 L x * ‖F j x‖ < ε := by
  choose G hG using fun j => InBandlimitedSpace.exists_schwartz hd (hF j)
  intro ε hε
  obtain ⟨R, hR, htail⟩ := finite_schwartz_polynomial_tail G L hL ε hε
  refine ⟨R, hR, ?_⟩
  intro j x hx
  simpa only [hG j] using htail j x hx


/-- A polynomial weight times any positive-width Gaussian has an arbitrarily
small tail, uniformly in direction and dimension once the parameters are fixed. -/
theorem gaussian_polynomial_tail {d : ℕ} (b L : ℝ) (hb : 0 < b) (hL : 0 ≤ L) :
    ∀ ε : ℝ, 0 < ε → ∃ R : ℝ, 1 ≤ R ∧ ∀ x : E d, R ≤ ‖x‖ →
      gaussianWeight 1 L x * Real.exp (-b * ‖x‖ ^ 2) < ε := by
  obtain ⟨G, hG⟩ := gaussian_schwartz d b hb
  intro ε hε
  obtain ⟨R, hR, htail⟩ := WeightedDensity.schwartz_real_weight_tail G L hL ε hε
  refine ⟨R, hR, ?_⟩
  intro x hx
  have h := htail x hx
  rw [hG x, Complex.norm_real, Real.norm_of_nonneg (Real.exp_pos _).le] at h
  exact h

/-- A single radius controls the precise finite-family-plus-Gaussian tail
expression in the manuscript's outer-chart estimate. -/
theorem finite_bandlimited_gaussian_tail {d m : ℕ} (hd : d ≠ 0) (σ L b : ℝ)
    (hL : 0 ≤ L) (hb : 0 < b) (F : Fin m → E d → ℂ)
    (hF : ∀ j, InBandlimitedSpace d σ (F j)) :
    ∀ ε : ℝ, 0 < ε → ∃ R : ℝ, 1 ≤ R ∧ ∀ j : Fin m, ∀ x : E d,
      R ≤ ‖x‖ → gaussianWeight 1 L x *
        (‖F j x‖ + Real.exp (-b * ‖x‖ ^ 2)) < ε := by
  intro ε hε
  obtain ⟨R₁, hR₁, htail₁⟩ := finite_bandlimited_polynomial_tail hd σ L hL F hF
    (ε / 2) (by positivity)
  obtain ⟨R₂, hR₂, htail₂⟩ := gaussian_polynomial_tail (d := d) b L hb hL
    (ε / 2) (by positivity)
  refine ⟨max R₁ R₂, hR₁.trans (le_max_left _ _), ?_⟩
  intro j x hx
  have h₁ := htail₁ j x ((le_max_left _ _).trans hx)
  have h₂ := htail₂ x ((le_max_right _ _).trans hx)
  rw [mul_add]
  linarith


#print axioms polynomial_exponential_tail
#print axioms finite_schwartz_polynomial_tail
#print axioms finite_bandlimited_polynomial_tail
#print axioms finite_bandlimited_gaussian_tail
end KernelEstimates
end Bandlimited
end
