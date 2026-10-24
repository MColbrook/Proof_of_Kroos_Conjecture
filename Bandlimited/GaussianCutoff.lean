module

public import Bandlimited.Definitions
public import Bandlimited.FourierConvention
public import Bandlimited.SchwartzCutoff
public import Bandlimited.GaussianSchwartz
public import Bandlimited.GaussianFourierNormalization
public import Mathlib.Analysis.Distribution.SchwartzSpace.Basic
public import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct

/-!
# Fourier cutoff of a Gaussian

Theorem fourier_cutoff proves Lemma 3.1 in all dimensions required by the
paper, with real exponents and real scales, actual smooth compact frequency
support, exact supremum errors, and one common finite-dimensional threshold.
The proof includes the dimension zero convention and uses convergence in
Schwartz space. Mathlib reuse is under its Apache 2.0 licence.
-/

@[expose] public section
open scoped Topology
open Filter MeasureTheory

noncomputable section

namespace Bandlimited

theorem gaussian_zero_dimension (A : ℝ) (x : E 0) : gaussian A x = 1 := by
  have hx : x = 0 := Subsingleton.elim _ _
  simp [gaussian, hx]

theorem gaussian_weight_zero_dimension (A L : ℝ) (x : E 0) :
    gaussianWeight A L x = 1 := by
  have hx : x = 0 := Subsingleton.elim _ _
  simp [gaussianWeight, hx]

theorem constant_one_bandlimited_zero (σ : ℝ) :
    InBandlimitedSpace 0 σ (fun _ => (1 : ℂ)) := by
  simp only [InBandlimitedSpace, ↓reduceIte]
  exact ⟨1, fun _ => rfl⟩

theorem gaussian_cutoff_zero_exact_supremum (A L : ℝ) :
    sSup (Set.range (fun x : E 0 => gaussianWeight A L x *
      ‖(1 : ℂ) - (gaussian A x : ℂ)‖)) = 0 := by
  simp only [gaussian_zero_dimension, Complex.ofReal_one, sub_self, norm_zero,
    mul_zero, Set.range_const, csSup_singleton]

/-- Individual limits imply the common real-parameter threshold needed in
Lemma 3.1. No restriction of the exponent `L` to integers is involved. -/
theorem finite_dimension_uniform_limit (s : ℕ) (e : ℕ → ℝ → ℝ)
    (he : ∀ k, k ≤ s → TendsToZeroAtInfinity (e k)) :
    ∀ ε : ℝ, 0 < ε → ∃ A₀ : ℝ, 1 ≤ A₀ ∧
      ∀ A : ℝ, A₀ ≤ A → ∀ k : ℕ, k ≤ s → e k A < ε := by
  induction s with
  | zero =>
    intro ε hε
    obtain ⟨B, hB⟩ := he 0 (by omega) ε hε
    refine ⟨max 1 B, le_max_left _ _, ?_⟩
    intro A hA k hk
    have hk0 : k = 0 := by omega
    subst k
    exact lt_of_le_of_lt (le_abs_self _) (hB A (le_trans (le_max_right _ _) hA))
  | succ s ih =>
    intro ε hε
    obtain ⟨B, hB1, hB⟩ := ih (fun k hk => he k (by omega)) ε hε
    obtain ⟨C, hC⟩ := he (s + 1) (by omega) ε hε
    refine ⟨max B C, le_trans hB1 (le_max_left _ _), ?_⟩
    intro A hA k hk
    by_cases hks : k ≤ s
    · exact hB A (le_trans (le_max_left _ _) hA) k hks
    · have hkeq : k = s + 1 := by omega
      subst k
      exact lt_of_le_of_lt (le_abs_self _)
        (hC A (le_trans (le_max_right _ _) hA))

/-- A natural exponent above the real exponent controls the paper's weight;
the actual scale `A` remains real. -/
theorem gaussian_weight_le_integer_weight {d : ℕ} {A L : ℝ} {m : ℕ}
    (hA : 1 ≤ A) (hL : 0 ≤ L) (hm : L ≤ (m : ℝ)) (x : E d) :
    gaussianWeight A L x ≤ (1 + ‖x‖) ^ m := by
  have hApos : 0 < A := lt_of_lt_of_le zero_lt_one hA
  have hdiv : ‖x‖ / A ≤ ‖x‖ := by
    apply (div_le_iff₀ hApos).2
    nlinarith [norm_nonneg x]
  unfold gaussianWeight
  calc
    (1 + ‖x‖ / A) ^ L ≤ (1 + ‖x‖) ^ L :=
      Real.rpow_le_rpow (by positivity) (by linarith) hL
    _ ≤ (1 + ‖x‖) ^ (m : ℝ) :=
      Real.rpow_le_rpow_of_exponent_le (by linarith [norm_nonneg x]) hm
    _ = (1 + ‖x‖) ^ m := Real.rpow_natCast _ _

/-- The required weighted pointwise bound follows from finitely many
Schwartz seminorms, with no unproved integration-by-parts assertion. -/
theorem gaussian_weight_schwartz_bound {d : ℕ} {A L : ℝ} {m : ℕ}
    (hA : 1 ≤ A) (hL : 0 ≤ L) (hm : L ≤ (m : ℝ))
    (f : SchwartzMap (E d) ℂ) (x : E d) :
    gaussianWeight A L x * ‖f x‖ ≤
      (2 : ℝ) ^ m * ((Finset.Iic (m, 0)).sup
        (fun i => SchwartzMap.seminorm ℂ i.1 i.2)) f := by
  calc
    gaussianWeight A L x * ‖f x‖ ≤ (1 + ‖x‖) ^ m * ‖f x‖ :=
      mul_le_mul_of_nonneg_right (gaussian_weight_le_integer_weight hA hL hm x)
        (norm_nonneg _)
    _ ≤ _ := by
      simpa only [norm_iteratedFDeriv_zero] using
        (SchwartzMap.one_add_le_sup_seminorm_apply (𝕜 := ℂ)
          (m := (m, 0)) (k := m) (n := 0) (le_refl _) (le_refl _) f x)

/-- A bump with its closed support strictly inside the required frequency ball.
The strict containment is essential for the manuscript's definition of
`C_c^∞(B(0, σ/4))`. -/
def frequencyBump (d : ℕ) (σ : ℝ) (hσ : 0 < σ) : ContDiffBump (0 : E d) where
  rIn := σ / 16
  rOut := σ / 8
  rIn_pos := by positivity
  rIn_lt_rOut := by linarith

theorem frequency_bump_smooth_frequency (d : ℕ) (σ : ℝ) (hσ : 0 < σ) :
    SmoothFrequency (σ / 4) (fun x => (frequencyBump d σ hσ x : ℂ)) := by
  let f := frequencyBump d σ hσ
  have hsupp : tsupport (fun x => (f x : ℂ)) = tsupport f := by
    unfold tsupport
    congr 1
    ext x
    change ((f x : ℂ) ≠ 0) ↔ f x ≠ 0
    exact not_congr Complex.ofReal_eq_zero
  refine ⟨Complex.ofRealCLM.contDiff.comp f.contDiff, ?_, ?_⟩
  · change HasCompactSupport (fun x => (f x : ℂ))
    change IsCompact (tsupport (fun x => (f x : ℂ)))
    rw [hsupp]
    exact f.hasCompactSupport
  · rw [hsupp, f.tsupport_eq]
    intro x hx
    have hx' : ‖x‖ ≤ σ / 8 := by
      simpa only [Metric.mem_closedBall, dist_zero_right, f, frequencyBump] using hx
    have hx'' : ‖x‖ < σ / 4 := by linarith
    simpa only [Metric.mem_ball, dist_zero_right] using hx''

theorem frequency_bump_even (d : ℕ) (σ : ℝ) (hσ : 0 < σ) (x : E d) :
    frequencyBump d σ hσ (-x) = frequencyBump d σ hσ x :=
  (frequencyBump d σ hσ).neg x

theorem frequency_bump_one (d : ℕ) (σ : ℝ) (hσ : 0 < σ) (x : E d)
    (hx : ‖x‖ ≤ σ / 16) : frequencyBump d σ hσ x = 1 := by
  apply (frequencyBump d σ hσ).one_of_mem_closedBall
  simpa only [Metric.mem_closedBall, dist_zero_right, frequencyBump] using hx

theorem SmoothFrequency.mul_contDiff {d : ℕ} {σ : ℝ} {φ ψ : E d → ℂ}
    (hφ : SmoothFrequency σ φ)
    (hψ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) ψ) :
    SmoothFrequency σ (fun x => φ x * ψ x) := by
  refine ⟨hφ.1.mul hψ, hφ.2.1.mul_right, ?_⟩
  exact tsupport_mul_subset_left.trans hφ.2.2

/-- The actual smooth compactly supported frequency function used for the
positive dimensional cutoff. The Fourier normalization is the manuscript's. -/
def gaussianCutoffFrequency (d : ℕ) (σ : ℝ) (hσ : 0 < σ) (A : ℝ) (ξ : E d) : ℂ :=
  (frequencyBump d σ hσ ξ : ℂ) *
    ((A ^ d * Real.pi ^ ((d : ℝ) / 2) * Real.exp (-A ^ 2 * ‖ξ‖ ^ 2 / 4) : ℝ) : ℂ)

theorem gaussian_cutoff_frequency_smooth (d : ℕ) (σ : ℝ) (hσ : 0 < σ) (A : ℝ) :
    SmoothFrequency (σ / 4) (gaussianCutoffFrequency d σ hσ A) := by
  apply (frequency_bump_smooth_frequency d σ hσ).mul_contDiff
  have hq : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun ξ : E d => -A ^ 2 * ‖ξ‖ ^ 2 / 4) := by
    exact (contDiff_const.mul (contDiff_norm_sq ℝ (E := E d))).div_const 4
  have hg : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun ξ : E d => A ^ d * Real.pi ^ ((d : ℝ) / 2) *
        Real.exp (-A ^ 2 * ‖ξ‖ ^ 2 / 4)) :=
    contDiff_const.mul (Real.contDiff_exp.comp hq)
  exact Complex.ofRealCLM.contDiff.comp hg

theorem gaussian_cutoff_frequency_even (d : ℕ) (σ : ℝ) (hσ : 0 < σ) (A : ℝ)
    (ξ : E d) : gaussianCutoffFrequency d σ hσ A (-ξ) =
      gaussianCutoffFrequency d σ hσ A ξ := by
  simp only [gaussianCutoffFrequency, frequency_bump_even, norm_neg]

theorem gaussian_cutoff_frequency_real (d : ℕ) (σ : ℝ) (hσ : 0 < σ) (A : ℝ) :
    IsRealValued (gaussianCutoffFrequency d σ hσ A) := by
  intro ξ
  simp only [gaussianCutoffFrequency, Complex.mul_im, Complex.ofReal_re,
    Complex.ofReal_im, zero_mul, mul_zero, add_zero]

theorem gaussian_cutoff_inverse_bandlimited (d : ℕ) (hd : d ≠ 0)
    (σ : ℝ) (hσ : 0 < σ) (A : ℝ) :
    InBandlimitedSpace d (σ / 4)
      (inverseFourier (gaussianCutoffFrequency d σ hσ A)) := by
  simp only [InBandlimitedSpace, hd, ↓reduceIte]
  exact ⟨gaussianCutoffFrequency d σ hσ A,
    gaussian_cutoff_frequency_smooth d σ hσ A, rfl⟩

/-- The positive dimensional cutoff, with the separate constant convention at
zero dimension exactly as in Lemma 3.1. -/
def gaussianCutoff (d : ℕ) (σ : ℝ) (hσ : 0 < σ) (A : ℝ) : E d → ℂ :=
  if d = 0 then fun _ => 1
  else inverseFourier (gaussianCutoffFrequency d σ hσ A)

theorem gaussian_cutoff_bandlimited (d : ℕ) (σ : ℝ) (hσ : 0 < σ) (A : ℝ) :
    InBandlimitedSpace d (σ / 4) (gaussianCutoff d σ hσ A) := by
  by_cases hd : d = 0
  · subst d
    simpa only [gaussianCutoff, ↓reduceIte] using constant_one_bandlimited_zero (σ / 4)
  · simpa only [gaussianCutoff, hd, ↓reduceIte] using
      gaussian_cutoff_inverse_bandlimited d hd σ hσ A

theorem gaussian_cutoff_real (d : ℕ) (σ : ℝ) (hσ : 0 < σ) (A : ℝ) :
    IsRealValued (gaussianCutoff d σ hσ A) := by
  by_cases hd : d = 0
  · intro x
    simp only [gaussianCutoff, hd, ↓reduceIte, Complex.one_im]
  · simpa only [gaussianCutoff, hd, ↓reduceIte] using
      inverseFourier_real_of_even (gaussianCutoffFrequency d σ hσ A)
        (gaussian_cutoff_frequency_real d σ hσ A)
        (gaussian_cutoff_frequency_even d σ hσ A)

/-- An exact factorial bound, sufficient for existence of the weighted
supremum at each real scale. -/
theorem polynomial_gaussian_bound (m : ℕ) (r : ℝ) (hr : 0 ≤ r) :
    (1 + r) ^ m * Real.exp (-r ^ 2) ≤
      (2 : ℝ) ^ m * (Nat.factorial m : ℝ) := by
  have hfac : 1 ≤ (Nat.factorial m : ℝ) := by
    exact_mod_cast Nat.succ_le_iff.mpr (Nat.factorial_pos m)
  have hfacpos : 0 < (Nat.factorial m : ℝ) := lt_of_lt_of_le zero_lt_one hfac
  have hs : (r ^ 2) ^ m * Real.exp (-r ^ 2) ≤ (Nat.factorial m : ℝ) := by
    have hp := (div_le_iff₀ hfacpos).mp
      (Real.pow_div_factorial_le_exp (r ^ 2) (sq_nonneg r) m)
    calc
      (r ^ 2) ^ m * Real.exp (-r ^ 2) ≤
          (Real.exp (r ^ 2) * (Nat.factorial m : ℝ)) * Real.exp (-r ^ 2) :=
        mul_le_mul_of_nonneg_right hp (Real.exp_pos _).le
      _ = (Nat.factorial m : ℝ) := by
        rw [mul_comm (Real.exp (r ^ 2)), mul_assoc, ← Real.exp_add]
        simp
  by_cases hr1 : r ≤ 1
  · have hp : (1 + r) ^ m ≤ (2 : ℝ) ^ m :=
      pow_le_pow_left₀ (by linarith) (by linarith) m
    have he : Real.exp (-r ^ 2) ≤ 1 := Real.exp_le_one_iff.mpr (by nlinarith)
    calc
      (1 + r) ^ m * Real.exp (-r ^ 2) ≤ (2 : ℝ) ^ m * 1 :=
        mul_le_mul hp he (Real.exp_pos _).le (by positivity)
      _ ≤ (2 : ℝ) ^ m * (Nat.factorial m : ℝ) :=
        mul_le_mul_of_nonneg_left hfac (by positivity)
  · have hr1' : 1 ≤ r := le_of_lt (lt_of_not_ge hr1)
    have hp : (1 + r) ^ m ≤ (2 * r) ^ m :=
      pow_le_pow_left₀ (by linarith) (by linarith) m
    have hp2 : r ^ m ≤ (r ^ 2) ^ m :=
      pow_le_pow_left₀ hr (by nlinarith) m
    calc
      (1 + r) ^ m * Real.exp (-r ^ 2) ≤ (2 * r) ^ m * Real.exp (-r ^ 2) :=
        mul_le_mul_of_nonneg_right hp (Real.exp_pos _).le
      _ = (2 : ℝ) ^ m * (r ^ m * Real.exp (-r ^ 2)) := by rw [mul_pow, mul_assoc]
      _ ≤ (2 : ℝ) ^ m * ((r ^ 2) ^ m * Real.exp (-r ^ 2)) :=
        mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_right hp2 (Real.exp_pos _).le) (by positivity)
      _ ≤ (2 : ℝ) ^ m * (Nat.factorial m : ℝ) :=
        mul_le_mul_of_nonneg_left hs (by positivity)

theorem cutoff_inverse_weighted_limit {d : ℕ} (f : SchwartzMap (E d) ℂ)
    (L : ℝ) (hL : 0 ≤ L) :
    ∀ ε : ℝ, 0 < ε → ∃ R₀ : ℝ, 1 ≤ R₀ ∧ ∀ R : ℝ, R₀ ≤ R →
      ∀ x : E d, (1 + ‖x‖) ^ L *
        ‖inverseFourier (compactCutoff f R) x - inverseFourier f x‖ < ε := by
  intro ε hε
  obtain ⟨m, hm⟩ := exists_nat_ge L
  have hpow : (0 : ℝ) < 2 ^ m := pow_pos (by norm_num) m
  have hi : Tendsto (fun R : ℝ => inverseFourierSchwartz (compactCutoff f R)) atTop
      (𝓝 (inverseFourierSchwartz f)) :=
    inverseFourierSchwartz_continuous.tendsto _ |>.comp (compactCutoff_tendsto f)
  have hs := ((schwartz_withSeminorms ℂ (E d) ℂ).tendsto_nhds'
    (fun R : ℝ => inverseFourierSchwartz (compactCutoff f R))
    (inverseFourierSchwartz f)).mp hi (Finset.Iic (m, 0)) (ε / 2 ^ m)
      (div_pos hε hpow)
  obtain ⟨B, hB⟩ := Filter.eventually_atTop.mp hs
  refine ⟨max 1 B, le_max_left _ _, ?_⟩
  intro R hR x
  have hsemi := hB R (le_trans (le_max_right _ _) hR)
  have hp := gaussian_weight_schwartz_bound (A := 1) (by norm_num) hL hm
    (inverseFourierSchwartz (compactCutoff f R) - inverseFourierSchwartz f) x
  have hsemi' : (2 : ℝ) ^ m * ((Finset.Iic (m, 0)).sup
      (fun i => SchwartzMap.seminorm ℂ i.1 i.2))
        (inverseFourierSchwartz (compactCutoff f R) - inverseFourierSchwartz f) < ε := by
    have ht := mul_lt_mul_of_pos_left hsemi hpow
    have hfamily : schwartzSeminormFamily ℂ (E d) ℂ =
        (fun i : ℕ × ℕ => SchwartzMap.seminorm ℂ i.1 i.2) := by
      funext i
      exact SchwartzMap.schwartzSeminormFamily_apply ℂ (E d) ℂ i.1 i.2
    rw [hfamily] at ht
    simpa only [mul_div_cancel₀ _ (ne_of_gt hpow)] using ht
  apply lt_of_le_of_lt _ hsemi'
  simpa only [gaussianWeight, div_one, sub_apply,
    inverseFourierSchwartz_apply] using hp

theorem compactCutoff_rescaled_smoothFrequency {d : ℕ} (f : SchwartzMap (E d) ℂ)
    (A R σ : ℝ) (hA : 0 < A) (hR : 1 ≤ R) (hrad : 2 * R / A < σ) :
    SmoothFrequency σ (fun ξ : E d => ((A ^ d : ℝ) : ℂ) * compactCutoff f R (A • ξ)) := by
  let φ : E d → ℂ := fun ξ => ((A ^ d : ℝ) : ℂ) * compactCutoff f R (A • ξ)
  have hdiff : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) φ := by
    exact contDiff_const.mul (((compactCutoff f R).smooth ⊤).comp
      (contDiff_id.const_smul A))
  have hsupp : tsupport φ ⊆ Metric.closedBall (0 : E d) (2 * R / A) := by
    change closure (Function.support φ) ⊆ _
    apply closure_minimal _ Metric.isClosed_closedBall
    intro ξ hξ
    have hfx : compactCutoff f R (A • ξ) ≠ 0 := by
      intro hz
      apply hξ
      dsimp [φ]
      rw [hz, mul_zero]
    have hm := compactCutoff_support f R (subset_tsupport (compactCutoff f R) hfx)
    have hn : A * ‖ξ‖ ≤ 2 * R := by
      simpa only [Metric.mem_closedBall, dist_zero_right, norm_smul, Real.norm_eq_abs,
        abs_of_pos hA, max_eq_right hR] using hm
    rw [Metric.mem_closedBall, dist_zero_right]
    exact (le_div_iff₀ hA).mpr (by nlinarith)
  refine ⟨hdiff, ?_, ?_⟩
  · exact (isCompact_closedBall (0 : E d) (2 * R / A)).of_isClosed_subset
      (isClosed_tsupport φ) hsupp
  · intro ξ hξ
    have hm := hsupp hξ
    rw [Metric.mem_ball, dist_zero_right]
    exact lt_of_le_of_lt (by simpa only [Metric.mem_closedBall, dist_zero_right] using hm) hrad

theorem compactCutoff_rescaled_bandlimited {d : ℕ} (hd : d ≠ 0)
    (f : SchwartzMap (E d) ℂ) (A R σ : ℝ) (hA : 0 < A) (hR : 1 ≤ R)
    (hrad : 2 * R / A < σ) :
    InBandlimitedSpace d σ (fun x => inverseFourier (compactCutoff f R) (A⁻¹ • x)) := by
  simp only [InBandlimitedSpace, hd, ↓reduceIte]
  refine ⟨fun ξ : E d => ((A ^ d : ℝ) : ℂ) * compactCutoff f R (A • ξ),
    compactCutoff_rescaled_smoothFrequency f A R σ hA hR hrad, ?_⟩
  funext x
  exact (inverseFourier_rescale (compactCutoff f R) A hA x).symm

theorem gaussian_frequency_schwartz (d : ℕ) :
    ∃ F : SchwartzMap (E d) ℂ, ∀ ξ, F ξ = GaussianNormalization.frequency d ξ := by
  obtain ⟨G, hG⟩ := gaussian_schwartz d (1 / 4) (by norm_num)
  refine ⟨((Real.pi ^ ((d : ℝ) / 2) : ℝ) : ℂ) • G, ?_⟩
  intro ξ
  change ((Real.pi ^ ((d : ℝ) / 2) : ℝ) : ℂ) * G ξ = _
  rw [hG]
  unfold GaussianNormalization.frequency
  rw [Complex.ofReal_mul]
  congr 1
  congr 1
  congr 1
  ring

def gaussianFrequencySchwartz (d : ℕ) : SchwartzMap (E d) ℂ :=
  Classical.choose (gaussian_frequency_schwartz d)

theorem gaussianFrequencySchwartz_apply (d : ℕ) (ξ : E d) :
    gaussianFrequencySchwartz d ξ = GaussianNormalization.frequency d ξ :=
  Classical.choose_spec (gaussian_frequency_schwartz d) ξ

theorem gaussianFrequencySchwartz_real (d : ℕ) : IsRealValued (gaussianFrequencySchwartz d) := by
  intro ξ
  rw [gaussianFrequencySchwartz_apply]
  exact Complex.ofReal_im _

theorem gaussianFrequencySchwartz_even (d : ℕ) (ξ : E d) :
    gaussianFrequencySchwartz d (-ξ) = gaussianFrequencySchwartz d ξ := by
  simp only [gaussianFrequencySchwartz_apply, GaussianNormalization.frequency, norm_neg]

theorem inverse_gaussianFrequencySchwartz (d : ℕ) (x : E d) :
    inverseFourier (gaussianFrequencySchwartz d) x = (Real.exp (-‖x‖ ^ 2) : ℂ) := by
  have heq : (gaussianFrequencySchwartz d : E d → ℂ) = GaussianNormalization.frequency d :=
    funext (gaussianFrequencySchwartz_apply d)
  rw [heq]
  exact inverseFourier_gaussianFrequency d x

def cutoffApproximation (d : ℕ) (σ A : ℝ) : E d → ℂ :=
  if d = 0 then fun _ => 1
  else if 1 ≤ σ * A / 32 then
    fun x => inverseFourier (compactCutoff (gaussianFrequencySchwartz d) (σ * A / 32))
      (A⁻¹ • x)
  else fun _ => 0

theorem zero_bandlimited (d : ℕ) (σ : ℝ) :
    InBandlimitedSpace d σ (fun _ => (0 : ℂ)) := by
  by_cases hd : d = 0
  · simp only [InBandlimitedSpace, hd, ↓reduceIte]
    exact ⟨0, fun _ => rfl⟩
  · simp only [InBandlimitedSpace, hd, ↓reduceIte]
    refine ⟨fun _ => 0, ⟨contDiff_const, ?_, ?_⟩, ?_⟩
    · simp [HasCompactSupport]
    · simp
    · funext x
      simp [inverseFourier]

theorem cutoffApproximation_bandlimited (d : ℕ) (σ A : ℝ) (hσ : 0 < σ) (hA : 0 < A) :
    InBandlimitedSpace d (σ / 4) (cutoffApproximation d σ A) := by
  by_cases hd : d = 0
  · subst d
    simpa only [cutoffApproximation, ↓reduceIte] using constant_one_bandlimited_zero (σ / 4)
  · by_cases hR : 1 ≤ σ * A / 32
    · have hrad : 2 * (σ * A / 32) / A < σ / 4 := by
        have heq : 2 * (σ * A / 32) / A = σ / 16 := by field_simp; ring
        rw [heq]
        linarith
      simpa only [cutoffApproximation, hd, hR, ↓reduceIte] using
        compactCutoff_rescaled_bandlimited hd (gaussianFrequencySchwartz d)
          A (σ * A / 32) (σ / 4) hA hR hrad
    · simpa only [cutoffApproximation, hd, hR, ↓reduceIte] using zero_bandlimited d (σ / 4)

theorem cutoffApproximation_real (d : ℕ) (σ A : ℝ) :
    IsRealValued (cutoffApproximation d σ A) := by
  by_cases hd : d = 0
  · intro x
    simp only [cutoffApproximation, hd, ↓reduceIte, Complex.one_im]
  · by_cases hR : 1 ≤ σ * A / 32
    · intro x
      simp only [cutoffApproximation, hd, hR, ↓reduceIte]
      exact inverseFourier_real_of_even _
        (compactCutoff_real _ (gaussianFrequencySchwartz_real d) _)
        (compactCutoff_even _ (gaussianFrequencySchwartz_even d) _) (A⁻¹ • x)
    · intro x
      simp only [cutoffApproximation, hd, hR, ↓reduceIte, Complex.zero_im]

theorem cutoffApproximation_schwartz (d : ℕ) (σ A : ℝ) (hA : 0 < A) :
    ∃ F : SchwartzMap (E d) ℂ, ∀ x, F x = cutoffApproximation d σ A x := by
  by_cases hd : d = 0
  · subst d
    obtain ⟨F, hF⟩ := gaussian_schwartz 0 1 zero_lt_one
    refine ⟨F, ?_⟩
    intro x
    have hx : x = 0 := Subsingleton.elim _ _
    simp [hF, hx, cutoffApproximation]
  · by_cases hR : 1 ≤ σ * A / 32
    · obtain ⟨F, hF⟩ := schwartz_rescale
        (inverseFourierSchwartz (compactCutoff (gaussianFrequencySchwartz d) (σ * A / 32)))
        A hA.ne'
      refine ⟨F, ?_⟩
      intro x
      rw [hF, inverseFourierSchwartz_apply]
      simp only [cutoffApproximation, hd, hR, ↓reduceIte]
    · exact ⟨0, fun x => by simp only [cutoffApproximation, hd, hR, ↓reduceIte,
        zero_apply]⟩

theorem gaussian_scale_schwartz (d : ℕ) (A : ℝ) (hA : 0 < A) :
    ∃ F : SchwartzMap (E d) ℂ, ∀ x, F x = (gaussian A x : ℂ) := by
  obtain ⟨F, hF⟩ := gaussian_schwartz d (A ^ 2)⁻¹ (inv_pos.mpr (pow_pos hA 2))
  refine ⟨F, ?_⟩
  intro x
  rw [hF]
  unfold gaussian
  congr 1
  congr 1
  simp only [div_eq_mul_inv]
  ring

def cutoffApproximationError (d : ℕ) (σ L A : ℝ) : ℝ :=
  sSup (Set.range (fun x : E d => gaussianWeight A L x *
    ‖cutoffApproximation d σ A x - (gaussian A x : ℂ)‖))

theorem cutoffApproximation_error_bdd (d : ℕ) (σ L A : ℝ) (hL : 0 ≤ L) (hA : 1 ≤ A) :
    BddAbove (Set.range (fun x : E d => gaussianWeight A L x *
      ‖cutoffApproximation d σ A x - (gaussian A x : ℂ)‖)) := by
  have hAp : 0 < A := lt_of_lt_of_le zero_lt_one hA
  obtain ⟨F, hF⟩ := cutoffApproximation_schwartz d σ A hAp
  obtain ⟨G, hG⟩ := gaussian_scale_schwartz d A hAp
  obtain ⟨m, hm⟩ := exists_nat_ge L
  refine ⟨(2 : ℝ) ^ m * ((Finset.Iic (m, 0)).sup
    (fun i => SchwartzMap.seminorm ℂ i.1 i.2)) (F - G), ?_⟩
  rintro _ ⟨x, rfl⟩
  have hp := gaussian_weight_schwartz_bound hA hL hm (F - G) x
  simpa only [sub_apply, hF, hG] using hp

theorem cutoffApproximationError_upper (d : ℕ) (σ L A : ℝ)
    (hL : 0 ≤ L) (hA : 1 ≤ A) (x : E d) :
    gaussianWeight A L x * ‖cutoffApproximation d σ A x - (gaussian A x : ℂ)‖ ≤
      cutoffApproximationError d σ L A :=
  le_csSup (cutoffApproximation_error_bdd d σ L A hL hA) (Set.mem_range_self x)

theorem cutoffApproximationError_nonneg (d : ℕ) (σ L A : ℝ)
    (hL : 0 ≤ L) (hA : 1 ≤ A) : 0 ≤ cutoffApproximationError d σ L A := by
  apply le_trans _ (cutoffApproximationError_upper d σ L A hL hA (0 : E d))
  simp only [gaussianWeight, norm_zero, zero_div, add_zero, Real.one_rpow, one_mul]
  exact norm_nonneg _

theorem cutoffApproximationError_zero (σ L A : ℝ) : cutoffApproximationError 0 σ L A = 0 := by
  simp only [cutoffApproximationError, cutoffApproximation, ↓reduceIte,
    gaussian_zero_dimension, Complex.ofReal_one, sub_self, norm_zero, mul_zero,
    Set.range_const, csSup_singleton]

theorem gaussian_weight_scale_identity {d : ℕ} (A L : ℝ) (hA : 0 < A) (x : E d) :
    gaussianWeight A L x = (1 + ‖A⁻¹ • x‖) ^ L := by
  simp only [gaussianWeight, norm_smul, Real.norm_eq_abs, abs_inv,
    abs_of_pos hA, div_eq_inv_mul]

theorem gaussian_scale_identity {d : ℕ} (A : ℝ) (hA : 0 < A) (x : E d) :
    (gaussian A x : ℂ) = (Real.exp (-‖A⁻¹ • x‖ ^ 2) : ℂ) := by
  unfold gaussian
  congr 1
  congr 1
  rw [norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos hA, mul_pow]
  simp only [div_eq_mul_inv, inv_pow]
  ring

theorem cutoffApproximationError_limit (d : ℕ) (σ L : ℝ) (hσ : 0 < σ) (hL : 0 ≤ L) :
    ∀ ε : ℝ, 0 < ε → ∃ A₀ : ℝ, 1 ≤ A₀ ∧
      ∀ A : ℝ, A₀ ≤ A → cutoffApproximationError d σ L A < ε := by
  intro ε hε
  by_cases hd : d = 0
  · subst d
    exact ⟨1, le_refl _, fun A hA => by simpa only [cutoffApproximationError_zero] using hε⟩
  · obtain ⟨R₀, hR₀1, hR₀⟩ := cutoff_inverse_weighted_limit
      (gaussianFrequencySchwartz d) L hL (ε / 2) (by positivity)
    refine ⟨max 1 (32 * R₀ / σ), le_max_left _ _, ?_⟩
    intro A hA
    have hA1 : 1 ≤ A := le_trans (le_max_left _ _) hA
    have hAp : 0 < A := lt_of_lt_of_le zero_lt_one hA1
    have hRA : R₀ ≤ σ * A / 32 := by
      have ht := (div_le_iff₀ hσ).mp (le_trans (le_max_right _ _) hA)
      nlinarith
    have hRA1 : 1 ≤ σ * A / 32 := le_trans hR₀1 hRA
    have hpoint (x : E d) : gaussianWeight A L x *
        ‖cutoffApproximation d σ A x - (gaussian A x : ℂ)‖ < ε / 2 := by
      have hp := hR₀ (σ * A / 32) hRA (A⁻¹ • x)
      rw [inverse_gaussianFrequencySchwartz] at hp
      have hg : cutoffApproximation d σ A x =
          inverseFourier (compactCutoff (gaussianFrequencySchwartz d) (σ * A / 32))
            (A⁻¹ • x) := by
        simp only [cutoffApproximation, hd, hRA1, ↓reduceIte]
      rw [hg, gaussian_weight_scale_identity A L hAp x, gaussian_scale_identity A hAp x]
      exact hp
    have hsup : cutoffApproximationError d σ L A ≤ ε / 2 := by
      unfold cutoffApproximationError
      apply csSup_le (Set.range_nonempty _)
      rintro _ ⟨x, rfl⟩
      exact (hpoint x).le
    exact lt_of_le_of_lt hsup (by linarith)

theorem cutoffApproximationError_tends_to_zero (d : ℕ) (σ L : ℝ)
    (hσ : 0 < σ) (hL : 0 ≤ L) :
    TendsToZeroAtInfinity (cutoffApproximationError d σ L) := by
  intro ε hε
  obtain ⟨A₀, hA₀1, hA₀⟩ := cutoffApproximationError_limit d σ L hσ hL ε hε
  refine ⟨A₀, ?_⟩
  intro A hA
  rw [abs_of_nonneg (cutoffApproximationError_nonneg d σ L A hL (le_trans hA₀1 hA))]
  exact hA₀ A hA

/-- Lemma 3.1, including actual smooth compact frequency support, real values,
real exponents L, exact supremum errors, dimension zero, and one common
real-scale threshold over every k≤s. -/
theorem fourier_cutoff : FourierCutoffStatement := by
  intro s L σ hL hσ
  refine ⟨fun k A => cutoffApproximation k σ A,
    fun k A => cutoffApproximationError k σ L A, ?_, ?_, ?_⟩
  · intro k hk A hA
    exact ⟨cutoffApproximation_bandlimited k σ A hσ (lt_of_lt_of_le zero_lt_one hA),
      cutoffApproximation_real k σ A,
      cutoffApproximationError_nonneg k σ L A hL hA,
      rfl, cutoffApproximationError_upper k σ L A hL hA⟩
  · intro A hA
    exact ⟨fun x => by simp only [cutoffApproximation, ↓reduceIte],
      cutoffApproximationError_zero σ L A⟩
  · exact finite_dimension_uniform_limit s (fun k A => cutoffApproximationError k σ L A)
      (fun k hk => cutoffApproximationError_tends_to_zero k σ L hσ hL)

#print axioms fourier_cutoff
#print axioms cutoffApproximationError_limit
#print axioms cutoffApproximationError_tends_to_zero
#print axioms gaussian_frequency_schwartz
#print axioms cutoffApproximation_bandlimited
#print axioms cutoffApproximation_real
#print axioms cutoffApproximation_schwartz
#print axioms gaussian_scale_schwartz
#print axioms cutoffApproximation_error_bdd
#print axioms cutoffApproximationError_upper
#print axioms cutoffApproximationError_nonneg
#print axioms cutoffApproximationError_zero
#print axioms cutoff_inverse_weighted_limit
#print axioms compactCutoff_rescaled_smoothFrequency
#print axioms compactCutoff_rescaled_bandlimited
#print axioms gaussian_cutoff_bandlimited
#print axioms gaussian_cutoff_real
#print axioms polynomial_gaussian_bound
#print axioms gaussian_zero_dimension
#print axioms gaussian_weight_zero_dimension
#print axioms constant_one_bandlimited_zero
#print axioms gaussian_cutoff_zero_exact_supremum
#print axioms finite_dimension_uniform_limit
#print axioms gaussian_weight_le_integer_weight
#print axioms gaussian_weight_schwartz_bound
#print axioms frequency_bump_smooth_frequency
#print axioms frequency_bump_even
#print axioms frequency_bump_one
#print axioms SmoothFrequency.mul_contDiff
#print axioms gaussian_cutoff_frequency_smooth
#print axioms gaussian_cutoff_frequency_even
#print axioms gaussian_cutoff_frequency_real
#print axioms gaussian_cutoff_inverse_bandlimited

end Bandlimited
