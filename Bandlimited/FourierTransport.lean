module

public import Bandlimited.FourierConvention
public import Mathlib.Analysis.Calculus.ContDiff.Operations
public import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-!
# Closure and transport of the actual inverse-Fourier class

All frequency functions have compact support strictly inside the stated
open Euclidean ball. The zero-dimensional class remains all constants.
Mathlib reuse: Schwartz Fourier linearity, Bochner conjugation and invariant
Haar integration, and smooth composition by continuous linear maps.
-/

@[expose] public section
noncomputable section
open MeasureTheory Set
open scoped FourierTransform RealInnerProductSpace BigOperators Topology

namespace Bandlimited

 theorem SmoothFrequency.mono {d : ℕ} {σ τ : ℝ} {φ : E d → ℂ}
    (hφ : SmoothFrequency σ φ) (hστ : σ ≤ τ) : SmoothFrequency τ φ := by
  refine ⟨hφ.1, hφ.2.1, ?_⟩
  intro ξ hξ
  exact Metric.ball_subset_ball hστ (hφ.2.2 hξ)

 theorem SmoothFrequency.zero_frequency (d : ℕ) (σ : ℝ) :
    SmoothFrequency σ (0 : E d → ℂ) := by
  refine ⟨contDiff_const, HasCompactSupport.zero, ?_⟩
  simp only [tsupport_zero, empty_subset]

 theorem SmoothFrequency.add_same_bandwidth {d : ℕ} {σ : ℝ} {φ ψ : E d → ℂ}
    (hφ : SmoothFrequency σ φ) (hψ : SmoothFrequency σ ψ) :
    SmoothFrequency σ (fun ξ => φ ξ + ψ ξ) := by
  refine ⟨hφ.1.add hψ.1, hφ.2.1.add hψ.2.1, ?_⟩
  exact (tsupport_add φ ψ).trans (union_subset hφ.2.2 hψ.2.2)

 theorem SmoothFrequency.const_mul {d : ℕ} {σ : ℝ} {φ : E d → ℂ}
    (hφ : SmoothFrequency σ φ) (c : ℂ) :
    SmoothFrequency σ (fun ξ => c * φ ξ) := by
  refine ⟨contDiff_const.mul hφ.1, ?_, ?_⟩
  · exact hφ.2.1.mul_left
  · exact tsupport_mul_subset_right.trans hφ.2.2

 theorem inverseFourier_zero {d : ℕ} :
    inverseFourier (0 : E d → ℂ) = 0 := by
  funext x
  simp [inverseFourier]

 theorem inverseFourier_add {d : ℕ} {σ : ℝ} {φ ψ : E d → ℂ}
    (hφ : SmoothFrequency σ φ) (hψ : SmoothFrequency σ ψ) (x : E d) :
    inverseFourier (fun ξ => φ ξ + ψ ξ) x =
      inverseFourier φ x + inverseFourier ψ x := by
  let φS := hφ.2.1.toSchwartzMap hφ.1
  let ψS := hψ.2.1.toSchwartzMap hψ.1
  have heq : inverseFourierSchwartz (φS + ψS) =
      inverseFourierSchwartz φS + inverseFourierSchwartz ψS := by
    unfold inverseFourierSchwartz
    rw [FourierTransform.fourierInv_add, map_add, smul_add]
  have hx := congrArg (fun F : SchwartzMap (E d) ℂ => F x) heq
  have hφcoe : (φS : E d → ℂ) = φ := rfl
  have hψcoe : (ψS : E d → ℂ) = ψ := rfl
  have hsumcoe : ((φS + ψS : SchwartzMap (E d) ℂ) : E d → ℂ) =
      (fun ξ => φ ξ + ψ ξ) := by
    funext ξ
    rw [add_apply]
    rfl
  simpa only [inverseFourierSchwartz_apply, add_apply, hsumcoe, hφcoe, hψcoe] using hx

 theorem inverseFourier_const_mul {d : ℕ} (φ : E d → ℂ) (c : ℂ) (x : E d) :
    inverseFourier (fun ξ => c * φ ξ) x = c * inverseFourier φ x := by
  unfold inverseFourier
  simp_rw [mul_assoc]
  rw [integral_const_mul]
  ring

 theorem InBandlimitedSpace.mono {d : ℕ} {σ τ : ℝ} {F : E d → ℂ}
    (hF : InBandlimitedSpace d σ F) (hστ : σ ≤ τ) :
    InBandlimitedSpace d τ F := by
  by_cases hd : d = 0
  · simpa only [InBandlimitedSpace, hd, ↓reduceIte] using hF
  · simp only [InBandlimitedSpace, hd, ↓reduceIte] at hF ⊢
    obtain ⟨φ, hφ, hF⟩ := hF
    exact ⟨φ, hφ.mono hστ, hF⟩

 theorem InBandlimitedSpace.zero_function (d : ℕ) (σ : ℝ) :
    InBandlimitedSpace d σ (0 : E d → ℂ) := by
  by_cases hd : d = 0
  · simp only [InBandlimitedSpace, hd, ↓reduceIte]
    exact ⟨0, fun _ => rfl⟩
  · simp only [InBandlimitedSpace, hd, ↓reduceIte]
    exact ⟨0, SmoothFrequency.zero_frequency d σ, inverseFourier_zero.symm⟩

 theorem InBandlimitedSpace.add_same_bandwidth {d : ℕ} {σ : ℝ} {F G : E d → ℂ}
    (hF : InBandlimitedSpace d σ F) (hG : InBandlimitedSpace d σ G) :
    InBandlimitedSpace d σ (fun x => F x + G x) := by
  by_cases hd : d = 0
  · simp only [InBandlimitedSpace, hd, ↓reduceIte] at hF hG ⊢
    obtain ⟨c, hc⟩ := hF
    obtain ⟨e, he⟩ := hG
    exact ⟨c + e, fun x => by rw [hc, he]⟩
  · simp only [InBandlimitedSpace, hd, ↓reduceIte] at hF hG ⊢
    obtain ⟨φ, hφ, rfl⟩ := hF
    obtain ⟨ψ, hψ, rfl⟩ := hG
    exact ⟨fun ξ => φ ξ + ψ ξ, hφ.add_same_bandwidth hψ,
      funext fun x => (inverseFourier_add hφ hψ x).symm⟩

 theorem InBandlimitedSpace.const_mul {d : ℕ} {σ : ℝ} {F : E d → ℂ}
    (hF : InBandlimitedSpace d σ F) (c : ℂ) :
    InBandlimitedSpace d σ (fun x => c * F x) := by
  by_cases hd : d = 0
  · simp only [InBandlimitedSpace, hd, ↓reduceIte] at hF ⊢
    obtain ⟨e, he⟩ := hF
    exact ⟨c * e, fun x => by rw [he]⟩
  · simp only [InBandlimitedSpace, hd, ↓reduceIte] at hF ⊢
    obtain ⟨φ, hφ, rfl⟩ := hF
    exact ⟨fun ξ => c * φ ξ, hφ.const_mul c,
      funext fun x => (inverseFourier_const_mul φ c x).symm⟩

 theorem InBandlimitedSpace.finset_sum {d : ℕ} {σ : ℝ} {ι : Type*}
    (t : Finset ι) (F : ι → E d → ℂ)
    (hF : ∀ i ∈ t, InBandlimitedSpace d σ (F i)) :
    InBandlimitedSpace d σ (fun x => ∑ i ∈ t, F i x) := by
  classical
  induction t using Finset.induction_on with
  | empty =>
    have hz : (fun _ : E d => (0 : ℂ)) = (0 : E d → ℂ) := by
      funext x
      exact (show (0 : E d → ℂ) x = (0 : ℂ) from Pi.zero_apply x).symm
    simpa only [Finset.sum_empty, hz] using InBandlimitedSpace.zero_function d σ
  | @insert i t hi ih =>
    have hmem : InBandlimitedSpace d σ (F i) := hF i (Finset.mem_insert_self _ _)
    have ht : ∀ j ∈ t, InBandlimitedSpace d σ (F j) :=
      fun j hj => hF j (Finset.mem_insert_of_mem hj)
    simpa only [Finset.sum_insert hi] using hmem.add_same_bandwidth (ih ht)

 theorem SmoothFrequency.conj_reflect {d : ℕ} {σ : ℝ} {φ : E d → ℂ}
    (hφ : SmoothFrequency σ φ) :
    SmoothFrequency σ (fun ξ => starRingEnd ℂ (φ (-ξ))) := by
  have hneg : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun ξ : E d => -ξ) :=
    contDiff_id.neg
  refine ⟨Complex.conjCLE.contDiff.comp (hφ.1.comp hneg), ?_, ?_⟩
  · exact (hφ.2.1.comp_homeomorph (Homeomorph.neg (E d))).comp_left (by simp)
  · have hs : tsupport (fun ξ => starRingEnd ℂ (φ (-ξ))) ⊆
        tsupport (fun ξ => φ (-ξ)) := tsupport_comp_subset (by simp) _
    have hn : tsupport (fun ξ => φ (-ξ)) ⊆
        (fun ξ : E d => -ξ) ⁻¹' tsupport φ :=
      tsupport_comp_subset_preimage φ continuous_neg
    intro ξ hξ
    have h := hφ.2.2 (hn (hs hξ))
    simpa only [Metric.mem_ball, dist_zero_right, norm_neg] using h

 theorem inverseFourier_conj_reflect {d : ℕ} (φ : E d → ℂ) (x : E d) :
    inverseFourier (fun ξ => starRingEnd ℂ (φ (-ξ))) x =
      starRingEnd ℂ (inverseFourier φ x) := by
  rw [inverseFourier_eq_mathlib_inverse, inverseFourier_eq_mathlib_inverse]
  simp only [map_mul, map_inv₀, Complex.conj_ofReal]
  congr 1
  rw [Real.fourierInv_eq', Real.fourierInv_eq', ← integral_conj]
  let H : E d → ℂ := fun ξ => Complex.exp
    (↑(2 * Real.pi * ⟪ξ, (2 * Real.pi)⁻¹ • x⟫) * Complex.I) •
      starRingEnd ℂ (φ (-ξ))
  have hpoint (ξ : E d) :
      starRingEnd ℂ (Complex.exp
        (↑(2 * Real.pi * ⟪ξ, (2 * Real.pi)⁻¹ • x⟫) * Complex.I) • φ ξ) = H (-ξ) := by
    simp only [H, smul_eq_mul, map_mul, ← Complex.exp_conj,
      Complex.conj_ofReal, Complex.conj_I, inner_neg_left, mul_neg,
      Complex.ofReal_neg, neg_mul, neg_neg]
  symm
  calc
    _ = ∫ ξ : E d, H (-ξ) := integral_congr_ae (Filter.Eventually.of_forall hpoint)
    _ = ∫ ξ : E d, H ξ := by
      simpa only [neg_one_smul, abs_inv, abs_pow, abs_neg, abs_one,
        one_pow, inv_one, one_smul] using
        (MeasureTheory.Measure.integral_comp_smul volume H (-1))

 theorem InBandlimitedSpace.conj {d : ℕ} {σ : ℝ} {F : E d → ℂ}
    (hF : InBandlimitedSpace d σ F) :
    InBandlimitedSpace d σ (fun x => starRingEnd ℂ (F x)) := by
  by_cases hd : d = 0
  · simp only [InBandlimitedSpace, hd, ↓reduceIte] at hF ⊢
    obtain ⟨c, hc⟩ := hF
    exact ⟨starRingEnd ℂ c, fun x => by rw [hc]⟩
  · simp only [InBandlimitedSpace, hd, ↓reduceIte] at hF ⊢
    obtain ⟨φ, hφ, rfl⟩ := hF
    exact ⟨fun ξ => starRingEnd ℂ (φ (-ξ)), hφ.conj_reflect,
      funext fun x => (inverseFourier_conj_reflect φ x).symm⟩

 theorem InBandlimitedSpace.real_part {d : ℕ} {σ : ℝ} {F : E d → ℂ}
    (hF : InBandlimitedSpace d σ F) :
    InBandlimitedSpace d σ (fun x => ((F x).re : ℂ)) := by
  have hsum := (hF.add_same_bandwidth hF.conj).const_mul ((2 : ℂ)⁻¹)
  have heq : (fun x => (2 : ℂ)⁻¹ * (F x + starRingEnd ℂ (F x))) =
      (fun x => ((F x).re : ℂ)) := by
    funext x
    apply Complex.ext <;> simp <;> ring
  rw [heq] at hsum
  exact hsum

 theorem InBandlimitedSpace.exists_frequency {d : ℕ} {σ : ℝ} {F : E d → ℂ}
    (hF : InBandlimitedSpace d σ F) (hσ : 0 < σ) :
    ∃ φ : E d → ℂ, SmoothFrequency σ φ ∧ F = inverseFourier φ := by
  by_cases hd : d = 0
  · subst d
    simp only [InBandlimitedSpace, ↓reduceIte] at hF
    obtain ⟨c, hc⟩ := hF
    refine ⟨fun _ => c, ⟨contDiff_const, HasCompactSupport.of_compactSpace _, ?_⟩, ?_⟩
    · intro ξ hξ
      have hξ0 : ξ = 0 := Subsingleton.elim _ _
      simpa only [hξ0, Metric.mem_ball, dist_self] using hσ
    · funext x
      rw [hc x]
      simp [inverseFourier, E, volume_euclideanSpace_eq_dirac]
  · simpa only [InBandlimitedSpace, hd, ↓reduceIte] using hF

 theorem InBandlimitedSpace.comp_linearIsometry {d : ℕ} {σ : ℝ}
    {F : E d → ℂ} (hF : InBandlimitedSpace d σ F) (U : E d ≃ₗᵢ[ℝ] E d) :
    InBandlimitedSpace d σ (fun x => F (U x)) := by
  by_cases hd : d = 0
  · simp only [InBandlimitedSpace, hd, ↓reduceIte] at hF ⊢
    obtain ⟨c, hc⟩ := hF
    exact ⟨c, fun x => hc (U x)⟩
  · simp only [InBandlimitedSpace, hd, ↓reduceIte] at hF ⊢
    obtain ⟨φ, hφ, rfl⟩ := hF
    have hUφ : SmoothFrequency σ (fun ξ => φ (U ξ)) := by
      refine ⟨hφ.1.comp U.toContinuousLinearEquiv.contDiff,
        hφ.2.1.comp_homeomorph U.toHomeomorph, ?_⟩
      intro ξ hξ
      have h := hφ.2.2 (tsupport_comp_subset_preimage φ U.continuous hξ)
      simpa only [Metric.mem_ball, dist_zero_right, U.norm_map] using h
    refine ⟨fun ξ => φ (U ξ), hUφ, ?_⟩
    funext x
    rw [inverseFourier_eq_mathlib_inverse, inverseFourier_eq_mathlib_inverse]
    have hfour : (𝓕⁻ (fun ξ => φ (U ξ))) ((2 * Real.pi)⁻¹ • x) =
        (𝓕⁻ φ) (U ((2 * Real.pi)⁻¹ • x)) := by
      simpa only [Function.comp_def] using
        Real.fourierInv_comp_linearIsometry U φ ((2 * Real.pi)⁻¹ • x)
    rw [hfour, U.map_smul]

#print axioms InBandlimitedSpace.mono
#print axioms InBandlimitedSpace.exists_frequency
#print axioms InBandlimitedSpace.finset_sum
#print axioms InBandlimitedSpace.real_part
#print axioms InBandlimitedSpace.comp_linearIsometry
#print axioms inverseFourier_conj_reflect

end Bandlimited
