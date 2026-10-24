module

public import Bandlimited.LaplaceInversion
public import Bandlimited.C0LocalIdeal
public import Bandlimited.BandlimitedOperations

/- Full fixed-bandwidth density for the manuscript's one-sided weighted C₀ space. -/

@[expose] public section
noncomputable section
open Set
open scoped Topology ZeroAtInfty BigOperators

namespace Bandlimited
namespace WeightedDensity

set_option maxHeartbeats 80000

 def bandlimitedWeightedSubmodule (c M δ : ℝ) : Submodule ℂ C₀(E 1, ℂ) where
  carrier G := ∃ F : E 1 → ℂ, InBandlimitedSpace 1 δ F ∧
    ∀ x, G x = (oneSidedWeight c M (x 0) : ℂ) * F x
  zero_mem' := ⟨0, InBandlimitedSpace.zero 1 δ, fun _ => by simp⟩
  add_mem' := by
    rintro G H ⟨F, hF, hGF⟩ ⟨K, hK, hHK⟩
    exact ⟨F + K, hF.add hK, fun x => by simp only [ZeroAtInftyContinuousMap.add_apply,
      Pi.add_apply, hGF, hHK, mul_add]⟩
  smul_mem' := by
    intro a G
    rintro ⟨F, hF, hGF⟩
    refine ⟨a • F, hF.smul a, fun x => ?_⟩
    simp only [ZeroAtInftyContinuousMap.smul_apply, Pi.smul_apply, smul_eq_mul, hGF]
    ring

 theorem exists_nonzero_bandlimited_schwartz (δ : ℝ) (hδ : 0 < δ) :
    ∃ q : SchwartzMap (E 1) ℂ, InBandlimitedSpace 1 (δ / 2) q ∧ q 0 ≠ 0 := by
  obtain ⟨g, e, hband, hzero, hconv⟩ := fourier_cutoff 1 0 (2 * δ) (by norm_num) (by positivity)
  obtain ⟨A, hA, hsmall⟩ := hconv (1 / 2) (by norm_num)
  have hb := hband 1 (le_refl _) A hA
  have hb' : InBandlimitedSpace 1 (δ / 2) (g 1 A) := by
    convert hb.1 using 1 <;> ring
  obtain ⟨q, hq⟩ := hb'.exists_schwartz (by omega)
  have hqfun : (q : E 1 → ℂ) = g 1 A := funext hq
  refine ⟨q, hqfun.symm ▸ hb', ?_⟩
  have herror := (hb.2.2.2.2 (0 : E 1)).trans_lt (hsmall A (le_refl _) 1 (le_refl _))
  have he : ‖g 1 A 0 - 1‖ < 1 / 2 := by
    simpa only [gaussianWeight, Real.rpow_zero, one_mul, gaussian, norm_zero, zero_pow,
      ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_div, neg_zero, Real.exp_zero,
      Complex.ofReal_one] using herror
  intro hq0
  rw [← hq 0, hq0, zero_sub, norm_neg, norm_one] at he
  norm_num at he

 theorem real_modulation_phase (t : ℝ) (x : E 1) :
    Complex.exp (-Complex.I * ((∑ i : Fin 1, x i * TensorDensity.scalarLine t i : ℝ) : ℂ)) =
      Complex.exp (-Complex.I * (t : ℂ) * (x 0 : ℂ)) := by
  congr 1
  simp only [Fin.sum_univ_one, TensorDensity.scalarLine_apply, Complex.ofReal_mul]
  ring

 theorem functional_zero_on_real_modulations (c M δ : ℝ)
    (hc : 0 < c) (hM : 0 ≤ M) (hδ : 0 < δ)
    (ℓ : C₀(E 1, ℂ) →L[ℂ] ℂ)
    (hkill : ∀ G ∈ bandlimitedWeightedSubmodule c M δ, ℓ G = 0)
    (q : SchwartzMap (E 1) ℂ) (hq : InBandlimitedSpace 1 (δ / 2) q) :
    ∀ t : ℝ, ℓ (laplaceC0 q c M hc hM (t : ℂ)) = 0 := by
  apply laplaceC0_real_zero q c M (δ / 2) hc hM (by positivity) ℓ
  intro t ht
  apply hkill
  have hmod := hq.modulate (by omega : 1 ≠ 0) (TensorDensity.scalarLine t)
    (show δ / 2 + ‖TensorDensity.scalarLine t‖ ≤ δ by
      rw [TensorDensity.norm_scalarLine]
      linarith)
  refine ⟨_, hmod, fun x => ?_⟩
  rw [laplaceC0_apply, laplaceFunction,
    clippedParameter_eq c (t : ℂ) (by simp) (by simpa using hc.le), real_modulation_phase]
  ring

 theorem functional_zero_weighted_factor (c M δ : ℝ)
    (hc : 0 < c) (hM : 0 ≤ M) (hδ : 0 < δ)
    (ℓ : C₀(E 1, ℂ) →L[ℂ] ℂ)
    (hkill : ∀ G ∈ bandlimitedWeightedSubmodule c M δ, ℓ G = 0)
    (q : SchwartzMap (E 1) ℂ) (hq : InBandlimitedSpace 1 (δ / 2) q) :
    ∀ g : C₀(E 1, ℂ),
      ℓ (weightedC0Map (schwartz_oneSided_weightedC0 q c M hc hM) * g) = 0 := by
  let Q := weightedC0Map (schwartz_oneSided_weightedC0 q c M hc hM)
  have hreal := functional_zero_on_real_modulations c M δ hc hM hδ ℓ hkill q hq
  have hSch : ∀ h : SchwartzMap (E 1) ℂ, ℓ (Q * C0SmoothDensity.schwartzC0 h) = 0 := by
    intro h
    have heq : Q * C0SmoothDensity.schwartzC0 h = weightedSchwartzProduct q h c M hc hM := by
      apply ZeroAtInftyContinuousMap.ext
      intro x
      simp only [ZeroAtInftyContinuousMap.mul_apply, Q, weightedC0Map_apply,
        C0SmoothDensity.schwartzC0_apply, weightedSchwartzProduct_apply]
      ring
    rw [heq]
    exact functional_zero_weightedSchwartzProduct q h c M hc hM ℓ hreal
  have hclosed : IsClosed {g : C₀(E 1, ℂ) | ℓ (Q * g) = 0} :=
    isClosed_eq (ℓ.continuous.comp (continuous_const.mul continuous_id)) continuous_const
  have hsub : Set.range (C0SmoothDensity.schwartzC0 : SchwartzMap (E 1) ℂ → C₀(E 1, ℂ)) ⊆
      {g | ℓ (Q * g) = 0} := by
    rintro _ ⟨h, rfl⟩
    exact hSch h
  intro g
  exact closure_minimal hsub hclosed (C0SmoothDensity.denseRange_schwartzC0 1 g)

 theorem bandlimitedWeightedSubmodule_dense (c M δ : ℝ)
    (hc : 0 < c) (hM : 0 ≤ M) (hδ : 0 < δ) :
    Dense (bandlimitedWeightedSubmodule c M δ : Set C₀(E 1, ℂ)) := by
  apply dense_submodule_of_dual_annihilator_trivial
  intro ℓ hkill
  obtain ⟨q, hq, hq0⟩ := exists_nonzero_bandlimited_schwartz δ hδ
  let qt (a : E 1) : SchwartzMap (E 1) ℂ := SchwartzMap.compSubConstCLM ℂ a q
  let Q (a : E 1) : C₀(E 1, ℂ) :=
    weightedC0Map (schwartz_oneSided_weightedC0 (qt a) c M hc hM)
  apply C0LocalIdeal.functional_zero_of_local_nonvanishing Q
  · intro x
    refine ⟨x, ?_⟩
    change (oneSidedWeight c M (x 0) : ℂ) * q (x - x) ≠ 0
    rw [sub_self]
    exact mul_ne_zero (Complex.ofReal_ne_zero.mpr (oneSidedWeight_positive c M (x 0)).ne') hq0
  · intro a g
    exact functional_zero_weighted_factor c M δ hc hM hδ ℓ hkill (qt a) (hq.translate a) g

end WeightedDensity

/-- Lemma 2.1 with arbitrary real c>0, M≥0, δ>0 and the actual Cc∞ inverse
Fourier class at the prescribed fixed bandwidth. -/
theorem one_sided_density : OneSidedDensityStatement := by
  intro c M δ hc hM hδ H hH ε hε
  let H₀ := WeightedDensity.weightedC0Map hH
  obtain ⟨G, hG, hdist⟩ := Metric.mem_closure_iff.mp
    (WeightedDensity.bandlimitedWeightedSubmodule_dense c M δ hc hM hδ H₀) ε hε
  obtain ⟨F, hF, hGF⟩ := hG
  refine ⟨F, hF, ‖G - H₀‖, ?_, ?_⟩
  · rw [dist_comm] at hdist
    simpa only [dist_eq_norm] using hdist
  · intro x
    have heq : G x - H₀ x = (oneSidedWeight c M (x 0) : ℂ) * (F x - H x) := by
      rw [hGF]
      change (oneSidedWeight c M (x 0) : ℂ) * F x -
        (oneSidedWeight c M (x 0) : ℂ) * H x = _
      ring
    have hp := BoundedContinuousFunction.norm_coe_le_norm (G - H₀).toBCF x
    change ‖G x - H₀ x‖ ≤ ‖G - H₀‖ at hp
    rw [heq, norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (WeightedDensity.oneSidedWeight_positive c M (x 0))] at hp
    exact hp

#print axioms one_sided_density

end Bandlimited
end
