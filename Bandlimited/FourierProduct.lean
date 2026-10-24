module

public import Bandlimited.FourierLinear
public import Mathlib.Analysis.InnerProductSpace.ProdL2
public import Mathlib.MeasureTheory.Integral.Prod

/-!
# Two-factor tensor products with separate frequency radii

The canonical Euclidean coordinate split preserves volume. Its frequency
support remains in the product of the original compact supports, including
zero-dimensional factors through their actual frequency witnesses.
-/

@[expose] public section
noncomputable section
open MeasureTheory Set
open scoped RealInnerProductSpace InnerProduct BigOperators Topology
namespace Bandlimited
namespace FourierProduct

 def splitIsometry (r k : ℕ) : E (r + k) ≃ₗᵢ[ℝ] WithLp 2 (E r × E k) :=
  (LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ finSumFinEquiv.symm).trans
    (PiLp.sumPiLpEquivProdLpPiLp 2 (fun _ => ℝ))

 abbrev split (r k : ℕ) : E (r + k) ≃L[ℝ] E r × E k :=
  (splitIsometry r k).toContinuousLinearEquiv.trans
    (WithLp.prodContinuousLinearEquiv 2 ℝ (E r) (E k))

 theorem split_measurePreserving (r k : ℕ) : MeasurePreserving (split r k) :=
  (WithLp.volume_preserving_ofLp (E r) (E k)).comp (splitIsometry r k).measurePreserving

 theorem split_inner {r k : ℕ} (x ξ : E (r + k)) :
    ⟪x, ξ⟫ = ⟪(split r k x).1, (split r k ξ).1⟫ +
      ⟪(split r k x).2, (split r k ξ).2⟫ := by
  rw [← (splitIsometry r k).inner_map_map x ξ, WithLp.prod_inner_apply]
  rfl

 theorem split_norm_bound {r k : ℕ} (ξ : E (r + k)) :
    ‖ξ‖ ≤ ‖(split r k ξ).1‖ + ‖(split r k ξ).2‖ := by
  have hsq := WithLp.prod_norm_sq_eq_of_L2 (splitIsometry r k ξ)
  rw [(splitIsometry r k).norm_map] at hsq
  change ‖ξ‖ ^ 2 = ‖(split r k ξ).1‖ ^ 2 + ‖(split r k ξ).2‖ ^ 2 at hsq
  nlinarith [norm_nonneg ξ, norm_nonneg (split r k ξ).1, norm_nonneg (split r k ξ).2,
    mul_nonneg (norm_nonneg (split r k ξ).1) (norm_nonneg (split r k ξ).2)]

 def frequency {r k : ℕ} (φ : E r → ℂ) (ψ : E k → ℂ) (ξ : E (r + k)) : ℂ :=
  φ (split r k ξ).1 * ψ (split r k ξ).2

 theorem frequency_support {r k : ℕ} (φ : E r → ℂ) (ψ : E k → ℂ) :
    tsupport (frequency φ ψ) ⊆
      (split r k) ⁻¹' (tsupport φ ×ˢ tsupport ψ) := by
  intro ξ hξ
  refine ⟨?_, ?_⟩
  · have hleft : ξ ∈ tsupport (fun ξ => φ (split r k ξ).1) :=
      tsupport_mul_subset_left hξ
    exact tsupport_comp_subset_preimage φ
      ((split r k).continuous.fst) hleft
  · have hright : ξ ∈ tsupport (fun ξ => ψ (split r k ξ).2) :=
      tsupport_mul_subset_right hξ
    exact tsupport_comp_subset_preimage ψ
      ((split r k).continuous.snd) hright

 theorem frequency_smooth {r k : ℕ} {δ τ : ℝ}
    {φ : E r → ℂ} {ψ : E k → ℂ}
    (hφ : SmoothFrequency δ φ) (hψ : SmoothFrequency τ ψ) :
    SmoothFrequency (δ + τ) (frequency φ ψ) := by
  have hcompact : IsCompact ((split r k) ⁻¹' (tsupport φ ×ˢ tsupport ψ)) :=
    (split r k).toHomeomorph.isClosedEmbedding.isCompact_preimage (hφ.2.1.prod hψ.2.1)
  refine ⟨(hφ.1.comp (split r k).contDiff.fst).mul
    (hψ.1.comp (split r k).contDiff.snd),
    hcompact.of_isClosed_subset (isClosed_tsupport _) (frequency_support φ ψ), ?_⟩
  intro ξ hξ
  obtain ⟨hξφ, hξψ⟩ := frequency_support φ ψ hξ
  have hδ : ‖(split r k ξ).1‖ < δ := by
    simpa only [Metric.mem_ball, dist_zero_right] using hφ.2.2 hξφ
  have hτ : ‖(split r k ξ).2‖ < τ := by
    simpa only [Metric.mem_ball, dist_zero_right] using hψ.2.2 hξψ
  simp only [Metric.mem_ball, dist_zero_right]
  exact (split_norm_bound ξ).trans_lt (add_lt_add hδ hτ)

 theorem inverseFourier_frequency {r k : ℕ} (φ : E r → ℂ) (ψ : E k → ℂ)
    (x : E (r + k)) :
    inverseFourier (frequency φ ψ) x =
      inverseFourier φ (split r k x).1 * inverseFourier ψ (split r k x).2 := by
  have hdot (ξ : E (r + k)) :
      (∑ i : Fin (r + k), x i * ξ i : ℝ) =
      (∑ i : Fin r, (split r k x).1 i * (split r k ξ).1 i : ℝ) +
      ∑ i : Fin k, (split r k x).2 i * (split r k ξ).2 i := by
    simpa only [EuclideanSpace.inner_eq_star_dotProduct, dotProduct, star_trivial] using split_inner ξ x
  let H : E r → ℂ := fun ξ => φ ξ * Complex.exp
    (Complex.I * ((∑ i : Fin r, (split r k x).1 i * ξ i : ℝ) : ℂ))
  let K : E k → ℂ := fun ξ => ψ ξ * Complex.exp
    (Complex.I * ((∑ i : Fin k, (split r k x).2 i * ξ i : ℝ) : ℂ))
  have hphase (ξ : E (r + k)) :
      frequency φ ψ ξ * Complex.exp
        (Complex.I * ((∑ i : Fin (r + k), x i * ξ i : ℝ) : ℂ)) =
      H (split r k ξ).1 * K (split r k ξ).2 := by
    rw [hdot, Complex.ofReal_add, mul_add, Complex.exp_add]
    dsimp [frequency, H, K]
    ring
  have hint : (∫ ξ : E (r + k), frequency φ ψ ξ * Complex.exp
      (Complex.I * ((∑ i : Fin (r + k), x i * ξ i : ℝ) : ℂ))) =
      (∫ ξ : E r, H ξ) * ∫ ξ : E k, K ξ := by
    simp_rw [hphase]
    change (∫ ξ : E (r + k), (fun z : E r × E k => H z.1 * K z.2) (split r k ξ)) = _
    exact ((split_measurePreserving r k).integral_comp
      (split r k).toHomeomorph.toMeasurableEquiv.measurableEmbedding
      (fun z : E r × E k => H z.1 * K z.2)).trans (integral_prod_mul H K)
  unfold inverseFourier
  rw [hint]
  simp only [pow_add, inv_mul_cancel₀, mul_inv, Complex.ofReal_mul]
  dsimp [H, K]
  ring

 def combinedEquiv {r k : ℕ} (U : E (r + k) ≃L[ℝ] E r × E k) :
    E (r + k) ≃L[ℝ] E (r + k) := U.trans (split r k).symm

 def firstMap {r k : ℕ} (U : E (r + k) ≃L[ℝ] E r × E k) : E (r + k) →L[ℝ] E r :=
  (ContinuousLinearMap.fst ℝ (E r) (E k)).comp U.toContinuousLinearMap

 def secondMap {r k : ℕ} (U : E (r + k) ≃L[ℝ] E r × E k) : E (r + k) →L[ℝ] E k :=
  (ContinuousLinearMap.snd ℝ (E r) (E k)).comp U.toContinuousLinearMap

 theorem combined_adjoint {r k : ℕ} (U : E (r + k) ≃L[ℝ] E r × E k)
    (ξ : E (r + k)) :
    FourierLinear.adjointEquiv (combinedEquiv U) ξ =
      (ContinuousLinearMap.adjoint (firstMap U)) (split r k ξ).1 + (ContinuousLinearMap.adjoint (secondMap U)) (split r k ξ).2 := by
  apply ext_inner_left ℝ
  intro x
  change ⟪x, (ContinuousLinearMap.adjoint (combinedEquiv U : E (r + k) →L[ℝ] E (r + k))) ξ⟫ = _
  rw [ContinuousLinearMap.adjoint_inner_right, inner_add_right,
    ContinuousLinearMap.adjoint_inner_right, ContinuousLinearMap.adjoint_inner_right]
  have h := split_inner (combinedEquiv U x) ξ
  have heq : split r k (combinedEquiv U x) = U x := by
    simp only [combinedEquiv, ContinuousLinearEquiv.trans_apply,
      ContinuousLinearEquiv.apply_symm_apply]
  rw [heq] at h
  exact h

 theorem combined_adjoint_norm_bound {r k : ℕ} (U : E (r + k) ≃L[ℝ] E r × E k)
    (ξ : E (r + k)) :
    ‖FourierLinear.adjointEquiv (combinedEquiv U) ξ‖ ≤
      ‖firstMap U‖ * ‖(split r k ξ).1‖ + ‖secondMap U‖ * ‖(split r k ξ).2‖ := by
  rw [combined_adjoint]
  apply (norm_add_le _ _).trans
  apply add_le_add
  · simpa only [ContinuousLinearMap.adjoint.norm_map] using
      ((firstMap U)†).le_opNorm (split r k ξ).1
  · simpa only [ContinuousLinearMap.adjoint.norm_map] using
      ((secondMap U)†).le_opNorm (split r k ξ).2

 theorem frequency_transported {r k : ℕ} {δ τ σ : ℝ}
    {φ : E r → ℂ} {ψ : E k → ℂ}
    (hφ : SmoothFrequency δ φ) (hψ : SmoothFrequency τ ψ)
    (U : E (r + k) ≃L[ℝ] E r × E k)
    (hband : ‖firstMap U‖ * δ + ‖secondMap U‖ * τ < σ) :
    SmoothFrequency σ (FourierLinear.transportedFrequency (combinedEquiv U) (frequency φ ψ)) := by
  have hprod := frequency_smooth hφ hψ
  apply FourierLinear.transportedFrequency_smooth_of_support_image
    (combinedEquiv U) (frequency φ ψ) hprod.1 hprod.2.1
  intro ξ hξ
  obtain ⟨hξφ, hξψ⟩ := frequency_support φ ψ hξ
  have hδ : ‖(split r k ξ).1‖ < δ := by
    simpa only [Metric.mem_ball, dist_zero_right] using hφ.2.2 hξφ
  have hτ : ‖(split r k ξ).2‖ < τ := by
    simpa only [Metric.mem_ball, dist_zero_right] using hψ.2.2 hξψ
  exact (combined_adjoint_norm_bound U ξ).trans_lt
    ((add_le_add (mul_le_mul_of_nonneg_left hδ.le (norm_nonneg _))
      (mul_le_mul_of_nonneg_left hτ.le (norm_nonneg _))).trans_lt hband)

end FourierProduct

 theorem InBandlimitedSpace.product_split {r k : ℕ} {δ τ : ℝ}
    {F : E r → ℂ} {G : E k → ℂ}
    (hF : InBandlimitedSpace r δ F) (hG : InBandlimitedSpace k τ G)
    (hδ : 0 < δ) (hτ : 0 < τ) :
    InBandlimitedSpace (r + k) (δ + τ)
      (fun x => F (FourierProduct.split r k x).1 * G (FourierProduct.split r k x).2) := by
  by_cases hd : r + k = 0
  · have hr : r = 0 := by omega
    have hk : k = 0 := by omega
    subst r
    subst k
    simp only [InBandlimitedSpace, ↓reduceIte]
    exact ⟨F (FourierProduct.split 0 0 0).1 * G (FourierProduct.split 0 0 0).2,
      fun x => by
        have hx : x = 0 := by ext i; exact Fin.elim0 i
        rw [hx]⟩
  · obtain ⟨φ, hφ, rfl⟩ := hF.exists_frequency hδ
    obtain ⟨ψ, hψ, rfl⟩ := hG.exists_frequency hτ
    simp only [InBandlimitedSpace, hd, ↓reduceIte]
    exact ⟨FourierProduct.frequency φ ψ, FourierProduct.frequency_smooth hφ hψ,
      funext fun x => (FourierProduct.inverseFourier_frequency φ ψ x).symm⟩

 theorem InBandlimitedSpace.mul_comp_of_equiv {s r k : ℕ} {δ τ σ : ℝ}
    {F : E r → ℂ} {G : E k → ℂ}
    (hF : InBandlimitedSpace r δ F) (hG : InBandlimitedSpace k τ G)
    (hδ : 0 < δ) (hτ : 0 < τ)
    (U : E s ≃L[ℝ] E r × E k)
    (hband : ‖(ContinuousLinearMap.fst ℝ (E r) (E k)).comp U.toContinuousLinearMap‖ * δ +
      ‖(ContinuousLinearMap.snd ℝ (E r) (E k)).comp U.toContinuousLinearMap‖ * τ < σ) :
    InBandlimitedSpace s σ (fun x => F (U x).1 * G (U x).2) := by
  have hdim : s = r + k := by
    have h := U.toLinearEquiv.finrank_eq
    simpa only [Module.finrank_prod, E, finrank_euclideanSpace_fin] using h
  subst s
  by_cases hd : r + k = 0
  · have hr : r = 0 := by omega
    have hk : k = 0 := by omega
    subst r
    subst k
    simp only [InBandlimitedSpace, ↓reduceIte]
    exact ⟨F (U 0).1 * G (U 0).2, fun x => by
        have hx : x = 0 := by ext i; exact Fin.elim0 i
        rw [hx]⟩
  · obtain ⟨φ, hφ, rfl⟩ := hF.exists_frequency hδ
    obtain ⟨ψ, hψ, rfl⟩ := hG.exists_frequency hτ
    simp only [InBandlimitedSpace, hd, ↓reduceIte]
    refine ⟨FourierLinear.transportedFrequency (FourierProduct.combinedEquiv U)
      (FourierProduct.frequency φ ψ), FourierProduct.frequency_transported hφ hψ U hband, ?_⟩
    funext x
    rw [FourierLinear.inverseFourier_transportedFrequency,
      FourierProduct.inverseFourier_frequency]
    simp only [FourierProduct.combinedEquiv, ContinuousLinearEquiv.trans_apply,
      ContinuousLinearEquiv.apply_symm_apply]

 theorem InBandlimitedSpace.mul_comp_of_bijective {s r k : ℕ} {δ τ σ : ℝ}
    {F : E r → ℂ} {G : E k → ℂ}
    (hF : InBandlimitedSpace r δ F) (hG : InBandlimitedSpace k τ G)
    (hδ : 0 < δ) (hτ : 0 < τ)
    (P : E s →L[ℝ] E r) (Q : E s →L[ℝ] E k)
    (hpair : Function.Bijective (fun x => (P x, Q x)))
    (hband : ‖P‖ * δ + ‖Q‖ * τ < σ) :
    InBandlimitedSpace s σ (fun x => F (P x) * G (Q x)) := by
  let U : E s ≃L[ℝ] E r × E k :=
    (LinearEquiv.ofBijective (P.prod Q).toLinearMap hpair).toContinuousLinearEquiv
  have hP : (ContinuousLinearMap.fst ℝ (E r) (E k)).comp U.toContinuousLinearMap = P := by
    ext x
    rfl
  have hQ : (ContinuousLinearMap.snd ℝ (E r) (E k)).comp U.toContinuousLinearMap = Q := by
    ext x
    rfl
  have hb : ‖(ContinuousLinearMap.fst ℝ (E r) (E k)).comp U.toContinuousLinearMap‖ * δ +
      ‖(ContinuousLinearMap.snd ℝ (E r) (E k)).comp U.toContinuousLinearMap‖ * τ < σ := by
    simpa only [hP, hQ] using hband
  exact hF.mul_comp_of_equiv hG hδ hτ U hb

#print axioms InBandlimitedSpace.mul_comp_of_bijective

#print axioms InBandlimitedSpace.product_split
#print axioms FourierProduct.inverseFourier_frequency

end Bandlimited
