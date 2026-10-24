module

public import Bandlimited.ConvexGaussianAssembly
public import Bandlimited.FourierProduct

/- The full convex weighted Gaussian theorem follows from the one-sided density
theorem. This explicit dependency is discharged only after the actual T08 theorem
has been checked; it is not an added axiom or a replacement principal statement. -/
@[expose] public section
noncomputable section
open Set
open scoped BigOperators RealInnerProductSpace
namespace Bandlimited
namespace ConvexGaussian

set_option maxHeartbeats 600000 in
theorem convex_weighted_gaussian_of_one_sided_density (hone : OneSidedDensityStatement) :
    ConvexWeightedGaussianStatement := by
  classical
  intro s hs L σ hL hσ
  obtain ⟨g, e, hge, hgzero, heconv⟩ := fourier_cutoff s L σ hL hσ
  let B : ℝ := uniformGaussianBound L
  let C : ℝ := 1 + B
  have hB : 0 < B := uniformGaussianBound_pos L
  have hC : 0 ≤ C := by dsimp [C]; positivity
  obtain ⟨Δ, hΔlim, hΔ⟩ := finite_error_budget s e C hC
    (fun k hk A hA => (hge k hk A hA).2.2.1) heconv
  refine ⟨Δ, hΔlim, ?_⟩
  intro A hA
  refine ⟨(hΔ A hA).1, ?_⟩
  intro f hf η hη
  let S := activeSubspace f
  let r := Module.finrank ℝ S
  have hApos : 0 < A := lt_of_lt_of_le zero_lt_one hA
  by_cases hr : r = 0
  · have hS : activeSubspace f = ⊥ := Submodule.finrank_eq_zero.mp hr
    have hfzero := profile_zero_of_active_eq_bot hf hS
    obtain ⟨hg, hreal, he, hesup, herr⟩ := hge s le_rfl A hA
    refine ⟨g s A, hg.mono (by linarith), hreal, ?_⟩
    intro x
    have hbudget : e s A ≤ Δ A := by
      have hscale : e s A ≤ C * e s A := by dsimp [C]; nlinarith
      exact hscale.trans ((hΔ A hA).2 s le_rfl)
    simpa only [hfzero x, neg_zero, Real.exp_zero, Complex.ofReal_one, one_mul] using
      (herr x).trans (hbudget.trans (le_add_of_nonneg_right hη.le))
  · have hrone : 1 ≤ r := Nat.one_le_iff_ne_zero.mpr hr
    have hrpos : 0 < (r : ℝ) := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hr)
    obtain ⟨v, Cbasis, hind, hspan, hCbasis, hsupport⟩ := profile_supporting_basis hf
    let T := slopeCoordinateEquiv S v hspan
    let P : E s →L[ℝ] E r := activeProjection S T
    let Q := complementProjection S
    let k := Module.finrank ℝ Sᗮ
    have hk : k ≤ s := by
      have hd := active_complement_dimensions S
      dsimp [k]
      omega
    obtain ⟨hg, hreal, he, hesup, herr⟩ := hge k hk A hA
    let θ : ℝ := σ / (8 * (1 + ‖P‖))
    have hθ : 0 < θ := by dsimp [θ]; positivity
    let δ : ℝ := θ / (r : ℝ)
    have hδ : 0 < δ := div_pos hθ hrpos
    have hrδ : (r : ℝ) * δ = θ := by dsimp [δ]; field_simp
    let ε : ℝ := η / (B + e k A + 1)
    have hε : 0 < ε := div_pos hη (by positivity)
    obtain ⟨m, F, hF, hactive⟩ := active_tensor_approximation hone hf v Cbasis hspan
      hCbasis hsupport A L δ ε hA hL hδ hε hrone
    let U : E r → ℂ := fun t => ∑ j : Fin m, ∏ i : Fin r, F j i (t i)
    have hU : InBandlimitedSpace r θ U := by
      have h := tensor_sum_bandlimited F hF
      change InBandlimitedSpace r ((r : ℝ) * δ) U at h
      rw [hrδ] at h
      exact h
    have hpair : Function.Bijective (fun x : E s => (P x, Q x)) :=
      active_complement_bijective S T
    have hband : ‖P‖ * θ + ‖Q‖ * (σ / 4) < σ := by
      have heq : (1 + ‖P‖) * θ = σ / 8 := by dsimp [θ]; field_simp
      have hp : ‖P‖ * θ < σ / 8 := by nlinarith
      have hq : ‖Q‖ * (σ / 4) ≤ σ / 4 := by
        simpa only [one_mul] using mul_le_mul_of_nonneg_right
          (complementProjection_norm_le S) (by positivity : 0 ≤ σ / 4)
      linarith
    let M : E s → ℂ := fun x => U (P x) * g k A (Q x)
    have hM : InBandlimitedSpace s σ M :=
      hU.mul_comp_of_bijective hg hθ (by positivity) P Q hpair hband
    refine ⟨fun x => ((M x).re : ℂ), hM.real_part, ?_, ?_⟩
    · intro x
      simp
    · intro x
      let y : S := S.orthogonalProjectionOnto x
      let wy := gaussianWeight A L (y : E s)
      let wz := gaussianWeight A L (Q x)
      have hwy : 0 ≤ wy := by dsimp [wy, gaussianWeight]; positivity
      have hwz : 0 ≤ wz := by dsimp [wz, gaussianWeight]; positivity
      have hw : 0 ≤ gaussianWeight A L x := by unfold gaussianWeight; positivity
      have hact : wy * ‖(Real.exp (-f x) : ℂ) * U (P x) -
          (gaussian A (y : E s) : ℂ)‖ ≤ ε := by
        rw [active_profile_projection hf x]
        exact (hactive y).le
      have hgaussy : wy * ‖(gaussian A (y : E s) : ℂ)‖ ≤ B := by
        rw [Complex.norm_real, Real.norm_of_nonneg (by unfold gaussian; positivity)]
        exact weighted_gaussian_uniform A L hApos hL (y : E s)
      have hgaussz : wz * ‖(gaussian A (Q x) : ℂ)‖ ≤ B := by
        rw [Complex.norm_real, Real.norm_of_nonneg (by unfold gaussian; positivity)]
        exact weighted_gaussian_uniform A L hApos hL (Q x)
      have hprod := weighted_product_error (gaussianWeight A L x) wy wz ε B (e k A)
        (Real.exp (-f x) : ℂ) (U (P x)) (g k A (Q x))
        (gaussian A (y : E s) : ℂ) (gaussian A (Q x) : ℂ)
        hw hwy hwz hε.le hB.le he
        (gaussianWeight_orthogonal_bound S A L hApos hL x)
        hact (herr (Q x)) hgaussy hgaussz
      have hMerror : gaussianWeight A L x *
          ‖(Real.exp (-f x) : ℂ) * M x - (gaussian A x : ℂ)‖ ≤
            ε * (B + e k A) + B * e k A := by
        have hgfact : gaussian A x = gaussian A (y : E s) * gaussian A (Q x) :=
          gaussian_orthogonal_factorization S A x
        simpa only [M, ← Complex.ofReal_mul, ← hgfact] using hprod
      have hsmall : ε * (B + e k A) < η := by
        have heq : ε * (B + e k A + 1) = η := by dsimp [ε]; field_simp
        nlinarith
      have hbudget : B * e k A ≤ Δ A := by
        have hscale : B * e k A ≤ C * e k A := by dsimp [C]; nlinarith
        exact hscale.trans ((hΔ A hA).2 k hk)
      have htotal : gaussianWeight A L x *
          ‖(Real.exp (-f x) : ℂ) * M x - (gaussian A x : ℂ)‖ ≤ Δ A + η := by
        linarith
      exact (mul_le_mul_of_nonneg_left (real_part_error_le (Real.exp (-f x))
        (gaussian A x) (M x)) hw).trans htotal

#print axioms convex_weighted_gaussian_of_one_sided_density
end ConvexGaussian
end Bandlimited
end
