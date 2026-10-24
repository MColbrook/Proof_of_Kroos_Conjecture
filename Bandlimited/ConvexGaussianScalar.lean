module

public import Bandlimited.WeightedSchwartz

/- Scalar-coordinate transport for the one-dimensional density theorem. -/
@[expose] public section
noncomputable section
open Set
namespace Bandlimited
namespace ConvexGaussian

def scalarBandlimited (δ : ℝ) : Set (ℝ → ℂ) :=
  {F | InBandlimitedSpace 1 δ (fun x : E 1 => F (x 0))}

theorem scalarWeightedC0_lift {W : ℝ → ℝ} {H : ℝ → ℂ}
    (hH : ScalarWeightedC0 W H) :
    WeightedC0 (fun x : E 1 => W (x 0)) (fun x : E 1 => H (x 0)) := by
  refine ⟨hH.1.comp (PiLp.continuous_apply 2 (fun _ : Fin 1 => ℝ) 0),
    hH.2.1.comp (PiLp.continuous_apply 2 (fun _ : Fin 1 => ℝ) 0), ?_⟩
  intro ε hε
  obtain ⟨R, hR, htail⟩ := hH.2.2 ε hε
  refine ⟨R, hR, ?_⟩
  intro x hx
  exact htail (x 0) (by simpa only [WeightedDensity.norm_one_dimensional] using hx)

/-- T08 supplies the scalar dense classes used by T09, with the exact same
one-sided weight and actual compact-frequency inverse transforms. -/
theorem oneSided_scalar_dense (hone : OneSidedDensityStatement)
    (c M δ : ℝ) (hc : 0 < c) (hM : 0 ≤ M) (hδ : 0 < δ) :
    ScalarWeightedDense (oneSidedWeight c M) (scalarBandlimited δ) := by
  refine ⟨?_, ?_⟩
  · intro F hF
    have hweighted := WeightedDensity.bandlimited_oneSided_weightedC0 hF c M hc hM
    simpa only [TensorDensity.scalarLine_apply] using TensorDensity.weightedC0_to_scalar hweighted
  · intro H hH ε hε
    obtain ⟨F, hF, b, hb, herr⟩ := hone c M δ hc hM hδ
      (fun x : E 1 => H (x 0)) (scalarWeightedC0_lift hH) ε hε
    refine ⟨fun t => F (TensorDensity.scalarLine t), ?_, b, hb, ?_⟩
    · change InBandlimitedSpace 1 δ
        (fun x : E 1 => F (TensorDensity.scalarLine (x 0)))
      simpa only [TensorDensity.scalarLine_coord] using hF
    · intro t
      simpa only [TensorDensity.scalarLine_apply] using herr (TensorDensity.scalarLine t)

#print axioms scalarWeightedC0_lift
#print axioms oneSided_scalar_dense
end ConvexGaussian
end Bandlimited
end
