module

public import Bandlimited.BodyGeometry
public import Mathlib.Analysis.Normed.Module.HahnBanach
public import Mathlib.Analysis.Convex.Function

/-! A supporting functional for the given BodyNorm, in the fixed Euclidean
topology. The dominated Hahn–Banach extension is Mathlib's theorem; the
seminorm and all bounds come only from the source norm assumptions. -/

@[expose] public section
noncomputable section
open Set
namespace Bandlimited

def BodyNorm.toSeminorm {d : ℕ} (ν : BodyNorm d) : Seminorm ℝ (E d) :=
  Seminorm.of ν.toFun ν.add_le (by simpa only [Real.norm_eq_abs] using ν.smul)

theorem BodyNorm.convexOn {d : ℕ} (ν : BodyNorm d) : ConvexOn ℝ univ ν.toFun := by
  refine ⟨convex_univ, ?_⟩
  intro x hx y hy a b ha hb hab
  calc
    ν.toFun (a • x + b • y) ≤ ν.toFun (a • x) + ν.toFun (b • y) := ν.add_le _ _
    _ = a * ν.toFun x + b * ν.toFun y := by
      rw [ν.smul, ν.smul, abs_of_nonneg ha, abs_of_nonneg hb]
    _ = a • ν.toFun x + b • ν.toFun y := rfl

theorem BodyNorm.supporting_functional {d : ℕ} (ν : BodyNorm d)
    {α β : ℝ} (hβ : 0 ≤ β) (hν : NormBounds α β ν)
    (v : E d) (hv : v ≠ 0) :
    ∃ ℓ : E d →L[ℝ] ℝ, ℓ v = ν.toFun v ∧
      (∀ x, |ℓ x| ≤ ν.toFun x) ∧ ‖ℓ‖ ≤ β := by
  let S := Submodule.span ℝ ({v} : Set (E d))
  let coord : S →ₗ[ℝ] ℝ := LinearEquiv.coord ℝ (E d) v hv
  let f : S →ₗ[ℝ] ℝ := ν.toFun v • coord
  have hp (x : S) : f x ≤ ν.toSeminorm x := by
    have hx : coord x • v = (x : E d) :=
      LinearEquiv.coord_apply_smul ℝ (E d) v hv x
    change ν.toFun v * coord x ≤ ν.toFun (x : E d)
    rw [← hx, ν.smul]
    calc
      ν.toFun v * coord x = coord x * ν.toFun v := mul_comm _ _
      _ ≤ |coord x| * ν.toFun v :=
        mul_le_mul_of_nonneg_right (le_abs_self _) (ν.nonneg v)
  obtain ⟨ℓ, hℓ, hbound⟩ :=
    Module.Dual.exists_continuous_extension_of_le_seminorm_real S f
      (p := ν.toSeminorm) (ν.continuous_of_bounds hβ hν) hp
  refine ⟨ℓ, ?_, hbound, ℓ.opNorm_le_bound hβ ?_⟩
  · have h := hℓ ⟨v, Submodule.mem_span_singleton_self v⟩
    change ℓ v = ν.toFun v * LinearEquiv.coord ℝ (E d) v hv
      ⟨v, Submodule.mem_span_singleton_self v⟩ at h
    simpa only [LinearEquiv.coord_self, mul_one] using h
  · intro x
    have h := hbound x
    change |ℓ x| ≤ ν.toFun x at h
    exact (show ‖ℓ x‖ ≤ ν.toFun x by
      simpa only [Real.norm_eq_abs] using h).trans (hν x).2

#print axioms BodyNorm.convexOn
#print axioms BodyNorm.supporting_functional

end Bandlimited
end
