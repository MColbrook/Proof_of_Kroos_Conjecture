module

public import Bandlimited.TensorDensity
public import Mathlib.Analysis.Normed.Module.HahnBanach
public import Mathlib.Analysis.Normed.Group.Quotient
public import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Quotient
public import Mathlib.Topology.ContinuousMap.ZeroAtInfty

/- Functional separation and the exact weighted C₀ identification for T08. -/

@[expose] public section
noncomputable section
open Set
open scoped ZeroAtInfty

namespace Bandlimited
namespace WeightedDensity

def weightedC0Map {d : ℕ} {W : E d → ℝ} {H : E d → ℂ}
    (hH : WeightedC0 W H) : C₀(E d, ℂ) where
  toFun x := (W x : ℂ) * H x
  continuous_toFun := hH.2.1
  zero_at_infty' := TensorDensity.vanishesAtInfinity_tendsto hH.2

@[simp] theorem weightedC0Map_apply {d : ℕ} {W : E d → ℝ} {H : E d → ℂ}
    (hH : WeightedC0 W H) (x : E d) : weightedC0Map hH x = (W x : ℂ) * H x := rfl

/-- Normed Hahn–Banach separation through the closed quotient. -/
theorem dense_submodule_of_dual_annihilator_trivial
    {X : Type*} [NormedAddCommGroup X] [NormedSpace ℂ X]
    (A : Submodule ℂ X)
    (h : ∀ ℓ : X →L[ℂ] ℂ, (∀ x ∈ A, ℓ x = 0) → ℓ = 0) :
    Dense (A : Set X) := by
  classical
  apply Submodule.dense_iff_topologicalClosure_eq_top.mpr
  apply le_antisymm le_top
  intro x hx
  by_contra hxA
  let B : Submodule ℂ X := A.topologicalClosure
  haveI : IsClosed (B : Set X) := A.isClosed_topologicalClosure
  have hqne : (B.mkQ x : X ⧸ B) ≠ 0 := by
    intro heq
    exact hxA ((Submodule.Quotient.mk_eq_zero B).mp heq)
  have hnorm : ‖(B.mkQ x : X ⧸ B)‖ ≠ 0 := norm_ne_zero_iff.mpr hqne
  obtain ⟨g, hg, hgx⟩ := exists_dual_vector ℂ (B.mkQ x : X ⧸ B) hnorm
  let ℓ : X →L[ℂ] ℂ := g.comp B.mkQL
  have hkill : ∀ y ∈ A, ℓ y = 0 := by
    intro y hy
    have hq : B.mkQ y = 0 := (Submodule.Quotient.mk_eq_zero B).mpr (A.le_topologicalClosure hy)
    change g (B.mkQ y) = 0
    rw [hq, map_zero]
  have hℓ : ℓ = 0 := h ℓ hkill
  have hval : g (B.mkQ x) = 0 := by
    change ℓ x = 0
    rw [hℓ]
    rfl
  have hcast : ((‖(B.mkQ x : X ⧸ B)‖ : ℝ) : ℂ) = 0 := hgx.symm.trans hval
  exact hnorm (Complex.ofReal_eq_zero.mp hcast)

#print axioms dense_submodule_of_dual_annihilator_trivial

end WeightedDensity
end Bandlimited
end
