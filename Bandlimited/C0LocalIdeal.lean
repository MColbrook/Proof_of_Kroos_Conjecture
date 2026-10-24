module

public import Bandlimited.C0SmoothDensity
public import Bandlimited.C0Families
public import Mathlib.Analysis.Complex.Basic

/- Removing a family of local nonvanishing factors in C₀. -/

@[expose] public section
noncomputable section
open Set
open scoped Topology ZeroAtInfty BigOperators

namespace Bandlimited
namespace C0LocalIdeal

set_option maxHeartbeats 80000

 theorem continuous_div_on_support {d : ℕ} (f : E d → ℂ) (hf : Continuous f)
    (S : E d → ℂ) (hS : Continuous S)
    (hne : ∀ x ∈ tsupport f, S x ≠ 0) : Continuous (fun x => f x / S x) := by
  apply continuous_of_tsupport
  intro x hx
  have hsub : tsupport (fun x => f x / S x) ⊆ tsupport f := by
    simpa only [div_eq_mul_inv] using
      (tsupport_mul_subset_left (f := f) (g := fun x => (S x)⁻¹))
  exact hf.continuousAt.div hS.continuousAt (hne x (hsub hx))

 def compactDivision {d : ℕ} (f : C₀(E d, ℂ)) (hf : HasCompactSupport f)
    (S : C₀(E d, ℂ)) (hne : ∀ x ∈ tsupport f, S x ≠ 0) : C₀(E d, ℂ) where
  toFun x := f x / S x
  continuous_toFun := continuous_div_on_support f f.continuous S S.continuous hne
  zero_at_infty' := HasCompactSupport.is_zero_at_infty (hf.mono (by
    intro x hx
    exact Function.mem_support.mpr (fun hfx => hx (by simp [hfx]))))

 @[simp] theorem compactDivision_apply {d : ℕ} (f : C₀(E d, ℂ)) (hf : HasCompactSupport f)
    (S : C₀(E d, ℂ)) (hne : ∀ x ∈ tsupport f, S x ≠ 0) (x : E d) :
    compactDivision f hf S hne x = f x / S x := rfl

 theorem kills_compact_of_local_nonvanishing {d : ℕ} {ι : Type*}
    (Q : ι → C₀(E d, ℂ)) (hcover : ∀ x : E d, ∃ i, Q i x ≠ 0)
    (ℓ : C₀(E d, ℂ) →L[ℂ] ℂ)
    (hkill : ∀ i (g : C₀(E d, ℂ)), ℓ (Q i * g) = 0)
    (f : C₀(E d, ℂ)) (hf : HasCompactSupport f) : ℓ f = 0 := by
  classical
  let U (i : ι) : Set (E d) := {x | Q i x ≠ 0}
  have hU : ∀ i, IsOpen (U i) := fun i =>
    isOpen_ne_fun (Q i).continuous continuous_const
  have hcoverK : tsupport f ⊆ ⋃ i, U i := by
    intro x hx
    obtain ⟨i, hi⟩ := hcover x
    exact mem_iUnion.mpr ⟨i, hi⟩
  obtain ⟨s, hs⟩ := hf.isCompact.elim_finite_subcover U hU hcoverK
  let S : C₀(E d, ℂ) := ∑ i ∈ s, Q i * star (Q i)
  have hSreal (x : E d) : (S x).re = ∑ i ∈ s, Complex.normSq (Q i x) := by
    simp only [S, C0Families.sum_apply, ZeroAtInftyContinuousMap.mul_apply,
      ZeroAtInftyContinuousMap.star_apply, Complex.re_sum, Complex.star_def, Complex.mul_conj,
      Complex.ofReal_re]
  have hSne : ∀ x ∈ tsupport f, S x ≠ 0 := by
    intro x hx hzero
    obtain ⟨i, hi⟩ := mem_iUnion.mp (hs hx)
    obtain ⟨his, hix⟩ := mem_iUnion.mp hi
    have hpos : 0 < ∑ j ∈ s, Complex.normSq (Q j x) := by
      apply Finset.sum_pos' (fun j hj => Complex.normSq_nonneg _)
      exact ⟨i, his, Complex.normSq_pos.mpr hix⟩
    rw [← hSreal x, hzero] at hpos
    simpa using hpos
  let g : C₀(E d, ℂ) := compactDivision f hf S hSne
  have hfg : f = S * g := by
    apply ZeroAtInftyContinuousMap.ext
    intro x
    change f x = S x * (f x / S x)
    by_cases hfx : f x = 0
    · simp only [hfx, zero_div, mul_zero]
    · exact (mul_div_cancel₀ (f x) (hSne x (subset_tsupport _ (Function.mem_support.mpr hfx)))).symm
  rw [hfg]
  have hexp : S * g = ∑ i ∈ s, Q i * (star (Q i) * g) := by
    simp only [S, Finset.sum_mul, mul_assoc]
  rw [hexp, map_sum]
  exact Finset.sum_eq_zero fun i hi => hkill i (star (Q i) * g)

 theorem dense_compactSupport (d : ℕ) : Dense {f : C₀(E d, ℂ) | HasCompactSupport f} := by
  intro f
  apply Metric.mem_closure_iff.mpr
  intro ε hε
  obtain ⟨g, hcp, hg⟩ := C0SmoothDensity.exists_compact_schwartz_approx f ε hε
  exact ⟨C0SmoothDensity.schwartzC0 g, hcp,
    by rw [dist_comm, dist_eq_norm]; exact hg⟩

 theorem functional_zero_of_local_nonvanishing {d : ℕ} {ι : Type*}
    (Q : ι → C₀(E d, ℂ)) (hcover : ∀ x : E d, ∃ i, Q i x ≠ 0)
    (ℓ : C₀(E d, ℂ) →L[ℂ] ℂ)
    (hkill : ∀ i (g : C₀(E d, ℂ)), ℓ (Q i * g) = 0) : ℓ = 0 := by
  have hclosed : IsClosed {f : C₀(E d, ℂ) | ℓ f = 0} :=
    isClosed_eq ℓ.continuous continuous_const
  have hsub : {f : C₀(E d, ℂ) | HasCompactSupport f} ⊆ {f | ℓ f = 0} := by
    intro f hf
    exact kills_compact_of_local_nonvanishing Q hcover ℓ hkill f hf
  have hclosure := closure_minimal hsub hclosed
  apply ContinuousLinearMap.ext
  intro f
  exact hclosure (dense_compactSupport d f)

#print axioms continuous_div_on_support
#print axioms kills_compact_of_local_nonvanishing
#print axioms functional_zero_of_local_nonvanishing

end C0LocalIdeal
end Bandlimited
end
