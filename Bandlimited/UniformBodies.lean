module

public import Bandlimited.UniformNormalization
public import Bandlimited.PolynomialTransport

/-! The dimension-only normalization gives a threshold uniform over all
symmetric convex bodies. This is a conditional reduction from T02 to T06;
it is not a proof of T02. -/

@[expose] public section
noncomputable section
open Set
namespace Bandlimited

theorem frontier_transport {d : ℕ} (f : E d ≃ₗ[ℝ] E d) (K : Set (E d))
    (x : E d) (hx : x ∈ frontier K) :
    f.symm x ∈ frontier (f ⁻¹' K) := by
  have h := f.toContinuousLinearEquiv.toHomeomorph.preimage_frontier K
  have h' : f ⁻¹' frontier K = frontier (f ⁻¹' K) := by
    simpa only [ContinuousLinearEquiv.coe_toHomeomorph,
      LinearEquiv.coe_toContinuousLinearEquiv'] using h
  rw [← h']
  change f (f.symm x) ∈ frontier K
  simpa only [f.apply_symm_apply] using hx

theorem boundary_error_transport {d : ℕ} (f : E d ≃ₗ[ℝ] E d)
    (K : Set (E d)) (p : Polynomial d) {ε : ℝ}
    (hp : BoundaryErrorLT (f ⁻¹' K) p (fun _ => 1) ε) :
    BoundaryErrorLT K (polynomialPullback f.symm.toLinearMap p) (fun _ => 1) ε := by
  obtain ⟨b, hb, hbound⟩ := hp
  refine ⟨b, hb, ?_⟩
  intro x
  rw [polynomialPullback_eval]
  exact hbound ⟨f.symm (x : E d), frontier_transport f K x x.property⟩

theorem all_bodies_uniform_of_bounded_norm_uniform
    (hbounded : BoundedNormUniformStatement) : AllBodiesUniformStatement := by
  intro d ε hε
  by_cases hd : 1 ≤ d
  · have hdpos : (0 : ℝ) < d := by exact_mod_cast (show 0 < d by omega)
    have hinv : (d : ℝ)⁻¹ ≤ d := by
      have hd1 : (1 : ℝ) ≤ d := by exact_mod_cast hd
      exact (inv_le_one₀ hdpos).2 hd1 |>.trans hd1
    obtain ⟨n₀, hn₀⟩ := hbounded d (d : ℝ)⁻¹ (d : ℝ) (inv_pos.mpr hdpos) hinv ε hε
    refine ⟨n₀, ?_⟩
    intro n hn K hK
    obtain ⟨f, ν, hν, hball⟩ := symmetric_body_uniform_normalization hd hK
    obtain ⟨p, hp, herr⟩ := hn₀ n hn ν hν
    rw [hball] at herr
    exact ⟨polynomialPullback f.symm.toLinearMap p,
      polynomialPullback_homogeneous _ hp, boundary_error_transport f K p herr⟩
  · have hd0 : d = 0 := by omega
    subst d
    refine ⟨0, ?_⟩
    intro n hn K hK
    obtain ⟨ν, α, β, hα, hαβ, hν, hball⟩ := symmetric_body_as_norm_ball hK
    refine ⟨0, MvPolynomial.isHomogeneous_zero _ _ _, 0, hε, ?_⟩
    intro x
    have hempty : frontier K = ∅ := by
      rw [← hball]
      exact zero_dimensional_boundary_empty ν
    exact False.elim (by simpa only [hempty, Set.mem_empty_iff_false] using x.property)

#print axioms frontier_transport
#print axioms boundary_error_transport
#print axioms all_bodies_uniform_of_bounded_norm_uniform

end Bandlimited
end
