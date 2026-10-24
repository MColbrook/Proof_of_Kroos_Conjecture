module

public import Bandlimited.WeightedSchwartz
public import Mathlib.Analysis.Calculus.BumpFunction.SmoothApprox
public import Mathlib.Topology.ContinuousMap.CompactlySupported

/- Uniform approximation of C₀ functions by smooth compactly supported functions. -/

@[expose] public section
noncomputable section
open Set Metric Filter
open scoped Topology ZeroAtInfty ContDiff

namespace Bandlimited
namespace C0SmoothDensity

set_option maxHeartbeats 60000

 theorem vanishesAtInfinity {d : ℕ} (f : C₀(E d, ℂ)) : VanishesAtInfinity f := by
  refine ⟨f.continuous, ?_⟩
  intro ε hε
  have ht : ∀ᶠ x in cocompact (E d), ‖f x‖ < ε := by
    simpa only [dist_zero_right] using
      (Metric.tendsto_nhds.mp (zero_at_infty f) ε hε)
  obtain ⟨K, hK, htail⟩ := Filter.mem_cocompact.mp ht
  obtain ⟨R, hR, hbound⟩ := hK.isBounded.exists_pos_norm_le
  refine ⟨R + 1, (by linarith), fun x hx => htail ?_⟩
  intro hxK
  have := hbound x hxK
  linarith

 def schwartzC0 {d : ℕ} (f : SchwartzMap (E d) ℂ) : C₀(E d, ℂ) where
  toFun := f
  continuous_toFun := f.continuous
  zero_at_infty' := TensorDensity.vanishesAtInfinity_tendsto ⟨f.continuous, fun ε hε => by
    obtain ⟨R, hR, ht⟩ := WeightedDensity.schwartz_real_weight_tail f 0 (by norm_num) ε hε
    refine ⟨R, (by linarith), fun x hx => ?_⟩
    simpa only [gaussianWeight, Real.rpow_zero, one_mul] using ht x hx⟩

 @[simp] theorem schwartzC0_apply {d : ℕ} (f : SchwartzMap (E d) ℂ) (x : E d) :
    schwartzC0 f x = f x := rfl

 theorem exists_compact_schwartz_approx {d : ℕ} (f : C₀(E d, ℂ)) (ε : ℝ)
    (hε : 0 < ε) :
    ∃ g : SchwartzMap (E d) ℂ, HasCompactSupport (g : E d → ℂ) ∧
      ‖(schwartzC0 g - f : C₀(E d, ℂ))‖ < ε := by
  have hu : UniformContinuous (f : E d → ℂ) :=
    f.continuous.uniformContinuous_of_tendsto_cocompact (zero_at_infty f)
  obtain ⟨g, hg, herr⟩ := hu.exists_contDiff_dist_le (show 0 < ε / 4 by positivity)
  obtain ⟨R, hR, htail⟩ := (vanishesAtInfinity f).2 (ε / 4) (by positivity)
  let ψ : ContDiffBump (0 : E d) :=
    ⟨R + 1, R + 2, (by linarith), (by linarith)⟩
  let ψC : E d → ℂ := fun x => (ψ x : ℂ)
  have hψC : ContDiff ℝ ∞ ψC := Complex.ofRealCLM.contDiff.comp ψ.contDiff
  have hψcp : HasCompactSupport ψC := ψ.hasCompactSupport.comp_left (g := fun r : ℝ => (r : ℂ)) (by simp)
  have hcp : HasCompactSupport (fun x => ψC x * g x) := hψcp.mul_right
  let G : SchwartzMap (E d) ℂ := hcp.toSchwartzMap (hψC.mul hg)
  refine ⟨G, hcp, lt_of_le_of_lt ?_ (show ε / 2 < ε by linarith)⟩
  change ‖(schwartzC0 G - f).toBCF‖ ≤ ε / 2
  apply (BoundedContinuousFunction.norm_le (f := (schwartzC0 G - f).toBCF)
    (by positivity : 0 ≤ ε / 2)).mpr
  intro x
  change ‖ψC x * g x - f x‖ ≤ ε / 2
  have hψ0 : 0 ≤ ψ x := ψ.nonneg
  have hψ1 : ψ x ≤ 1 := ψ.le_one
  have hnormψ : ‖ψC x‖ ≤ 1 := by
    simpa only [ψC, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hψ0] using hψ1
  have hnormsub : ‖ψC x - 1‖ ≤ 1 := by
    have heq : ψC x - 1 = ((ψ x - 1 : ℝ) : ℂ) := by simp only [ψC, Complex.ofReal_sub, Complex.ofReal_one]
    rw [heq, Complex.norm_real, Real.norm_eq_abs, abs_of_nonpos (by linarith)]
    linarith
  by_cases hx : ‖x‖ ≤ R + 1
  · have hψx : ψC x = 1 := by
      change (ψ x : ℂ) = 1
      rw [ψ.one_of_mem_closedBall]
      · rfl
      · simpa only [mem_closedBall, dist_zero_right, ψ] using hx
    rw [hψx, one_mul]
    exact (show ‖g x - f x‖ < ε / 4 by simpa only [dist_eq_norm] using herr x).le.trans
      (by linarith)
  · have hxR : R ≤ ‖x‖ := by linarith [lt_of_not_ge hx]
    calc
      ‖ψC x * g x - f x‖ = ‖ψC x * (g x - f x) + (ψC x - 1) * f x‖ := by congr 1; ring
      _ ≤ ‖ψC x * (g x - f x)‖ + ‖(ψC x - 1) * f x‖ := norm_add_le _ _
      _ ≤ ‖g x - f x‖ + ‖f x‖ := by
        simp only [norm_mul]
        exact add_le_add (mul_le_of_le_one_left (norm_nonneg _) hnormψ)
          (mul_le_of_le_one_left (norm_nonneg _) hnormsub)
      _ ≤ ε / 2 := by
        have hgx : ‖g x - f x‖ < ε / 4 := by simpa only [dist_eq_norm] using herr x
        have hfx := htail x hxR
        linarith

 theorem denseRange_schwartzC0 (d : ℕ) :
    DenseRange (schwartzC0 : SchwartzMap (E d) ℂ → C₀(E d, ℂ)) := by
  intro f
  apply Metric.mem_closure_iff.mpr
  intro ε hε
  obtain ⟨g, hcp, hg⟩ := exists_compact_schwartz_approx f ε hε
  exact ⟨schwartzC0 g, ⟨g, rfl⟩, by rw [dist_comm, dist_eq_norm]; exact hg⟩

#print axioms exists_compact_schwartz_approx
#print axioms denseRange_schwartzC0

end C0SmoothDensity
end Bandlimited
end
