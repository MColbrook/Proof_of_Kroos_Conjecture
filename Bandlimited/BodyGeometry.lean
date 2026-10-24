module

public import Bandlimited.Definitions
public import Mathlib.Analysis.Normed.Module.Ball.RadialEquiv

/-! Basic norm-ball geometry used when passing from spherical kernels to
uniform boundary approximation. Only the BodyNorm axioms and stated norm
bounds are used. -/

@[expose] public section
noncomputable section
open Set
namespace Bandlimited

@[simp] theorem BodyNorm.map_zero {d : ℕ} (ν : BodyNorm d) : ν.toFun 0 = 0 :=
  (ν.zero_iff 0).2 rfl

@[simp] theorem BodyNorm.map_neg {d : ℕ} (ν : BodyNorm d) (x : E d) :
    ν.toFun (-x) = ν.toFun x := by
  simpa only [neg_one_smul, abs_neg, abs_one, one_mul] using ν.smul (-1) x

theorem BodyNorm.abs_sub_le {d : ℕ} (ν : BodyNorm d) (x y : E d) :
    |ν.toFun x - ν.toFun y| ≤ ν.toFun (x - y) := by
  have hxy := ν.add_le (x - y) y
  have hyx := ν.add_le (y - x) x
  have hneg : ν.toFun (y - x) = ν.toFun (x - y) := by
    rw [← neg_sub x y, ν.map_neg]
  rw [sub_add_cancel] at hxy hyx
  rw [hneg] at hyx
  exact abs_le.mpr ⟨by linarith, by linarith⟩

theorem BodyNorm.continuous_of_bounds {d : ℕ} (ν : BodyNorm d)
    {α β : ℝ} (hβ : 0 ≤ β) (hν : NormBounds α β ν) : Continuous ν.toFun := by
  have hLip : LipschitzWith ⟨β, hβ⟩ ν.toFun := by
    apply LipschitzWith.of_dist_le_mul
    intro x y
    rw [dist_eq_norm, dist_eq_norm, Real.norm_eq_abs]
    change |ν.toFun x - ν.toFun y| ≤ β * ‖x - y‖
    exact (ν.abs_sub_le x y).trans (hν (x - y)).2
  exact hLip.continuous

theorem BodyNorm.frontier_value {d : ℕ} (ν : BodyNorm d)
    {α β : ℝ} (hβ : 0 ≤ β) (hν : NormBounds α β ν)
    {x : E d} (hx : x ∈ frontier (normBall ν)) : ν.toFun x = 1 := by
  have hc := ν.continuous_of_bounds hβ hν
  have hcl : IsClosed (normBall ν) := isClosed_le hc continuous_const
  have hxcl : x ∈ closure (normBall ν) := frontier_subset_closure hx
  have hxle : ν.toFun x ≤ 1 := by
    have := hcl.closure_eq ▸ hxcl
    exact this
  by_contra hne
  have hxlt : ν.toFun x < 1 := lt_of_le_of_ne hxle hne
  have hopen : IsOpen {x | ν.toFun x < 1} := isOpen_lt hc continuous_const
  have hxint : x ∈ interior (normBall ν) :=
    mem_interior.mpr ⟨{x | ν.toFun x < 1},
      (fun y hy => show ν.toFun y ≤ 1 from hy.le), hopen, hxlt⟩
  exact hx.2 hxint

theorem BodyNorm.frontier_ne_zero {d : ℕ} (ν : BodyNorm d)
    {α β : ℝ} (hβ : 0 ≤ β) (hν : NormBounds α β ν)
    {x : E d} (hx : x ∈ frontier (normBall ν)) : x ≠ 0 := by
  intro hx0
  have hval := ν.frontier_value hβ hν hx
  rw [hx0, ν.map_zero] at hval
  norm_num at hval

theorem BodyNorm.radial_surjective_frontier {d : ℕ} (ν : BodyNorm d)
    {α β : ℝ} (hβ : 0 ≤ β) (hν : NormBounds α β ν)
    (x : ↥(frontier (normBall ν))) :
    ∃ u : Sphere d, radial ν u = (x : E d) := by
  have hx0 : (x : E d) ≠ 0 := ν.frontier_ne_zero hβ hν x.property
  have hn0 : ‖(x : E d)‖ ≠ 0 := norm_ne_zero_iff.mpr hx0
  have hnorm : ‖‖(x : E d)‖⁻¹ • (x : E d)‖ = 1 := by
    rw [norm_smul, Real.norm_eq_abs,
      abs_of_nonneg (inv_nonneg.mpr (norm_nonneg _)), inv_mul_cancel₀ hn0]
  let u : Sphere d := ⟨‖(x : E d)‖⁻¹ • (x : E d), by
    simpa only [Metric.mem_sphere, dist_zero_right] using hnorm⟩
  have hnu : ν.toFun (u : E d) = ‖(x : E d)‖⁻¹ := by
    change ν.toFun (‖(x : E d)‖⁻¹ • (x : E d)) = _
    rw [ν.smul, abs_of_nonneg (inv_nonneg.mpr (norm_nonneg _)),
      ν.frontier_value hβ hν x.property, mul_one]
  refine ⟨u, ?_⟩
  simp only [radial, hnu, inv_inv]
  change ‖(x : E d)‖ • (‖(x : E d)‖⁻¹ • (x : E d)) = _
  rw [smul_smul, mul_inv_cancel₀ hn0, one_smul]

theorem boundary_error_of_radial {d : ℕ} (ν : BodyNorm d)
    {α β : ℝ} (hβ : 0 ≤ β) (hν : NormBounds α β ν)
    (p : Polynomial d) (ε : ℝ)
    (h : ∃ b : ℝ, b < ε ∧ ∀ u : Sphere d,
      |evalPolynomial p (radial ν u) - 1| ≤ b) :
    BoundaryErrorLT (normBall ν) p (fun _ => 1) ε := by
  obtain ⟨b, hb, hbound⟩ := h
  refine ⟨b, hb, ?_⟩
  intro x
  obtain ⟨u, hu⟩ := ν.radial_surjective_frontier hβ hν x
  simpa only [hu] using hbound u

#print axioms BodyNorm.frontier_ne_zero
#print axioms BodyNorm.radial_surjective_frontier
#print axioms boundary_error_of_radial

def unitOne : E 1 := PiLp.single 2 0 1

theorem BodyNorm.one_dimensional_formula (ν : BodyNorm 1) (x : E 1) :
    ν.toFun x = |x 0| * ν.toFun unitOne := by
  have hx : x = (x 0) • unitOne := by
    ext i
    fin_cases i
    simp [unitOne]
  conv_lhs => rw [hx]
  exact ν.smul (x 0) unitOne

def oneDimensionalPolynomial (ν : BodyNorm 1) (n : ℕ) : Polynomial 1 :=
  (MvPolynomial.C (ν.toFun unitOne) * MvPolynomial.X 0) ^ (2 * n)

theorem oneDimensionalPolynomial_homogeneous (ν : BodyNorm 1) (n : ℕ) :
    (oneDimensionalPolynomial ν n).IsHomogeneous (2 * n) := by
  simpa only [oneDimensionalPolynomial, one_mul] using
    (MvPolynomial.isHomogeneous_C_mul_X (ν.toFun unitOne) (0 : Fin 1)).pow (2 * n)

theorem oneDimensionalPolynomial_exact (ν : BodyNorm 1) (n : ℕ) (x : E 1)
    (hx : ν.toFun x = 1) : evalPolynomial (oneDimensionalPolynomial ν n) x = 1 := by
  have hnorm : |ν.toFun unitOne * x 0| = 1 := by
    rw [abs_mul, abs_of_nonneg (ν.nonneg unitOne), mul_comm]
    rw [← ν.one_dimensional_formula x, hx]
  have hsq : (ν.toFun unitOne * x 0) ^ 2 = 1 := by
    rw [← sq_abs, hnorm]
    norm_num
  simp only [oneDimensionalPolynomial, evalPolynomial, map_pow, map_mul,
    MvPolynomial.eval_C, MvPolynomial.eval_X, pow_mul, hsq, one_pow]

theorem zero_dimensional_boundary_empty (ν : BodyNorm 0) :
    frontier (normBall ν) = ∅ := by
  have hball : normBall ν = univ := by
    ext x
    have hx : x = 0 := Subsingleton.elim _ _
    simp [normBall, hx]
  rw [hball, frontier_univ]

#print axioms BodyNorm.one_dimensional_formula
#print axioms oneDimensionalPolynomial_homogeneous
#print axioms oneDimensionalPolynomial_exact
#print axioms zero_dimensional_boundary_empty

#print axioms BodyNorm.abs_sub_le
#print axioms BodyNorm.continuous_of_bounds
#print axioms BodyNorm.frontier_value

end Bandlimited
end
