module

public import Bandlimited.MainReductions
public import Mathlib.Analysis.Convex.Gauge

/-! A symmetric convex body is the unit ball of an actual norm. Mathlib's
Minkowski functional supplies all gauge laws; compactness and an interior
ball give positive lower and upper Euclidean norm bounds. -/

@[expose] public section
noncomputable section
open Set
namespace Bandlimited

theorem symmetric_body_zero_interior {d : ℕ} {K : Set (E d)}
    (hK : IsSymmetricConvexBody K) : (0 : E d) ∈ interior K := by
  obtain ⟨x, hx⟩ := hK.2.2.1
  let e : E d ≃ₜ E d := {
    toFun := fun x => -x
    invFun := fun x => -x
    left_inv := neg_neg
    right_inv := neg_neg
    continuous_toFun := continuous_neg
    continuous_invFun := continuous_neg }
  have himage : e '' K = K := by
    ext y
    constructor
    · rintro ⟨z, hz, rfl⟩
      exact (hK.2.2.2 z).1 hz
    · intro hy
      exact ⟨-y, (hK.2.2.2 y).1 hy, neg_neg y⟩
  have hi := e.image_interior K
  rw [himage] at hi
  have hnx : -x ∈ interior K := by
    rw [← hi]
    exact ⟨x, hx, rfl⟩
  have hz := hK.2.1.interior hx hnx (a := (1 / 2 : ℝ)) (b := (1 / 2 : ℝ))
    (by norm_num) (by norm_num) (by norm_num)
  simpa only [smul_neg, add_neg_cancel] using hz

theorem symmetric_body_gauge_smul {d : ℕ} {K : Set (E d)}
    (hK : IsSymmetricConvexBody K) (a : ℝ) (x : E d) :
    gauge K (a • x) = |a| * gauge K x := by
  have hsym : ∀ x ∈ K, -x ∈ K := fun x hx => (hK.2.2.2 x).1 hx
  by_cases ha : 0 ≤ a
  · simpa only [smul_eq_mul, abs_of_nonneg ha] using gauge_smul_of_nonneg ha x
  · have han : 0 ≤ -a := by linarith
    calc
      gauge K (a • x) = gauge K (-((-a) • x)) := by simp
      _ = gauge K ((-a) • x) := gauge_neg hsym _
      _ = (-a) * gauge K x := by
        simpa only [smul_eq_mul] using gauge_smul_of_nonneg han x
      _ = |a| * gauge K x := by rw [abs_of_nonpos (by linarith : a ≤ 0)]

theorem symmetric_body_as_norm_ball {d : ℕ} {K : Set (E d)}
    (hK : IsSymmetricConvexBody K) :
    ∃ ν : BodyNorm d, ∃ α β : ℝ, 0 < α ∧ α ≤ β ∧
      NormBounds α β ν ∧ normBall ν = K := by
  have hnhds : K ∈ nhds (0 : E d) :=
    mem_interior_iff_mem_nhds.mp (symmetric_body_zero_interior hK)
  have habs : Absorbent ℝ K := absorbent_nhds_zero hnhds
  have hvon : Bornology.IsVonNBounded ℝ K := hK.1.isVonNBounded ℝ
  let ν : BodyNorm d := {
    toFun := gauge K
    nonneg := gauge_nonneg
    zero_iff := fun x => gauge_eq_zero habs hvon
    smul := symmetric_body_gauge_smul hK
    add_le := gauge_add_le hK.2.1 habs }
  obtain ⟨R, hR, houter⟩ := hK.1.isBounded.subset_closedBall_lt 0 (0 : E d)
  obtain ⟨r, hr, hinner⟩ := Metric.mem_nhds_iff.mp hnhds
  refine ⟨ν, R⁻¹, max R⁻¹ r⁻¹, inv_pos.mpr hR, le_max_left _ _, ?_, ?_⟩
  · intro x
    constructor
    · change R⁻¹ * ‖x‖ ≤ gauge K x
      simpa only [div_eq_inv_mul] using le_gauge_of_subset_closedBall habs hR.le houter (x := x)
    · change gauge K x ≤ max R⁻¹ r⁻¹ * ‖x‖
      calc
        gauge K x ≤ ‖x‖ / r := (le_div_iff₀ hr).2 (by
          simpa only [mul_comm] using mul_gauge_le_norm (x := x) hinner)
        _ = r⁻¹ * ‖x‖ := div_eq_inv_mul _ _
        _ ≤ max R⁻¹ r⁻¹ * ‖x‖ := mul_le_mul_of_nonneg_right (le_max_right _ _) (norm_nonneg _)
  · ext x
    change gauge K x ≤ 1 ↔ x ∈ K
    rw [gauge_le_one_iff_mem_closure hK.2.1 hnhds, hK.1.isClosed.closure_eq]

theorem constant_sequence_of_bounded_norm_uniform
    (h : BoundedNormUniformStatement) : ConstantSequenceStatement := by
  intro d K hK
  obtain ⟨ν, α, β, hα, hαβ, hν, hball⟩ := symmetric_body_as_norm_ball hK
  apply sequence_of_eventual_constant_approximation K
  intro ε hε
  obtain ⟨n₀, hn₀⟩ := h d α β hα hαβ ε hε
  refine ⟨n₀, ?_⟩
  intro n hn
  obtain ⟨p, hp, herr⟩ := hn₀ n hn ν hν
  exact ⟨p, hp, hball ▸ herr⟩

#print axioms symmetric_body_zero_interior
#print axioms symmetric_body_gauge_smul
#print axioms symmetric_body_as_norm_ball
#print axioms constant_sequence_of_bounded_norm_uniform

end Bandlimited
end
