module

public import Bandlimited.BodyGauge
public import Mathlib.Topology.Instances.Matrix
public import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv
public import Mathlib.LinearAlgebra.Matrix.Adjugate

/-! Maximal determinant frames for the uniform linear normalization of a
symmetric convex body. This is the determinant argument in the final section
of the manuscript, rather than an unproved ellipsoid theorem. -/

@[expose] public section
noncomputable section
open Set
open scoped BigOperators
namespace Bandlimited

def frameMatrix {d : ℕ} (v : Fin d → E d) : Matrix (Fin d) (Fin d) ℝ :=
  fun i j => v j i

theorem maximal_frame_exists {d : ℕ} {K : Set (E d)}
    (hK : IsSymmetricConvexBody K) :
    ∃ v : Fin d → E d, (∀ j, v j ∈ K) ∧ (frameMatrix v).det ≠ 0 ∧
      ∀ w : Fin d → E d, (∀ j, w j ∈ K) →
        |(frameMatrix w).det| ≤ |(frameMatrix v).det| := by
  classical
  have hzero : (0 : E d) ∈ K := interior_subset (symmetric_body_zero_interior hK)
  let : CompactSpace ↥K := isCompact_iff_compactSpace.mp hK.1
  let : Nonempty ↥K := ⟨⟨0, hzero⟩⟩
  have hmat : Continuous (fun v : Fin d → ↥K =>
      frameMatrix (fun j => (v j : E d))) := by
    apply continuous_pi
    intro i
    apply continuous_pi
    intro j
    exact (EuclideanSpace.proj i).continuous.comp
      (continuous_subtype_val.comp (continuous_apply j))
  have hdet : Continuous (fun v : Fin d → ↥K =>
      |(frameMatrix (fun j => (v j : E d))).det|) := hmat.matrix_det.abs
  obtain ⟨v, hv, hmax⟩ := isCompact_univ.exists_isMaxOn Set.univ_nonempty hdet.continuousOn
  let v' : Fin d → E d := fun j => (v j : E d)
  have hvK (j : Fin d) : v' j ∈ K := (v j).property
  have hmax' (w : Fin d → E d) (hw : ∀ j, w j ∈ K) :
      |(frameMatrix w).det| ≤ |(frameMatrix v').det| :=
    hmax (show (fun j => (⟨w j, hw j⟩ : ↥K)) ∈ Set.univ from Set.mem_univ _)
  have hnhds : K ∈ nhds (0 : E d) :=
    mem_interior_iff_mem_nhds.mp (symmetric_body_zero_interior hK)
  obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.mp hnhds
  let w : Fin d → E d := fun j => PiLp.single 2 j (r / 2)
  have hw (j : Fin d) : w j ∈ K := by
    apply hball
    simp only [Metric.mem_ball, dist_zero_right, w, PiLp.norm_single,
      Real.norm_eq_abs, abs_of_pos (half_pos hr)]
    linarith
  have hdiag : frameMatrix w = Matrix.diagonal (fun _ : Fin d => r / 2) := by
    ext i j
    simp only [frameMatrix, w, PiLp.single_apply, Matrix.diagonal_apply]
  have hwd : (frameMatrix w).det ≠ 0 := by
    rw [hdiag, Matrix.det_diagonal]
    simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
    exact pow_ne_zero _ (by positivity)
  have hvd : (frameMatrix v').det ≠ 0 :=
    abs_pos.mp ((abs_pos.mpr hwd).trans_le (hmax' w hw))
  exact ⟨v', hvK, hvd, hmax'⟩

theorem maximal_frame_coefficient_bound {d : ℕ} {K : Set (E d)}
    (v : Fin d → E d) (hv : ∀ j, v j ∈ K) (hvd : (frameMatrix v).det ≠ 0)
    (hmax : ∀ w : Fin d → E d, (∀ j, w j ∈ K) →
      |(frameMatrix w).det| ≤ |(frameMatrix v).det|)
    (c : Fin d → ℝ) (x : E d) (hx : x ∈ K) (hrep : x = ∑ j, c j • v j)
    (i : Fin d) : |c i| ≤ 1 := by
  classical
  let A := frameMatrix v
  let w : Fin d → E d := Function.update v i x
  have hw (j : Fin d) : w j ∈ K := by
    by_cases hj : j = i
    · simp only [w, hj, Function.update_self]
      exact hx
    · simpa only [w, Function.update_of_ne hj] using hv j
  have hupdate : frameMatrix w = A.updateCol i (fun k => x k) := by
    ext k j
    by_cases hj : j = i <;> simp [frameMatrix, w, A, Matrix.updateCol, hj]
  have hcoord : (fun k : Fin d => x k) = fun k => ∑ j : Fin d, c j * A k j := by
    funext k
    rw [hrep]
    simp only [WithLp.ofLp_sum, Finset.sum_apply, PiLp.smul_apply, smul_eq_mul, A, frameMatrix]
  have hdet : (frameMatrix w).det = c i * A.det := by
    rw [hupdate, hcoord]
    simpa only [smul_eq_mul] using Matrix.det_updateCol_sum A i c
  have hbound := hmax w hw
  rw [hdet, abs_mul] at hbound
  have hdpos : 0 < |A.det| := abs_pos.mpr hvd
  have hdiv : |c i| ≤ |A.det| / |A.det| := (le_div_iff₀ hdpos).2 hbound
  simpa only [div_self hdpos.ne'] using hdiv

#print axioms maximal_frame_exists
#print axioms maximal_frame_coefficient_bound

end Bandlimited
end
