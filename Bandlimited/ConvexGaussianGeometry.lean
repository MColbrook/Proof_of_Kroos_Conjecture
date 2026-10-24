module

public import Bandlimited.ConvexWeightedGaussian
public import Mathlib.Analysis.InnerProductSpace.ProdL2
public import Mathlib.Topology.Algebra.Module.Equiv.Prod

/- Orthogonal splitting of the active subspace and its complement. -/
@[expose] public section
noncomputable section
open Set
open scoped BigOperators RealInnerProductSpace
namespace Bandlimited
namespace ConvexGaussian

set_option maxHeartbeats 50000

def complementCoordinates {d : ℕ} (S : Submodule ℝ (E d)) :
    Sᗮ ≃ₗᵢ[ℝ] E (Module.finrank ℝ Sᗮ) :=
  (stdOrthonormalBasis ℝ Sᗮ).repr

#check complementCoordinates

def activeProjection {d r : ℕ} (S : Submodule ℝ (E d)) (T : S ≃L[ℝ] E r) :
    E d →L[ℝ] E r := T.toContinuousLinearMap.comp S.orthogonalProjectionOnto

#check activeProjection

def complementProjection {d : ℕ} (S : Submodule ℝ (E d)) :
    E d →L[ℝ] E (Module.finrank ℝ Sᗮ) :=
  (complementCoordinates S).toContinuousLinearMap.comp Sᗮ.orthogonalProjectionOnto

#check complementProjection

def activeComplementEquiv {d r : ℕ} (S : Submodule ℝ (E d)) (T : S ≃L[ℝ] E r) :
    E d ≃L[ℝ] E r × E (Module.finrank ℝ Sᗮ) :=
  ((S.orthogonalDecomposition.toContinuousLinearEquiv).trans
    (WithLp.prodContinuousLinearEquiv 2 ℝ S Sᗮ)).trans
      (T.prodCongr (complementCoordinates S).toContinuousLinearEquiv)

#check activeComplementEquiv

theorem activeComplementEquiv_apply {d r : ℕ} (S : Submodule ℝ (E d))
    (T : S ≃L[ℝ] E r) (x : E d) :
    activeComplementEquiv S T x = (activeProjection S T x, complementProjection S x) := by
  change (T (WithLp.ofLp (S.orthogonalDecomposition x)).1,
      (complementCoordinates S) (WithLp.ofLp (S.orthogonalDecomposition x)).2) =
    (T (S.orthogonalProjectionOnto x),
      (complementCoordinates S) (Sᗮ.orthogonalProjectionOnto x))
  rw [Submodule.orthogonalDecomposition_apply]

#check activeComplementEquiv_apply

theorem active_complement_bijective {d r : ℕ} (S : Submodule ℝ (E d))
    (T : S ≃L[ℝ] E r) :
    Function.Bijective (fun x : E d => (activeProjection S T x, complementProjection S x)) := by
  simpa only [← activeComplementEquiv_apply S T] using (activeComplementEquiv S T).bijective

#check active_complement_bijective

@[simp] theorem norm_complementProjection {d : ℕ} (S : Submodule ℝ (E d)) (x : E d) :
    ‖complementProjection S x‖ = ‖Sᗮ.orthogonalProjectionOnto x‖ :=
  (complementCoordinates S).norm_map _

#check norm_complementProjection

theorem complementProjection_norm_le {d : ℕ} (S : Submodule ℝ (E d)) :
    ‖complementProjection S‖ ≤ 1 := by
  refine (complementProjection S).opNorm_le_bound zero_le_one ?_
  intro x
  change ‖complementProjection S x‖ ≤ 1 * ‖x‖
  rw [norm_complementProjection, one_mul]
  exact Sᗮ.norm_orthogonalProjectionOnto_apply_le x

#check complementProjection_norm_le

theorem active_complement_dimensions {d : ℕ} (S : Submodule ℝ (E d)) :
    Module.finrank ℝ S + Module.finrank ℝ Sᗮ = d := by
  simpa only [E, finrank_euclideanSpace_fin] using S.finrank_add_finrank_orthogonal

#check active_complement_dimensions

theorem active_profile_projection {d : ℕ} {f : E d → ℝ}
    (hf : IsConvexProfile f) (x : E d) :
    f x = f ((activeSubspace f).orthogonalProjectionOnto x) := by
  have h := profile_constant_on_orthogonal_fibres hf
    ((activeSubspace f).orthogonalProjectionOnto x)
    ((activeSubspace f)ᗮ.orthogonalProjectionOnto x)
    (((activeSubspace f)ᗮ.orthogonalProjectionOnto x).property)
  simpa only [← Submodule.starProjection_apply,
    Submodule.starProjection_add_starProjection_orthogonal] using h

#check active_profile_projection

theorem gaussian_orthogonal_factorization {d : ℕ} (S : Submodule ℝ (E d))
    (A : ℝ) (x : E d) :
    gaussian A x = gaussian A ((S.orthogonalProjectionOnto x : S) : E d) *
      gaussian A (complementProjection S x) := by
  unfold gaussian
  simp only [Submodule.norm_coe]
  rw [norm_complementProjection, ← Real.exp_add, S.norm_sq_eq_add_norm_sq_projection x]
  congr 1
  ring

#check gaussian_orthogonal_factorization

theorem gaussianWeight_orthogonal_bound {d : ℕ} (S : Submodule ℝ (E d))
    (A L : ℝ) (hA : 0 < A) (hL : 0 ≤ L) (x : E d) :
    gaussianWeight A L x ≤
      gaussianWeight A L ((S.orthogonalProjectionOnto x : S) : E d) *
        gaussianWeight A L (complementProjection S x) := by
  have hnorm : ‖x‖ ≤ ‖S.orthogonalProjectionOnto x‖ + ‖Sᗮ.orthogonalProjectionOnto x‖ := by
    conv_lhs => rw [← S.starProjection_add_starProjection_orthogonal x]
    exact norm_add_le _ _
  have hlin : 1 + ‖x‖ / A ≤
      (1 + ‖S.orthogonalProjectionOnto x‖ / A) *
        (1 + ‖Sᗮ.orthogonalProjectionOnto x‖ / A) := by
    have hdiv := (div_le_div_of_nonneg_right hnorm hA.le)
    have hcross := mul_nonneg (div_nonneg (norm_nonneg (S.orthogonalProjectionOnto x)) hA.le)
      (div_nonneg (norm_nonneg (Sᗮ.orthogonalProjectionOnto x)) hA.le)
    rw [add_div] at hdiv
    nlinarith
  unfold gaussianWeight
  rw [norm_complementProjection, ← Real.mul_rpow (by positivity) (by positivity)]
  exact Real.rpow_le_rpow (by positivity) hlin hL

#print axioms active_complement_bijective
#print axioms active_profile_projection
#print axioms gaussian_orthogonal_factorization
end ConvexGaussian
end Bandlimited
end
