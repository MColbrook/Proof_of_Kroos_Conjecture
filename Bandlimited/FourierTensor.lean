module

public import Bandlimited.FourierTransport
public import Bandlimited.TensorDensity
public import Mathlib.MeasureTheory.Integral.Pi
public import Mathlib.MeasureTheory.Integral.Prod

/-!
# Tensor products in the inverse-Fourier class

The proof uses the canonical Euclidean Lebesgue measure and exact manuscript
normalization. Each one-dimensional bandwidth is delta; the resulting
Euclidean bandwidth is bounded by r*delta. Dimension zero is handled by the
constant-function convention.
-/

@[expose] public section
noncomputable section
open MeasureTheory Set
open scoped BigOperators Topology

namespace Bandlimited
namespace FourierTensor
open TensorDensity

def lineIsometry : ℝ ≃ₗᵢ[ℝ] E 1 where
  toFun := scalarLine
  invFun := fun x => x 0
  left_inv := fun t => scalarLine_apply t 0
  right_inv := scalarLine_coord
  map_add' := by
    intro a b
    ext i
    simp only [scalarLine_apply, PiLp.add_apply]
  map_smul' := by
    intro c a
    ext i
    simp only [scalarLine_apply, PiLp.smul_apply, smul_eq_mul, RingHom.id_apply]
  norm_map' := by
    intro t
    change ‖scalarLine t‖ = ‖t‖
    simpa only [Real.norm_eq_abs] using norm_scalarLine t

 theorem lineIsometry_apply (t : ℝ) : lineIsometry t = scalarLine t := rfl

 theorem scalarLine_contDiff :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) scalarLine :=
  by
    have hcoe : (lineIsometry : ℝ → E 1) = scalarLine := funext lineIsometry_apply
    rw [← hcoe]
    exact lineIsometry.toContinuousLinearEquiv.contDiff

 theorem coordinate_contDiff {r : ℕ} (i : Fin r) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun x : E r => x i) := by
  exact ((PiLp.proj 2 (fun _ : Fin r => ℝ) i) : E r →L[ℝ] ℝ).contDiff

 theorem inverseFourier_scalar (φ : E 1 → ℂ) (t : ℝ) :
    inverseFourier φ (scalarLine t) = ((2 * Real.pi : ℝ)⁻¹ : ℂ) *
      ∫ ξ : ℝ, φ (scalarLine ξ) * Complex.exp (Complex.I * (↑(t * ξ) : ℂ)) := by
  unfold inverseFourier
  simp only [pow_one]
  congr 1
  symm
  convert lineIsometry.measurePreserving.integral_comp
    lineIsometry.toHomeomorph.toMeasurableEquiv.measurableEmbedding
    (fun ξ : E 1 => φ ξ * Complex.exp
    (Complex.I * ((∑ i : Fin 1, scalarLine t i * ξ i : ℝ) : ℂ))) using 1
  simp only [lineIsometry_apply, scalarLine_apply, Fin.sum_univ_one]

 def productFrequency {r : ℕ} (φ : Fin r → E 1 → ℂ) (ξ : E r) : ℂ :=
  ∏ i, φ i (scalarLine (ξ i))

 theorem productFrequency_contDiff {r : ℕ} (φ : Fin r → E 1 → ℂ)
    (hφ : ∀ i, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (φ i)) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (productFrequency φ) := by
  apply contDiff_prod
  intro i hi
  exact (hφ i).comp (scalarLine_contDiff.comp (coordinate_contDiff i))

 theorem productFrequency_tsupport {r : ℕ} (φ : Fin r → E 1 → ℂ)
    (i : Fin r) :
    tsupport (productFrequency φ) ⊆
      (fun ξ : E r => scalarLine (ξ i)) ⁻¹' tsupport (φ i) := by
  apply closure_minimal
  · intro ξ hξ
    have hne : φ i (scalarLine (ξ i)) ≠ 0 :=
      Finset.prod_ne_zero_iff.mp hξ i (Finset.mem_univ i)
    exact subset_closure hne
  · exact (isClosed_tsupport (φ i)).preimage
      (continuous_scalarLine.comp (coordinate_contDiff i).continuous)

 theorem productFrequency_smooth {r : ℕ} (hr : 0 < r) {δ : ℝ}
    (φ : Fin r → E 1 → ℂ) (hφ : ∀ i, SmoothFrequency δ (φ i)) :
    SmoothFrequency ((r : ℝ) * δ) (productFrequency φ) := by
  have hcoords (ξ : E r) (hξ : ξ ∈ tsupport (productFrequency φ)) (i : Fin r) :
      |ξ i| < δ := by
    have h := (hφ i).2.2 (productFrequency_tsupport φ i hξ)
    simpa only [Metric.mem_ball, dist_zero_right, norm_scalarLine] using h
  have hball : tsupport (productFrequency φ) ⊆ Metric.ball 0 ((r : ℝ) * δ) := by
    intro ξ hξ
    simp only [Metric.mem_ball, dist_zero_right]
    apply lt_of_le_of_lt (norm_le_sum_abs ξ)
    calc
      (∑ i : Fin r, |ξ i|) < ∑ _i : Fin r, δ :=
        Finset.sum_lt_sum_of_nonempty (Finset.univ_nonempty_iff.mpr
          (by exact ⟨⟨0, hr⟩⟩)) (fun i _ => hcoords ξ hξ i)
      _ = (r : ℝ) * δ := by simp
  refine ⟨productFrequency_contDiff φ (fun i => (hφ i).1), ?_, hball⟩
  exact (isCompact_closedBall (0 : E r) ((r : ℝ) * δ)).of_isClosed_subset
    (isClosed_tsupport _) (hball.trans Metric.ball_subset_closedBall)

 theorem inverseFourier_productFrequency {r : ℕ} (φ : Fin r → E 1 → ℂ)
    (x : E r) :
    inverseFourier (productFrequency φ) x =
      ∏ i : Fin r, inverseFourier (φ i) (scalarLine (x i)) := by
  have hphase (ξ : E r) :
      productFrequency φ ξ * Complex.exp
        (Complex.I * ((∑ i : Fin r, x i * ξ i : ℝ) : ℂ)) =
      ∏ i : Fin r, φ i (scalarLine (ξ i)) *
        Complex.exp (Complex.I * (↑(x i * ξ i) : ℂ)) := by
    simp only [productFrequency, Complex.ofReal_sum, Finset.mul_sum,
      Complex.exp_sum, Finset.prod_mul_distrib]
  have hint : (∫ ξ : E r, productFrequency φ ξ * Complex.exp
      (Complex.I * ((∑ i : Fin r, x i * ξ i : ℝ) : ℂ))) =
      ∏ i : Fin r, ∫ t : ℝ, φ i (scalarLine t) *
        Complex.exp (Complex.I * (↑(x i * t) : ℂ)) := by
    simp_rw [hphase]
    rw [← MeasurePreserving.integral_comp
      (PiLp.volume_preserving_toLp (Fin r))
      (MeasurableEquiv.toLp 2 (Fin r → ℝ)).measurableEmbedding]
    exact integral_fintype_prod_volume_eq_prod (E := fun _ : Fin r => ℝ)
      (fun i t => φ i (scalarLine t) *
        Complex.exp (Complex.I * (↑(x i * t) : ℂ)))
  change ((((2 * Real.pi) ^ r : ℝ)⁻¹ : ℂ) *
      ∫ ξ : E r, productFrequency φ ξ * Complex.exp
        (Complex.I * ((∑ i : Fin r, x i * ξ i : ℝ) : ℂ))) = _
  rw [hint]
  simp_rw [inverseFourier_scalar]
  rw [Finset.prod_mul_distrib]
  simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin,
    Complex.ofReal_pow, inv_pow]

end FourierTensor

 theorem InBandlimitedSpace.tensor_product {r : ℕ} {δ : ℝ}
    (F : Fin r → E 1 → ℂ) (hF : ∀ i, InBandlimitedSpace 1 δ (F i)) :
    InBandlimitedSpace r ((r : ℝ) * δ)
      (fun x => ∏ i : Fin r, F i (TensorDensity.scalarLine (x i))) := by
  classical
  by_cases hr : r = 0
  · simp only [InBandlimitedSpace, hr, ↓reduceIte]
    exact ⟨1, fun x => by simp [hr]⟩
  · have hphi (i : Fin r) :
        ∃ φ : E 1 → ℂ, SmoothFrequency δ φ ∧ F i = inverseFourier φ := by
      simpa only [InBandlimitedSpace, Nat.one_ne_zero, ↓reduceIte] using hF i
    choose φ hφ hFφ using hphi
    simp only [InBandlimitedSpace, hr, ↓reduceIte]
    refine ⟨FourierTensor.productFrequency φ,
      FourierTensor.productFrequency_smooth (Nat.pos_of_ne_zero hr) φ hφ, ?_⟩
    funext x
    rw [FourierTensor.inverseFourier_productFrequency]
    apply Finset.prod_congr rfl
    intro i hi
    rw [hFφ i]

#print axioms InBandlimitedSpace.tensor_product
#print axioms FourierTensor.inverseFourier_productFrequency

end Bandlimited
