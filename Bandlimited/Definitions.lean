module

public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.RingTheory.MvPolynomial.Homogeneous
public import Mathlib.Topology.ContinuousMap.Basic
public import Mathlib.Analysis.Convex.Function
public import Mathlib.Analysis.Calculus.ContDiff.Defs
public import Mathlib.Topology.Algebra.Support
public import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
public import Mathlib.MeasureTheory.Constructions.HaarToSphere
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Ring

/-!
# Mathematical definitions and principal statements

The concrete polynomial, Fourier and weighted spaces used throughout the proof.
These proposition-valued definitions are proved in the subsequent modules.
The independently elaborated statement of record is the root `Challenge.lean`.
See `docs/SOURCE.md` and `docs/CLAIM_INVENTORY.md` for source provenance.
-/

@[expose] public section

open scoped BigOperators
open MeasureTheory Set

noncomputable section

namespace Bandlimited

abbrev E (d : ℕ) := EuclideanSpace ℝ (Fin d)
abbrev Polynomial (d : ℕ) := MvPolynomial (Fin d) ℝ
abbrev Sphere (d : ℕ) := ↥(Metric.sphere (0 : E d) 1)

def evalPolynomial {d : ℕ} (p : Polynomial d) (x : E d) : ℝ :=
  MvPolynomial.eval (fun i => x i) p

/- A norm consists only of the usual norm assumptions; it contains no
approximation, compactness, or Fourier conclusion. -/
structure BodyNorm (d : ℕ) where
  toFun : E d → ℝ
  nonneg : ∀ x, 0 ≤ toFun x
  zero_iff : ∀ x, toFun x = 0 ↔ x = 0
  smul : ∀ (a : ℝ) x, toFun (a • x) = |a| * toFun x
  add_le : ∀ x y, toFun (x + y) ≤ toFun x + toFun y

def normBall {d : ℕ} (ν : BodyNorm d) : Set (E d) := {x | ν.toFun x ≤ 1}

def radial {d : ℕ} (ν : BodyNorm d) (u : Sphere d) : E d :=
  (ν.toFun (u : E d))⁻¹ • (u : E d)

def NormBounds {d : ℕ} (α β : ℝ) (ν : BodyNorm d) : Prop :=
  ∀ x, α * ‖x‖ ≤ ν.toFun x ∧ ν.toFun x ≤ β * ‖x‖

def IsSymmetricConvexBody {d : ℕ} (K : Set (E d)) : Prop :=
  IsCompact K ∧ Convex ℝ K ∧ (interior K).Nonempty ∧
    ∀ x, x ∈ K ↔ -x ∈ K

def rho {d : ℕ} (u v : Sphere d) : ℝ :=
  min ‖(u : E d) - (v : E d)‖ ‖(u : E d) + (v : E d)‖

/- A common strict upper bound expresses `sup error < ε`, rather than merely
pointwise strict inequalities on a possibly noncompact domain. -/
def BoundaryErrorLT {d : ℕ} (K : Set (E d)) (p : Polynomial d)
    (f : ↥(frontier K) → ℝ) (ε : ℝ) : Prop :=
  ∃ b : ℝ, b < ε ∧ ∀ x : ↥(frontier K),
    |evalPolynomial p (x : E d) - f x| ≤ b

def EvenOnBoundary {d : ℕ} {K : Set (E d)}
    (f : ↥(frontier K) → ℝ) : Prop :=
  ∀ x y : ↥(frontier K), (y : E d) = -(x : E d) → f y = f x

def OddOnBoundary {d : ℕ} {K : Set (E d)}
    (f : ↥(frontier K) → ℝ) : Prop :=
  ∀ x y : ↥(frontier K), (y : E d) = -(x : E d) → f y = -f x

/- T01: an actual sequence at every even degree, for every body. -/
def ConstantSequenceStatement : Prop :=
  ∀ (d : ℕ) (K : Set (E d)), IsSymmetricConvexBody K →
    ∃ h : ℕ → Polynomial d,
      (∀ n, (h n).IsHomogeneous (2 * n)) ∧
      ∀ ε : ℝ, 0 < ε → ∃ n₀ : ℕ, ∀ n, n₀ ≤ n →
        BoundaryErrorLT K (h n) (fun _ => 1) ε

/- T02: the threshold precedes the norm, uniformly over its whole class. -/
def BoundedNormUniformStatement : Prop :=
  ∀ (d : ℕ) (α β : ℝ), 0 < α → α ≤ β →
    ∀ ε : ℝ, 0 < ε → ∃ n₀ : ℕ, ∀ n, n₀ ≤ n →
      ∀ ν : BodyNorm d, NormBounds α β ν →
        ∃ p : Polynomial d, p.IsHomogeneous (2 * n) ∧
          BoundaryErrorLT (normBall ν) p (fun _ => 1) ε

/- T03: all sufficiently large consecutive pairs, including both parities. -/
def ConsecutiveDegreesStatement : Prop :=
  ∀ (d : ℕ) (K : Set (E d)), IsSymmetricConvexBody K →
    ∀ f : C(↥(frontier K), ℝ), ∀ ε : ℝ, 0 < ε →
      ∃ n₀ : ℕ, ∀ n, n₀ ≤ n →
        ∃ p q : Polynomial d, p.IsHomogeneous n ∧
          q.IsHomogeneous (n + 1) ∧ BoundaryErrorLT K (p + q) f ε

/- T04 and T05: no restriction to a subsequence of the allowed parity. -/
def EvenFunctionsStatement : Prop :=
  ∀ (d : ℕ) (K : Set (E d)), IsSymmetricConvexBody K →
    ∀ f : C(↥(frontier K), ℝ), EvenOnBoundary f →
      ∀ ε : ℝ, 0 < ε → ∃ n₀ : ℕ, ∀ n, n₀ ≤ n →
        ∃ p : Polynomial d, p.IsHomogeneous (2 * n) ∧ BoundaryErrorLT K p f ε

def OddFunctionsStatement : Prop :=
  ∀ (d : ℕ) (K : Set (E d)), IsSymmetricConvexBody K →
    ∀ f : C(↥(frontier K), ℝ), OddOnBoundary f →
      ∀ ε : ℝ, 0 < ε → ∃ n₀ : ℕ, ∀ n, n₀ ≤ n →
        ∃ p : Polynomial d, p.IsHomogeneous (2 * n + 1) ∧
          BoundaryErrorLT K p f ε

/- T06: no norm-equivalence bounds are assumed, and K follows the threshold. -/
def AllBodiesUniformStatement : Prop :=
  ∀ d : ℕ, ∀ ε : ℝ, 0 < ε → ∃ n₀ : ℕ, ∀ n, n₀ ≤ n →
    ∀ K : Set (E d), IsSymmetricConvexBody K →
      ∃ p : Polynomial d, p.IsHomogeneous (2 * n) ∧
        BoundaryErrorLT K p (fun _ => 1) ε

def AngularKernelErrorLT {d : ℕ} (ν : BodyNorm d) (v : Sphere d)
    (N : ℕ) (A L : ℝ) (p : Polynomial d) (ε : ℝ) : Prop :=
  ∃ b : ℝ, b < ε ∧ ∀ u : Sphere d,
    (1 + (N : ℝ) / A * rho u v) ^ L *
      |evalPolynomial p (radial ν u) -
        Real.exp (-((N : ℝ) ^ 2 / A ^ 2) * (rho u v) ^ 2)| ≤ b

/- T07: L is real, A and N₀ precede ν,v,N, and every sufficiently large
even N is covered. -/
def UniformGaussianStatement : Prop :=
  ∀ (s : ℕ), 1 ≤ s → ∀ α β L ε : ℝ,
    0 < α → α ≤ β → 0 ≤ L → 0 < ε →
      ∃ A : ℝ, 1 ≤ A ∧ ∃ N₀ : ℕ, 2 ≤ N₀ ∧
        ∀ ν : BodyNorm (s + 1), NormBounds α β ν →
          ∀ (v : Sphere (s + 1)) (N : ℕ), Even N → N₀ ≤ N →
            ∃ p : Polynomial (s + 1), p.IsHomogeneous N ∧
              AngularKernelErrorLT ν v N A L p ε

/- Fourier convention: exp(i <x,ξ>) and the exact (2π)^(-d) factor. -/
def inverseFourier {d : ℕ} (φ : E d → ℂ) (x : E d) : ℂ :=
  (((2 * Real.pi) ^ d : ℝ)⁻¹ : ℂ) *
    ∫ ξ : E d,
      φ ξ * Complex.exp (Complex.I * ((∑ i : Fin d, x i * ξ i : ℝ) : ℂ))

def SmoothFrequency {d : ℕ} (σ : ℝ) (φ : E d → ℂ) : Prop :=
  ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) φ ∧ HasCompactSupport φ ∧
    tsupport φ ⊆ Metric.ball (0 : E d) σ

/- Dimension zero is explicitly all constants on the one-point space. -/
def InBandlimitedSpace (d : ℕ) (σ : ℝ) (F : E d → ℂ) : Prop :=
  if d = 0 then ∃ c : ℂ, ∀ x, F x = c
  else ∃ φ : E d → ℂ, SmoothFrequency σ φ ∧ F = inverseFourier φ

def IsRealValued {d : ℕ} (F : E d → ℂ) : Prop := ∀ x, (F x).im = 0

def VanishesAtInfinity {d : ℕ} (F : E d → ℂ) : Prop :=
  Continuous F ∧ ∀ ε : ℝ, 0 < ε → ∃ R : ℝ, 0 ≤ R ∧
    ∀ x, R ≤ ‖x‖ → ‖F x‖ < ε

def WeightedC0 {d : ℕ} (W : E d → ℝ) (H : E d → ℂ) : Prop :=
  Continuous H ∧ VanishesAtInfinity (fun x => (W x : ℂ) * H x)

def WeightedErrorLT {d : ℕ} (W : E d → ℝ) (F H : E d → ℂ)
    (ε : ℝ) : Prop :=
  ∃ b : ℝ, b < ε ∧ ∀ x, W x * ‖F x - H x‖ ≤ b

def oneSidedWeight (c M t : ℝ) : ℝ :=
  (1 + |t|) ^ M * Real.exp (-c * max t 0)

/- T08: actual smooth compactly supported inverse Fourier transforms. -/
def OneSidedDensityStatement : Prop :=
  ∀ c M δ : ℝ, 0 < c → 0 ≤ M → 0 < δ →
    ∀ H : E 1 → ℂ,
      WeightedC0 (fun x => oneSidedWeight c M (x 0)) H →
      ∀ ε : ℝ, 0 < ε → ∃ F : E 1 → ℂ,
        InBandlimitedSpace 1 δ F ∧
          WeightedErrorLT (fun x => oneSidedWeight c M (x 0)) F H ε

/- Scalar versions make the arbitrary factors in T09 explicit. -/
def ScalarWeightedC0 (W : ℝ → ℝ) (H : ℝ → ℂ) : Prop :=
  Continuous H ∧ Continuous (fun t => (W t : ℂ) * H t) ∧
    ∀ ε : ℝ, 0 < ε → ∃ R : ℝ, 0 ≤ R ∧
      ∀ t, R ≤ |t| → ‖(W t : ℂ) * H t‖ < ε

def ScalarWeightedDense (W : ℝ → ℝ) (D : Set (ℝ → ℂ)) : Prop :=
  (∀ F ∈ D, ScalarWeightedC0 W F) ∧
    ∀ H : ℝ → ℂ, ScalarWeightedC0 W H → ∀ ε : ℝ, 0 < ε →
      ∃ F ∈ D, ∃ b : ℝ, b < ε ∧ ∀ t, W t * ‖F t - H t‖ ≤ b

/- T09: weights are arbitrary positive continuous functions. -/
def TensorDensityStatement : Prop :=
  ∀ (r : ℕ), 1 ≤ r → ∀ W : Fin r → ℝ → ℝ,
    (∀ i, Continuous (W i)) → (∀ i t, 0 < W i t) →
    ∀ D : Fin r → Set (ℝ → ℂ), (∀ i, ScalarWeightedDense (W i) (D i)) →
      ∀ H : E r → ℂ, WeightedC0 (fun x => ∏ i : Fin r, W i (x i)) H →
        ∀ ε : ℝ, 0 < ε → ∃ m : ℕ,
          ∃ F : Fin m → Fin r → ℝ → ℂ,
            (∀ j i, F j i ∈ D i) ∧
              WeightedErrorLT (fun x => ∏ i : Fin r, W i (x i))
                (fun x => ∑ j : Fin m, ∏ i : Fin r, F j i (x i)) H ε

def gaussianWeight {d : ℕ} (A L : ℝ) (x : E d) : ℝ :=
  (1 + ‖x‖ / A) ^ L

def gaussian {d : ℕ} (A : ℝ) (x : E d) : ℝ :=
  Real.exp (-‖x‖ ^ 2 / A ^ 2)

def TendsToZeroAtInfinity (e : ℝ → ℝ) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ A₀ : ℝ, ∀ A, A₀ ≤ A → |e A| < ε

/- T10 includes k=0 and common convergence across all k≤s. -/
def FourierCutoffStatement : Prop :=
  ∀ (s : ℕ) (L σ : ℝ), 0 ≤ L → 0 < σ →
    ∃ g : (k : ℕ) → ℝ → E k → ℂ,
      ∃ e : ℕ → ℝ → ℝ,
        (∀ (k : ℕ), k ≤ s → ∀ A : ℝ, 1 ≤ A →
          InBandlimitedSpace k (σ / 4) (g k A) ∧ IsRealValued (g k A) ∧
            0 ≤ e k A ∧
            e k A = sSup (Set.range (fun x : E k =>
              gaussianWeight A L x * ‖g k A x - (gaussian A x : ℂ)‖)) ∧
            ∀ x : E k,
              gaussianWeight A L x * ‖g k A x - (gaussian A x : ℂ)‖ ≤ e k A) ∧
        (∀ A : ℝ, 1 ≤ A → (∀ x : E 0, g 0 A x = 1) ∧ e 0 A = 0) ∧
        ∀ ε : ℝ, 0 < ε → ∃ A₀ : ℝ, 1 ≤ A₀ ∧
          ∀ A : ℝ, A₀ ≤ A → ∀ k : ℕ, k ≤ s → e k A < ε

def IsConvexProfile {d : ℕ} (f : E d → ℝ) : Prop :=
  ConvexOn ℝ Set.univ f ∧ (∀ x, 0 ≤ f x) ∧ f 0 = 0 ∧
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x y, |f x - f y| ≤ C * ‖x - y‖

def HasProfileLipschitzBound {d : ℕ} (C : ℝ) (f : E d → ℝ) : Prop :=
  IsConvexProfile f ∧ ∀ x y, |f x - f y| ≤ C * ‖x - y‖

/- T11: Δ is independent of f and of its Lipschitz constant. The arbitrary
positive η expresses an infimum bound without falsely requiring attainment. -/
def ConvexWeightedGaussianStatement : Prop :=
  ∀ (s : ℕ), 1 ≤ s → ∀ L σ : ℝ, 0 ≤ L → 0 < σ →
    ∃ Δ : ℝ → ℝ, TendsToZeroAtInfinity Δ ∧
      ∀ A : ℝ, 1 ≤ A → 0 ≤ Δ A ∧
        ∀ f : E s → ℝ, IsConvexProfile f → ∀ η : ℝ, 0 < η →
          ∃ F : E s → ℂ, InBandlimitedSpace s σ F ∧ IsRealValued F ∧
            ∀ x : E s,
              gaussianWeight A L x *
                ‖(Real.exp (-f x) : ℂ) * F x - (gaussian A x : ℂ)‖ ≤ Δ A + η

/- T12: one finite family, chosen before all f in the common Lipschitz class. -/
def FiniteFamilyStatement : Prop :=
  ∀ (s : ℕ), 1 ≤ s → ∀ L σ C τ : ℝ,
    0 ≤ L → 0 < σ → 0 < C → 0 < τ →
      ∃ A : ℝ, 1 ≤ A ∧ ∃ J : ℕ, 0 < J ∧
        ∃ F : Fin J → E s → ℂ,
          (∀ j, InBandlimitedSpace s σ (F j) ∧ IsRealValued (F j)) ∧
            ∀ f : E s → ℝ, HasProfileLipschitzBound C f →
              ∃ j : Fin J, ∃ b : ℝ, b < τ ∧ ∀ x : E s,
                gaussianWeight A L x *
                  ‖(Real.exp (-f x) : ℂ) * F j x - (gaussian A x : ℂ)‖ ≤ b

/- The canonical Euclidean surface measure. Mathlib defines `toSphere` by
dimension times the Lebesgue measure of the associated unit cone. Attribution:
Mathlib/MeasureTheory/Constructions/HaarToSphere.lean. -/
noncomputable def surfaceMeasure (s : ℕ) : Measure (Sphere (s + 1)) :=
  (volume : Measure (E (s + 1))).toSphere

def gaussianKernel {d : ℕ} (lam : ℝ) (u v : Sphere d) : ℝ :=
  Real.exp (-lam ^ 2 * (rho u v) ^ 2)

def tailKernel {d : ℕ} (lam L : ℝ) (u v : Sphere d) : ℝ :=
  (1 + lam * rho u v) ^ (-L)

noncomputable def sphericalGaussianIntegral (s : ℕ) (lam : ℝ)
    (u : Sphere (s + 1)) : ℝ :=
  ∫ v : Sphere (s + 1), gaussianKernel lam u v ∂surfaceMeasure s

noncomputable def sphericalTailIntegral (s : ℕ) (lam L : ℝ)
    (u : Sphere (s + 1)) : ℝ :=
  ∫ v : Sphere (s + 1), tailKernel lam L u v ∂surfaceMeasure s

/- T13: c_s,C_s are chosen before L; C_(s,L) can depend on L. The same
positive quadrature rule satisfies both uniform estimates. -/
def PositiveSphericalQuadratureStatement : Prop :=
  ∀ s : ℕ, 1 ≤ s → ∃ c C : ℝ, 0 < c ∧ 0 < C ∧
    ∀ L : ℝ, (s : ℝ) < L → ∃ C_L : ℝ, 0 < C_L ∧
      ∀ lam : ℝ, 1 ≤ lam →
        (∀ u v : Sphere (s + 1),
          sphericalGaussianIntegral s lam u = sphericalGaussianIntegral s lam v ∧
          sphericalTailIntegral s lam L u = sphericalTailIntegral s lam L v) ∧
        (∀ u : Sphere (s + 1),
          c * (lam ^ s)⁻¹ ≤ sphericalGaussianIntegral s lam u ∧
          sphericalGaussianIntegral s lam u ≤ C * (lam ^ s)⁻¹ ∧
          sphericalTailIntegral s lam L u ≤ C_L * (lam ^ s)⁻¹) ∧
        ∀ ζ : ℝ, 0 < ζ → ∃ m : ℕ, 0 < m ∧
          ∃ v : Fin m → Sphere (s + 1), ∃ w : Fin m → ℝ,
            (∀ i, 0 < w i) ∧ ∀ u : Sphere (s + 1),
              |(∑ i : Fin m, w i * gaussianKernel lam u (v i)) -
                sphericalGaussianIntegral s lam u| <
                  ζ * sphericalGaussianIntegral s lam u ∧
              (∑ i : Fin m, w i * tailKernel lam L u (v i)) ≤
                2 * sphericalTailIntegral s lam L u

/- This is the conjunction of the principal mathematical statements.
It is a proposition-valued definition, NOT a proof of any conjunct. -/
def PrincipalResultsStatement : Prop :=
  ConstantSequenceStatement ∧ BoundedNormUniformStatement ∧
    ConsecutiveDegreesStatement ∧ EvenFunctionsStatement ∧ OddFunctionsStatement ∧
    AllBodiesUniformStatement ∧ UniformGaussianStatement ∧
    OneSidedDensityStatement ∧ TensorDensityStatement ∧ FourierCutoffStatement ∧
    ConvexWeightedGaussianStatement ∧ FiniteFamilyStatement ∧
    PositiveSphericalQuadratureStatement


end Bandlimited

end
