module

public import Bandlimited.PrincipalResults

/-!
# Proofs of the compared principal declarations

The full analytic, geometric and algebraic proofs are in `Bandlimited/`.
This module imports no Challenge source. Comparator matches these fourteen roots
against the separately elaborated statements in the root `Challenge.lean`.
-/

@[expose] public section
namespace VerifiedPaper

/-- Uniform approximation of one along every even degree. -/
theorem t01 : Bandlimited.ConstantSequenceStatement :=
  Bandlimited.constant_sequence

/-- Uniformity over all norms with fixed Euclidean bounds. -/
theorem t02 : Bandlimited.BoundedNormUniformStatement :=
  Bandlimited.bounded_norm_uniform

/-- The full consecutive-degree approximation theorem (Kroó's conjecture). -/
theorem t03 : Bandlimited.ConsecutiveDegreesStatement :=
  Bandlimited.consecutive_degrees

/-- Even homogeneous approximation of every even continuous boundary function. -/
theorem t04 : Bandlimited.EvenFunctionsStatement :=
  Bandlimited.even_functions

/-- Odd homogeneous approximation of every odd continuous boundary function. -/
theorem t05 : Bandlimited.OddFunctionsStatement :=
  Bandlimited.odd_functions

/-- Uniformity over all symmetric convex bodies in a fixed dimension. -/
theorem t06 : Bandlimited.AllBodiesUniformStatement :=
  Bandlimited.all_bodies_uniform

/-- Uniform homogeneous Gaussian approximation with polynomially weighted errors. -/
theorem t07 : Bandlimited.UniformGaussianStatement :=
  Bandlimited.uniform_gaussian

/-- Density of arbitrarily small-bandwidth functions under a one-sided exponential weight. -/
theorem t08 : Bandlimited.OneSidedDensityStatement :=
  Bandlimited.one_sided_density

/-- Tensor-product density for arbitrary positive continuous factor weights. -/
theorem t09 : Bandlimited.TensorDensityStatement :=
  Bandlimited.tensor_density

/-- Gaussian Fourier cutoff in all dimensions up to the fixed bound, including zero. -/
theorem t10 : Bandlimited.FourierCutoffStatement :=
  Bandlimited.fourier_cutoff

/-- Gaussian approximation for every nonnegative Lipschitz convex profile. -/
theorem t11 : Bandlimited.ConvexWeightedGaussianStatement :=
  Bandlimited.convex_weighted_gaussian

/-- A finite family of real bandlimited approximants for the common Lipschitz class. -/
theorem t12 : Bandlimited.FiniteFamilyStatement :=
  Bandlimited.finite_family

/-- Positive spherical quadrature and the sharp scale-order integral bounds. -/
theorem t13 : Bandlimited.PositiveSphericalQuadratureStatement :=
  Bandlimited.positive_spherical_quadrature

/-- The conjunction of all thirteen principal mathematical results. -/
theorem all_principal : Bandlimited.PrincipalResultsStatement :=
  Bandlimited.principal_results

end VerifiedPaper
