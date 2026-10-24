# Reused proofs and library attribution

The formalization uses Lean 4.35.0-rc3 and Mathlib4 revision `b63f6e8a68d220e3b3bc4f3792bb53650d375f24`. Mathlib is licensed under Apache-2.0. The public repository contains the new development, not vendored Mathlib sources or caches; upstream copyright and attribution remain with the pinned dependencies.

The [import inventory](reuse-imports.json) lists direct canonical Mathlib imports per proof module. Principal proof applications in Solution use the accompanying complete Bandlimited development. A conditional reduction is not advertised as a closed result until its assumptions have been discharged in `Bandlimited/PrincipalResults.lean`.

Central reuse includes:

- `Module.Dual.exists_continuous_extension_of_le_seminorm_real` in [Hahn--Banach](https://github.com/leanprover-community/mathlib4/blob/b63f6e8a68d220e3b3bc4f3792bb53650d375f24/Mathlib/Analysis/Normed/Module/HahnBanach.lean) constructs dominated supporting functionals. Dual separation is also used in `WeightedDensityDual`.
- Smooth compact approximation and bump functions in Mathlib supply the dense smooth compactly supported subspace of continuous functions vanishing at infinity. The weighted embeddings and error identities are proved in this project.
- Banach-valued Morera results, analytic boundary uniqueness and Schwartz Fourier inversion support `BoundaryUniqueness`, `C0Families`, `LaplaceC0` and `LaplaceInversion`. They provide an alternative to the manuscript's finite-complex-measure proof route.
- The real [Stone--Weierstrass theorem](https://github.com/leanprover-community/mathlib4/blob/b63f6e8a68d220e3b3bc4f3792bb53650d375f24/Mathlib/Topology/ContinuousMap/StoneWeierstrass.lean) supplies ordinary boundary polynomial density. Prescribed homogeneous degrees and even/odd lifting are proved in `PolynomialLifting` and `MainReductions`.
- Mathlib partitions of unity support the explicit tensor-density construction. The factor replacement estimate and arbitrary-weight conclusion are proved in `TensorDensity`.
- `ConvexOn.exists_affine_le_of_lt` supplies supporting affine minorants. These produce an alternative proved active-subspace argument in `ConvexWeightedGaussian`, without assuming the manuscript's differentiability argument.
- Arzelà--Ascoli compactness, the compact-open topology and `IsCompact.elim_finite_subcover` support `FiniteFamily`. Weighted error continuity is established separately.
- Schwartz Fourier continuity, scaling, Fourier inversion, conjugate/reflection identities, linear changes of variables and finite-dimensional adjoints support the actual inverse-Fourier class. `FourierConvention` and `GaussianFourierNormalization` prove the exact conversion to the manuscript's convention.
- `Complex.exp_bound'` and `Real.pow_div_factorial_le_exp` support the Taylor estimates. The actual polynomial construction, half-degree bound, homogenisation and small-height error are proved in `KernelTaylor`.
- Mathlib's multivariate homogeneous-component and substitution theorems support real polynomial homogeneity, parity and linear transport. The conclusions use actual `MvPolynomial` objects.
- The canonical [surface measure](https://github.com/leanprover-community/mathlib4/blob/b63f6e8a68d220e3b3bc4f3792bb53650d375f24/Mathlib/MeasureTheory/Constructions/HaarToSphere.lean) and orthogonal invariance underpin the spherical construction. Spherical caps and layer-cake integration give the required scale-order estimates.
- Exact arithmetic tactics (`norm_num`, `ring`, `field_simp`, `positivity`, `linarith`, `nlinarith`) produce ordinary Lean proof terms. `NumericalBounds.lean` gives the corresponding axiom reports.

These are proved library results, not literature hypotheses or custom axioms. The solution axiom reports and independent kernel replay determine the actual trust boundary. The manuscript's prior mathematical literature supplies context; it is not imported as an unproved assumption.

The portable Comparator procedure follows the official [PalomarTemplate script](https://github.com/PalomarRegistry/PalomarTemplate/blob/main/scripts/verify-comparator.sh), accessed 24 October 2026, under Apache-2.0. The bundled Comparator and filtered export interface are credited to Lean FRO and contributors, including Henrik Böving. NanoDa and con-ron retain their upstream licences. See NOTICE.
