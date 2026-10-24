> Scope note: this document refers to the frozen source identified in [SOURCE.md](SOURCE.md). Source line numbers do not refer to subsequent manuscript edits. Original local replay descriptions are historical evidence, distinguished from the repository checks in [CHECKING.md](CHECKING.md).

# Exact verification scope

This is a primary AI scope audit, not an independent review. It maps every one of the 81 inventory IDs. The original claim text, full constants, assumptions and source lines remain in [CLAIM_INVENTORY.md](CLAIM_INVENTORY.md). All thirteen principal conclusions have unconditional kernel-checked proofs. The final 14-root local Comparator replay and independent kernel checks passed; the OS sandbox was explicitly disabled on Windows. A checked principal conclusion does not certify every unused intermediate proof-route sentence verbatim.

The formal proof uses several alternative arguments: direct C0 duality and Fourier inversion for T08; supporting affine slopes for T11; spherical caps and layer-cake bounds for T13; ambient residual coordinates for T07; parity polynomial projection for odd functions; and coarser dimension-only normalization for T06. These changes preserve the full intended principal results. The distinctions below identify exactly which additional claims are not separately certified. No missing item is assumed as an axiom in a verified proof.

| ID | Checked coverage and precise limitation | Lean source / evidence |
|---|---|---|
| D01 | Concrete Euclidean spaces, including dimensions zero and one | Definitions; BodyGeometry; FourierTransport |
| D02 | Actual real MvPolynomial.IsHomogeneous; zero is included | Definitions; PolynomialLifting; KernelTaylor |
| D03 | Actual norm axioms and Minkowski gauge representation checked | BodyGeometry; BodyGauge |
| D04 | Actual real continuous boundary functions and common strict error envelope | Definitions; PolynomialLifting |
| D05 | Chord definition, antipodal symmetry, sharp sqrt(2) bound checked | AngularGeometry; KernelGeometry |
| D06 | Exact inverse convention and Mathlib 2π conversion checked | FourierConvention; GaussianFourierNormalization; LaplaceInversion |
| D07 | Actual C∞ compact support inside open frequency ball | Definitions; FourierTransport; FourierLinear; FourierProduct |
| D08 | Schwartz representatives and real-part closure checked | BandlimitedOperations; FourierTransport |
| D09 | Actual dimension-zero constants and Gaussian factor 1/error 0 checked | Definitions; GaussianCutoff; FourierProduct |
| D10 | Actual real-exponent one-sided weight and weighted-C0 predicate | Definitions; WeightedSchwartz; OneSidedDensity |
| D11 | Actual real-exponent Gaussian weights; finite uniform Gaussian bound checked, not exact source supremum constant | Definitions; ConvexGaussianErrors |
| D12 | Actual convex nonnegative normalized common-Lipschitz class | Definitions; FiniteFamily |
| D13 | Actual unnormalized surface measure and kernels | Definitions; SphericalTheorem |
| T01 | Full intended principal conclusion kernel checked; local Comparator and independent kernel replay passed | PrincipalResults: constant_sequence; Solution: VerifiedPaper.t01 |
| T02 | Full intended principal conclusion kernel checked; local Comparator and independent kernel replay passed | PrincipalResults: bounded_norm_uniform; Solution: VerifiedPaper.t02 |
| T03 | Full intended principal conclusion kernel checked; local Comparator and independent kernel replay passed | PrincipalResults: consecutive_degrees; Solution: VerifiedPaper.t03 |
| T04 | Full intended principal conclusion kernel checked; local Comparator and independent kernel replay passed | PrincipalResults: even_functions; Solution: VerifiedPaper.t04 |
| T05 | Full intended principal conclusion kernel checked; local Comparator and independent kernel replay passed | PrincipalResults: odd_functions; Solution: VerifiedPaper.t05 |
| T06 | Full intended principal conclusion kernel checked; local Comparator and independent kernel replay passed | PrincipalResults: all_bodies_uniform; Solution: VerifiedPaper.t06 |
| T07 | Full intended principal conclusion kernel checked; local Comparator and independent kernel replay passed | PrincipalResults: uniform_gaussian; Solution: VerifiedPaper.t07 |
| T08 | Full intended principal conclusion kernel checked; local Comparator and independent kernel replay passed | PrincipalResults: one_sided_density; Solution: VerifiedPaper.t08 |
| T09 | Full intended principal conclusion kernel checked; local Comparator and independent kernel replay passed | PrincipalResults: tensor_density; Solution: VerifiedPaper.t09 |
| T10 | Full intended principal conclusion kernel checked; local Comparator and independent kernel replay passed | PrincipalResults: fourier_cutoff; Solution: VerifiedPaper.t10 |
| T11 | Full intended principal conclusion kernel checked; local Comparator and independent kernel replay passed | PrincipalResults: convex_weighted_gaussian; Solution: VerifiedPaper.t11 |
| T12 | Full intended principal conclusion kernel checked; local Comparator and independent kernel replay passed | PrincipalResults: finite_family; Solution: VerifiedPaper.t12 |
| T13 | Full intended principal conclusion kernel checked; local Comparator and independent kernel replay passed | PrincipalResults: positive_spherical_quadrature; Solution: VerifiedPaper.t13 |
| W01 | Weighted embedding and exact norm/error identities used; a standalone surjective linear-isometry structure X_W≃C0 is not separately declared | WeightedSchwartz; WeightedDensityDual; OneSidedDensity |
| W02 | Dual annihilator/Hahn–Banach criterion checked; Riesz finite-complex-measure representation is unused and not separately formalized | WeightedDensityDual |
| W03 | Actual nonzero Schwartz bandlimited q with q(0)≠0 checked; the precise normalized q(0)=1/dilation family is not separately selected | OneSidedDensity.exists_nonzero_bandlimited_schwartz; BandlimitedOperations |
| W04 | Modulation and bandwidth preservation checked; the associated finite complex measure is unused and not formalized | BandlimitedOperations; OneSidedDensity.functional_zero_on_real_modulations |
| W05 | All-tail weighted Schwartz domination checked; the displayed total-variation-measure inequality is unused and not formalized | WeightedSchwartz; LaplaceC0 |
| W06 | C0-valued Laplace strip continuity/holomorphy and scalarized functional argument checked; the particular measure integral H_eta is not constructed | C0Families; LaplaceC0 |
| W07 | Boundary uniqueness/holomorphic extension checked; finite complex measure Fourier uniqueness is replaced by C0-valued Fourier inversion, not separately formalized | BoundaryUniqueness; LaplaceInversion |
| W08 | Local nonvanishing-factor removal and density checked; the particular q_eta/exhaustion argument is replaced by a finite local cover | C0LocalIdeal; OneSidedDensity |
| W09 | Full tensor-density conclusion checked through finite interval/rectangular partitions of unity and telescoping replacement of factors, substantially following the source route | TensorDensity |
| A01 | Actual smooth compact cutoff and real inverse transform checked; no separate claim that every selected cutoff is radial is needed | SchwartzCutoff; GaussianCutoff |
| A02 | Exact Fourier scaling and Gaussian normalization checked for the selected construction | FourierConvention; GaussianFourierNormalization; GaussianCutoff |
| A03 | Schwartz derivative/cutoff tail estimates and weighted uniform convergence checked; the exact displayed integration-by-parts L1 estimate is not separately selected | SchwartzCutoff; GaussianCutoff |
| A04 | Constancy on the orthogonal complement checked through affine minorants; a.e. gradients/distributional derivative/mollification route is unused and not formalized | ConvexWeightedGaussian |
| A05 | Spanning independent supporting affine slopes and coordinate equivalence checked; slopes need not be attained gradients, unlike the source proof route | ConvexWeightedGaussian |
| A06 | One-sided product-weight domination checked with rate 1/(r+1); the exact source rate 1/r is not separately certified | ConvexWeightedGaussian |
| A07 | Full target weighted-C0 membership checked | ConvexGaussianTarget |
| A08 | Active-space weighted approximation and actual compact-frequency transport checked; the particular source hyperrectangle description is not separately declared | ConvexGaussianActive; FourierTensor; FourierLinear; FourierProduct |
| A09 | Actual orthogonal factorization and smooth Fourier product support checked | ConvexGaussianGeometry; FourierProduct; ConvexGaussianTheorem |
| A10 | Uniform Δ independent of every profile checked; its chosen expression uses a coarser finite error budget than the source C_L max e_k formula | ConvexGaussianErrors; ConvexGaussianTheorem |
| A11 | Zero active rank and zero complementary dimension checked, including actual dimension-zero factor | ConvexGaussianTheorem; GaussianCutoff; FourierProduct |
| A12 | Compactness in compact-open/locally uniform topology checked; the particular displayed series metric is not separately formalized | FiniteFamily |
| A13 | Uniform weighted exponential-difference continuity/neighborhood bound checked; a standalone ssup-error functional is not separately defined | FiniteFamily.weighted_exp_difference_eventually |
| A14 | Nonempty finite subcover, finite bandlimited family, common Fourier mass and simultaneous tails checked | FiniteFamily; UniformGaussian; KernelTails |
| K01 | D,C,bandwidth and uniform choice order checked; final proof uses B=(2D)^L and τ=ε/(16B), without a separate τ<1/4 constraint | UniformGaussian |
| K02 | Supporting functional with source domination and operator bound checked | SupportingFunctional |
| K03 | Ambient-space residual/projection coordinates checked; the particular isometry U:R^s→v-perp is avoided and not separately selected | SupportingChart; KernelGeometry |
| K04 | Full nonnegativity, zero, convexity and common Lipschitz bound checked for the ambient profile, constant along v | SupportingChart; UniformGaussian |
| K05 | Exact radial reciprocal-profile and chart identities checked | ChartBoundary; SupportingChart |
| K06 | Exact chart norm bound and chord–sine sharp sqrt(2) inequality checked; assembled chart-weight bound uses coarser 2D, not the source sqrt(2)D constant | AngularGeometry; ChartAngularBounds; KernelWeights |
| K07 | Direct quantitative local Gaussian error O_D(M^3/(N A^2)) checked; the separately stated normalized-vector O(||t||^2) and chord O(M^2/N) asymptotics are not separately declared | LocalAngularGaussian; LocalAngularError |
| K08 | Actual real polynomial of degree ≤N/2 from real parts of Fourier moments checked; Hermitian symmetrization/coefficient reality also checked under explicit Hermitian hypothesis | KernelTaylor |
| K09 | Full exp(-N) Taylor error checked using Complex.exp_bound' and Real.pow_div_factorial_le_exp; the separate Stirling inequality n!≥(n/e)^n is not used or separately declared | KernelTaylor; NumericalBounds |
| K10 | Fraction-free homogeneous extension, rational evaluation, antipodal symmetry and conditional total-degree equality checked; nonzeroness of the particular selected p is not asserted in the principal theorem | KernelTaylor; KernelGeometry; UniformGaussian |
| K11 | Full exp(-N/4) polynomial bound checked also at the supporting hyperplane, with absolute height ≤1/2 | KernelTaylor.homogeneousApproximation_small_height |
| K12 | Height Lipschitz/separation, Gaussian tail and polynomially weighted decay checked; assembled global weight uses 2 in place of sharp sqrt(2) | SupportingHeight; KernelWeights; KernelTails |
| K13 | Uniform compact-q rescaling ratio and central weighted error checked with a finite uniform Gaussian bound | Rescaling; KernelScalarEstimates; KernelErrorAssembly |
| K14 | Weighted Taylor decay and direct central angular Gaussian comparison checked; the separate exact derivative maximum sqrt(2/e)/A is not used or declared | KernelTaylor; LocalAngularError; UniformGaussian |
| K15 | Finite-family Schwartz tails, outer-chart Gaussian and uniform Taylor error checked with coarse 2D chart constant | KernelTails; KernelWeights; UniformGaussian |
| K16 | Complete three-region assembly with common ε/2 envelope, threshold before norm/centre/degree, checked | UniformGaussian |
| Q01 | Canonical surface measure and orthogonal centre invariance checked; the exact one-dimensional radial integration identity is unused and not formalized | SphericalQuadrature; SphericalCaps; SphericalTheorem |
| Q02 | Full sharp λ^-s Gaussian/tail bounds checked by spherical caps and layer-cake estimates; the specific radial-density argument is not separately formalized | SphericalCaps; SphericalEstimates; SphericalGaussian |
| Q03 | Positive finite quadrature checked by Bochner-average closed-convex-hull approximation and finite convex combinations in a normed function space; explicit cell construction is not formalized | SphericalQuadrature; SphericalTheorem |
| Q04 | Exact one-dimensional homogeneous constant approximation checked, including degree zero | BodyGeometry |
| Q05 | Uniform choice of L, Gaussian scale and errors before each norm checked | KernelToBoundary |
| Q06 | Actual homogeneous finite polynomial sum and full uniform boundary error checked | KernelToBoundary; Summation |
| Q07 | Actual single sequence at every even degree checked from eventual approximation | MainReductions; BodyGauge; PrincipalResults |
| Q08 | Compact maximal-determinant frame and coordinate-box coefficient bound checked; norm proof uses the signed convex frame combination | MaximalFrame; UniformNormalization |
| Q09 | Polynomial and boundary transport and full T06 checked using coarser dimension-only norm bounds 1/d,d; sharp 1/sqrt(d),sqrt(d) bounds are not separately formalized | UniformNormalization; PolynomialTransport; UniformBodies |
| Q10 | Stone–Weierstrass boundary density and even parity projection checked | PolynomialLifting |
| Q11 | Actual homogeneous component lifting at all prescribed sufficiently large degrees and uniform convergence checked | PolynomialLifting |
| Q12 | Full odd-function conclusion checked via odd polynomial projection/lifting; the particular g_j=x_j f/||x||^2 decomposition is avoided and not separately formalized | PolynomialLifting |
| Q13 | Even/odd decomposition and both consecutive-degree parity cases checked | MainReductions; PolynomialLifting |
| H01 | Historical attribution: outside Lean mathematical proof scope | claim_inventory; bibliography |
| H02 | Historical attribution: outside Lean mathematical proof scope | claim_inventory; bibliography |
| H03 | Bibliographic metadata: outside Lean mathematical proof scope | claim_inventory; bibliography |

In this repository the proof modules are under `Bandlimited/` and the independent statement surface is the self-contained root `Challenge.lean`. The mirrored Challenge proof graph used in the original local development is not distributed. All review reports are AI reviews; no independent human review is claimed. Current reproduction commands and results are documented in [CHECKING.md](CHECKING.md) and `evidence/`.
