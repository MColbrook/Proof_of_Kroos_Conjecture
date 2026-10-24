# Mathematical results and exact scope

The mathematical author is Matthew J. Colbrook. The Lean development and the reviews were produced with AI assistance, as described in [REVIEWS.md](REVIEWS.md). The public theorem roots are `VerifiedPaper.t01` through `VerifiedPaper.t13`; `VerifiedPaper.all_principal` is their conjunction. They formalize the thirteen principal conclusions of a frozen manuscript version, rather than every sentence or auxiliary assertion of the paper.

The source fingerprint is SHA256 `70890207abc8b2e842d3bde78e1e834d7c7471ee447c7cfa907a809f71a55a91` (1,024 lines). That snapshot predates the subsequent bibliography expansion and the weighted approximation consequence added with it. The manuscript itself is not distributed in this repository. [SOURCE.md](SOURCE.md) describes provenance. References to source lines below refer to that snapshot; they do not identify the author's currently edited manuscript.

## Concrete objects

The statements use `EuclideanSpace ℝ (Fin d)`, real `MvPolynomial` objects and Mathlib's `MvPolynomial.IsHomogeneous`. A symmetric convex body is compact, convex and invariant under negation, with nonempty interior. A body norm satisfies the ordinary positivity, homogeneity and triangle axioms. Neither predicate assumes smoothness, strict convexity, curvature, a polytope structure, or an approximation conclusion. Homogeneous spaces contain the zero polynomial, as usual.

Boundary functions are real continuous functions on the actual topological frontier. Boundary errors have one common bound strictly below the requested tolerance. Thus the statements express strict uniform approximation, including on noncompact domains when those occur later, rather than merely separate pointwise strict inequalities.

The bandlimited class is defined by the actual inverse Fourier integral

$$
F(x)=(2\pi)^{-d}\int_{\mathbb R^d}\phi(\xi)e^{i\langle x,\xi\rangle}\,d\xi,
$$

where `φ` is smooth, compactly supported, and its closed support lies inside the specified open frequency ball. In dimension zero this class consists of constants on the one-point space. In Lean the smoothness order is `((⊤ : ℕ∞) : WithTop ℕ∞)`; this is the smooth order in the pinned API. It does not impose real analyticity. A weighted `C₀` predicate requires a continuous target whose product with the weight is continuous and vanishes at infinity in the ordinary sense.

## The thirteen principal conclusions

In the table, `ε`, `η`, `δ`, `σ`, `c`, `C`, `A`, `L`, `M`, `α`, `β`, `λ` and `ζ` are real unless otherwise stated; dimensions, degrees and finite-family sizes are natural numbers. Positive and nonnegative requirements are explicit. The order of the choices is part of each conclusion.

| Root and statement | Assumptions, constants and conclusion |
| --- | --- |
| `t01` — `ConstantSequenceStatement` | For every dimension `d` and symmetric convex body `K`, a sequence of real homogeneous polynomials of degrees `2n`, for every `n`, converges uniformly to `1` on `∂K`. Source lines 115–120. |
| `t02` — `BoundedNormUniformStatement` | For fixed `d`, `0 < α ≤ β` and `ε > 0`, a threshold `n₀` is selected before the norm. Every `n ≥ n₀` and every norm satisfying `α‖x‖ ≤ ν(x) ≤ β‖x‖` admit a homogeneous polynomial of degree `2n` with boundary error `< ε`. Source lines 121–128. |
| `t03` — `ConsecutiveDegreesStatement` | For every such `K`, every real continuous `f` on `∂K` and `ε > 0`, every sufficiently large natural `n` admits homogeneous `p`, `q` of degrees `n`, `n+1` with `‖p+q-f‖∞ < ε`. Both parities of `n` are covered. Source lines 129–135. |
| `t04` — `EvenFunctionsStatement` | Every even real continuous boundary function admits homogeneous approximation of degree `2n` at every sufficiently large `n`. Source lines 134–135 and 945–962. |
| `t05` — `OddFunctionsStatement` | Every odd real continuous boundary function admits homogeneous approximation of degree `2n+1` at every sufficiently large `n`. Source lines 134–135 and 964–975. |
| `t06` — `AllBodiesUniformStatement` | For fixed `d` and `ε > 0`, one threshold works for every symmetric convex body in that dimension and every subsequent even degree `2n`. There are no externally supplied norm-equivalence bounds. The polynomial may depend on the body. Source lines 138–149. |
| `t07` — `UniformGaussianStatement` | For `s ≥ 1`, `0 < α ≤ β`, real `L ≥ 0` and `ε > 0`, choose `A ≥ 1` and integer `N₀ ≥ 2` before the norm, centre and degree. Every admissible norm on `ℝ^(s+1)`, unit centre `v` and even `N ≥ N₀` admit homogeneous `p` of degree `N` approximating `exp(-(N/A)²ρ(u,v)²)` on the radial boundary, with uniform error `< ε` after multiplication by `(1+(N/A)ρ(u,v))^L`. Here `ρ(u,v)=min(‖u-v‖,‖u+v‖)`. Source lines 156–174. |
| `t08` — `OneSidedDensityStatement` | For arbitrary `c > 0`, real `M ≥ 0` and bandwidth `δ > 0`, the actual smooth compact-frequency class in one dimension is dense in the complex weighted `C₀` space for `W(t)=(1+|t|)^M exp(-c max(t,0))`. Every target and every positive error are included. Source lines 235–247. |
| `t09` — `TensorDensityStatement` | In every positive finite dimension, arbitrary positive continuous one-variable weights and arbitrary dense subsets of their weighted `C₀` spaces give density of finite sums of products in the corresponding product-weighted space. No exponential form of the weights is assumed. Source lines 303–314. |
| `t10` — `FourierCutoffStatement` | For fixed natural `s`, real `L ≥ 0` and `σ > 0`, real bandlimited approximants to `exp(-‖x‖²/A²)` have frequency radius `σ/4` for each `k ≤ s` and real `A ≥ 1`. The actual supremum errors, weighted by `(1+‖x‖/A)^L`, tend to zero uniformly over `k ≤ s` as real `A → ∞`. The dimension-zero factor is exactly `1`, with error `0`. Source lines 340–351. |
| `t11` — `ConvexWeightedGaussianStatement` | For `s ≥ 1`, real `L ≥ 0` and `σ > 0`, choose `Δ(A) → 0` depending only on these parameters. For every globally Lipschitz nonnegative convex `f` with `f(0)=0`, every `A ≥ 1` and every `η > 0`, a real bandlimited `F` of radius `σ` has weighted error at most `Δ(A)+η` against the Gaussian after multiplication by `exp(-f)`. There is no common bound on the Lipschitz constants of these profiles. Arbitrarily small slack expresses the source infimum bound without asserting attainment. Source lines 378–388. |
| `t12` — `FiniteFamilyStatement` | For `s ≥ 1`, real `L ≥ 0` and positive `σ`, `C`, `τ`, select one `A ≥ 1` and one nonempty finite family of real bandlimited functions before the profile. Every normalized nonnegative convex profile with Lipschitz bound `C` has a member of that family whose weighted Gaussian error is `< τ`. Source lines 510–520. |
| `t13` — `PositiveSphericalQuadratureStatement` | For every `s ≥ 1`, choose positive `c_s`, `C_s` before real `L > s`, and then positive `C_(s,L)`. For all `λ ≥ 1`, the Gaussian and polynomial-tail spherical integrals are independent of the centre; the Gaussian integral lies between `c_s λ^(-s)` and `C_s λ^(-s)`, and the tail integral is at most `C_(s,L) λ^(-s)`. For each `ζ > 0`, one nonempty finite quadrature rule with strictly positive weights satisfies both the relative Gaussian error `< ζ` and the tail bound by twice its integral, uniformly in the centre. The measure is the canonical unnormalized Euclidean surface measure. Source lines 831–852. |

The first six conclusions also include the zero-dimensional formal boundary case; the implementation treats low dimensions explicitly. No body-dependent threshold replaces the uniform thresholds in `t02` or `t06`, and none of the degree conclusions is restricted to a selected subsequence.

## Mathematical context and mechanism

The consecutive-degree result `t03`, together with its parity versions, is the homogeneous approximation assertion discussed as Kroó's conjecture in [Kroó's 2023 survey, §3](https://drna.padovauniversitypress.it/system/files/papers/KrooSurvey2023.pdf). Earlier positive results include regular convex bodies in [Kroó–Szabados (2009)](https://acta.hu/download.phtml?id=3045) and the elementary constructions in [Totik (2013)](https://www.math.u-szeged.hu/pot/M2homogen.pdf). These references explain context; Lean does not certify historical priority or the bibliography.

The formal development connects small-bandwidth density (`t08`, `t09`), Gaussian approximation with convex weights (`t10`, `t11`), compactness producing a finite common family (`t12`), homogeneous local Gaussian approximation (`t07`), and positive spherical quadrature (`t13`). These yield constant approximation and the parity and consecutive-degree conclusions. The statements retain the uniformity needed to pass from each local construction to every body in a fixed dimension.

## What the certificate does not establish

The historical local evidence checks the thirteen principal conclusions and their conjunction. The complete [claim inventory](CLAIM_INVENTORY.md) and [scope matrix](VERIFICATION_SCOPE.md) distinguish those results from the remaining auxiliary assertions. In particular:

- The source proof's finite-complex-measure route is replaced by a weighted-`C₀` duality and Fourier-inversion argument. Its unused measure-specific intermediate assertions are not separately certified.
- Supporting affine slopes replace the gradient, distributional derivative and mollification route. The source's explicit series metric for local convergence is also not separately formalized.
- Spherical caps and layer-cake bounds replace the exact radial integration identity. The normalization argument uses sufficient coarser dimension-only constants instead of separately proving the source's sharp square-root constants.
- The selected local polynomial is homogeneous in the mathematical sense. Its additional nonzeroness, and hence equality of its total degree with the prescribed degree, is not a separate certified assertion. This does not weaken membership in the homogeneous polynomial space in the principal statements.
- Bibliography, historical attribution, novelty, prose, and future changes to the paper lie outside the mathematical certificate. The weighted approximation consequence added after the frozen snapshot is not among these thirteen Lean results and is not included in `all_principal`.

`Challenge.lean` contains fourteen deliberate theorem proof placeholders for Comparator to check against `Solution.lean`. They are specification holes, not solution proofs, and are never imported by `Solution.lean` or its dependency graph. The permitted solution axioms are only `propext`, `Classical.choice` and `Quot.sound`. See the checking documentation for exact commands, outputs, and the distinction between a successful local replay and Palomar registry acceptance.
