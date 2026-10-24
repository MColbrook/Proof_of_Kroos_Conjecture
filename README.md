# A proof of Kroó’s conjecture

Lean 4 formalization of the principal results of Matthew J. Colbrook's *Homogeneous polynomial approximation on symmetric convex bodies: a proof of Kroó’s conjecture*.

## Main result

Let $K\subset\mathbb R^d$ be an origin-symmetric convex body with nonempty interior, and let $H_n^d$ denote the real homogeneous polynomials of degree $n$. For every continuous real function $f$ on $\partial K$,

$$
\lim_{n\to\infty}\inf_{p\in H_n^d+H_{n+1}^d}\|f-p\|_{C(\partial K)}=0.
$$

Even functions admit approximation in every sufficiently large even degree, and odd functions in every sufficiently large odd degree. Approximation of the constant function by degree-$2n$ homogeneous polynomials is uniform over all such bodies in each fixed dimension. No smoothness or curvature assumptions are imposed on the boundary.

Earlier results established the planar case ([Benko–Kroó](https://doi.org/10.1090/S0002-9947-08-04625-4) and [Varjú](https://doi.org/10.1007/s00365-006-0639-2)), polytopes (Varjú), and regular convex bodies ([Kroó–Szabados](https://acta.hu/download.phtml?id=3045)). [Kroó's 2023 survey](https://drna.padovauniversitypress.it/2023/1/1) states the general conjecture as Problem 1. The result addresses this problem for arbitrary symmetric convex bodies and is relevant to multivariate approximation theory and convex geometry.

## Formalized results

The submission contains thirteen principal results, named `VerifiedPaper.t01` through `VerifiedPaper.t13`, and their conjunction `VerifiedPaper.all_principal`.

| Declarations | Mathematical content |
|---|---|
| `t01`–`t02` | Approximation of the constant function on each body, and uniformly over norms with fixed equivalence bounds |
| `t03`–`t05` | Approximation at consecutive degrees, and the even and odd cases |
| `t06` | A degree threshold uniform over all symmetric convex bodies in a fixed dimension |
| `t07` | Homogeneous Gaussian approximation with polynomially weighted uniform errors |
| `t08`–`t09` | Small-bandwidth density with one-sided exponential weights, and tensor-product density |
| `t10` | Gaussian Fourier cutoff in polynomially weighted uniform norms |
| `t11`–`t12` | Gaussian approximation with convex weights, and finite-family selection for Lipschitz classes |
| `t13` | Positive spherical quadrature and uniform Gaussian and tail estimates |

The statements use actual multivariate polynomials, the topological boundary, and inverse Fourier integrals, with the full uniform quantifiers. Some proofs use alternative arguments and coarser sufficient constants. The weighted approximation consequence obtained by homogenization in the manuscript is outside the submitted formalization. The [result map](docs/RESULTS.md) gives the exact statements and the [scope notes](docs/VERIFICATION_SCOPE.md) describe the correspondence in detail.

## Reading the proof

- [Challenge.lean](Challenge.lean) is the independent statement of record. It imports only Mathlib and defines the objects needed to read all thirteen results.
- [Solution.lean](Solution.lean) proves the corresponding declarations using the library in [Bandlimited/](Bandlimited/).
- [Bandlimited/PrincipalResults.lean](Bandlimited/PrincipalResults.lean) collects the main library theorems; [Bandlimited.lean](Bandlimited.lean) is the library entry point.
- [AxiomReport.lean](AxiomReport.lean) reports the proof dependencies, and [NumericalBounds.lean](NumericalBounds.lean) checks the numerical estimates.

Challenge's fourteen deliberate `sorry` placeholders specify the statements for Comparator. Solution and the proof library are independent of Challenge and contain no proof holes. The allowed axioms are `propext`, `Classical.choice`, and `Quot.sound`.

## Building and checking

Install [elan](https://github.com/leanprover/elan), Git, and Python 3.11 or later. From the repository root, run:

```sh
lake exe cache get
lake build
lake env lean AxiomReport.lean
python3 scripts/audit.py
```

The project uses Lean **4.35.0-rc3**. Mathlib and all transitive dependencies are pinned in [lakefile.toml](lakefile.toml) and [lake-manifest.json](lake-manifest.json). On Windows, use `python` in place of `python3` if appropriate.

For the complete repository verification on Linux, install `bubblewrap` and run:

```sh
bash scripts/verify.sh
```

This audits the package, builds the project, prints axiom reports, and runs Comparator with Lean, NanoDa, and con-ron, keeping the operating-system sandbox enabled. The [Verify formalization workflow](.github/workflows/verify.yml) runs these checks on GitHub. The recorded local replay and reproduction details are in [docs/CHECKING.md](docs/CHECKING.md).

## Palomar

The registry title is **A proof of Kroó’s conjecture**. The submission uses [comparator.json](comparator.json), with the project at the repository root and metadata in [formalization.yaml](formalization.yaml).

Once the repository is public, run the manual [Palomar preflight workflow](.github/workflows/palomar-preflight.yml) for the intended commit. It calls Palomar's full mechanical verifier. Follow the [submission instructions](docs/PALOMAR.md), then use the [Palomar submission form](https://submit.palomar-registry.org/). Registration follows Palomar's verification and review process.

## Authorship and licence

Mathematical author and responsible maintainer: **Matthew J. Colbrook**, University of Cambridge. The Lean development and documentation were prepared with substantial OpenAI Codex assistance. The [production account](docs/AI_ASSISTANCE.md) and [review records](docs/REVIEWS.md) describe that work and the AI reviews; no independent human peer review is claimed.

Repository sources are licensed under **Apache-2.0**. See [LICENSE](LICENSE), [NOTICE](NOTICE), and [proof reuse](docs/REUSE.md). Dependencies retain their own licences. The manuscript is maintained separately and is not included in the repository.
