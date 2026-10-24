# Homogeneous polynomial approximation on symmetric convex bodies

Lean proofs of the thirteen principal results of Matthew J. Colbrook's manuscript on Kroó's conjecture. The development uses actual multivariate polynomials and inverse Fourier integrals, with the full uniform quantifiers in the statements.

For every origin-symmetric convex body $K\subset\mathbb R^d$ with nonempty interior and every $f\in C(\partial K;\mathbb R)$, the error of approximation by homogeneous polynomials of consecutive degrees $n,n+1$ tends to zero as $n\to\infty$. Even and odd functions admit approximation along their respective parities. Approximation of the constant function is uniform over all such bodies in a fixed dimension.

The analytic construction produces homogeneous polynomials with a common Gaussian profile and polynomially weighted uniform errors. The development also proves small-bandwidth weighted density, Gaussian Fourier cutoff, convex weighted approximation, finite-family selection and positive spherical quadrature. See [the mathematical account and result map](docs/RESULTS.md).

## Read the statements

- [Challenge.lean](Challenge.lean) is the self-contained statement of record. It imports only Mathlib and includes every definition needed to interpret the thirteen results.
- [Solution.lean](Solution.lean) proves the same fourteen declarations: the thirteen results and their conjunction.
- [Bandlimited/](Bandlimited/) contains the analytic, geometric and algebraic proof development. [Bandlimited.lean](Bandlimited.lean) is its library entry point.
- [AxiomReport.lean](AxiomReport.lean) prints the axiom dependencies of every compared declaration. [NumericalBounds.lean](NumericalBounds.lean) proves the numerical bounds by exact arithmetic and analytic inequalities.

The fourteen deliberate `sorry` placeholders in Challenge are specifications for Comparator. Neither Solution nor the proof library imports Challenge. There are no proof holes or custom axioms supporting the Solution. The permitted axioms are exactly `propext`, `Classical.choice` and `Quot.sound`; native-execution trust is excluded.

## Build

Install [elan](https://github.com/leanprover/elan) and Git, then run from this directory:

```sh
lake exe cache get
lake build
lake env lean AxiomReport.lean
python3 scripts/audit.py
```

The project pins Lean **4.35.0-rc3** and Mathlib commit **b63f6e8a68d220e3b3bc4f3792bb53650d375f24**. The committed `lake-manifest.json` pins every transitive Git dependency. Use Python 3.11 or later. On Windows, `python` may replace `python3`.

## Comparator and independent kernels

On Linux, with `bubblewrap` installed and usable:

```sh
bash scripts/verify.sh
```

This script performs the source audit and build, prints axiom reports, and invokes the bundled Lean Comparator with Lean, NanoDa and con-ron. It fails rather than silently disabling the operating-system sandbox. The GitHub Actions workflow performs the same checks on Linux. It has not been run on GitHub before this repository is uploaded.

Windows can build and inspect axioms; the public verification script requires Linux for the sandboxed Comparator step. The separately documented local Windows replay uses read-only pinned dependency caches and explicitly disables the unavailable OS sandbox. Its result is not a production Palomar acceptance. See [checking commands, output and limits](docs/CHECKING.md).

## Scope and source fidelity

The source correspondence is fixed to the manuscript snapshot with SHA-256 `70890207abc8b2e842d3bde78e1e834d7c7471ee447c7cfa907a809f71a55a91`. The manuscript itself is not distributed in this repository. Later editorial changes and the subsequently added weighted approximation consequence are outside this recorded comparison. Editing the paper does not silently update the formal claim.

All thirteen principal conclusions are preserved. Several proofs use alternative arguments and coarser sufficient constants; this is not a line-by-line certification of every auxiliary assertion in the manuscript. The [81-item inventory](docs/CLAIM_INVENTORY.md), [exact scope matrix](docs/VERIFICATION_SCOPE.md), and [source provenance](docs/SOURCE.md) make these distinctions explicit.

Proof checking establishes the stated Lean propositions and their axiom dependencies. Source fidelity and mathematical interpretation require separate review. [Review records](docs/REVIEWS.md) identify the AI reviews and their limits; no independent human peer review is claimed.

## Palomar submission

The root layout follows the [current Palomar submission standard](https://github.com/PalomarRegistry/PalomarPolicy/blob/main/CONTRIBUTING.md), checked on 24 October 2026. The metadata is in [formalization.yaml](formalization.yaml), expressed as JSON-compatible YAML, and the single selected Comparator configuration is [comparator.json](comparator.json).

After uploading and committing this folder as the root of a public GitHub repository, use the [Palomar submission form](https://submit.palomar-registry.org/) with its `owner/name`, the exact full 40-character commit SHA, and the repository-relative configuration path `comparator.json`. The project directory is the repository root; the metadata path is `formalization.yaml`. Recheck Palomar's policy when submitting. Registration still requires Palomar's mechanical and editorial review. See [the submission notes](docs/PALOMAR.md).

No Git repository, commit, remote, push or Palomar submission was created during preparation.

## Authorship and reuse

Mathematical author and responsible maintainer: **Matthew J. Colbrook**, University of Cambridge. The Lean development and documentation were prepared with substantial OpenAI Codex assistance, including separately identified AI reviews. See [the production account](docs/AI_ASSISTANCE.md).

New repository sources are provided under **Apache-2.0**. Mathlib, Lean and the checking tools retain their own licences and attribution. See [LICENSE](LICENSE), [NOTICE](NOTICE), and [proof reuse](docs/REUSE.md). Cited papers and the separately maintained manuscript are not relicensed by this repository.
