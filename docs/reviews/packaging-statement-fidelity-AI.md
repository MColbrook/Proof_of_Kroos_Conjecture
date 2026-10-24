# AI review: public repository statement fidelity

Date: 24 October 2026. Reviewer: a separate Codex AI statement-review agent. This is a source-level review, not human peer review, not an independently invented proof, and not a fresh Lean, Comparator or external-kernel execution. The reviewer did not develop the Lean proofs or the new `Challenge.lean`. It inspected earlier AI review records as well as the concrete sources, so the report does not claim independence from all prior analysis.

## Inputs

The author was editing the live manuscript during repository preparation. The reviewer did not read or modify that live file. The source comparison used only the preserved 1,024-line snapshot in the original verification workspace, SHA256:

```text
70890207abc8b2e842d3bde78e1e834d7c7471ee447c7cfa907a809f71a55a91
```

The snapshot is not bundled with this public repository. Its provenance and the limits of external access are described in [SOURCE.md](../SOURCE.md). The reviewer directly read the principal source statements at lines 115–174, 235–247, 303–314, 340–351, 378–388, 510–520 and 831–852, the detailed inventory, the concrete definitions and the solution entry. It also read the earlier final fidelity and proof-trust reviews to identify historical limitations rather than silently inheriting a claim that every source assertion had been formalized.

The inspected hashes were:

| File | SHA256 |
| --- | --- |
| New `Challenge.lean` | `b3261e7ee23bdf4537208e13a61405eb8a2acf98ed37a3deb065416205f8a309` |
| `Solution.lean` | `88512b75052d4d47087c85358ed8db31cc5a202fe1dacae475d3cbb4516f2a91` |
| `Bandlimited/Definitions.lean` | `f50047e1912784c9461db238fbde55a96570396bf2cc996958901cd19cc93445` |

## Mechanical definition comparison

A case-sensitive text comparison extracted the region from `@[expose] public section` through the end of the mathematical definitions in the original `Bandlimited/Definitions.lean`, and the corresponding region of the new `Challenge.lean` before `namespace VerifiedPaper`. Before documentation was expanded, the regions were exactly equal after trimming outer whitespace. A second independent comparison of the final documented challenge removed Lean block and line comments and normalized whitespace: the mathematical regions were again **equal**. No mathematical definition body changed. The final challenge has fourteen theorem proof placeholders; its imports are Mathlib-only, and its targets correspond to `VerifiedPaper.t01` through `t13` and `all_principal`.

Each target uses the same named concrete proposition as the corresponding solution theorem. The challenge replaces its proof with an explicit `sorry`; the solution retains an application of a closed proved theorem. The challenge's placeholders must not be confused with solution axioms, and its success in compiling would not itself prove any target. The permitted axiom and actual proof checks apply to the solution closure.

## Mathematical statement comparison

No material weakening or hidden hypothesis was found in the thirteen concrete statements against the frozen principal source statements. In particular:

- Bodies and norms are defined by their ordinary mathematical conditions, without regularity or approximation hypotheses.
- The polynomial type is the genuine real multivariate polynomial type with actual homogeneity. The boundary is the topological frontier, and continuous functions are actual continuous maps.
- The thresholds in `t02` and `t06` precede the varying norm and body. The scale and threshold in `t07` precede the norm, centre and even degree. All sufficiently large prescribed degrees are included.
- The bandlimited predicate constructs actual smooth compactly supported inverse Fourier data, with the stated `(2π)^(-d)` normalization. The dimension-zero convention and real weight exponents are retained.
- `t10` includes the actual supremum error, not only an unspecified upper bound. `t11` chooses one error function before the profile, without a common Lipschitz bound, and preserves the source infimum assertion through arbitrary positive slack. `t12` selects a nonempty finite family before the profile.
- `t13` uses the canonical unnormalized Euclidean surface measure and the same positive finite quadrature rule for both uniform inequalities. Its two Gaussian scale constants precede the real tail exponent.
- Strict error predicates contain one common bound strictly below the tolerance, so they do not weaken uniform supremum claims to unrelated pointwise statements.

The thirteen-result map, parameter restrictions, constants, quantifier order and exact source locations are summarized in [RESULTS.md](../RESULTS.md). The additional dimension-zero cases in the body statements are handled explicitly by the implementation.

## Limits and findings for publication

The inspected old `source_manifest.json` contained stale early-stage fields claiming zero principal results had been proved. That historical manifest should not serve as the new repository's current status; current provenance must distinguish the frozen source fingerprint from the later successful checks. The new metadata is maintained separately by the packaging agent.

The historical full-graph checks used a proof-bearing mirrored challenge. The new challenge is an improved submission interface, but its distinct hash must have its own comparison evidence. The reviewer has not run that comparison and does not claim that the historical certificate applies byte-for-byte to the newly packaged challenge.

The certificate covers the principal conclusions, with alternative proved arguments. It does not separately prove the unused finite-complex-measure route, gradient/mollification route, explicit local series metric, exact radial integral formula, sharper normalization constants, or nonzeroness of the selected local polynomial. None of these omissions supplies an axiom to the solution. Bibliography, history and prose are also outside the Lean certificate.

The weighted approximation consequence added to the manuscript after the frozen snapshot is not included in these targets. No claim is made that the current, moving manuscript has been compared line by line with this repository.

On the inspected source evidence, the new challenge preserves the earlier thirteen principal statements and provides a clearer separate specification. Submission readiness also depends on the actual new build and comparison outputs, applicable Palomar policy, and the repository's licensing and provenance records. Those are separate from this statement review.
