# Mathematical source and version

The mathematical source is Matthew J. Colbrook, *Homogeneous polynomial approximation on symmetric convex bodies*, unpublished manuscript, frozen before the subsequent title, abstract and bibliography edits.

- Frozen source SHA-256: `70890207abc8b2e842d3bde78e1e834d7c7471ee447c7cfa907a809f71a55a91`.
- Source size: 38,362 bytes; 1,024 lines.
- Principal result inventory: T01--T13.
- Formal result names: `VerifiedPaper.t01` through `VerifiedPaper.t13`, and `VerifiedPaper.all_principal`.

The full manuscript is kept separately by the author and is not included here. Its SHA identifies the version used for the statement-fidelity reviews. The complete mathematical claims can be read without the manuscript in [Challenge.lean](../Challenge.lean), [RESULTS.md](RESULTS.md), and the [claim inventory](CLAIM_INVENTORY.md). Source line numbers in the inventory refer to this frozen version only.

The repository preparation did not read, write, copy or compile the live manuscript that the author was editing. Later changes must be checked against the formal statements before claiming that the repository verifies a later version. In particular, the weighted approximation consequence added to the introduction after the original formal verification is not included in the thirteen compared results.

The source-based provenance in `formalization.yaml` describes the relationship to this manuscript. It does not claim that every historical assertion, reference, auxiliary calculation or particular proof route in that manuscript is a Lean theorem. [VERIFICATION_SCOPE.md](VERIFICATION_SCOPE.md) lists the exact limits.
