# Palomar preparation

Requirements were checked on 24 October 2026 against the official [submission standard](https://github.com/PalomarRegistry/PalomarPolicy/blob/main/CONTRIBUTING.md), [submission service](https://github.com/PalomarRegistry/PalomarSubmission), [starter project](https://github.com/PalomarRegistry/PalomarTemplate), and [toolchain policy](https://raw.githubusercontent.com/PalomarRegistry/PalomarSubmission/main/toolchains.json). The observed minimum was Lean `v4.35.0-rc2`; this repository pins `v4.35.0-rc3` with a matching Mathlib revision.

## Prepared layout

| Requirement | Repository file or check |
|---|---|
| Pinned Lean and dependencies | `lean-toolchain`, `lakefile.toml`, `lake-manifest.json` |
| Auditable statement, separate proved implementation | `Challenge.lean`, `Solution.lean` |
| One selected configuration | `comparator.json`, fourteen roots |
| Only standard axioms | `propext`, `Classical.choice`, `Quot.sound`; `AxiomReport.lean` |
| Root licence, matching SPDX metadata | `LICENSE`, `project.license: Apache-2.0` |
| Human authors and responsible maintainers | Matthew J. Colbrook; AI work disclosed separately |
| Source-based provenance and meaningful mathematical account | `formalization.yaml`, `docs/RESULTS.md`, `docs/SOURCE.md` |
| Honest review and automation account | `docs/AI_ASSISTANCE.md`, `docs/REVIEWS.md` |
| Module headers, source caps and clean files | `scripts/audit.py` |
| Sandboxed Comparator and independent kernels | `scripts/verify.sh`, Linux CI |

Challenge contains all necessary local definitions directly and imports only Mathlib. There is no transitive import of a project-specific proof module. Its fourteen deliberate theorem placeholders are excluded from the proof-development `sorry_count`; none supports Solution. Its line count exceeds Palomar's preferred 300-line warning threshold but stays well below the 1,000-line and 100-KiB hard limits. Keeping the thirteen statements and their definitions together makes the submitted result auditable. Every individual Lean file is below the separate 10,000-line cap.

The public source tree contains no compiled artifacts, dependency caches, symlinks, submodules, LFS pointers or live manuscript. Metadata and the repository licence are consistent. The fresh local proof replay is documented in CHECKING.md; it does not claim an OS sandbox that Windows cannot supply. The Linux CI requires the sandbox and does not silently fall back.

Submit through https://submit.palomar-registry.org/ when ready.

## Later submission

1. Review the finished repository and licence, then upload its contents as the root of a public GitHub repository.
2. Let the Linux verification workflow pass at the intended revision.
3. Obtain that revision's full 40-character commit SHA. Palomar reviews the immutable public commit, not an uncommitted folder, branch or tag.
4. Select the repository root as the project, `comparator.json` as the configuration, and `formalization.yaml` as the metadata. State the submitter's actual relationship to the substantive development.
5. Recheck the current requirements before submission. Palomar's mechanical and editorial acceptance can only occur after submission.

No registration, publication, commit or push has been made during preparation. The prospective GitHub repository URL and future commit SHA are intentionally not invented or inserted into the metadata.
