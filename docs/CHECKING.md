# Checking and reproducibility

## Portable verification

Run the repository-root commands in the README. The complete Linux verification is:

```sh
bash scripts/verify.sh
```

It performs the source and metadata audit, retrieves the pinned Mathlib cache, builds all default Lake targets, prints the fourteen principal axiom reports and ten numerical reports, and runs the bundled Comparator against a protected configuration requiring Lean, NanoDa and con-ron. It records source/configuration SHA-256 fingerprints before checking and confirms they are unchanged afterwards. The public configuration stays limited to Palomar's permitted submitted keys. The wrapper fails if the Linux sandbox cannot start; it never silently disables it.

On native Windows, `pwsh -NoProfile -File scripts/verify.ps1 -BuildOnly` runs only the source audit, ordinary Lean build and axiom reports. Full sandboxed checking requires Linux or the prepared GitHub Actions workflow.

## Repository preparation replay

**Passed** on 24 October 2026. The actual replay ran from `2026-10-24T12:54:36.272Z` to `2026-10-24T13:35:49.045Z`.

| Check | Actual result |
|---|---|
| Fresh compilation | All 69 submitted Lean sources accepted |
| Principal axiom reports | Fourteen reports, each using only `propext`, `Classical.choice`, `Quot.sound` |
| Challenge/Solution Comparator | All fourteen selected roots accepted, exit 0 |
| con-ron | 56,994 declarations accepted (`--verified`) |
| NanoDa | Solution accepted |
| Lean default kernel | Solution accepted |
| Additional paranoid Lean replay | Exit 0 |
| Source stability | All 69 Lean source fingerprints unchanged before and after replay |
| Native Windows OS sandbox | Unavailable; the attempt returned exit 2 and is retained |

The complete [checking record](../evidence/local-replay.json), [axiom output](../evidence/axioms.txt), [Comparator output](../evidence/comparator.txt), [additional replay output](../evidence/paranoid.txt), [compiler output](../evidence/compilation.txt), and [versions](../evidence/versions.txt) are included. The [evidence index](../evidence/README.md) describes the remaining files.

The local source compilation and export were fresh; they were not copied from the original verification project. The result is a local mathematical replay, not production Palomar acceptance or a hosted Linux CI run.

The local machine is Windows x86_64. Lean is `4.35.0-rc3`, commit `470d5ce1400764999581fd26d5d72b00d990b0f4`, with Lake `5.0.0-src+470d5ce`. Mathlib is pinned to `b63f6e8a68d220e3b3bc4f3792bb53650d375f24`. All nine dependency working trees were independently inspected as clean, with Git HEADs matching the pinned manifest. Two canonical Mathlib caches at that same revision were used read-only. No original project proof `.olean` was used as an input.

The replay freshly elaborates all 69 submitted Lean sources in dependency order to an external temporary build directory. Its first search-path entry is that new output directory; subsequent entries are the authenticated dependency caches. It then exports the fourteen roots from the independently elaborated Challenge and Solution and replays the Solution proof closure. The live manuscript is not part of any command.

The actual local command patterns are:

```text
lean --memory=4096 --threads=2 -o <build>/<module>.olean <module>.lean
leanexport Challenge -- <fourteen roots, permitted axioms and primitive roots>
leanexport Solution -- <same roots>
lake comparator --config comparator.json --challenge-from-export <Challenge.ndjson> --solution-from-export <Solution.ndjson>
lake comparator --inadvisably-no-sandbox --config <local generated configuration> --challenge-from-export <Challenge.ndjson> --solution-from-export <Solution.ndjson>
leanchecker-paranoid --silent --from-export <Solution.ndjson>
```

The fresh compilation retained fourteen expected Challenge placeholder warnings and 48 pre-existing style-linter warnings (for example unused simplification arguments). These are not missing proofs; the Solution axiom reports contain no `sorryAx`.

The first local Comparator attempt could not start because Git was absent from the runner process PATH. The environment was corrected without changing any Lean source or regenerating old-development artifacts; the already fresh exports were reused only after rechecking all 69 source hashes. Both the startup failure and the corrected run are retained in the checking record.

The local generated configuration names the installed NanoDa and con-ron binaries. It is not the submitted `comparator.json`. The sandboxed Windows attempt and its actual result are retained; the deliberate local fallback is explicitly reported. A successful local replay supplies mathematical evidence, but it does not establish OS-sandbox security or production Palomar acceptance.

Published logs replace local absolute directory prefixes with `<repository>`, `<work>`, `<toolchain>` and dependency-cache placeholders; no command arguments affecting the mathematics are changed. Raw local logs and large exports are kept outside the clean source package. The portable Linux script rebuilds and exports the sources itself rather than trusting those files.

## Independent source and metadata checks

The repository audit checks all sources, not just built modules: module headers, line caps, Challenge size/imports, deliberate placeholders confined to Challenge, forbidden proof-trust constructs, pinned Git revisions, metadata provenance, human author and maintainer fields, classification shape, licence consistency, compiled artifacts, symlinks, Git LFS pointers and size limits. It is a preparation check; Palomar additionally authenticates libraries, parses source headers with Lean, checks taxonomy identifiers, detects the licence, and performs editorial review.

`formalization.yaml` was also tested against the saved official upstream v0.4 JSON schema using a local validator implementing all keywords present in that schema. This is recorded separately from Palomar's profile audit and from a claim of production acceptance.

The Challenge is below the 1,000-line/100-KiB hard limits but exceeds the preferred 300-line auditability threshold because it states thirteen substantial results and their concrete mathematical definitions. The source-only package audit also notes that dependencies are intentionally not vendored. Those notices are not proof failures.

## Scope of the verdict

The fourteen roots are T01--T13 and their conjunction. They certify the exact Lean statements, with at most `propext`, `Classical.choice` and `Quot.sound`. They do not certify all unused intermediate sentences in a particular manuscript proof, historical claims, bibliographical completeness, later manuscript edits, or the subsequently added weighted approximation consequence. See [RESULTS.md](RESULTS.md), [VERIFICATION_SCOPE.md](VERIFICATION_SCOPE.md) and the independent AI statement review.

Current hosted results are available in [GitHub Actions](https://github.com/MColbrook/Proof_of_Kroos_Conjecture/actions). Before submission, run the separate full **Palomar preflight** workflow for the exact intended commit; [PALOMAR.md](PALOMAR.md) gives the steps. The recorded local replay above is distinct from those hosted runs and from Palomar registration.
