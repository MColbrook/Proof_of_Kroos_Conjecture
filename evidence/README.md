# Checking evidence

These records apply to the cleaned repository, including its new self-contained Challenge. They do not reuse the old mirrored-Challenge certificate as evidence for this version.

- `local-replay.json`: actual commands, UTC times, exit codes, source identities, compared roots and kernel verdicts.
- `source-hashes.json`: the 69 Lean sources guarded during the fresh replay.
- `compilation.txt`: complete output of all 69 source compilations, in dependency order.
- `axioms.txt`: the fourteen principal `#print axioms` reports.
- `numerical-bounds.txt`: exact numerical/analytic bounds and their axiom reports.
- `comparator.txt`: the successful new Challenge/Solution comparison with Lean, NanoDa and con-ron.
- `comparator-startup-attempts.txt`: the unsupported Windows sandbox attempt and missing-Git startup failure, retained rather than discarded.
- `paranoid.txt`: actual command and exit status of the additional paranoid Lean replay.
- `versions.txt`: actual Lean, Lake and Git version output.
- `exports.txt`: the filtered export commands, exit codes and byte counts.
- `dependency-and-tool-audit.json`: all nine authenticated dependency revisions, clean working-tree checks and installed checking-binary hashes.
- `script-checks.json`: protected configuration generation, Bash failure propagation and PowerShell syntax checks.
- `metadata-schema-validation.json`: validation against the recorded official upstream v0.4 schema; the local validator and its limits are identified.
- `submission-input-hashes.json`: fingerprints of current Lean sources and submission configuration/licence files.
- `package-audit.txt`: source-package and metadata-profile audit output.

Local absolute directory prefixes are replaced by descriptive placeholders in published command/log displays. Mathematical inputs, declaration names, values, output and exit codes are unchanged. Raw local logs and large proof exports remain outside this source package.

Windows does not provide the required Linux namespaces. The successful local comparison explicitly disabled that OS sandbox, and its warning is retained verbatim. The public Linux workflow keeps the sandbox enabled and has not yet been executed on GitHub. Neither these files nor AI reviews constitute Palomar acceptance or human peer review.
