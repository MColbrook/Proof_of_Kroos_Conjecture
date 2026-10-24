# Authorship, AI assistance and reviews

Matthew J. Colbrook is the author of the mathematical manuscript. AI agents operating through Codex produced the Lean formalization, checking orchestration, repository packaging and review documents. This distinction is intentional: the source's mathematical authorship is not attributed to an AI system. Exact underlying model revisions were not reliably exposed in the execution records and are not inferred.

## Review boundaries

All reviews distributed here are **AI reviews**. None is presented as independent human peer review. A separate reviewing agent may inspect work by another agent without supplying an independently invented mathematical proof. Source inspection, statement comparison, ordinary Lean checking and external kernel replay are different activities; a report records only the activities it actually performed.

The historical statement-fidelity review compared the frozen manuscript, the actual concrete Lean definitions, and the principal proof interfaces. It checked quantifier order, domains, nonvacuity, real and complex function classes, exact Fourier normalization, the dimension-zero convention, real exponents and uniformity in the body, norm and profile. That reviewer had previously extracted manuscript claims and reviewed the specification; this overlap was disclosed.

The historical proof-trust review inspected the closed analytic and geometric proofs and their axiom boundary. That reviewer had developed checking scripts and made an earlier supporting arithmetic-tactic repair; it did not claim wholly independent tooling authorship. Its report was a source review, not a fresh execution of all checkers. Other AI reviews examined `t07`, proof reuse, auxiliary scope and clarity. Reports completed while final checking was pending retain that historical status; completed checking logs supply the later outcome.

The [repository packaging statement review](reviews/packaging-statement-fidelity-AI.md) is a further source-level review by a separate AI agent. It compares the new self-contained `Challenge.lean` with the previously checked concrete definitions and the frozen manuscript. It does not upgrade the historical local certificate to production Palomar acceptance, nor claim a fresh independent kernel replay.

The [independent packaging and portability review](reviews/packaging-portability-AI.md) additionally checked the repository layout, metadata, dependency pins, verification scripts, Bash syntax, source-package audit and local documentation links. It did not execute the new proof replay or hosted Linux CI.

## Changed Challenge packaging

The earlier local challenge used an independently compiled mirror of the proof graph. That mirror was an import-path copy of the solution proofs, not a second mathematical proof. Historical logs referring to that arrangement must be interpreted accordingly.

The public repository instead supplies a self-contained `Challenge.lean`: its mathematical definitions are unchanged, it imports only Mathlib modules, and its fourteen target theorems have deliberate proof placeholders. The solution imports the proved `Bandlimited` modules and never imports the challenge. This packaging change avoids distributing a duplicate custom proof graph as the specification. Historical evidence applies to the recorded source hashes and configuration; fresh evidence for the new challenge must be distinguished from that earlier run.

## Reuse and attribution

The formalization builds on Lean and Mathlib. Library proof reuse is via the pinned Mathlib imports and named theorems, not unproved literature assumptions or imported custom axioms. Upstream license notices and the pinned dependency revision identify that reuse. `Mathlib/MeasureTheory/Constructions/HaarToSphere.lean`, for example, supplies the canonical sphere measure used by the concrete statements; the source acknowledges it explicitly.

The paper's prior literature supplies mathematical context, as summarized in [RESULTS.md](RESULTS.md). Those works are not unproved mathematical dependencies of the solution. The checks do not determine bibliographic completeness, publication priority, or whether a later result already implies one of the conclusions.

## How to read the evidence

The principal scope is thirteen results and their conjunction; it does not mean every original proof-route sentence has a corresponding Lean lemma. [RESULTS.md](RESULTS.md), [CLAIM_INVENTORY.md](CLAIM_INVENTORY.md) and [VERIFICATION_SCOPE.md](VERIFICATION_SCOPE.md) provide the precise accounting.

The historical Windows Comparator run disabled its operating-system sandbox and printed `WARNING: Sandbox disabled, this run is not trustworthy.` The successful mathematical checking record and independent proof-kernel replays are preserved with that limitation. No production sandbox security, registry acceptance or independent human review is implied. Repository preparation itself neither commits nor publishes the work.
