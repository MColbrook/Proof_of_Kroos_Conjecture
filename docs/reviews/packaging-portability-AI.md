# Repository packaging and portability review — AI

Date: 24 October 2026.

This is a source-level review by a separate Codex AI agent. The reviewer previously performed a read-only audit of the original proof project's dependency closure, pinned dependency working trees, checking binaries and scripts. It did not construct the new repository, modify its mathematical proofs, or edit the manuscript. That prior audit role is disclosed rather than treated as complete independence from the project.

## Material inspected

The review inspected README.md, formalization.yaml, lakefile.toml, lake-manifest.json, comparator.json, LICENSE, NOTICE, the self-contained Challenge and Solution import interfaces, the source audit, both public verification scripts, GitHub Actions configuration, source/version and reuse documentation, ignore rules, and line-ending rules. It also checked local Markdown links throughout the repository.

The new Challenge imports only canonical Mathlib modules. Its fourteen deliberate statement placeholders are confined to the specification; Solution imports the proved Bandlimited development. The configuration compares the thirteen principal declarations and their conjunction and permits only propext, Classical.choice and Quot.sound. The exact statements and their mathematical interpretation remain the subject of the separate statement-fidelity review.

The Lakefile and committed manifest have matching root names and Mathlib pins. The nine dependency revisions match the independently inspected clean upstream working trees. No cached proof artifacts, duplicate Challenge proof graph, hardcoded personal cache path, or parent-manuscript dependency appears in the public build procedure. Attribution and the Apache-2.0 project licence agree with the metadata and documentation.

## Actual checks

The reviewer ran scripts/audit.py using the bundled Python executable. It reported:

```text
WARNING: Challenge exceeds Palomar's 32 KiB/300 line auditability warning threshold
WARNING: Mathlib is not yet fetched; Palomar authenticates the pin and its exact toolchain independently
Package audit passed: 69 Lean sources; 97 source-package files; 676064 bytes.
This local audit is preparation evidence, not a Palomar verification or editorial decision.
```

The counts describe the repository at review time, before this review file and any final checking records were added. Neither warning indicates a mathematical proof failure. The Challenge remains below the documented hard limits; dependency sources are intentionally not vendored.

An independent local Markdown-link scan reported no missing repository targets. Git Bash `bash -n scripts/verify.sh` returned exit code 0. The first attempt to invoke `python` by its short name failed because Python was absent from this machine's PATH; the successful audit used the available bundled executable. The README explicitly requires Python 3.11 or later.

## Portability and trust boundaries

The Linux wrapper requires bubblewrap and the checking binaries, uses a protected temporary configuration for external kernels, enables shell failure propagation, and does not silently disable the sandbox. The native Windows wrapper explicitly limits its opt-in BuildOnly mode to ordinary Lean checking and reports that Comparator and independent kernel replay have not run. Its default invocation refuses to imply full sandboxed verification.

The workflow pins its actions, requests read-only repository permissions, and prepares the disposable Linux runner for bubblewrap. The reviewer inspected this procedure but did not execute GitHub Actions, a Linux build, the sandboxed Comparator, or the new mathematical proof replay. Those results must come from actual checking logs and cannot be inferred from this review. The documentation correctly distinguishes the prepared portable workflow, local Windows evidence, source-fidelity review, and eventual Palomar review.

No blocking packaging or portability issue was found in the inspected source. This is an AI preparation review, not Palomar acceptance, an independently executed CI result, or independent human peer review.
