# Contributing

Use the pinned toolchain and dependencies. Run the commands in the README before proposing a change.

Keep Challenge independent of the proof library. Its only imports may be from the canonical libraries permitted by Palomar, and the mathematical definitions must remain explicit. Deliberate statement placeholders belong only in Challenge; proof holes, custom axioms and native-execution trust must not support Solution.

A statement change requires a separate fidelity review and a fresh Comparator run. A proof change requires a fresh build, axiom report and kernel replay. Update `formalization.yaml`, the result map and scope notes whenever the advertised mathematical content changes. Do not infer source fidelity for a new manuscript revision from an older hash.

Do not add build artifacts, dependency trees, proof exports, local configuration files, credentials, or unrelated documents. The portable CI uses Linux and keeps the Comparator sandbox enabled. Report genuine unsupported checker behaviour rather than weakening the required checks.

Contributions are under the repository's Apache-2.0 licence. Credit reused proofs and preserve applicable third-party notices.
