# There is no symmetric configuration 59₈

This Lean project verifies the nonexistence of a symmetric incidence configuration with 59 points and 59 lines, eight incidences at each point and line, and at most one line through any two distinct points. `Challenge.lean` states the theorem as an explicit condition on binary integer matrices. `Solution.lean` proves it using the ported original proof.

- [Paper on Hexagon](https://hexagonmath.org/2611.00901v1)
- [Original Lean proof and Python checker](https://github.com/jjtripodo-lgtm/symconf59-checker/tree/71db581317719397e01fa182cdce91358a444b0b)

The project pins Lean 4.35.0-rc2 and Mathlib. Build the two targets with `lake build Challenge Solution` and compare them with `lake comparator --config comparator.json --paranoid`. The mechanical preflight runs Palomar's pinned verification workflow.

The formalization and port used AI assistance. See `formalization.yaml` for provenance and review scope. This release is licensed under Apache-2.0.
