# Lean proof of symmetric configuration 59₈ nonexistence

The final theorem, [`Symconf59.no_unrestricted_incidence59`](Symconf59/Unrestricted59.lean), excludes a binary 59 × 59 integer incidence matrix with eight ones in every row and column and at most one common one for any distinct pair of rows. It assumes no cyclicity, automorphism, or restriction on the leave-cycle profiles.

The 100 proof modules are the source from the original Lean kernel replay. `SOURCE_FULL_SHA256.txt` binds the proof modules, build order, and audit scripts. The final axiom audit covers 19 declarations and permits only `propext`, `Classical.choice`, and `Quot.sound`.

From the `lean/` directory, with Elan installed:

```sh
sha256sum -c SOURCE_FULL_SHA256.txt
lake exe cache get
lake build
lake env bash verify_full.sh
```

The proof pins Lean 4.31.0-rc1 and Mathlib revision `0ed37c9258f123a2c76a2175596f75c2bd50f941`. The audit builds the full ordered source graph in a fresh temporary directory and checks the final theorem and its axiom dependencies. The formalization was developed with AI assistance.
