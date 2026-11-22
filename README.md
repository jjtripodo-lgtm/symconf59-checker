# Checker for symmetric configuration 59₈

This is the computational companion to John Tripodo’s six-page manuscript *There is no symmetric configuration 59₈*. The theorem excludes every symmetric incidence configuration with 59 points and 59 lines, eight incidences per point and per line, and at most one common line for any two distinct points.

The replay uses the Python 3 standard library and exact integer and rational arithmetic. From this directory, run:

```sh
sha256sum -c SHA256SUMS
python3 verify59.py
python3 -O verify59.py
python3 -m unittest -v
```

The verifier enumerates 29,269 partitions of 59 into parts of size at least 3. The moment tests retain 15 profiles, and all 12 shift exclusions reduce those to three. The verifier checks both mixed-profile exclusions and the anisotropic kernel form modulo 353 for the single-cycle case. It also checks the determinant and Hasse cross-checks and compares the replay against the three saved JSON certificates. The test suite deliberately corrupts certificate copies and breaks the moment sieve to check that optimized Python still rejects bad inputs.

The saved `sieve59.json` also preserves the historical odd-cycle-filtered diagnostic. Its 12 moment survivors are a separate count from the 15 in the parity-free proof. The current replay covers the full parity-free census.

`SHA256SUMS` records the exact published Python and JSON bytes. The reviewed manuscript source before the public-link and disclosure edits has SHA-256 `53988caa036a1c2043c52d22eefb83a054a7be795f8ba1ebcb6e594aa45620ee`.

## Formal proof

The [standalone Lean project](lean/) contains the full kernel proof. Its final declaration is [`Symconf59.no_unrestricted_incidence59`](lean/Symconf59/Unrestricted59.lean), which states the unrestricted incidence-matrix theorem.
