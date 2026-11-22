# The four-scale Möbius filter

Let `M(n) = ∑_{1 ≤ j ≤ n} μ(j)` be the Mertens function. For `x ≥ 0` and `N = ⌊4x⌋`, the filter `F` takes the following value throughout the half-open interval `[N/4, (N+1)/4)`.

```text
−M(N) + 5 M(⌊N/2⌋) − 8 M(⌊N/4⌋) + 4 M(⌊N/8⌋).
```

`Filter.lean`, `Grid.lean`, `Jump.lean`, `Intervals.lean`, and `Orbit.lean` establish the grid identity and account for the jumps and both endpoint terms. `Linear.lean` proves the unconditional bound `F(x) ≥ −10x` for every `x > 0`.

`Conclusion.lean` derives a lower bound of order `x^(1/2+ε)` for every `ε > 0` from three explicit hypotheses. These are RH, the truncation error bound `Perron.Truncation` for the four partial sums, and the growth bound `Perron.ReciprocalGrowth` on `1/ζ` for `0 < ε < 1/2`. The compiler log records the theorem's full type. [Compiler log](evidence/filter-audit.log).

`MertensTransfer.lean` gives a second implication. If `a ≥ 0`, `A ≥ 0`, and `|M(n)| ≤ A n^a` for every positive integer `n`, then `|F(x)| ≤ 18 A (4x)^a` for every real `x ≥ 0`. This theorem assumes the stated Mertens bound.

## From the filter to the Riemann hypothesis

`RHFilter.Source.jumps_hasSum` computes the Dirichlet series of the jumps directly from the Möbius coefficients. For `Re s > 1`, `Abel.transform_eq_source` identifies that series with the normalized Mellin transform of the step function. The symbol is `P(z) = −(1−z)(1−2z)²`, where `z = 2^(−s)`. Both factors are nonzero for `1/2 < Re s < 1`. A two-sided estimate `|F(x)| ≤ Cε x^(1/2+ε)` for each positive `ε` extends the transform holomorphically to `Re s > 1/2`. The identity `ζ(s)G(s) = P(2^(−s))` then rules out zeros of ζ in the open strip `1/2 < Re s < 1`. [Series of jumps](JumpSeries.lean) · [Abel summation](AbelEuler.lean) · [Deduction of RH](OwnPath.lean).

## Reproducing the build

With Elan and Git installed, run these commands from the repository root.

```sh
lake exe cache get
lake build FilterResearch
lake env lean filter/OwnPath.lean
```

The recorded build used Lean 4.34.1 and the Mathlib revision pinned in `lakefile.toml`. The build report lists source and binary hashes for 17 modules. The Mertens report records the additional audit of the two transfer theorems. Binary hashes can vary across build environments. [Build report](evidence/filter-build.json) · [Mertens report](evidence/mertens.json).
