# From a lower bound on the integer grid to the Riemann hypothesis

The theorem `RHFilter.rh_of_signed_grid_minorant` derives the Riemann hypothesis from one estimate. For each ε > 0, there must be a constant C ≥ 0, independent of N, such that every integer N ≥ 1 satisfies the following inequality. [Lean theorem](SignedClosure.lean).

```text
−C N^(1/2+ε) ≤ −M(N) + 5 M(⌊N/2⌋) − 8 M(⌊N/4⌋) + 4 M(⌊N/8⌋).
```

Here M(N) is the sum of the Möbius function over 1 ≤ n ≤ N. The right-hand side is exactly F(N/4). Since F is constant on each interval [N/4, (N+1)/4), the grid estimate yields the corresponding lower bound for every real x > 0. Proving this uniform bound from the Möbius coefficients remains open for 0 < ε < 1/2.

## How the one-sided bound implies RH

Fix 1/2 < a < 1. The lower bound `F(x) ≥ −C x^a` makes `H(t) = F(t/4) + C t^a` nonnegative for t > 1. With Mellin weight `t^(−s−1)` on (1, ∞), the added term contributes exactly `C/(s−a)`. For `Re s > 1`, the transform of F(t/4) equals `P(2^(−s))/(s ζ(s))`, where `P(z) = −(1−z)(1−2z)²`. Abel summation establishes this identity using every signed jump on the grid. [Shifted function](../filter/LandauSource.lean) · [Abel identity](../filter/AbelEuler.lean).

The nonvanishing of ζ on the real interval (0, 1), together with regularization at its pole at 1, gives the continuation near the real axis that Landau's lemma requires. Applied to H, the lemma gives integrability against `t^(−σ−1)` for every real σ > a. Its Mellin transform is then holomorphic throughout `Re s > a`. Subtracting the compensating term and multiplying by s gives a function G satisfying `ζ(s)G(s) = P(2^(−s))`. The right-hand side is nonzero for `a < Re s < 1`, so ζ has no zeros in that strip. Taking a arbitrarily close to 1/2 from above covers the right half of the critical strip. The functional equation covers the left half. [Continuation on the real axis](../filter/LandauAxis.lean) · [Proof](../filter/OneSidedConverse.lean).

## Dependencies and build instructions

The proof uses three external results. These establish Landau's lemma, holomorphy of the Mellin transform, and the nonvanishing of ζ on the real interval (0, 1). The dependency manifest pins the eight upstream modules by SHA-256. The build uses Lean 4.33.1 and the same Mathlib revision as those upstream sources. [Dependency manifest](upstream.json) · [Landau's lemma and holomorphy](https://github.com/leanprover-community/riemann-hypothesis/blob/40e56bab026552e089d7afcfeff08d2defb9c005/src/Formalism/ZetaNonvanishing/LandauEq.lean) · [Real-axis nonvanishing](https://github.com/leanprover-community/riemann-hypothesis/blob/40e56bab026552e089d7afcfeff08d2defb9c005/src/Formalism/ZetaNonvanishing/ZetaRealNonvanish.lean).

With Python 3, Git, and Elan installed, run these commands from this directory.

```sh
python fetch_landau.py
lake exe cache get
lake build SignedClosure
lake env lean SignedClosure.lean
```

The last command prints the complete types and axioms of the two theorems, one on the real-valued filter and one on the integer grid.

GitHub Actions completed these checks on commit `19d9391`. Both theorem audits report `propext`, `Classical.choice`, and `Quot.sound`. [Verified workflow run](https://github.com/sallyperlastrada-crypto/rh-lean-mobius-filter/actions/runs/45066521543) · [Build record with pinned revisions and log hash](evidence/github-build.json).
