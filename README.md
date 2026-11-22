# The Riemann hypothesis from a lower bound for the Möbius filter F

The Lean theorem `RHFilter.rh_of_signed_grid_minorant` proves that a uniform lower bound on a signed sum of four Mertens function values implies the Riemann hypothesis (RH). **Proving the lower bound for every 0 < ε < 1/2 remains open in this approach.**

Let M(N) be the sum of the Möbius function μ(n) over 1 ≤ n ≤ N, with M(0) = 0. The hypothesis is that for every ε > 0 there exists C ≥ 0 such that, for every integer N ≥ 1,

```text
−C N^(1/2+ε) ≤ −M(N) + 5 M(⌊N/2⌋) − 8 M(⌊N/4⌋) + 4 M(⌊N/8⌋).
```

The right-hand side is exactly F(N/4). Lean 4.33.1 verified the implication both for this integer grid and for F on the positive real axis. The axiom audit for each theorem lists `propext`, `Classical.choice`, and `Quot.sound`. [Lean statements](one-sided/SignedClosure.lean) · [Verified GitHub build](https://github.com/sallyperlastrada-crypto/rh-lean-mobius-filter/actions/runs/45066521543) · [Instructions for reproducing the build](one-sided/README.md).

The two-sided version, `RHFilter.rh_of_bilateral_filter`, assumes a bound on the absolute value of F. Run the following commands from the repository root to reproduce that build.

```sh
lake exe cache get
lake build FilterResearch
lake env lean filter/OwnPath.lean
```

## Relationship to the external proof

The proof from the one-sided lower bound uses three analytic lemmas from the Alpöge–Claude sources. Their dependencies span eight modules. The signed lower bound above is the arithmetic hypothesis of the filter theorem. [Dependency revisions and hashes](one-sided/upstream.json) · [Build record](one-sided/evidence/github-build.json).

A separate file declares `RHDeposit.riemannHypothesis : RiemannHypothesis`. Its arithmetic input is the Dirichlet L-function nonvanishing theorem of **Levent Alpöge with Claude**. This proof uses that theorem and reflection alone, independently of F. [Declaration](ClosedRH.lean) · [Pinned upstream source at commit `40e56bab`](https://github.com/leanprover-community/riemann-hypothesis/blob/40e56bab026552e089d7afcfeff08d2defb9c005/src/Main.lean).

1. `RHReduction.of_every_character` specializes the external theorem to the character modulo one. Its L-function equals ζ, so ζ is nonzero for `Re s > 1/2`, away from its pole.
2. For a nontrivial zero to the left of the critical line, `RHReduction.completed_zero_of_nontrivial` passes to the completed zeta function. The proof treats `s = 0` and the points `−2, −4, …` before dividing by the gamma factor.
3. The functional equation gives a reflected zero at `1 − s` in the half-plane already excluded. Every nontrivial zero therefore satisfies `Re s = 1/2`. The formalization uses Mathlib's definitions. [Lean reduction](RHReduction.lean).

## Verification status of the external route

| Component | Evidence |
| --- | --- |
| Alpöge–Claude arithmetic theorem | External verification checked the theorem against Mathlib's specification. The theorem's axiom audit lists `propext`, `Classical.choice`, and `Quot.sound`. [MIT verification](https://math.mit.edu/~drew/grh/) |
| Deduction from nonvanishing modulo one | The four theorems in the reduction compiled and their axioms were audited. [Lean source](RHReduction.lean) · [Local verification records](evidence/) |
| Upstream theorem signature | `SignatureAudit.lean` states the reduction as an implication. Running `python verify_upstream.py` compares the signature with the pinned source and verifies the SHA-256 hash of the MIT log. [Signature audit](SignatureAudit.lean) |
| Final application `RHDeposit.riemannHypothesis` | The declaration has no explicit mathematical hypotheses. An integrated build of this module with the full upstream `Main` remains outstanding. |

To run the optional build with the full external proof, start from the repository root.

```sh
cd external
lake update
lake build ClosedRH
lake env lean ../ClosedRH.lean
```

The final command prints the axioms of the imported declaration. This project pins Lean `v4.33.1`. The upstream documentation gives the storage requirements and the steps for checking the proof export. [Precompiled distribution](https://proofsandreasons.io/rh-oleans.html) · [Export verification instructions](https://math.mit.edu/~drew/grh/).

## Results for the filter F

The filter project uses Lean `v4.34.1` for its grid, endpoint, jump, and telescoping identities and for its deductions about the lower bound. For `0 < ε < 1/2`, its Perron argument still requires a quantitative truncation estimate and a subpower growth bound on `1/ζ`. [Filter project and verified results](filter/README.md).
