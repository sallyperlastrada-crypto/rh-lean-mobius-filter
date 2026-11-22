# Filtro di Möbius su quattro scale

Per `N = ⌊4x⌋` e `M(n) = ∑_{1 ≤ j ≤ n} μ(j)`, il valore di `F` sulla cella `[N/4,(N+1)/4)` è

```text
−M(N) + 5 M(⌊N/2⌋) − 8 M(⌊N/4⌋) + 4 M(⌊N/8⌋).
```

`Filter.lean`, `Grid.lean`, `Jump.lean`, `Intervals.lean` e `Orbit.lean` verificano l'identità, i salti e i termini ai due estremi. `Linear.lean` dimostra in particolare `F(x) ≥ −10x` per `x > 0`.

`Conclusion.lean` deduce il minorante di ordine `x^(1/2+ε)` per ogni `ε > 0` da tre premesse esplicite. La prima è RH. Le altre due sono `Perron.Truncation`, per l'errore di troncamento dei quattro prefissi, e una stima `Perron.ReciprocalGrowth` su `1/ζ` per `0 < ε < 1/2`. Il tipo completo del teorema si legge nel [log del compilatore](evidence/filter-audit.log).

`MertensTransfer.lean` dà una seconda deduzione. Per `a ≥ 0`, `A ≥ 0` e `|M(n)| ≤ A n^a` su tutti gli interi positivi, si ha `|F(x)| ≤ 18 A (4x)^a` su tutti i reali `x ≥ 0`. La stima di Mertens figura tra le premesse.

## Verifica

Da questa directory, con Elan e Git installati, eseguire

```sh
lake update
lake exe cache get
lake build SourceFilter
```

La compilazione registrata ha usato Lean 4.34.1 con Mathlib al commit fissato in `lakefile.toml`. Il [rapporto dei 17 moduli](evidence/filter-build.json) contiene gli hash dei sorgenti e dei binari. Il [rapporto Mertens](evidence/mertens.json) contiene l'audit aggiuntivo dei due teoremi di trasferimento. I binari possono differire tra ambienti di compilazione.
