# Dal minorante sulla griglia all'ipotesi di Riemann

Il teorema finale in [SignedClosure.lean](SignedClosure.lean) richiede una stima su una funzione esplicita degli interi. Per ogni ε > 0 occorre una costante non negativa C, indipendente da N, tale che per tutti gli N ≥ 1 valga

```text
−C N^(1/2+ε) ≤ −M(N) + 5 M(⌊N/2⌋) − 8 M(⌊N/4⌋) + 4 M(⌊N/8⌋).
```

Qui M è la somma inclusiva della funzione di Möbius. Il raccordo esatto identifica questo valore con F(N/4) e trasporta la stima a tutti i reali x > 0. Il minorante uniforme è la premessa aritmetica da dimostrare.

## Il passaggio che usa soltanto il minorante

Fissato 1/2 < a < 1, la premessa F(x) ≥ −C x^a rende non negativa su t > 1 la funzione H(t) = F(t/4) + C t^a. Nella convenzione di Mellin con peso t^(−s−1), il compensatore contribuisce esattamente C/(s−a). La trasformata iniziale di F(t/4) è P(2^(−s))/(s ζ(s)), dove P(z) = −(1−z)(1−2z)². Questa identità si dimostra per Re s > 1 utilizzando ogni salto firmato della griglia. [Sorgente](../filter/LandauSource.lean) · [Identità di Abel](../filter/AbelEuler.lean).

Il non annullamento reale di ζ su (0,1) e la regolarizzazione del polo in 1 danno la continuazione nei pressi dell'asse reale richiesta dal lemma di Landau. Applicato ad H, il lemma dà l'integrabilità su ogni retta reale σ > a. La trasformata è quindi olomorfa nel semipiano Re s > a. Togliendo il compensatore e moltiplicando per s si ottiene G con ζG = P(2^(−s)). Poiché il simbolo è diverso da zero per a < Re s < 1, anche ζ è diversa da zero in quella striscia. Gli esponenti a possono avvicinarsi a 1/2. L'equazione funzionale tratta l'altro lato. [Regolarizzazione](../filter/LandauAxis.lean) · [Dimostrazione](../filter/OneSidedConverse.lean).

## Dipendenze e riproduzione

I tre risultati esterni sono il lemma di Landau, l'olomorfia della trasformata e il non annullamento sull'intervallo reale (0,1). I loro otto moduli transitivi sono fissati per SHA-256 in [upstream.json](upstream.json). La prova usa Lean 4.33.1 e la stessa revisione di Mathlib dei sorgenti originali. [Landau e olomorfia](https://github.com/leanprover-community/riemann-hypothesis/blob/40e56bab026552e089d7afcfeff08d2defb9c005/src/Formalism/ZetaNonvanishing/LandauEq.lean) · [Non annullamento reale](https://github.com/leanprover-community/riemann-hypothesis/blob/40e56bab026552e089d7afcfeff08d2defb9c005/src/Formalism/ZetaNonvanishing/ZetaRealNonvanish.lean).

Da questa directory, con Python 3, Git ed Elan, eseguire

```sh
python fetch_landau.py
lake exe cache get
lake build SignedClosure
lake env lean SignedClosure.lean
```

L'ultimo comando stampa il tipo completo e gli assiomi dei due teoremi sul filtro reale e sulla griglia intera.

GitHub Actions ha completato questa sequenza sul commit `19d9391`. Entrambi gli audit riportano `propext`, `Classical.choice` e `Quot.sound`. [Esecuzione verificata](https://github.com/sallyperlastrada-crypto/rh-lean-filtro-mobius/actions/runs/45066521543) · [Verbale con revisioni e impronta del log](evidence/github-build.json).
