# Percorso verso RH con il filtro di Möbius F

La funzione a gradini `F` è definita dai prefissi firmati di Möbius. Il teorema `RHFilter.rh_of_bilateral_filter` deduce l'ipotesi di Riemann da una stima di `|F|` di ordine `x^(1/2+ε)` per ogni ε positivo. Il suo termine di prova usa il simbolo del filtro, la trasformata di Mellin della griglia esatta e l'equazione funzionale. La dimostrazione aritmetica della stima resta aperta. [Percorso Lean](filter/OwnPath.lean) · [Griglia e bordi](filter/README.md).

Per compilare il percorso del filtro dalla radice, con la versione di Lean e la revisione di Mathlib fissate nel repository, eseguire

```sh
lake exe cache get
lake build FilterResearch
lake env lean filter/OwnPath.lean
```

## Riscontro con la prova esterna

Il [raccordo monolaterale](one-sided/README.md) impiega otto moduli esterni per il passaggio dal minorante di F all'olomorfia della trasformata positiva. La sua compilazione integrata è in verifica.

[`ClosedRH.lean`](ClosedRH.lean) dichiara `RHDeposit.riemannHypothesis : RiemannHypothesis`. L'apporto aritmetico di questo riscontro è di **Levent Alpöge con Claude**. Il termine di prova applica la riduzione per riflessione al loro teorema di non annullamento delle funzioni L di Dirichlet. Il filtro F non compare nella sua dimostrazione. La dipendenza è fissata al [commit `40e56bab`](https://github.com/leanprover-community/riemann-hypothesis/blob/40e56bab026552e089d7afcfeff08d2defb9c005/src/Main.lean).

1. `RHReduction.of_every_character` specializza il teorema esterno al carattere modulo uno. La sua funzione L coincide con ζ. Ne segue il non annullamento di ζ per `Re s > 1/2`, escluso il polo.
2. Per uno zero non banale a sinistra della linea, `RHReduction.completed_zero_of_nontrivial` passa alla funzione completata. La prova tratta `s = 0` e i punti `−2, −4, …` prima della divisione per il fattore Gamma.
3. L'equazione funzionale dà uno zero riflesso in `1 − s`, nel semipiano già escluso. Resta `Re s = 1/2`. La [riduzione Lean](RHReduction.lean) usa le definizioni di Mathlib.

## Stato della verifica

| Componente | Evidenza |
| --- | --- |
| Teorema aritmetico di Alpöge–Claude | Verificato esternamente contro la specifica di Mathlib. L'audit del singolo teorema riporta `propext`, `Classical.choice`, `Quot.sound`. [Verifiche MIT](https://math.mit.edu/~drew/grh/) |
| Deduzione dal non annullamento modulo uno | Compilazione e audit dei quattro teoremi in [`RHReduction.lean`](RHReduction.lean). [Verifiche locali](evidence/) |
| Firma della dipendenza | [`SignatureAudit.lean`](SignatureAudit.lean) enuncia il raccordo come implicazione. `python verify_upstream.py` confronta la firma con il sorgente al commit fissato e verifica lo SHA-256 del log MIT. |
| Applicazione finale `RHDeposit.riemannHypothesis` | Sorgente senza ipotesi matematiche esplicite. La compilazione integrata del nuovo modulo con l'intero `Main` esterno resta da eseguire. |

Per ripetere la build facoltativa che importa l'intera prova esterna, eseguire dalla radice

```sh
cd external
lake update
lake build ClosedRH
lake env lean ../ClosedRH.lean
```

L'ultimo comando stampa gli assiomi della dichiarazione effettivamente importata. Il progetto fissa Lean `v4.33.1`. Le [dimensioni della distribuzione precompilata](https://proofsandreasons.io/rh-oleans.html) e le [istruzioni per ripetere il controllo dell'esportazione](https://math.mit.edu/~drew/grh/) descrivono i requisiti della verifica esterna.

## Risultati sul filtro F

Il [progetto `filter/`](filter/README.md) conserva la propria versione verificata di Lean, `v4.34.1`. Comprende griglia, bordi, salti, telescopia e raccordi al minorante. Nel regime `0 < ε < 1/2` la sua via di Perron richiede ancora la troncatura quantitativa e la crescita subpotenza di `1/ζ`. La deduzione di RH in `ClosedRH` usa il teorema esterno e procede indipendentemente dal minorante di F.
