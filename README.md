# Graphic sequences: the Erdős–Gallai and Havel–Hakimi theorems in Lean 4

Author and maintainer: **Juan Pablo Traverso Gianini**. Licence: Apache-2.0 (see `LICENSE`).

A sequence `d : Fin n → ℕ` is *graphic* when some simple graph on `Fin n` has degree `d i` at
every vertex `i`. This repository formalizes two characterizations of graphic sequences:

1. **Erdős–Gallai (1960)** (`GraphicSequences.isGraphic_iff_erdos_gallai`). A non-increasing
   sequence `d₀ ≥ … ≥ d_{n−1}` is graphic if and only if:
   - its sum is even, and
   - for every `k ≤ n`, `d₀ + … + d_{k−1} ≤ k(k − 1) + ∑_{i ≥ k} min(d_i, k)`.
2. **Havel (1955), Hakimi (1962)** (`GraphicSequences.isGraphic_iff_havel_hakimi`). A non-increasing
   sequence `d₀ ≥ … ≥ d_m` is graphic if and only if:
   - `d₀ ≤ m`;
   - the terms `d₁, …, d_{d₀}` are positive; and
   - the reduced sequence is graphic. The reduced sequence is obtained by deleting `d₀` and
     subtracting one from the next `d₀` terms.

## Files

- [`Challenge.lean`](Challenge.lean): the audited statements. It imports only Mathlib.
- [`Solution.lean`](Solution.lean) and
  [`DegreeSeqLib/DegreeSequences.lean`](DegreeSeqLib/DegreeSequences.lean): the proofs.
- [`comparator.json`](comparator.json): the theorems that are compared.
- [`MATHLIB_DEFINITIONS.md`](MATHLIB_DEFINITIONS.md): verbatim copies of the Mathlib definitions
  used.
- [`formalization.yaml`](formalization.yaml): provenance, sources and process.

## How the proofs go

* **Havel–Hakimi.**
  - Adding a vertex joined to the first `d₀` vertices of a realization of the reduced sequence
    realizes `d`.
  - Conversely, a switch replaces edges `0k, iw` by `0i, kw` whenever `deg k ≤ deg i`. Repeated
    switches make vertex `0` adjacent to exactly `1, …, d₀`. Deleting vertex `0` then realizes
    the reduced sequence.
* **Erdős–Gallai, necessity.** The sum of the degrees is twice the number of edges. For the
  inequality, the first `k` vertices carry at most `k(k − 1)` degree inside themselves, and each
  later vertex `i` contributes at most `min(d_i, k)`.
* **Erdős–Gallai, sufficiency.** The proof follows Choudum (1986), by strong induction on the
  sum of the sequence.
  1. Subtract one from two well-chosen terms. The result is still non-increasing, and it still
     satisfies the conditions.
  2. Realize the reduced sequence by induction.
  3. Add the edge between the two vertices, or perform a switch.

## Sources

* P. Erdős, T. Gallai, *Gráfok előírt fokú pontokkal* (Graphs with prescribed degrees of
  vertices), Mat. Lapok 11 (1960) 264–274.
* V. Havel, *A remark on the existence of finite graphs*, Časopis Pěst. Mat. 80 (1955) 477–480,
  doi:10.21136/CPM.1955.108220.
* S. L. Hakimi, *On realizability of a set of integers as degrees of the vertices of a linear
  graph. I*, J. SIAM 10 (1962) 496–506, doi:10.1137/0110037.
* S. A. Choudum, *A simple proof of the Erdős–Gallai theorem on graph sequences*, Bull. Austral.
  Math. Soc. 33 (1986) 67–70, doi:10.1017/S0004972700002872.

## Authorship and use of AI

The author chose the results. The statements and proof plans were written with Claude in Claude
Code. Harmonic's Aristotle produced the proofs, which were audited and rebuilt locally. Lean
checks everything mechanically. See `formalization.yaml`.

## Building

Lean `v4.35.0-rc3`, Mathlib `c55e6e786f49471c72fbddbec5415808896aec1e`:

```bash
lake exe cache get
lake build
```
