/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import Mathlib

/-!
# Graphic sequences: the Erdős–Gallai and Havel–Hakimi theorems

A sequence `d : Fin n → ℕ` is *graphic* (`IsGraphic`) if some simple graph on `Fin n` has degree
`d i` at every vertex `i`.

* `GraphicSequences.isGraphic_iff_erdos_gallai`: **Erdős–Gallai (1960).** A non-increasing sequence
  `d₀ ≥ d₁ ≥ … ≥ d_{n-1}` is graphic if and only if its sum is even and, for every `k ≤ n`,
  `d₀ + … + d_{k-1} ≤ k (k - 1) + ∑_{i ≥ k} min (d_i, k)`.
* `GraphicSequences.isGraphic_iff_havel_hakimi`: **Havel (1955), Hakimi (1962).** A non-increasing
  sequence `d₀ ≥ d₁ ≥ … ≥ d_m` is graphic if and only if `d₀ ≤ m`, the next `d₀` terms are
  positive, and the sequence obtained by deleting `d₀` and subtracting one from the next `d₀`
  terms is graphic (`havelHakimi d`).

The Mathlib definitions used in these statements are reproduced verbatim, with file and line at the
pinned Mathlib revision, in `MATHLIB_DEFINITIONS.md` at the root of this repository.
-/

@[expose] public section

open SimpleGraph Finset

namespace GraphicSequences

/-- `d` is graphic: some simple graph on `Fin n` has degree sequence `d`. -/
def IsGraphic {n : ℕ} (d : Fin n → ℕ) : Prop :=
  ∃ (G : SimpleGraph (Fin n)) (_ : DecidableRel G.Adj), ∀ i, G.degree i = d i

/-- The Havel–Hakimi reduction of `d₀, d₁, …, d_m`: delete `d₀` and subtract one from each of the
next `d₀` terms. -/
def havelHakimi {m : ℕ} (d : Fin (m + 1) → ℕ) : Fin m → ℕ :=
  fun j => if j.val < d 0 then d j.succ - 1 else d j.succ

/-- **Erdős–Gallai theorem (1960).** A non-increasing sequence of natural numbers is the degree
sequence of a simple graph if and only if its sum is even and every initial segment satisfies the
Erdős–Gallai inequality. -/
theorem isGraphic_iff_erdos_gallai {n : ℕ} (d : Fin n → ℕ) (hd : Antitone d) :
    IsGraphic d ↔ Even (∑ i, d i) ∧
      ∀ k ≤ n, ∑ i with i.val < k, d i ≤ k * (k - 1) + ∑ i with k ≤ i.val, min (d i) k := by
  sorry

/-- **Havel–Hakimi theorem (Havel 1955, Hakimi 1962).** A non-increasing sequence `d₀, …, d_m` is
graphic if and only if `d₀ ≤ m`, the terms `d₁, …, d_{d₀}` are positive, and its Havel–Hakimi
reduction is graphic. -/
theorem isGraphic_iff_havel_hakimi {m : ℕ} (d : Fin (m + 1) → ℕ) (hd : Antitone d) :
    IsGraphic d ↔ d 0 ≤ m ∧ (∀ j : Fin m, j.val < d 0 → 1 ≤ d j.succ) ∧
      IsGraphic (havelHakimi d) := by
  sorry

end GraphicSequences
