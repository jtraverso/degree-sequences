/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import Mathlib
public import DegreeSeqLib.DegreeSequences

/-!
# Proofs of the statements in `Challenge.lean`

The definitions below are verbatim copies of those in `Challenge.lean`; they coincide with those
of `DegreeSeqLib/DegreeSequences.lean` (namespace `DegreeSequences`), where the theorems are
proved: Havel–Hakimi by an edge-switching argument, and Erdős–Gallai (necessity by counting the
edges at an initial segment, sufficiency by Choudum's induction on the sum of the sequence).
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
      ∀ k ≤ n, ∑ i with i.val < k, d i ≤ k * (k - 1) + ∑ i with k ≤ i.val, min (d i) k :=
  DegreeSequences.isGraphic_iff_erdos_gallai d hd

/-- **Havel–Hakimi theorem (Havel 1955, Hakimi 1962).** A non-increasing sequence `d₀, …, d_m` is
graphic if and only if `d₀ ≤ m`, the terms `d₁, …, d_{d₀}` are positive, and its Havel–Hakimi
reduction is graphic. -/
theorem isGraphic_iff_havel_hakimi {m : ℕ} (d : Fin (m + 1) → ℕ) (hd : Antitone d) :
    IsGraphic d ↔ d 0 ≤ m ∧ (∀ j : Fin m, j.val < d 0 → 1 ≤ d j.succ) ∧
      IsGraphic (havelHakimi d) :=
  DegreeSequences.isGraphic_iff_havel_hakimi d hd

end GraphicSequences
