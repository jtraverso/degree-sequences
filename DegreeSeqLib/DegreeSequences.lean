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

* `DegreeSequences.isGraphic_iff_erdos_gallai`: **Erdős–Gallai (1960).** A non-increasing sequence
  `d₀ ≥ d₁ ≥ … ≥ d_{n-1}` is graphic if and only if its sum is even and, for every `k ≤ n`,
  `d₀ + … + d_{k-1} ≤ k (k - 1) + ∑_{i ≥ k} min (d_i, k)`.
* `DegreeSequences.isGraphic_iff_havel_hakimi`: **Havel (1955), Hakimi (1962).** A non-increasing
  sequence `d₀ ≥ d₁ ≥ … ≥ d_m` is graphic if and only if `d₀ ≤ m`, the next `d₀` terms are
  positive, and the sequence obtained by deleting `d₀` and subtracting one from the next `d₀`
  terms is graphic (`havelHakimi d`).
-/

@[expose] public section

open SimpleGraph Finset

namespace DegreeSequences

/-- `d` is graphic: some simple graph on `Fin n` has degree sequence `d`. -/
def IsGraphic {n : ℕ} (d : Fin n → ℕ) : Prop :=
  ∃ (G : SimpleGraph (Fin n)) (_ : DecidableRel G.Adj), ∀ i, G.degree i = d i

/-- The Havel–Hakimi reduction of `d₀, d₁, …, d_m`: delete `d₀` and subtract one from each of the
next `d₀` terms. -/
def havelHakimi {m : ℕ} (d : Fin (m + 1) → ℕ) : Fin m → ℕ :=
  fun j => if j.val < d 0 then d j.succ - 1 else d j.succ

lemma degree_eq_sum_ite {V : Type*} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj] (v : V) :
    G.degree v = ∑ w, if G.Adj v w then 1 else 0 := by
  rw [← card_neighborFinset_eq_degree, neighborFinset_eq_filter, Finset.card_filter]

/-- Edit a graph: remove the edges in `R`, add the pairs in `A`. -/
def editGraph {V : Type*} (G : SimpleGraph V) (R A : Finset (Sym2 V)) : SimpleGraph V where
  Adj x y := x ≠ y ∧ ((G.Adj x y ∧ s(x, y) ∉ R) ∨ s(x, y) ∈ A)
  symm := ⟨by
    intro x y h
    obtain ⟨h1, h2⟩ := h
    refine ⟨h1.symm, ?_⟩
    have hs : s(y, x) = s(x, y) := Sym2.eq_swap
    rw [hs]
    rcases h2 with ⟨h2, h3⟩ | h2
    · exact Or.inl ⟨h2.symm, h3⟩
    · exact Or.inr h2⟩
  loopless := ⟨fun x h => h.1 rfl⟩

lemma sum_ite_sym2_eq {V : Type*} [Fintype V] [DecidableEq V] (v : V) (e : Sym2 V)
    (he : ¬ e.IsDiag) :
    (∑ w, if s(v, w) = e then 1 else 0) = if v ∈ e then 1 else 0 := by
  induction e using Sym2.ind with
  | _ a b =>
  have hab : a ≠ b := by simpa using he
  by_cases hva : v = a
  · subst hva
    rw [Finset.sum_eq_single b]
    · simp
    · intro w _ hw
      simp [hw, hab]
    · simp
  by_cases hvb : v = b
  · subst hvb
    rw [Finset.sum_eq_single a]
    · simp [Sym2.eq_swap]
    · intro w _ hw
      simp [hw, hva]
    · simp
  · rw [Finset.sum_eq_zero]
    · simp [hva, hvb]
    · intro w _
      simp [hva, hvb]

lemma sum_ite_mem_finset {V : Type*} [Fintype V] [DecidableEq V] (v : V) (R : Finset (Sym2 V))
    (hR : ∀ e ∈ R, ¬ e.IsDiag) :
    (∑ w, if s(v, w) ∈ R then 1 else 0) = ∑ e ∈ R, if v ∈ e then 1 else 0 := by
  have : ∀ w, (if s(v, w) ∈ R then 1 else 0) = ∑ e ∈ R, if s(v, w) = e then 1 else 0 := by
    intro w
    rw [Finset.sum_ite_eq]
  simp_rw [this]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun e he => sum_ite_sym2_eq v e (hR e he)

lemma degree_editGraph {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (R A : Finset (Sym2 V)) [DecidableRel (editGraph G R A).Adj]
    (hR : ∀ e ∈ R, e ∈ G.edgeSet) (hA : ∀ e ∈ A, e ∉ G.edgeSet ∧ ¬ e.IsDiag) (v : V) :
    (editGraph G R A).degree v + ∑ e ∈ R, (if v ∈ e then 1 else 0) =
      G.degree v + ∑ e ∈ A, (if v ∈ e then 1 else 0) := by
  rw [← sum_ite_mem_finset v R (fun e he => G.not_isDiag_of_mem_edgeSet (hR e he)),
    ← sum_ite_mem_finset v A (fun e he => (hA e he).2), degree_eq_sum_ite, degree_eq_sum_ite,
    ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun w _ => ?_
  have h1 : s(v, w) ∈ R → G.Adj v w := fun h => hR _ h
  have h2 : s(v, w) ∈ A → ¬ G.Adj v w ∧ v ≠ w := fun h =>
    ⟨(hA _ h).1, by simpa using (hA _ h).2⟩
  have h3 : G.Adj v w → v ≠ w := G.ne_of_adj
  simp only [editGraph]
  by_cases a : G.Adj v w <;> by_cases b : s(v, w) ∈ R <;> by_cases c : s(v, w) ∈ A <;>
    by_cases d : v = w <;> simp_all


lemma degree_fin_succ {m : ℕ} (G : SimpleGraph (Fin (m + 1))) [DecidableRel G.Adj]
    (v : Fin (m + 1)) :
    G.degree v = (if G.Adj v 0 then 1 else 0) + #{w : Fin m | G.Adj v w.succ} := by
  rw [← card_neighborFinset_eq_degree, neighborFinset_eq_filter, Fin.card_filter_univ_succ']

/-- The graph obtained from `H` by adding a new vertex `0` joined to the first `d 0` vertices. -/
def hhExtend {m : ℕ} (d : Fin (m + 1) → ℕ) (H : SimpleGraph (Fin m)) :
    SimpleGraph (Fin (m + 1)) :=
  SimpleGraph.fromRel fun v w =>
    (v = 0 ∧ ∃ j : Fin m, w = j.succ ∧ j.val < d 0) ∨
      (∃ j k : Fin m, v = j.succ ∧ w = k.succ ∧ H.Adj j k)

lemma hhExtend_adj_zero_zero {m : ℕ} (d : Fin (m + 1) → ℕ) (H : SimpleGraph (Fin m)) :
    ¬ (hhExtend d H).Adj 0 0 := (hhExtend d H).loopless.irrefl 0

lemma hhExtend_adj_zero_succ {m : ℕ} (d : Fin (m + 1) → ℕ) (H : SimpleGraph (Fin m))
    (j : Fin m) : (hhExtend d H).Adj 0 j.succ ↔ j.val < d 0 := by
  simp [hhExtend, (Fin.succ_ne_zero _).symm]

lemma hhExtend_adj_succ_succ {m : ℕ} (d : Fin (m + 1) → ℕ) (H : SimpleGraph (Fin m))
    (j k : Fin m) : (hhExtend d H).Adj j.succ k.succ ↔ H.Adj j k := by
  simp only [hhExtend, fromRel_adj, ne_eq, Fin.succ_inj, Fin.succ_ne_zero, false_and,
    exists_and_left, exists_eq_left', false_or]
  exact ⟨fun h => h.2.elim id fun h' => h'.symm, fun h => ⟨H.ne_of_adj h, Or.inl h⟩⟩

lemma isGraphic_of_havelHakimi {m : ℕ} (d : Fin (m + 1) → ℕ) (h0 : d 0 ≤ m)
    (hpos : ∀ j : Fin m, j.val < d 0 → 1 ≤ d j.succ) (hH : IsGraphic (havelHakimi d)) :
    IsGraphic d := by
  classical
  obtain ⟨H, _, hH⟩ := hH
  refine ⟨hhExtend d H, inferInstance, fun v => ?_⟩
  rw [degree_fin_succ]
  induction v using Fin.cases with
  | zero =>
    simp only [hhExtend_adj_zero_zero, ite_false, zero_add, hhExtend_adj_zero_succ]
    rw [Fin.card_filter_val_lt]
    omega
  | succ j =>
    have h1 : (hhExtend d H).Adj j.succ 0 ↔ j.val < d 0 := by
      rw [(hhExtend d H).adj_comm, hhExtend_adj_zero_succ]
    simp only [h1, hhExtend_adj_succ_succ]
    have h2 : #{k : Fin m | H.Adj j k} = H.degree j := by
      rw [← card_neighborFinset_eq_degree, neighborFinset_eq_filter]
    rw [h2, hH j]
    unfold havelHakimi
    have := hpos j
    split_ifs <;> omega


lemma exists_switch {V : Type*} [Fintype V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (a i k : V) (hai : a ≠ i) (hdeg : G.degree k ≤ G.degree i)
    (hai' : ¬ G.Adj a i) (hak : G.Adj a k) :
    ∃ (G' : SimpleGraph V) (_ : DecidableRel G'.Adj), (∀ v, G'.degree v = G.degree v) ∧
      ∀ v, (G'.Adj a v ↔ (v ≠ k ∧ G.Adj a v) ∨ v = i) := by
  classical
  have hik : i ≠ k := fun h => hai' (h ▸ hak)
  have hak' : a ≠ k := hak.ne
  have hia : ¬ G.Adj i a := fun h => hai' h.symm
  obtain ⟨w, hiw, hkw, hwk⟩ : ∃ w, G.Adj i w ∧ ¬ G.Adj k w ∧ w ≠ k := by
    by_contra hcon
    push Not at hcon
    by_cases hik' : G.Adj i k
    · have hsub : (G.neighborFinset i).erase k ⊆ ((G.neighborFinset k).erase a).erase i := by
        intro w hw
        simp only [mem_erase, mem_neighborFinset] at hw ⊢
        refine ⟨fun h => ?_, fun h => ?_, ?_⟩
        · subst h; exact G.loopless.irrefl _ hw.2
        · subst h; exact hia hw.2
        · by_contra h; exact hw.1 (hcon w hw.2 h)
      have h1 := card_le_card hsub
      have h2 : a ∈ G.neighborFinset k := by simpa using hak.symm
      have h3 : i ∈ (G.neighborFinset k).erase a := by simpa using ⟨hai.symm, hik'.symm⟩
      have h4 : k ∈ G.neighborFinset i := by simpa using hik'
      rw [card_erase_of_mem h4, card_erase_of_mem h3, card_erase_of_mem h2,
        card_neighborFinset_eq_degree, card_neighborFinset_eq_degree] at h1
      have h5 : 0 < G.degree i := by
        rw [← card_neighborFinset_eq_degree]; exact card_pos.mpr ⟨k, h4⟩
      have h6 : 1 < G.degree k := by
        rw [← card_neighborFinset_eq_degree]
        exact one_lt_card.mpr ⟨a, h2, i, (mem_erase.mp h3).2, hai⟩
      omega
    · have hsub : G.neighborFinset i ⊆ (G.neighborFinset k).erase a := by
        intro w hw
        simp only [mem_erase, mem_neighborFinset] at hw ⊢
        refine ⟨fun h => ?_, ?_⟩
        · subst h; exact hia hw
        · by_contra h; exact hik' (hcon w hw h ▸ hw)
      have h1 := card_le_card hsub
      have h2 : a ∈ G.neighborFinset k := by simpa using hak.symm
      rw [card_erase_of_mem h2, card_neighborFinset_eq_degree,
        card_neighborFinset_eq_degree] at h1
      have h6 : 0 < G.degree k := by
        rw [← card_neighborFinset_eq_degree]; exact card_pos.mpr ⟨a, h2⟩
      omega
  have hiw' : i ≠ w := hiw.ne
  have haw : a ≠ w := fun h => hai' (h ▸ hiw.symm)
  set R : Finset (Sym2 V) := {s(a, k), s(i, w)} with hRdef
  set A : Finset (Sym2 V) := {s(a, i), s(k, w)} with hAdef
  have hR : ∀ e ∈ R, e ∈ G.edgeSet := by
    simp [hRdef, hak, hiw]
  have hA : ∀ e ∈ A, e ∉ G.edgeSet ∧ ¬ e.IsDiag := by
    simp [hAdef, hai', hkw, hai, hwk.symm]
  refine ⟨editGraph G R A, inferInstance, fun v => ?_, fun v => ?_⟩
  · have key := degree_editGraph G R A hR hA v
    have hne1 : s(a, k) ≠ s(i, w) := by simp [hai, haw]
    have hne2 : s(a, i) ≠ s(k, w) := by simp [hak', haw]
    rw [hRdef, hAdef, sum_pair hne1, sum_pair hne2] at key
    simp only [Sym2.mem_iff] at key
    by_cases h1 : v = a
    · subst h1; simp [hak', hai, haw] at key; omega
    by_cases h2 : v = k
    · subst h2; simp [hak'.symm, hik.symm, hwk.symm] at key; omega
    by_cases h3 : v = i
    · subst h3; simp [hai.symm, hik, hiw'] at key; omega
    by_cases h4 : v = w
    · subst h4; simp [haw.symm, hiw'.symm, hwk] at key; omega
    simp [h1, h2, h3, h4] at key; omega
  · simp only [editGraph, hRdef, hAdef, mem_insert, mem_singleton, Sym2.eq_iff, true_and,
      hai, hak', haw, false_and, or_false, ne_eq]
    constructor
    · rintro ⟨-, ⟨h1, h2⟩ | h⟩
      · exact Or.inl ⟨h2, h1⟩
      · exact Or.inr h
    · rintro (⟨h1, h2⟩ | rfl)
      · exact ⟨h2.ne, Or.inl ⟨h2, h1⟩⟩
      · exact ⟨hai, Or.inr rfl⟩


/-- The vertices `1, …, d 0` of `Fin (m + 1)`. -/
def hhSet {m : ℕ} (d : Fin (m + 1) → ℕ) : Finset (Fin (m + 1)) :=
  ({v : Fin (m + 1) | v.val < d 0 + 1} : Finset _).erase 0

lemma mem_hhSet {m : ℕ} (d : Fin (m + 1) → ℕ) (v : Fin (m + 1)) :
    v ∈ hhSet d ↔ v ≠ 0 ∧ v.val < d 0 + 1 := by
  simp [hhSet]

lemma card_hhSet {m : ℕ} (d : Fin (m + 1) → ℕ) (h0 : d 0 ≤ m) : #(hhSet d) = d 0 := by
  rw [hhSet, card_erase_of_mem (by simp), Fin.card_filter_val_lt]
  omega

lemma hh_forward_aux {m : ℕ} (d : Fin (m + 1) → ℕ) (hd : Antitone d) (h0 : d 0 ≤ m) (r : ℕ) :
    ∀ (G : SimpleGraph (Fin (m + 1))) (_ : DecidableRel G.Adj), (∀ i, G.degree i = d i) →
      #{v ∈ hhSet d | ¬ G.Adj 0 v} ≤ r →
      ∃ (G' : SimpleGraph (Fin (m + 1))) (_ : DecidableRel G'.Adj),
        (∀ i, G'.degree i = d i) ∧ ∀ v ∈ hhSet d, G'.Adj 0 v := by
  induction r with
  | zero =>
    intro G _ hG hr
    refine ⟨G, inferInstance, hG, fun v hv => ?_⟩
    by_contra h
    have : v ∈ ({v ∈ hhSet d | ¬ G.Adj 0 v} : Finset _) := mem_filter.mpr ⟨hv, h⟩
    have := card_pos.mpr ⟨v, this⟩
    omega
  | succ r ih =>
    intro G _ hG hr
    by_cases hall : ∀ v ∈ hhSet d, G.Adj 0 v
    · exact ⟨G, inferInstance, hG, hall⟩
    push Not at hall
    obtain ⟨i, hiA, hi⟩ := hall
    have hiA' := (mem_hhSet d i).mp hiA
    obtain ⟨k, hk, hkA⟩ : ∃ k, G.Adj 0 k ∧ k ∉ hhSet d := by
      by_contra hc
      push Not at hc
      have hsub : G.neighborFinset 0 ⊆ (hhSet d).erase i := by
        intro v hv
        rw [mem_neighborFinset] at hv
        exact mem_erase.mpr ⟨fun e => hi (e ▸ hv), hc v hv⟩
      have := card_le_card hsub
      rw [card_neighborFinset_eq_degree, hG, card_erase_of_mem hiA, card_hhSet d h0] at this
      have : i.val ≠ 0 := fun e => hiA'.1 (Fin.ext e)
      omega
    have hik : i ≤ k := by
      rw [mem_hhSet] at hkA
      have hk0 : k ≠ 0 := fun e => G.loopless.irrefl 0 (e ▸ hk)
      rw [Fin.le_iff_val_le_val]
      have := not_and.mp hkA hk0
      omega
    obtain ⟨G', _, hdeg, hadj⟩ := exists_switch G 0 i k (Ne.symm hiA'.1)
      (by rw [hG, hG]; exact hd hik) hi hk
    refine ih G' inferInstance (fun v => (hdeg v).trans (hG v)) ?_
    have hsub : ({v ∈ hhSet d | ¬ G'.Adj 0 v} : Finset _) ⊆
        ({v ∈ hhSet d | ¬ G.Adj 0 v} : Finset _).erase i := by
      intro v hv
      rw [mem_filter, hadj] at hv
      rw [mem_erase, mem_filter]
      refine ⟨fun e => hv.2 (Or.inr e), hv.1, fun h => hv.2 (Or.inl ⟨?_, h⟩)⟩
      rintro rfl
      exact hkA hv.1
    have h1 := card_le_card hsub
    rw [card_erase_of_mem (mem_filter.mpr ⟨hiA, hi⟩)] at h1
    omega

lemma havelHakimi_of_isGraphic {m : ℕ} (d : Fin (m + 1) → ℕ) (hd : Antitone d)
    (hG : IsGraphic d) :
    d 0 ≤ m ∧ (∀ j : Fin m, j.val < d 0 → 1 ≤ d j.succ) ∧ IsGraphic (havelHakimi d) := by
  classical
  obtain ⟨G, _, hG⟩ := hG
  have h0 : d 0 ≤ m := by
    have := G.degree_lt_card_verts 0
    rw [hG, Fintype.card_fin] at this
    omega
  obtain ⟨G', _, hdeg, hadj⟩ := hh_forward_aux d hd h0 _ G inferInstance hG le_rfl
  have hN : G'.neighborFinset 0 = hhSet d := by
    symm
    refine eq_of_subset_of_card_le (fun v hv => (mem_neighborFinset _ _ _).mpr (hadj v hv)) ?_
    rw [card_neighborFinset_eq_degree, hdeg, card_hhSet d h0]
  have hj : ∀ j : Fin m, G'.Adj j.succ 0 ↔ j.val < d 0 := by
    intro j
    rw [G'.adj_comm, ← mem_neighborFinset, hN, mem_hhSet, Fin.val_succ]
    simp [Fin.succ_ne_zero]
  have hdj : ∀ j : Fin m,
      d j.succ = (if j.val < d 0 then 1 else 0) + #{k : Fin m | G'.Adj j.succ k.succ} := by
    intro j
    rw [← hdeg, degree_fin_succ]
    simp only [hj]
  refine ⟨h0, fun j hj' => ?_, G'.comap Fin.succ, inferInstance, fun j => ?_⟩
  · rw [hdj j]; simp only [hj', ite_true]; omega
  · rw [← card_neighborFinset_eq_degree, neighborFinset_eq_filter]
    simp only [comap_adj]
    unfold havelHakimi
    rw [hdj j]
    split_ifs <;> simp


lemma eg_necessary {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (k : ℕ) :
    ∑ i with i.val < k, G.degree i ≤ k * (k - 1) + ∑ i with k ≤ i.val, min (G.degree i) k := by
  set S : Finset (Fin n) := {i | i.val < k} with hSdef
  set T : Finset (Fin n) := {i | k ≤ i.val} with hTdef
  have hS : #S ≤ k := by rw [hSdef, Fin.card_filter_val_lt]; omega
  have hsplit : ∀ i, G.degree i = (∑ j ∈ S, if G.Adj i j then 1 else 0) +
      ∑ j ∈ T, if G.Adj i j then 1 else 0 := by
    intro i
    rw [degree_eq_sum_ite, ← Finset.sum_filter_add_sum_filter_not univ (fun j : Fin n => j.val < k)]
    simp only [not_lt, hSdef, hTdef]
  have h1 : ∑ i ∈ S, G.degree i = (∑ i ∈ S, ∑ j ∈ S, if G.Adj i j then 1 else 0) +
      ∑ i ∈ S, ∑ j ∈ T, if G.Adj i j then 1 else 0 := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun i _ => hsplit i
  have h2 : (∑ i ∈ S, ∑ j ∈ S, if G.Adj i j then 1 else 0) ≤ k * (k - 1) := by
    calc (∑ i ∈ S, ∑ j ∈ S, if G.Adj i j then 1 else 0) ≤ ∑ i ∈ S, (k - 1) := by
          refine Finset.sum_le_sum fun i hi => ?_
          rw [Finset.sum_boole]
          have : ({j ∈ S | G.Adj i j} : Finset _) ⊆ S.erase i := by
            intro j hj
            rw [mem_filter] at hj
            exact mem_erase.mpr ⟨(G.ne_of_adj hj.2).symm, hj.1⟩
          have h := card_le_card this
          rw [card_erase_of_mem hi] at h
          simp only [Nat.cast_id]
          omega
      _ = #S * (k - 1) := by rw [sum_const, smul_eq_mul]
      _ ≤ k * (k - 1) := Nat.mul_le_mul_right _ hS
  have h3 : (∑ i ∈ S, ∑ j ∈ T, if G.Adj i j then 1 else 0) ≤ ∑ j ∈ T, min (G.degree j) k := by
    rw [Finset.sum_comm]
    refine Finset.sum_le_sum fun j _ => ?_
    refine le_min ?_ ?_
    · rw [degree_eq_sum_ite]
      calc (∑ i ∈ S, if G.Adj i j then 1 else 0) = ∑ i ∈ S, if G.Adj j i then 1 else 0 := by
            simp only [G.adj_comm]
        _ ≤ ∑ i, if G.Adj j i then 1 else 0 :=
            Finset.sum_le_sum_of_subset_of_nonneg (subset_univ _) (fun _ _ _ => Nat.zero_le _)
    · calc (∑ i ∈ S, if G.Adj i j then 1 else 0) ≤ ∑ i ∈ S, 1 :=
            Finset.sum_le_sum fun i _ => by split_ifs <;> simp
        _ = #S := by simp
        _ ≤ k := hS
  rw [h1]
  omega

lemma bot_isGraphic {n : ℕ} (d : Fin n → ℕ) (h : ∀ i, d i = 0) : IsGraphic d :=
  ⟨⊥, inferInstance, fun i => by rw [bot_degree, h]⟩

lemma augment {V : Type*} [Fintype V] [DecidableEq V] (G' : SimpleGraph V) [DecidableRel G'.Adj]
    (d : V → ℕ) (t p : V) (htp : t ≠ p) (hp1 : 1 ≤ d p)
    (hdeg : ∀ v, G'.degree v + (if v = t then 1 else 0) + (if v = p then 1 else 0) = d v)
    (hQ : d t ≤ #{x | x ≠ t ∧ d p ≤ d x}) :
    ∃ (G : SimpleGraph V) (_ : DecidableRel G.Adj), ∀ v, G.degree v = d v := by
  classical
  by_cases hadj : G'.Adj t p
  · obtain ⟨x, hxt, hpx, htx⟩ : ∃ x, x ≠ t ∧ d p ≤ d x ∧ ¬ G'.Adj t x := by
      by_contra hc
      push Not at hc
      have hsub : ({x | x ≠ t ∧ d p ≤ d x} : Finset V) ⊆ G'.neighborFinset t := by
        intro x hx
        rw [mem_filter] at hx
        exact (mem_neighborFinset _ _ _).mpr (hc x hx.2.1 hx.2.2)
      have h1 := card_le_card hsub
      rw [card_neighborFinset_eq_degree] at h1
      have h2 := hdeg t
      simp only [ite_true, htp, ite_false] at h2
      omega
    have hxp : x ≠ p := fun h => htx (h ▸ hadj)
    have hdx : G'.degree x = d x := by
      have := hdeg x; simp only [hxt, hxp, ite_false] at this; omega
    have hdp : G'.degree p + 1 = d p := by
      have := hdeg p; simp only [htp.symm, ite_false, ite_true] at this; omega
    obtain ⟨y, hxy, hyp, hpy⟩ : ∃ y, G'.Adj x y ∧ y ≠ p ∧ ¬ G'.Adj p y := by
      by_contra hc
      push Not at hc
      have hsub : (G'.neighborFinset x).erase p ⊆ (G'.neighborFinset p).erase t := by
        intro y hy
        simp only [mem_erase, mem_neighborFinset] at hy ⊢
        refine ⟨fun h => htx (h ▸ hy.2).symm, hc y hy.2 hy.1⟩
      have h1 := card_le_card hsub
      have h2 := pred_card_le_card_erase (s := G'.neighborFinset x) (a := p)
      have h3 : t ∈ G'.neighborFinset p := (mem_neighborFinset _ _ _).mpr hadj.symm
      rw [card_erase_of_mem h3, card_neighborFinset_eq_degree] at h1
      rw [card_neighborFinset_eq_degree] at h2
      have h4 : 0 < G'.degree p := by
        rw [← card_neighborFinset_eq_degree]; exact card_pos.mpr ⟨t, h3⟩
      omega
    have hyt : y ≠ t := fun h => htx (h ▸ hxy).symm
    have hxy' : x ≠ y := hxy.ne
    set R : Finset (Sym2 V) := {s(x, y)} with hRdef
    set A : Finset (Sym2 V) := {s(t, x), s(p, y)} with hAdef
    have hR : ∀ e ∈ R, e ∈ G'.edgeSet := by simp [hRdef, hxy]
    have hA : ∀ e ∈ A, e ∉ G'.edgeSet ∧ ¬ e.IsDiag := by
      simp [hAdef, htx, hpy, hxt.symm, hyp.symm]
    refine ⟨editGraph G' R A, inferInstance, fun v => ?_⟩
    have key := degree_editGraph G' R A hR hA v
    have hne : s(t, x) ≠ s(p, y) := by simp [htp, hyt.symm]
    rw [hRdef, hAdef, sum_pair hne, sum_singleton] at key
    rw [hRdef, hAdef]
    simp only [Sym2.mem_iff] at key
    have hv := hdeg v
    by_cases h1 : v = t
    · subst h1; simp [hxt.symm, hyt.symm, htp] at key hv; omega
    by_cases h2 : v = p
    · subst h2; simp [hxp.symm, hyp.symm, h1] at key hv; omega
    by_cases h3 : v = x
    · subst h3; simp [h1, h2, hxy'] at key hv; omega
    by_cases h4 : v = y
    · subst h4; simp [h1, h2, h3] at key hv; omega
    simp [h1, h2, h3, h4] at key hv; omega
  · set A : Finset (Sym2 V) := {s(t, p)} with hAdef
    have hA : ∀ e ∈ A, e ∉ G'.edgeSet ∧ ¬ e.IsDiag := by simp [hAdef, hadj, htp]
    refine ⟨editGraph G' ∅ A, inferInstance, fun v => ?_⟩
    have key := degree_editGraph G' ∅ A (by simp) hA v
    rw [hAdef, sum_singleton, sum_empty] at key
    rw [hAdef]
    simp only [Sym2.mem_iff] at key
    have hv := hdeg v
    by_cases h1 : v = t
    · subst h1; simp [htp] at key hv; omega
    by_cases h2 : v = p
    · subst h2; simp [h1] at key hv; omega
    simp [h1, h2] at key hv; omega


/-- Subtract one from the entries at `t` and `p`. -/
def egReduce {n : ℕ} (d : Fin n → ℕ) (t p : Fin n) : Fin n → ℕ :=
  fun i => d i - (if i = t then 1 else 0) - (if i = p then 1 else 0)

lemma egReduce_add {n : ℕ} (d : Fin n → ℕ) (t p : Fin n) (htp : t ≠ p) (ht : 1 ≤ d t)
    (hp : 1 ≤ d p) (i : Fin n) :
    d i = egReduce d t p i + (if i = t then 1 else 0) + (if i = p then 1 else 0) := by
  unfold egReduce
  rcases eq_or_ne i t with rfl | hit
  · simp [htp]; omega
  rcases eq_or_ne i p with rfl | hip
  · simp [hit]; omega
  simp [hit, hip]

lemma egReduce_antitone {n : ℕ} (d : Fin n → ℕ) (hd : Antitone d) (t p : Fin n) (htp : t < p)
    (hp1 : 1 ≤ d p) (hpz : ∀ i, p < i → d i = 0)
    (htmax : ∀ i, t < i → i < p → d i < d t) : Antitone (egReduce d t p) := by
  intro i j hij
  have hji := hd hij
  have F2 : i = t → j ≠ t → j ≠ p → d j < d i := by
    rintro rfl hjt hjp
    rcases lt_or_gt_of_ne hjp with h | h
    · exact htmax j (lt_of_le_of_ne hij (Ne.symm hjt)) h
    · rw [hpz j h]; have := hd htp.le; omega
  have F3 : i = p → j ≠ p → d j = 0 := by
    rintro rfl hjp
    exact hpz j (lt_of_le_of_ne hij (Ne.symm hjp))
  have F4 : j = t → i ≠ p := by
    rintro rfl rfl
    exact absurd (lt_of_le_of_lt hij htp) (lt_irrefl _)
  have F5 : i = t → i ≠ p := by rintro rfl; exact htp.ne
  have F6 : j = t → j ≠ p := by rintro rfl; exact htp.ne
  unfold egReduce
  split_ifs <;> simp_all <;> omega

lemma egReduce_sum_lt {n : ℕ} (d : Fin n → ℕ) (t p : Fin n) (htp : t ≠ p) (ht : 1 ≤ d t)
    (hp : 1 ≤ d p) (F : Finset (Fin n)) :
    ∑ i ∈ F, d i = ∑ i ∈ F, egReduce d t p i + (if t ∈ F then 1 else 0) +
      (if p ∈ F then 1 else 0) := by
  rw [Finset.sum_congr rfl fun i _ => egReduce_add d t p htp ht hp i, sum_add_distrib,
    sum_add_distrib, sum_ite_eq', sum_ite_eq']

lemma egReduce_sum_min {n : ℕ} (d : Fin n → ℕ) (t p : Fin n) (htp : t ≠ p) (ht : 1 ≤ d t)
    (hp : 1 ≤ d p) (k : ℕ) (F : Finset (Fin n)) :
    ∑ i ∈ F, min (d i) k = ∑ i ∈ F, min (egReduce d t p i) k +
      (if t ∈ F then (if d t ≤ k then 1 else 0) else 0) +
      (if p ∈ F then (if d p ≤ k then 1 else 0) else 0) := by
  have key : ∀ i, min (d i) k = min (egReduce d t p i) k +
      (if i = t then (if d t ≤ k then 1 else 0) else 0) +
      (if i = p then (if d p ≤ k then 1 else 0) else 0) := by
    intro i
    unfold egReduce
    rcases eq_or_ne i t with rfl | hit
    · simp only [ite_true, htp, ite_false]; split_ifs <;> omega
    rcases eq_or_ne i p with rfl | hip
    · simp only [ite_true, hit, ite_false]; split_ifs <;> omega
    simp [hit, hip]
  rw [Finset.sum_congr rfl fun i _ => key i, sum_add_distrib, sum_add_distrib, sum_ite_eq',
    sum_ite_eq']

lemma eg_case_i {n : ℕ} (d : Fin n → ℕ) (hev : Even (∑ i, d i)) (t p : Fin n) (htp : t ≠ p)
    (hp1 : 1 ≤ d p) (k : ℕ) (hkt : k ≤ t.val) (hkp : k ≤ p.val) (hle : ∀ i, d i ≤ d t)
    (hLk : ∑ i with i.val < k, d i = k * d t) (h1 : d t ≤ k) :
    ∑ i with i.val < k, d i + 2 ≤ k * (k - 1) + ∑ i with k ≤ i.val, min (d i) k := by
  have hMk : ∑ i with k ≤ i.val, min (d i) k = ∑ i with k ≤ i.val, d i :=
    Finset.sum_congr rfl fun i _ => min_eq_left ((hle i).trans h1)
  have htot : ∑ i with i.val < k, d i + ∑ i with k ≤ i.val, d i = ∑ i, d i := by
    rw [← Finset.sum_filter_add_sum_filter_not univ (fun i : Fin n => i.val < k)]
    simp only [not_lt]
  have hge : d t + d p ≤ ∑ i with k ≤ i.val, d i := by
    rw [← sum_pair htp]
    refine Finset.sum_le_sum_of_subset_of_nonneg ?_ (fun _ _ _ => Nat.zero_le _)
    intro i hi
    simp only [mem_insert, mem_singleton] at hi
    rcases hi with rfl | rfl <;> simp [hkt, hkp]
  have hnl : k * d t ≤ k * (k - 1) + d t := by
    rcases k with _ | k
    · simp
    · simp only [Nat.add_sub_cancel]
      have := Nat.mul_le_mul_left k h1
      rw [Nat.succ_mul]
      nlinarith
  obtain ⟨u, hu⟩ := Nat.even_mul_pred_self k
  obtain ⟨v, hv⟩ := hev
  rw [hMk, hLk]
  rw [hLk] at htot
  generalize k * d t = Y at *
  generalize k * (k - 1) = X at *
  omega

lemma eg_case_ii {n : ℕ} (d : Fin n → ℕ) (hEG : ∀ k ≤ n, ∑ i with i.val < k, d i ≤
      k * (k - 1) + ∑ i with k ≤ i.val, min (d i) k)
    (t p : Fin n) (htp : t < p) (k : ℕ) (hkt : k ≤ t.val) (hLk : ∑ i with i.val < k, d i = k * d t)
    (htop : ∀ i ≤ t, d i = d t) (hp1 : 1 ≤ d p) (h1 : k < d t) (h2 : d p ≤ k) :
    ∑ i with i.val < k, d i + 1 ≤ k * (k - 1) + ∑ i with k ≤ i.val, min (d i) k := by
  have htp' : t.val < p.val := htp
  have hkn : k < n := by have := p.isLt; omega
  set kk : Fin n := ⟨k, hkn⟩ with hkk
  have hdkk : d kk = d t := htop kk (by rw [Fin.le_iff_val_le_val]; exact hkt)
  have hL1 : ∑ i with i.val < k + 1, d i = ∑ i with i.val < k, d i + d t := by
    have : (univ.filter fun i : Fin n => i.val < k + 1) =
        insert kk (univ.filter fun i : Fin n => i.val < k) := by
      ext i; simp [hkk, Fin.ext_iff]; omega
    rw [this, sum_insert (by simp [hkk]), hdkk, add_comm]
  set N := ∑ i with k + 1 ≤ i.val, min (d i) k with hN
  set c := ∑ i with k + 1 ≤ i.val, (if k + 1 ≤ d i then 1 else 0) with hc
  have hM0 : ∑ i with k ≤ i.val, min (d i) k = k + N := by
    have : (univ.filter fun i : Fin n => k ≤ i.val) =
        insert kk (univ.filter fun i : Fin n => k + 1 ≤ i.val) := by
      ext i; simp [hkk, Fin.ext_iff]; omega
    rw [this, sum_insert (by simp [hkk]), hdkk, min_eq_right h1.le]
  have hM1 : ∑ i with k + 1 ≤ i.val, min (d i) (k + 1) = N + c := by
    rw [hN, hc, ← sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    split_ifs <;> omega
  have hNc : k * c + 1 ≤ N := by
    have hpmem : p ∈ (univ.filter fun i : Fin n => k + 1 ≤ i.val) := by simp; omega
    calc k * c + 1 = ∑ i with k + 1 ≤ i.val,
          (k * (if k + 1 ≤ d i then 1 else 0) + (if i = p then 1 else 0)) := by
          rw [sum_add_distrib, ← mul_sum, sum_ite_eq']
          simp only [hpmem, ite_true, hc]
      _ ≤ N := by
          refine Finset.sum_le_sum fun i _ => ?_
          rcases eq_or_ne i p with rfl | hip
          · simp only [ite_true]; split_ifs <;> omega
          · simp only [hip, ite_false]; split_ifs <;> omega
  have hE := hEG (k + 1) hkn
  rw [hL1, hM1, Nat.add_sub_cancel] at hE
  rw [hM0]
  have hnl1 : k * (k - 1) + k = k * k := by
    rcases k with _ | k
    · simp
    · simp only [Nat.add_sub_cancel]; ring
  have hnl2 : (k + 1) * k = k * k + k := by ring
  have hnl3 : d t ≤ k + c → k * d t ≤ k * k + k * c := fun h => by
    have := Nat.mul_le_mul_left k h
    rw [Nat.mul_add] at this
    exact this
  rw [hLk] at hE ⊢
  rw [hnl2] at hE
  generalize k * d t = Y at *
  generalize k * (k - 1) = X at *
  generalize k * c = Z at *
  generalize k * k = W at *
  omega


lemma egReduce_EG {n : ℕ} (d : Fin n → ℕ) (hd : Antitone d) (hev : Even (∑ i, d i))
    (hEG : ∀ k ≤ n, ∑ i with i.val < k, d i ≤ k * (k - 1) + ∑ i with k ≤ i.val, min (d i) k)
    (t p : Fin n) (htp : t < p) (hp1 : 1 ≤ d p) (htop : ∀ i ≤ t, d i = d t) :
    ∀ k ≤ n, ∑ i with i.val < k, egReduce d t p i ≤
      k * (k - 1) + ∑ i with k ≤ i.val, min (egReduce d t p i) k := by
  intro k hk
  have htp' : t ≠ p := htp.ne
  have htpv : t.val < p.val := htp
  have ht1 : 1 ≤ d t := le_trans hp1 (hd htp.le)
  have hL := egReduce_sum_lt d t p htp' ht1 hp1 (univ.filter fun i : Fin n => i.val < k)
  have hM := egReduce_sum_min d t p htp' ht1 hp1 k (univ.filter fun i : Fin n => k ≤ i.val)
  simp only [mem_filter, mem_univ, true_and] at hL hM
  have hE := hEG k hk
  by_cases hkt : k ≤ t.val
  · have hle : ∀ i, d i ≤ d t := fun i => by
      rcases le_total i t with h | h
      · exact (htop i h).le
      · exact hd h
    have hLk : ∑ i with i.val < k, d i = k * d t := by
      have : ∀ i ∈ univ.filter (fun i : Fin n => i.val < k), d i = d t := fun i hi =>
        htop i (by rw [mem_filter] at hi; rw [Fin.le_iff_val_le_val]; omega)
      rw [sum_congr rfl this, sum_const, smul_eq_mul, Fin.card_filter_val_lt, min_eq_right hk]
    by_cases h1 : d t ≤ k
    · have := eg_case_i d hev t p htp' hp1 k hkt (by omega) hle hLk h1
      split_ifs at hL hM <;> omega
    · by_cases h2 : d p ≤ k
      · have := eg_case_ii d hEG t p htp k hkt hLk htop hp1 (by omega) h2
        split_ifs at hL hM <;> omega
      · split_ifs at hL hM <;> omega
  · split_ifs at hL hM <;> omega

theorem eg_sufficient {n : ℕ} (s : ℕ) : ∀ (d : Fin n → ℕ), ∑ i, d i = s → Antitone d →
    Even (∑ i, d i) →
    (∀ k ≤ n, ∑ i with i.val < k, d i ≤ k * (k - 1) + ∑ i with k ≤ i.val, min (d i) k) →
    IsGraphic d := by
  induction s using Nat.strong_induction_on with
  | _ s ih =>
  intro d hs hd hev hEG
  by_cases hz : ∀ i, d i = 0
  · exact bot_isGraphic d hz
  push Not at hz
  obtain ⟨i0, hi0⟩ := hz
  set P : Finset (Fin n) := univ.filter (fun i => 1 ≤ d i) with hPdef
  have hPne : P.Nonempty := ⟨i0, by simp [hPdef]; omega⟩
  set p := P.max' hPne with hpdef
  have hp1 : 1 ≤ d p := by
    have := P.max'_mem hPne
    rw [← hpdef, hPdef, mem_filter] at this
    exact this.2
  have hpz : ∀ i, p < i → d i = 0 := by
    intro i hi
    by_contra h
    have : i ∈ P := by simp [hPdef]; omega
    exact absurd (P.le_max' i this) (not_le.mpr hi)
  have hn : 0 < n := Nat.lt_of_le_of_lt (Nat.zero_le _) p.isLt
  set z : Fin n := ⟨0, hn⟩ with hz
  -- Erdős–Gallai at `k = 1`
  have hE1 := hEG 1 (by omega)
  have hL1 : ∑ i with i.val < 1, d i = d z := by
    have : (univ.filter fun i : Fin n => i.val < 1) = {z} := by
      ext i; simp [hz, Fin.ext_iff]
    rw [this, sum_singleton]
  have hcount : ∑ i with 1 ≤ i.val, min (d i) 1 ≤ p.val := by
    calc ∑ i with 1 ≤ i.val, min (d i) 1 ≤ ∑ i with 1 ≤ i.val, (if i ≤ p then 1 else 0) := by
          refine sum_le_sum fun i _ => ?_
          split_ifs with h
          · exact min_le_right _ _
          · rw [hpz i (not_le.mp h)]; simp
      _ = #((univ.filter fun i : Fin n => 1 ≤ i.val).filter (· ≤ p)) := by
          rw [sum_boole]; simp
      _ ≤ #(Ioc z p) := by
          refine card_le_card fun i hi => ?_
          simp only [mem_filter, mem_univ, true_and] at hi
          rw [mem_Ioc, Fin.lt_def]
          exact ⟨by simp [hz]; omega, hi.2⟩
      _ = p.val := by rw [Fin.card_Ioc]; simp [hz]
  rw [hL1] at hE1
  simp only [Nat.sub_self, mul_zero, zero_add] at hE1
  have hzle : ∀ j : Fin n, z ≤ j := fun j => Fin.le_iff_val_le_val.mpr (Nat.zero_le _)
  have hzp : d p ≤ d z := hd (hzle p)
  have hp0 : 0 < p.val := by omega
  -- choose `t`
  set T : Finset (Fin n) := univ.filter (fun i => i < p ∧ ∀ j ≤ i, d j = d i) with hTdef
  have hzT : z ∈ T := by
    simp only [hTdef, mem_filter, mem_univ, true_and]
    refine ⟨by rw [Fin.lt_def]; simpa [hz] using hp0, fun j hj => ?_⟩
    rw [le_antisymm hj (hzle j)]
  set t := T.max' ⟨z, hzT⟩ with htdef
  have htT : t ∈ T := T.max'_mem _
  simp only [hTdef, mem_filter, mem_univ, true_and] at htT
  obtain ⟨htp, htop⟩ := htT
  have hzt : z ≤ t := T.le_max' z hzT
  have hdzt : d z = d t := htop z hzt
  have htmax : ∀ i, t < i → i < p → d i < d t := by
    intro i hti hip
    by_contra h
    have hdi : d i = d t := le_antisymm (hd hti.le) (not_lt.mp h)
    have : i ∈ T := by
      simp only [hTdef, mem_filter, mem_univ, true_and]
      refine ⟨hip, fun j hj => le_antisymm ?_ (hd hj)⟩
      rw [hdi, ← hdzt]
      exact hd (hzle j)
    exact absurd (T.le_max' i this) (not_le.mpr hti)
  have ht1 : 1 ≤ d t := le_trans hp1 (hd htp.le)
  have hQ : d t ≤ #(univ.filter fun x : Fin n => x ≠ t ∧ d p ≤ d x) := by
    calc d t = d z := hdzt.symm
      _ ≤ p.val := le_trans hE1 hcount
      _ = #((Iic p).erase t) := by
          rw [card_erase_of_mem (mem_Iic.mpr htp.le), Fin.card_Iic]; simp
      _ ≤ _ := by
          refine card_le_card fun x hx => ?_
          simp only [mem_erase, mem_Iic] at hx
          simp only [mem_filter, mem_univ, true_and]
          exact ⟨hx.1, hd hx.2⟩
  -- the reduced sequence
  have hsum := egReduce_sum_lt d t p htp.ne ht1 hp1 univ
  simp only [mem_univ, ite_true] at hsum
  have hG' := ih (∑ i, egReduce d t p i) (by omega) (egReduce d t p) rfl
    (egReduce_antitone d hd t p htp hp1 hpz htmax)
    (by rw [hsum] at hev; obtain ⟨v, hv⟩ := hev; exact ⟨v - 1, by omega⟩)
    (egReduce_EG d hd hev hEG t p htp hp1 htop)
  obtain ⟨G', _, hG'⟩ := hG'
  obtain ⟨G, inst, hG⟩ := augment G' d t p htp.ne hp1 (fun v => by
    rw [hG', egReduce_add d t p htp.ne ht1 hp1 v]) hQ
  exact ⟨G, inst, hG⟩

/-- **Erdős–Gallai theorem (1960).** A non-increasing sequence of natural numbers is the degree
sequence of a simple graph if and only if its sum is even and every initial segment satisfies the
Erdős–Gallai inequality. -/
theorem isGraphic_iff_erdos_gallai {n : ℕ} (d : Fin n → ℕ) (hd : Antitone d) :
    IsGraphic d ↔ Even (∑ i, d i) ∧
      ∀ k ≤ n, ∑ i with i.val < k, d i ≤ k * (k - 1) + ∑ i with k ≤ i.val, min (d i) k := by
  constructor
  · rintro ⟨G, _, hG⟩
    refine ⟨?_, fun k _ => ?_⟩
    · have h := G.sum_degrees_eq_twice_card_edges
      simp only [hG] at h
      rw [h]
      exact even_two_mul _
    · simpa only [hG] using eg_necessary G k
  · rintro ⟨hev, hEG⟩
    exact eg_sufficient _ d rfl hd hev hEG

/-- **Havel–Hakimi theorem (Havel 1955, Hakimi 1962).** A non-increasing sequence `d₀, …, d_m` is
graphic if and only if `d₀ ≤ m`, the terms `d₁, …, d_{d₀}` are positive, and its Havel–Hakimi
reduction is graphic. -/
theorem isGraphic_iff_havel_hakimi {m : ℕ} (d : Fin (m + 1) → ℕ) (hd : Antitone d) :
    IsGraphic d ↔ d 0 ≤ m ∧ (∀ j : Fin m, j.val < d 0 → 1 ≤ d j.succ) ∧
      IsGraphic (havelHakimi d) := by
  exact ⟨havelHakimi_of_isGraphic d hd,
    fun ⟨h0, hpos, hH⟩ => isGraphic_of_havelHakimi d h0 hpos hH⟩

end DegreeSequences
