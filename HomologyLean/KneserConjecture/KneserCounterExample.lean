/-
Copyright (c) 2025 Sebastian Kumar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Kumar
-/

import HomologyLean.KneserConjecture.KneserConjecture
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Fintype.Basic
import Mathlib.Tactic

/-!
# Kneser Counterexample: k + 2 Colors Suffice

This file proves that k + 2 colors are sufficient to color the n-subsets of a (2n+k)-element
set such that no two disjoint n-subsets have the same color.

This shows that Kneser's conjecture (requiring k + 1 colors forces a monochromatic disjoint pair)
is tight and cannot be strengthened to k + 2 colors.

## Main Results

* `kneser_counterexample`: With k + 2 colors, we can avoid monochromatic disjoint pairs

## Implementation

The coloring partitions n-subsets by their minimum element:
- Color i (for i < k+1): n-subsets with minimum element = i
- Color k+1: n-subsets with minimum element ≥ k+1

Two n-subsets with the same color either share their minimum element (if color < k+1),
or are both subsets of a (2n-1)-element set (if color = k+1), forcing them to intersect
by the pigeonhole principle.
-/

noncomputable section

namespace Kneser

/-! ### Counterexample Construction -/

/-- Two n-subsets with the same minimum element must intersect (share that minimum). -/
theorem same_min_not_disjoint {n k : ℕ} {A B : Finset (Fin (2 * n + k))}
    (hA : A.Nonempty) (hB : B.Nonempty)
    (h_same_min : A.min' hA = B.min' hB) :
    ¬Disjoint A B := by
  intro h_disj
  have hA_min : A.min' hA ∈ A := Finset.min'_mem A hA
  have hB_min : B.min' hB ∈ B := Finset.min'_mem B hB
  rw [Finset.disjoint_iff_ne] at h_disj
  exact h_disj (A.min' hA) hA_min (B.min' hB) hB_min h_same_min

/-- An n-subset of Finset.univ is nonempty when n > 0 -/
theorem nSubset_nonempty {n k : ℕ} (hn : 0 < n)
    (A : nSubsets (Finset.univ : Finset (Fin (2 * n + k))) n) : A.1.Nonempty := by
  have hA := A.2
  unfold nSubsets at hA
  rw [Finset.mem_powersetCard] at hA
  rw [← Finset.card_pos, hA.2]
  exact hn

/-- Two n-subsets of {k+1, ..., 2n+k-1} must intersect when n > 0 (pigeonhole).
The set {k+1, ..., 2n+k-1} has 2n-1 elements, so two n-subsets must overlap. -/
theorem high_min_subsets_intersect {n k : ℕ} (hn : 0 < n)
    {A B : Finset (Fin (2 * n + k))}
    (hA_card : A.card = n) (hB_card : B.card = n)
    (hA_min : ∀ x ∈ A, k + 1 ≤ x.val) (hB_min : ∀ x ∈ B, k + 1 ≤ x.val) : ¬Disjoint A B := by
  intro h_disj
  -- |A ∪ B| = 2n
  have h_union_card : (A ∪ B).card = 2 * n := by
    rw [Finset.card_union_of_disjoint h_disj, hA_card, hB_card]
    omega
  -- S = {x | x ≥ k + 1}
  let S := Finset.univ.filter (fun x : Fin (2 * n + k) => k + 1 ≤ x.val)
  -- A ∪ B ⊆ S
  have h_subset : A ∪ B ⊆ S := by
    intro x hx
    simp only [S, Finset.mem_filter, Finset.mem_univ, true_and]
    rcases Finset.mem_union.mp hx with hA | hB
    · exact hA_min x hA
    · exact hB_min x hB
  -- |S| = 2n - 1
  have hS_card : S.card = 2 * n - 1 := by
    let Sc := Finset.univ.filter (fun x : Fin (2 * n + k) => x.val < k + 1)
    have h_part : S ∪ Sc = Finset.univ := by
      ext x
      simp only [S, Sc, Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and]
      simp
      omega
    have h_disj_parts : Disjoint S Sc := by
      rw [Finset.disjoint_iff_ne]
      intro x hx y hy
      simp only [S, Sc, Finset.mem_filter] at hx hy
      omega
    have hSc_card : Sc.card = k + 1 := by
      have h_bound : k + 1 ≤ 2 * n + k := by omega
      let f : Fin (k + 1) → Fin (2 * n + k) := fun i => ⟨i.val, by omega⟩
      have hf : Function.Injective f := by
        intro x y h
        simp [f] at h
        exact Fin.eq_of_val_eq h
      have h_img : Sc = Finset.univ.image f := by
        ext x
        simp only [Sc, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image, f]
        constructor
        · intro hx
          use ⟨x.val, hx⟩
        · intro h
          rcases h with ⟨y, _, rfl⟩
          simp
          simpa using y.isLt
      rw [h_img, Finset.card_image_of_injective _ hf]
      simp
    have h_univ : (Finset.univ : Finset (Fin (2 * n + k))).card = 2 * n + k := Fintype.card_fin _
    rw [← h_part, Finset.card_union_of_disjoint h_disj_parts, hSc_card] at h_univ
    omega
  have := Finset.card_le_card h_subset
  rw [h_union_card, hS_card] at this
  omega


/-- The minimum element coloring: partition n-subsets by their minimum element.
Classes are {min = 0}, {min = 1}, ..., {min = k}, {min ≥ k + 1}.
This gives k + 2 classes where no class contains two disjoint n-subsets. -/
def minElementColoring (n k : ℕ) (A : Finset (Fin (2 * n + k))) (hA : A.Nonempty) : Fin (k + 2) :=
  let m := A.min' hA
  if h : m.val < k + 1 then ⟨m.val, Nat.lt_add_one_of_lt h⟩ else ⟨k + 1, Nat.lt_succ_self _⟩
/-- The coloring for the counterexample, adapted for n-subsets -/
def counterexampleColoring (n k : ℕ) (hn : 0 < n)
    (A : nSubsets (Finset.univ : Finset (Fin (2 * n + k))) n) : Fin (k + 2) :=
  minElementColoring n k A.1 (nSubset_nonempty hn A)

/-- The counterexample: with k + 2 colors, we can color n-subsets so that
no two disjoint n-subsets have the same color.

This shows that k + 2 is the tight bound - Kneser's conjecture cannot be
strengthened to k + 2 classes. -/
theorem kneser_counterexample (n k : ℕ) (hn : 0 < n) :
    ∃ (coloring : (A : nSubsets (Finset.univ : Finset (Fin (2 * n + k))) n) → Fin (k + 2)),
      ∀ (A B : nSubsets Finset.univ n),
        coloring A = coloring B → Disjoint A.1 B.1 → A = B := by
  use counterexampleColoring n k hn
  intro A B h_same_color h_disj
  by_contra hAB
  -- A and B have the same color but are disjoint and distinct
  unfold counterexampleColoring minElementColoring at h_same_color
  set mA := A.1.min' (nSubset_nonempty hn A) with hmA_def
  set mB := B.1.min' (nSubset_nonempty hn B) with hmB_def
  -- Case analysis on whether min < k + 1 or not
  by_cases hA_low : mA.val < k + 1 <;> by_cases hB_low : mB.val < k + 1
  · -- Both have min < k + 1, so they have the same min
    rw [dif_pos hA_low, dif_pos hB_low] at h_same_color
    simp only [Fin.mk.injEq] at h_same_color
    have h_same_min : mA = mB := Fin.ext h_same_color
    exact same_min_not_disjoint (nSubset_nonempty hn A) (nSubset_nonempty hn B) h_same_min h_disj
  · -- A low, B high
    rw [dif_pos hA_low, dif_neg hB_low] at h_same_color
    simp only [Fin.mk.injEq] at h_same_color
    omega
  · -- A high, B low
    rw [dif_neg hA_low, dif_pos hB_low] at h_same_color
    simp only [Fin.mk.injEq] at h_same_color
    omega
  · -- Both have min ≥ k + 1, use pigeonhole
    push_neg at hA_low hB_low
    have hA_card : A.1.card = n := by
      have := A.2
      unfold nSubsets at this
      rw [Finset.mem_powersetCard] at this
      exact this.2
    have hB_card : B.1.card = n := by
      have := B.2
      unfold nSubsets at this
      rw [Finset.mem_powersetCard] at this
      exact this.2
    have hA_min_bound : ∀ x ∈ A.1, k + 1 ≤ x.val := by
      intro x hx
      have : mA ≤ x := Finset.min'_le A.1 x hx
      omega
    have hB_min_bound : ∀ x ∈ B.1, k + 1 ≤ x.val := by
      intro x hx
      have : mB ≤ x := Finset.min'_le B.1 x hx
      omega
    exact high_min_subsets_intersect hn hA_card hB_card hA_min_bound hB_min_bound h_disj

end Kneser
