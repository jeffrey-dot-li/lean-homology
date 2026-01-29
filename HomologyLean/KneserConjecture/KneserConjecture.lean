/-
Copyright (c) 2025 Sebastian Kumar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Kumar
-/

import HomologyLean.KneserConjecture.Basic
import HomologyLean.KneserConjecture.BorsukUlam
import HomologyLean.KneserConjecture.KneserCounterExample

/-!
# Kneser's Conjecture

This file formalizes Lovász's proof of Kneser's Conjecture using algebraic topology.

## Main Results

* `kneser_conjecture`: The main conjecture - any coloring with k + 1 colors has a monochromatic
  disjoint pair
* `KneserGraph.chromaticNumber`: The chromatic number of KG(n,k) is k + 2

## References

* L. Lovász, "Kneser's Conjecture, Chromatic Number, and Homotopy",
  Journal of Combinatorial Theory, Series A 25 (1978), 319-324.
-/

noncomputable section

namespace Kneser

variable {α : Type*} [DecidableEq α]

/-! ### Kneser's Conjecture -/

/-- **Kneser's Conjecture (Set-Theoretic Formulation)**: If we partition the n-subsets of a
(2n + k)-element set into k + 1 classes, then one of the classes contains two disjoint n-subsets.

Equivalently: any coloring of n-subsets with k + 1 colors has a monochromatic disjoint pair. -/
theorem kneser_conjecture {n k : ℕ} (hn : 0 < n) (S : Finset α) (hS : S.card = 2 * n + k)
    (coloring : nSubsets S n → Fin (k + 1)) :
    ∃ (A : nSubsets S n) (B : nSubsets S n),
      coloring A = coloring B ∧ Disjoint A.1 B.1 ∧ A ≠ B := by
  sorry

/-- The Kneser graph is not (k+1)-colorable when n ≥ 1.
This is the lower bound, equivalent to `kneser_conjecture`. -/
theorem KneserGraph.not_colorable (n k : ℕ) (hn : 0 < n) :
    ¬ (KneserGraph n k).Colorable (k + 1) := by
  sorry

/-- **Kneser's Conjecture (Chromatic Number)**: The chromatic number of the Kneser graph
KG(n,k) is exactly k + 2 for n ≥ 1.

This was conjectured by Kneser in 1955 and proved by Lovász in 1978 using
the Borsuk-Ulam theorem. -/
theorem KneserGraph.chromaticNumber (n k : ℕ) (hn : 0 < n) :
    (KneserGraph n k).chromaticNumber = k + 2 := by
  rw [show (k + 2 : ℕ∞) = ↑(k + 1) + 1 by norm_cast]
  rw [SimpleGraph.chromaticNumber_eq_iff_colorable_not_colorable]
  exact ⟨KneserGraph.colorable n k, KneserGraph.not_colorable n k hn⟩

/-- The chromatic number being k+2 implies not (k+1)-colorable. -/
theorem KneserGraph.not_colorable_of_chromaticNumber (n k : ℕ)
    (h : (KneserGraph n k).chromaticNumber = k + 2) :
    ¬ (KneserGraph n k).Colorable (k + 1) := by
  rw [show (k + 2 : ℕ∞) = ↑(k + 1) + 1 by norm_cast] at h
  rw [SimpleGraph.chromaticNumber_eq_iff_colorable_not_colorable] at h
  exact h.2

end Kneser
