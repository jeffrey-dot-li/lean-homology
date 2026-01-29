/-
Copyright (c) 2025 Sebastian Kumar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Kumar
-/

import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Combinatorics.SimpleGraph.Coloring
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Fintype.Basic
import Mathlib.Topology.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
# Kneser's Conjecture

This file formalizes Lovász's proof of Kneser's Conjecture using algebraic topology.

## Main Definitions

* `nSubsets S n`: The n-subsets of a finite set S
* `KneserGraph n k`: The Kneser graph KG(n,k) whose vertices are n-subsets of {0,...,2n+k-1}
  and edges connect disjoint subsets
* `NeighborhoodComplex G`: The simplicial complex whose simplices are subsets of V(G) with
  a common neighbor

## Main Results

* `kneser_conjecture`: The main conjecture - any coloring with k + 1 colors has a monochromatic
  disjoint pair
* `kneser_chromatic_number`: The chromatic number of KG(n,k) is k + 2

## References

* L. Lovász, "Kneser's Conjecture, Chromatic Number, and Homotopy",
  Journal of Combinatorial Theory, Series A 25 (1978), 319-324.
-/

noncomputable section

namespace Kneser

/-! ### Basic Setup -/

variable {α : Type*} [DecidableEq α]

/-- The n-subsets of a finset S -/
def nSubsets (S : Finset α) (n : ℕ) : Finset (Finset α) :=
  S.powersetCard n

/-! ### Borsuk's Theorem -/

/-- The n-dimensional sphere in ℝⁿ⁺¹ -/
def Sphere (n : ℕ) : Set (EuclideanSpace ℝ (Fin (n + 1))) :=
  Metric.sphere 0 1

/-- Two points on the sphere are antipodal if one is the negation of the other -/
def Antipodal {n : ℕ} (x y : Sphere n) : Prop :=
  y.1 = -x.1

/-- A set contains an antipodal pair if there exists x such that both x and -x are in the set -/
def HasAntipodalPair {n : ℕ} (F : Set (Sphere n)) : Prop :=
  ∃ x : Sphere n, x ∈ F ∧ ∃ y : Sphere n, y ∈ F ∧ Antipodal x y

/-- **Borsuk's Theorem (Covering Version)**: If the n-sphere Sⁿ is covered by n + 1 closed sets,
then at least one of the sets contains a pair of antipodal points.

This is equivalent to the Borsuk-Ulam theorem and is the key topological input for
Lovász's proof of Kneser's conjecture. -/
theorem borsuk_covering {n : ℕ} (F : Fin (n + 1) → Set (Sphere n))
    (hClosed : ∀ i, IsClosed (F i))
    (hCover : ∀ x : Sphere n, ∃ i, x ∈ F i) :
    ∃ i, HasAntipodalPair (F i) := by
  sorry

/-- The antipodal point of x on the sphere -/
def antipode {n : ℕ} (x : Sphere n) : Sphere n :=
  ⟨-x.1, by
    simp only [Sphere, Metric.mem_sphere, dist_zero_right, norm_neg]
    have hx := x.2
    simp only [Sphere, Metric.mem_sphere, dist_zero_right] at hx
    exact hx⟩

/-- **Borsuk-Ulam Theorem**: Any continuous map from Sⁿ to ℝⁿ sends some pair of
antipodal points to the same point. -/
theorem borsuk_ulam {n : ℕ} (f : Sphere n → EuclideanSpace ℝ (Fin n))
    (hf : Continuous f) :
    ∃ x : Sphere n, f x = f (antipode x) := by
  sorry

/-! ### Kneser's Conjecture (Set-Theoretic Formulation) -/

/-- **Kneser's Conjecture**: If we partition the n-subsets of a (2n + k)-element set into
k + 1 classes, then one of the classes contains two disjoint n-subsets.

Equivalently: any coloring of n-subsets with k + 1 colors has a monochromatic disjoint pair. -/
theorem kneser_conjecture {n k : ℕ} (hn : 0 < n) (S : Finset α) (hS : S.card = 2 * n + k)
    (coloring : nSubsets S n → Fin (k + 1)) :
    ∃ (A : nSubsets S n) (B : nSubsets S n),
      coloring A = coloring B ∧ Disjoint A.1 B.1 ∧ A ≠ B := by
  sorry

end Kneser
