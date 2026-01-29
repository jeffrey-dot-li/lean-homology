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

/-!
# Kneser Graph: Basic Definitions

This file contains the basic definitions for the Kneser graph formalization.

## Main Definitions

* `nSubsets S n`: The n-subsets of a finite set S
* `KneserVertex n k`: The vertex type for KG(n,k) - n-subsets of {0,...,2n+k-1}
* `KneserGraph n k`: The Kneser graph where edges connect disjoint subsets
-/

noncomputable section

namespace Kneser

/-! ### Basic Setup -/

variable {α : Type*} [DecidableEq α]

/-- The n-subsets of a finset S -/
def nSubsets (S : Finset α) (n : ℕ) : Finset (Finset α) :=
  S.powersetCard n

/-! ### Kneser Graph -/

/-- The vertex type for the Kneser graph KG(n,k): n-subsets of {0, ..., 2n+k-1} -/
def KneserVertex (n k : ℕ) : Type :=
  { A : Finset (Fin (2 * n + k)) // A.card = n }

/-- The Kneser graph KG(n,k).
Vertices are n-subsets of {0, ..., 2n+k-1}, and two vertices are adjacent
iff their corresponding subsets are disjoint. -/
def KneserGraph (n k : ℕ) : SimpleGraph (KneserVertex n k) where
  Adj A B := A ≠ B ∧ Disjoint A.1 B.1
  symm := fun _ _ ⟨hne, hdisj⟩ => ⟨hne.symm, Disjoint.symm hdisj⟩
  loopless := fun _ h => h.1 rfl

end Kneser
