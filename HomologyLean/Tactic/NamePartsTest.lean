import HomologyLean.Tactic.NameParts

namespace HomologyLean.Tactic.NamePartsTest

-- Basic: names both sides of an equality
example (a b c : Nat) (h : a + b = c) : a + b = c := by
  name_parts ?LHS = ?RHS
  exact h

-- Addition structure: names summands
example (a b c : Nat) : a + b + c = a + b + c := by
  name_parts ?X + ?Y = _
  rfl

-- Mixed named and anonymous holes
example (a b : Nat) : a + b = a + b := by
  name_parts ?S = _
  rfl

-- Works with integers and subtraction
example (x y z : Int) (h : x - y = z) : x - y = z := by
  name_parts ?A = ?B
  exact h

-- Nested arithmetic
example (a b c d : Nat) (h : (a + b) * (c + d) = 0) : (a + b) * (c + d) = 0 := by
  name_parts ?P * ?Q = ?Z
  exact h

-- Propositions: names parts of a conjunction goal
example (p q : Prop) (hp : p) (hq : q) : p ∧ q := by
  name_parts ?A ∧ ?B
  exact ⟨hp, hq⟩

end HomologyLean.Tactic.NamePartsTest
