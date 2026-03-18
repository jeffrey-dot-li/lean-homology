import HomologyLean.Tactic.NameParts
import Mathlib.CategoryTheory.Preadditive.Basic
import Mathlib.CategoryTheory.Linear.Basic
import Mathlib.CategoryTheory.Limits.Shapes.BinaryProducts

open CategoryTheory

namespace HomologyLean.Tactic.NamePartsTest

/-! ## Why `name_parts` exists

`name_parts` solves a gap between existing tactics:

- **`refine ?A = ?B`** fails on morphism/module equalities: Lean cannot resolve
  `HAdd`, `CategoryStruct`, etc. when both arguments to the operator are metavariables.
  Error: "typeclass instance problem is stuck". (Tested with `fail_if_success` below.)

- **`set A := expr`** works, but you must spell out the exact sub-expression for each
  binding. On a goal with four summands you need four `set` calls copying long expressions;
  `name_parts ?A + ?B = ?C + ?D` does it in one line via pattern matching.

- **`change ?A = ?B`** elaborates against the goal type (so it doesn't get stuck), but
  it's a no-op—it does **not** introduce `let`-bindings into the context.

`name_parts` combines the strengths: it uses `change`-style elaboration (avoiding stuck
typeclasses) and introduces named `let`-bindings (like `set`), all in a single pattern.
-/

section RefineCannotDo
/-! ### `refine` fails with stuck typeclasses on morphism equalities

`refine ?LHS = ?RHS` elaborates `?LHS` and `?RHS` independently before unifying with
the goal. When the `=` is between morphisms (or module elements), Lean needs to resolve
`@Eq (X ⟶ Y) ?LHS ?RHS`, but `X ⟶ Y` depends on `Category C`—a typeclass that can't
be inferred while both sides are bare metavariables.

`name_parts` avoids this by elaborating the whole pattern against the goal type
(like `change`), so the typeclass context is already known.
-/

-- Morphism equality: `refine ?A = ?B` → "Type mismatch ... Prop of sort Type"
-- `name_parts` succeeds and introduces let-bindings.
example {C : Type*} [Category C] [Preadditive C] {X Y : C}
    (f g : X ⟶ Y) (h : f + g = f - g) : f + g = f - g := by
  fail_if_success refine ?LHS = ?RHS
  name_parts ?LHS = ?RHS
  guard_target = LHS = RHS
  exact h

-- Multiple holes under `+` or `≫`: `refine ?A + ?B = ?C + ?D` → "stuck HAdd"
-- `name_parts` handles this because the pattern is elaborated against a known type.
example {C : Type*} [Category C] [Preadditive C] {X Y Z : C}
    (f f' : X ⟶ Y) (g g' : Y ⟶ Z)
    (h : f ≫ g + f' ≫ g' = f' ≫ g + f ≫ g') :
    f ≫ g + f' ≫ g' = f' ≫ g + f ≫ g' := by
  fail_if_success refine ?A + ?B = ?C_ + ?D
  name_parts ?A + ?B = ?C_ + ?D
  guard_target = A + B = C_ + D
  exact h

-- Holes under `≫`: `refine ?A ≫ ?B = _` → "stuck CategoryStruct"
example {C : Type*} [Category C] {W X Y Z : C}
    (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z) :
    f ≫ g ≫ h = f ≫ (g ≫ h) := by
  fail_if_success refine ?A ≫ ?B = _
  name_parts ?A ≫ ?B = _
  guard_target = A ≫ B = A ≫ B
  rfl

-- Scalar-morphism decomposition with smul, add, sub
example {C : Type*} [Category C] [Preadditive C] [Linear ℤ C] {X Y : C}
    (f g : X ⟶ Y) (h : (2 : ℤ) • f + g = f - g) :
    (2 : ℤ) • f + g = f - g := by
  name_parts ?A + ?B = ?C_ - ?D
  guard_target = A + B = C_ - D
  exact h

-- Four summands in one line (would need four `set` calls otherwise)
example {C : Type*} [Category C] [Preadditive C] [Linear ℤ C] {X Y Z : C}
    (f : X ⟶ Y) (g h₁ : Y ⟶ Z) (n : ℤ)
    (hyp : n • f ≫ g + (1 - n) • f ≫ h₁ = n • f ≫ h₁ + (1 - n) • f ≫ g) :
    n • f ≫ g + (1 - n) • f ≫ h₁ = n • f ≫ h₁ + (1 - n) • f ≫ g := by
  name_parts ?A + ?B = ?C_ + ?D
  guard_target = A + B = C_ + D
  exact hyp

end RefineCannotDo

section BasicFunctionality
/-! ### Basic functionality on simple types -/

example (a b c : Nat) (h : a + b = c) : a + b = c := by
  name_parts ?LHS = ?RHS
  guard_target = LHS = RHS
  exact h

example (a b c : Nat) : a + b + c = a + b + c := by
  name_parts ?X + ?Y = _
  guard_target = X + Y = X + Y
  rfl

-- Mixed named and anonymous holes
example (a b : Nat) : a + b = a + b := by
  name_parts ?S = _
  guard_target = S = S
  rfl

-- Nested arithmetic
example (a b c d : Nat) (h : (a + b) * (c + d) = 0) : (a + b) * (c + d) = 0 := by
  name_parts ?P * ?Q = ?Z
  guard_target = P * Q = Z
  exact h

-- Propositions
example (p q : Prop) (hp : p) (hq : q) : p ∧ q := by
  name_parts ?A ∧ ?B
  guard_target = A ∧ B
  exact ⟨hp, hq⟩

-- Naming one side of a non-trivial equality: `?A = _` names only the LHS
example (a b c : Nat) (h : a + b = c) : a + b = c := by
  name_parts ?A = _
  guard_target = A = c
  exact h

end BasicFunctionality

section NoContextPollution
/-! ### Regression test: no context pollution after complex sub-proofs

When a `have ... := by` sub-proof uses tactics like `apply prod.hom_ext` that leave
metavariable artifacts in the shared elaboration context, `name_parts` must not
materialize those artifacts as unwanted `let`-bindings. The fix: snapshot mvar IDs
before elaboration and only collect mvars created by the pattern elaboration itself.
-/

open Lean Elab Tactic Meta in
elab "guard_hyp_count " n:num : tactic => withMainContext do
  let lctx ← getLCtx
  let count := lctx.decls.toList.filterMap id |>.length
  let expected := n.getNat
  unless count == expected do
    throwError "guard_hyp_count: expected {expected} hypotheses, got {count}"

set_option linter.unusedTactic false in
open Limits in
example {C : Type*} [Category C] [Preadditive C] [HasBinaryProducts C]
    {X Y Z : C} (f g : X ⟶ Y ⨯ Z)
    (hfst : f ≫ prod.fst = g ≫ prod.fst)
    (hsnd : f ≫ prod.snd = g ≫ prod.snd) :
    f + g = g + f := by
  have key : f = g := by
    apply prod.hom_ext
    · exact hfst
    · exact hsnd
  guard_hyp_count 13
  name_parts ?LHS = ?RHS
  guard_hyp_count 15   -- exactly +2 (LHS, RHS), no pollution
  guard_target = LHS = RHS
  subst key; abel

end NoContextPollution

end HomologyLean.Tactic.NamePartsTest
