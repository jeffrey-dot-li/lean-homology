# assistants.md

Guidance for Code Assistant Agents working in this repository.

## Project Overview

Lean 4 formalization of homotopy computations in algebraic topology.

## Terminal Settings

Commands use `fish` shell syntax.

## Skills & Agents

Use the **lean4-theorem-proving** skill and its sub-commands for all Lean 4 proof work:

| Task | Skill / Agent |
|------|---------------|
| Build & check errors | `/lean4-theorem-proving:build-lean` |
| Fill a `sorry` | `/lean4-theorem-proving:fill-sorry` |
| Repair a broken proof | `/lean4-theorem-proving:repair-goal`, `/lean4-theorem-proving:repair-file` |
| Search mathlib | `/lean4-theorem-proving:search-mathlib` |
| Analyze remaining sorries | `/lean4-theorem-proving:analyze-sorries` |
| Golf / shorten proofs | `/lean4-theorem-proving:golf-proofs` |
| Clean linter warnings | `/lean4-theorem-proving:clean-warnings` |
| Check axiom hygiene | `/lean4-theorem-proving:check-axioms` |
| Refactor have-blocks | `/lean4-theorem-proving:refactor-have` |
| Interactive repair | `/lean4-theorem-proving:repair-interactive` |

For batch work, use **subagents** (`lean4-subagents:lean4-sorry-filler`, `lean4-proof-repair`, etc.).

The skill provides comprehensive references for tactics, patterns, error handling, and mathlib search. Consult those instead of duplicating guidance here.

## Operating Instructions

- Use `lean_diagnostic_messages` on the entire theorem after completing a proof
- Ensure no errors before proceeding to the next proof
- **Never leave a theorem without verifying it compiles**

## Project-Specific Patterns

### Working with Quotients

```lean
have h := Quotient.mk_out q          -- extract representative
exact Quotient.exact (some_equality)  -- quotient equality → relation
exact Quotient.sound (some_relation)  -- relation → quotient equality
```

### Working with Homotopies

```lean
-- Path.Homotopic ≈ ContinuousMap.HomotopyRel ... {0, 1}
refine ⟨{
  toFun := fun ⟨s, t⟩ => ...
  continuous_toFun := by continuity / fun_prop
  map_zero_left := by ...
  map_one_left := by ...
  prop' := by ...
}⟩
```

### Using Covering Maps

```lean
set lift := cov.liftPath γ e γ_0
have h_lifts := cov.liftPath_lifts γ e γ_0
have h_mono := cov.liftPath_apply_one_eq_of_homotopicRel h e₁ e₂
```
