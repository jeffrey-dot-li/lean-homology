---
name: plan
description: Draft sorry'd theorem/lemma structure for a larger result from a proof sketch.
---

# Plan Mode

Draft the theorem/lemma structure needed to prove a larger result.

Topic / proof sketch: $ARGUMENTS

## Procedure

1. **Research first** — search Mathlib and this project to understand what already exists.
2. Work **interactively** with the user to decompose the proof into lemmas.
3. Write all declarations with `sorry` proofs — **no filled proofs in this mode**.
4. Each lemma should be **provable independently in ~30 lines or fewer**.
5. Verify each `sorry`'d statement compiles with `lean_diagnostic_messages` before moving on.
6. Present the full dependency structure: which lemmas feed into which.

## Decomposition principle

The top-level theorem should read like a proof outline — each step composing named lemmas with simple plumbing (`rw`, `exact`, `simp`, `apply`). If the top-level proof still needs >10 lines of non-trivial tactics at any step, a lemma might be missing from the decomposition.

Prefer **general, reusable lemma statements** over proof-specific helpers. A good decomposition builds tools (e.g., `sigmaι_cancel`, `sigmaι_comp_fst_eq`) that apply beyond the current theorem.

## Output

A compilable file (or section) of `sorry`'d declarations with clear names and docstrings. Iterate with the user until the decomposition is right.

## Rules

- Every declaration must compile (with sorry) after writing.
- Use clear, descriptive names following Mathlib conventions.
- Include `/-- ... -/` docstrings explaining the mathematical content.
