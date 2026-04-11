/-
## Bug: `lean_multi_attempt` reports false success for `simpa ... using rfl`

### Summary

`lean_multi_attempt` reports success for a `simpa` proof that fails in the real file.
Like `MultiAttemptMinRepro.lean`, this appears to involve zeta-reducing a `let`-bound
variable before running the snippet.

### How to reproduce

1. Open this file and wait for it to check.
2. Confirm that the proof on line 15 errors with:
   `Type mismatch: After simplification, term rfl has type True but is expected to have type y = 7`.
3. Call `lean_multi_attempt` at line 15 with:
   ```json
   {
     "file_path": ".claude/bugs/MultiAttemptMinRepro2.lean",
     "line": 15,
     "snippets": ["simpa [h] using rfl"]
   }
   ```
4. **Observed:** `goals: []` and no errors, i.e. false success.

### Why this should fail in-file

In the real goal, `y` is a local `let`-bound variable with goal `y = 7`.
`simpa [h] using rfl` starts from `rfl : True`/`?m = ?m` and cannot turn that into `y = 7`
without unfolding the `let`.

If `multi_attempt` zeta-reduces `let y := h 5` first, the goal becomes `h 5 = 7`,
which `simpa [h]` can close.
-/

def h (n : Nat) : Nat := n + 2

example : True := by
  let y := h 5
  suffices y = 7 by trivial
  simpa [h] using rfl
