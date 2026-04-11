/-
## Bug: `lean_multi_attempt` reports false success for `dsimp`-based tactics

### Summary

`lean_multi_attempt` returns `goals: []` (proof complete) for a snippet,
but the same tactics fail when written into the file.

### How to reproduce

1. Open this file and wait for it to check.
2. Confirm that `omega` on line 50 errors:
   ```json
   {
     "file_path": ".claude/bugs/MultiAttemptMinRepro.lean",
     "line": 50,
     "severity": "error"
   }
   ```
   Error: `omega could not prove the goal` — because `dsimp [g]` on
   line 49 made no progress (`y` is still opaque).

3. Call `lean_multi_attempt` at line 49 (replacing `dsimp [g]`):
   ```json
   {
     "file_path": ".claude/bugs/MultiAttemptMinRepro.lean",
     "line": 49,
     "snippets": ["dsimp [g]\nomega"]
   }
   ```

4. **Expected:** Should report an error matching the file.
5. **Observed:** Reports `goals: []`, `diagnostics: []` (success).

### Root cause

`dsimp [g]` does not unfold `g` inside the `let`-bound `y` in the real
file (goal stays `y + 3 = f 5 + 5`). But `multi_attempt` apparently
zeta-reduces the `let` binding before running tactics, so `dsimp [g]`
sees `g 5 + 3 = f 5 + 5` and successfully unfolds `g`.
-/

def f (n : Nat) : Nat := n + 1
def g (n : Nat) : Nat := f n + 2

example : True := by
  let y := g 5
  suffices y + 3 = f 5 + 5 by trivial
  -- Goal: `y + 3 = f 5 + 5` where `y : Nat := g 5`.
  -- `dsimp [g]` makes no progress — `y` stays opaque.
  -- `omega` then fails because it sees `y` and `f 5` as unrelated.
  -- But `multi_attempt` at line 49 with `"dsimp [g]\nomega"` claims success.
  dsimp [g]
  omega
