# Bug: `lean_multi_attempt` reports false success (empty goals) for tactics that fail in file

## Summary

`lean_multi_attempt` returns `goals: []` and `diagnostics: []` for a tactic snippet, indicating the proof is complete. The same tactics fail when written into the file.

## Minimal reproduction

**File:** [`.claude/bugs/MultiAttemptMinRepro.lean`](MultiAttemptMinRepro.lean) (standalone, no imports)

```lean
def f (n : Nat) : Nat := n + 1
def g (n : Nat) : Nat := f n + 2

example : True := by
  let y := g 5
  suffices y + 3 = f 5 + 5 by trivial
  dsimp [g]  -- makes no progress: y stays opaque
  omega      -- fails: sees y and f 5 as unrelated
```

### File behavior

- `dsimp [g]` makes no progress (goal stays `y + 3 = f 5 + 5`)
- `omega` fails with: `omega could not prove the goal`

### `multi_attempt` behavior

```json
{
  "file_path": ".claude/bugs/MultiAttemptMinRepro.lean",
  "line": 49,
  "snippets": ["dsimp [g]\nomega"]
}
```

**Result:** `goals: []`, `diagnostics: []` — reports success.

## Root cause

`dsimp [g]` does not unfold `g` inside the `let`-bound variable `y` in the real file. The goal remains `y + 3 = f 5 + 5` where `y : Nat := g 5`.

`multi_attempt` apparently zeta-reduces the `let` binding before running tactics, so `dsimp [g]` sees `g 5 + 3 = f 5 + 5` (with `g 5` exposed) and successfully unfolds it to `f 5 + 2 + 3 = f 5 + 5`, which `omega` then closes.

## Impact

Silent correctness bug — the tool reports success with no warnings. An agent trusting `multi_attempt` writes tactics that fail, then must debug the discrepancy.
