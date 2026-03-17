# Non-terminal `simp` analysis for `EilenbergZilber.lean`

I scanned the unrestricted `simp` occurrences in
`HomologyLean/SingularHomology/EilenbergZilber.lean`, using the Lean style-guide rule
from <https://leanprover-community.github.io/extras/simp.html>:

- mid-proof `simp only [...]` is acceptable;
- unrestricted `simp` should preferably be terminal;
- `simpa` is preferred when simplification is only being used to finish a goal.

For this note, I counted only unrestricted `simp`:

- included: `simp`, `simp [lemmas]`, `simp at h`, `simp at ⊢ h`
- excluded: `simp only`, `simp_rw`, `simpa`

## High-level conclusion

There are many unrestricted `simp` calls in the file, but almost all of them are already
terminal in the sense relevant to the style guide.

The real non-terminal cases are a small arithmetic cluster:

- lines 577, 582, 641, 643: `simp [Fin.val_cast] ...; omega`
- line 1438: `simp [SimplexCategory.len_mk] at hi; omega`

So this file does **not** have a broad non-terminal-`simp` problem. The issue is local and
mostly concentrated in small proofs that normalize `Fin`/`len` arithmetic before handing the
goal to `omega`.

## What I checked with Lean MCP

I used Lean MCP in two ways:

1. `lean_goal` to confirm representative terminal `simp`s really close their current goal.
   For example:
   - line 370: `simp` leaves `goals_after = []`
   - line 1499: `simp [MonoidalCategory.curriedTensor]` leaves `goals_after = []`
2. `lean_multi_attempt` to test the arithmetic cases without editing the file.
   Representative results:
   - line 577:
     `simp [Fin.val_cast] at hr_eq ⊢` leaves a remaining equality goal, but
     `simpa [Fin.val_cast] using hr_eq` closes it.
   - line 582:
     `simpa using hr_eq.symm` closes the local goal directly.
   - line 641:
     `simpa using hr_eq.symm` also closes the local goal directly.

This confirms that the arithmetic cluster is genuinely non-terminal, and that most of those
sites can be cleaned up without changing the proof structure.

## Terminal unrestricted `simp`s

These are unrestricted `simp`s, but they are already terminal and so are not the style-guide
problem under discussion.

### Goal-closing `simp` / theorem-ending `simp`

- line 71: `subst hn; simp`
- line 116: `subst h; simp`
- line 358: `simp [CategoryTheory.Limits.Sigma.ι_comp_map']`
- line 370: `simp`
- line 420: `simp [CategoryTheory.Limits.Sigma.ι_comp_map']`
- line 1471: `simp`
- line 1499: `simp [MonoidalCategory.curriedTensor]`
- line 1528: `simp [MonoidalCategory.curriedTensor]`
- line 1600: `simp [Category.assoc, MonoidalCategory.tensorHom_def]`

### Goal-closing `simp` on a local subgoal

- line 65: `apply ...; simp [SSet.yonedaEquiv_comp]`
- line 351: `simp [SimplexCategory.hom_zero_zero]`
- line 661: `simp [Category.assoc]`
- line 669: `simp [Category.assoc]`
- line 699: `simp [Equiv.ulift]`
- line 729: `simp [Equiv.ulift]`

### `by simp` micro-proofs

These are local proofs where `simp` is the whole proof term or closes the local goal it is
introduced to solve.

- line 340: `have : ... := by simp [Shuffle.sign, Shuffle.invCount]`
- line 1003: `from by simp [Category.assoc]`
- line 1130: `from by simp [faceSimplex, idSimplex, SimplicialObject.δ, ...]`
- line 1154: `from by simp [faceSimplex, idSimplex, SimplicialObject.δ, ...]`
- line 1459: `from by simp [ComplexShape.down_Rel]`
- line 1461: `... (by simp)`
- line 1491: `(fun h => by simp [ComplexShape.down_Rel] at h)`
- line 1494: `from by simp [ComplexShape.down_Rel]`
- line 1520: `(fun h => by simp [ComplexShape.down_Rel] at h)`
- line 1523: `from by simp [ComplexShape.down_Rel]`
- line 1526: `from by simp [ComplexShape.ε₂, ComplexShape.ε]`

## Genuine non-terminal unrestricted `simp`s

## 1. `Fin.val_cast` cleanup before `omega`

Occurrences:

- line 577
- line 582
- line 641
- line 643

These all have the same shape: use unrestricted `simp` to normalize away `Fin.cast` in
equalities, then finish the arithmetic with `omega`.

### Line 577

Current pattern:

```lean
simp [Fin.val_cast] at hr_eq ⊢; omega
```

Lean MCP result:

- `simp [Fin.val_cast] at hr_eq ⊢` does **not** close the goal by itself.
- `simpa [Fin.val_cast] using hr_eq` **does** close the goal.

Diagnosis:

- This is a textbook non-terminal `simp`.
- The unrestricted simplifier is only being used to make the goal match an already available
  hypothesis.

Best cleanup:

```lean
simpa [Fin.val_cast] using hr_eq
```

### Lines 582, 641, 643

Current pattern:

```lean
simp [Fin.val_cast] at hr_eq; omega
```

or, at line 643, the same pattern inside `Fin.ext (by ...)`.

Lean MCP result:

- `simpa using hr_eq.symm` closes the representative goals at lines 582 and 641 directly.

Diagnosis:

- These are the same phenomenon as line 577, except the target equality is the reverse
  orientation of `hr_eq`.
- Again, unrestricted `simp` is only preparing the goal for a hypothesis that is already in
  the context.

Best cleanup:

```lean
simpa using hr_eq.symm
```

For line 643, the same replacement should work inside the nested `by` proof.

## 2. `SimplexCategory.len_mk` normalization before `omega`

Occurrence:

- line 1438

Current pattern:

```lean
by
  simp [SimplexCategory.len_mk] at hi
  omega
```

Diagnosis:

- This is also a genuine non-terminal unrestricted `simp`.
- Here the bound proof can in fact be made terminal directly.

Verified cleanup:

```lean
by
  simpa [SimplexCategory.len_mk] using hi
```

## Summary by site

### Genuine non-terminal unrestricted `simp`

- 577: replace with `simpa [Fin.val_cast] using hr_eq`
- 582: replace with `simpa using hr_eq.symm`
- 641: replace with `simpa using hr_eq.symm`
- 643: same as 641, inside a nested `by`
- 1438: replace with `by simpa [SimplexCategory.len_mk] using hi`

### Not a problem under the style-guide rule

- every other unrestricted `simp` in the file is already terminal, or is a `by simp`
  micro-proof closing the local goal it was introduced to solve

## Overall takeaway

Compared to the `erw` audit, this is a much smaller cleanup task.

The file's unrestricted `simp`s are mostly fine. The real style-guide issues are a handful of
small arithmetic proofs where `simp` is being used as a preparatory normalization step before
`omega`. In every case here, the cleanup is simpler than that pattern: each one collapses to a
terminal `simpa`.
