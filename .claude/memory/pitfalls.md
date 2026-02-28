# Pitfalls

Things that look like they should work but don't. Check here before trying common approaches.

## `rfl` cannot unfold recursive calls inside a pattern-matched definition

Inside a recursive `def` with pattern matching (e.g. `| 0 => ... | 1 => ... | n + 2 => ...`),
you **cannot** use `rfl`, `change`, or `unfold` to reduce a recursive call like `f 0` from within the `| 1 =>` case.
The equation lemma doesn't exist yet during compilation.

**Symptom**: `rfl` fails with "type mismatch: rfl has type ?m = ?m but expected f ... = ..."

**Fix**: Bundle the morphism with its key property using a Subtype, so each inductive step receives
the property from the IH instead of trying to unfold the recursive call:
```lean
-- Define a @[simp] predicate so it reduces at concrete n values
@[simp] def myProp : (n : ℕ) → (α : ...) → Prop
  | 0, α => ...
  | n + 1, α => ...

private def myAux : ∀ n, { α : ... // myProp n α }
  | 0 => ⟨base, base_proof⟩
  | n + 1 => by
    obtain ⟨prev, hprev⟩ := myAux n
    simp only [myProp] at hprev  -- reduces the match
    ...

def myDef (n : ℕ) := (myAux n).1
```

**Key details**:
- The `@[simp]` on the Prop definition is essential — `unfold` alone won't reduce `match` in Subtypes
- Use `simp only [myProp] at h` to reduce the property at concrete indices
- Structure projections (e.g. `.g` of a `ShortComplex`) may not reduce for `exact` — use `simp` or `dsimp` first

## `obtain ⟨a, b⟩ := ...` can't eliminate `∃` into `Type`

`Exists.casesOn` can only produce `Prop`, not data. If your `desc` function needs the
witness from an existence theorem, you need `PSigma` (`Σ'`) not `∃`.

**Symptom**: "type mismatch ... expected type must be a sort" or the `obtain` hangs/fails.

**Fix**: Write a `PSigma`-returning wrapper:
```lean
def foo_psigma (...) : Σ' (i : ι) (τ : ...), σ = τ ≫ sigmaι X i := by
  classical
  have h := foo_exists ...  -- the ∃ version
  exact ⟨h.choose, h.choose_spec.choose, h.choose_spec.choose_spec⟩
```
Then `obtain ⟨i, t, ht⟩ := foo_psigma ...` works in any context.

## `F.map` for `TopCat.toSSet ⋙ eval (op [n])` is NOT definitional

`(F.map g y).down` does NOT reduce by `rfl`/`dsimp` to `y.down ≫ g`.

**Fix**: `simp only [F, Functor.comp_map, evaluation_obj_map]` then `change _ = t ≫ sigmaι f i`.
Or in the reverse direction, `simpa using ht` when the hypothesis already has the concrete form.

## `have ⟨a, b⟩ := ...` parsing with Unicode subscripts

Pattern-matching `have` can fail with "unexpected token '⟨'" when variable names contain
complex Unicode (e.g. `αₙ₊₁`). Use `obtain ⟨a, b⟩ := ...` or simpler ASCII names instead.

## `0 + n ≠ n` definitionally — use product order to avoid casts

`Nat.add` recurses on the **second** argument, so `n + 0 = n` is definitional but `0 + n ≠ n`.
This matters for `crossProduct p q` which outputs at degree `p + q`:
- `crossProduct n 0` → degree `n + 0 = n` ✓ (no cast)
- `crossProduct 0 n` → degree `0 + n ≠ n` ✗ (needs `Nat.zero_add` cast)

**Fix**: When building cross products with a fixed factor (e.g. `Δ[1]`), put the variable-degree
space **first**: use `X ⨯ Δ[1]` (not `Δ[1] ⨯ X`) so that `crossProduct n 1` outputs at `n + 1`
and `crossProduct n 0` outputs at `n`. Route through `prod.braiding` to swap if the original
construction uses the other order.

Similarly, `1 + n ≠ n + 1` definitionally. Using `crossProduct n 1` avoids the `add_comm 1 n ▸`
cast that `crossProduct 1 n` would require.

## `Sigma.hom_ext` introduces `Sigma.ι (fun x ↦ R) τ` not `mι τ`

After `apply Sigma.hom_ext; intro τ`, the coprojection is `Sigma.ι (fun x ↦ Rmod R) τ`,
which does NOT syntactically match `mι τ` even though they're definitionally equal.

**Symptom**: `rw [some_lemma_about_mι]` fails with "did not find occurrence of pattern".

**Fix**: Add `have hτ : Sigma.ι (fun x ↦ Rmod R) τ = mι (R := R) τ := rfl` then `rw [hτ]`
before the rewrite that needs `mι`.
