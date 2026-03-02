# Proof Strategies

General tactics and Lean patterns. Read this before starting any proof work.

## Goal state discipline (CRITICAL)

**Keep intermediate goals compact.** Bloated goals make it impossible for the user to
supervise progress vs looping, and impossible for the agent to reason about what to do next.

### Correctness first, style second
- **Priority 1:** Get the proof to compile. Use `simp`, `aesop`, `grind`, whatever works.
- **Priority 2:** Optimize for speed (`simp` → `simp only`, `grind` → direct proof, etc.) *after* it compiles.
- `simp only` is a Mathlib style requirement because library lemmas are used heavily downstream. For *our* proofs, correctness comes first — replace `simp` with `simp only` via `simp?` as a polish step, not during initial proving.
- Keeping goals concise is about **reasoning efficiency during proving**, not style.

### `simp` vs `simp only` during proving
- Default to **`simp`** during `/fill-sorry`. It's faster to write, and correctness comes first.
- The only reason to use `simp only [...]` during proving is when you want to **partially simplify** — i.e., reduce to a specific level without going all the way down. In this case, write a comment explaining what you're deliberately *not* simplifying and why (e.g., `-- simp only to avoid unfolding SCF internals`).
- Replace `simp` with `simp only` via `simp?` as a **polish step** after the proof compiles.

### Push simplification up, not down
- Simplify **before** `congr`, `ext`, or structural tactics — not after.
- If `simp`/`dsimp` would reduce a goal from 15 lines to 3, do it *before* splitting into subgoals.
- Unfolding definitions too early (e.g., `SCF`, `singChain`, `TopCat.toSSet`) causes goal blowup. Instead, use rewrite lemmas (like `mι_comp_map`) that keep the goal in high-level categorical language.

### Extract rewrite lemmas to avoid unfolding
- If the proof needs to unfold a definition, push through it, and re-fold — that's a missing lemma.
- Example: `mι_comp_map` captures `mι s ≫ chain_map f = mι (f_*(s))` without ever exposing `colimit.ι_desc` or `TopCat.toSSet` internals.
- The main proof stays in compact categorical notation; the ugly unfolding is isolated in the helper lemma.

### `congr` introduces `id` wrappers
- `congr 1` can wrap subterms in `id (...)`, which blocks `simp only` pattern matching.
- Either `dsimp` immediately after `congr`, or use `change`/`show` to state the clean goal, or accept a `simp` at the end.

---


## General Lean Pitfalls and Strategies

### Definitional equality is gold (CRITICAL)

**The single most impactful design choice in Lean 4/Mathlib proofs is ensuring types and terms
match _definitionally_ (by `rfl`/reduction) rather than merely _propositionally_ (requiring
`rw`/`simp`/`eqToHom`/`cast`).** When you have a choice of construction, representation, or
argument order, always pick the one that preserves definitional equality. When you're stuck
because `rfl` fails, `simp` can't match, or goals are polluted with `eqToHom`, the root cause
is almost always a definitional-vs-propositional gap.

**Why it matters so much:**
- `rfl` closes goals instantly; propositional rewrites cost lines and can cascade
- Type unification works automatically with definitional equality; `eqToHom` blocks it
- `simp` patterns match definitionally-equal terms; syntactic mismatches from propositional
  equality cause "made no progress" on visually-matching goals
- `ConcreteCategory.hom` and other opaque wrappers are not definitionally transparent —
  going pointwise through them creates goals that no amount of `simp` can close

**Instances of this principle throughout the project:**

| Situation | Definitional (prefer) | Propositional (avoid) | Details |
|-----------|----------------------|----------------------|---------|
| Argument order | `crossProduct n 0` (degree `n+0 = n`) | `crossProduct 0 n` (degree `0+n ≠ n`) | [proof-strategies.md § `0+n ≠ n`](#0--n--n-definitionally--use-product-order-to-avoid-casts) |
| Building NatIsos | `NatIso.ofComponents` (`.hom.app X` reduces) | Functor-level `≪≫` (leaves stray `𝟙`) | [monoidal-tensor.md § ofComponents](api/monoidal-tensor.md) |
| TopCat pointwise | Stay categorical (`prod.lift_fst`) | Go pointwise through `ConcreteCategory.hom` | [topcat-limits.md](api/topcat-limits.md) |
| Coercion matching | `erw` / `convert` (handles defeq mismatch) | `rw` / `simp` (fails on syntactic mismatch) | [monoidal-tensor.md § ConcreteCategory.hom vs Hom.hom](api/monoidal-tensor.md) |
| Opaque goal exprs | `convert target_lemma` (unifier matches) | `have hf : f = id` (re-elaboration fails) | [proof-strategies.md § convert](#use-convert-to-bypass-opaque-subexpressions-you-cant-restate) |

**When stuck, ask:** "Is the real problem that two things are propositionally but not
definitionally equal?" If yes, restructure to restore definitional equality — or use `erw`/
`convert`/`change` to bridge the gap.


### `rfl` cannot unfold recursive calls inside a pattern-matched definition

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

### `obtain ⟨a, b⟩ := ...` can't eliminate `∃` into `Type`

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

### `have ⟨a, b⟩ := ...` parsing with Unicode subscripts

Pattern-matching `have` can fail with "unexpected token '⟨'" when variable names contain
complex Unicode (e.g. `αₙ₊₁`). Use `obtain ⟨a, b⟩ := ...` or simpler ASCII names instead.

### `0 + n ≠ n` definitionally — use product order to avoid casts

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

### Use `convert` to bypass opaque subexpressions you can't restate

When the goal contains an elaborated subexpression (e.g. involving `ConcreteCategory.hom`,
`default` resolved to a specific type, complex coercions) that you **cannot reproduce** in a
`have`/`suffices` statement due to elaboration failures (lost coercions, unresolved typeclasses,
`SimplexCategory.Hom.mk` vs `⟶` mismatch), use `convert` instead of `rw`/`have`.

**Symptom**: Writing `have hf : f = id` or `suffices h : expr = ...` fails with type mismatch,
coercion errors, or unresolved `default`/typeclass — even though the same expression exists in
the goal and was built fine by the elaborator.

**Fix**: Use `convert target_lemma args` to let Lean's unifier match the goal against the lemma
and generate subgoals from the already-elaborated context:
```lean
-- Goal: stdSimplex.map ⇑(ConcreteCategory.hom ...) ⟨i, hi⟩ = ⟨i, hi⟩
-- Can't write: have hf : ⇑(ConcreteCategory.hom ...) = id  (elaboration fails)
-- Instead:
convert stdSimplex.map_id_apply ⟨i, hi⟩  -- Lean unifies f with id automatically
```

**Why it works**: `convert` operates on the goal's already-elaborated terms. It doesn't require
you to re-elaborate the problematic expression — it just asks "what subgoals would make this
lemma's conclusion match the current goal?" and lets Lean's unifier handle the rest.
