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

### Use `conv`/`slice` before `have` for targeted rewrites (CRITICAL)

When `rw`/`simp` fail because the goal is large and the pattern appears nested inside
a complex expression, **always reach for `conv` or `slice_lhs`/`slice_rhs` first**. Do NOT
default to writing a giant `have` block that restates the subexpression — this produces
bloated, fragile code and wastes time on elaboration mismatches.

**Bad pattern (avoid):**
```lean
-- rw [lemma] failed because goal is big
have h : complex_subexpr = rewritten_form := by ...  -- 5+ lines restating the goal
rw [h]
```

**Good pattern (prefer):**
```lean
-- rw [lemma] failed because goal is big
conv_rhs => enter [1, 1, 2]; rw [lemma]        -- surgical, 1 line
-- or for categorical compositions:
slice_lhs 3 4 => erw [Functor.map_id, ...]     -- targets morphisms 3-4
```

**When to use each:**
- `slice_lhs i j` / `slice_rhs i j`: for rewriting a contiguous range of morphisms in
  a categorical composition `a ≫ b ≫ c ≫ d`. Handles `Category.assoc` automatically.
- `conv_lhs` / `conv_rhs` + `enter`: for anything else — rewrites inside `⊗ₘ`, under `∑`,
  inside functor applications, etc. More general than `slice`.
- `have` with manual restatement: **last resort only**, when the subexpression genuinely
  can't be targeted by `conv`/`slice` (e.g., it spans both sides of the equation).

### Extract rewrite lemmas to avoid unfolding
- If the proof needs to unfold a definition, push through it, and re-fold — that's a missing lemma.
- Example: `mι_comp_map` captures `mι s ≫ chain_map f = mι (f_*(s))` without ever exposing `colimit.ι_desc` or `TopCat.toSSet` internals.
- The main proof stays in compact categorical notation; the ugly unfolding is isolated in the helper lemma.

### `congr` pitfalls
- `congr 1` can wrap subterms in `id (...)`, which blocks `simp only` pattern matching.
  Either `dsimp` immediately after `congr`, or use `change`/`show` to state the clean goal.
- `congr 1` on `F.map f = F.map g` (for a concrete-category functor like `toTop`) does
  **not** reduce to `f = g` — it goes pointwise through `ConcreteCategory.hom`, producing
  goals about function values. Use `congr 1` **twice** to peel off the functor application,
  or fold both sides into `F.map(f ≫ ...) = F.map(g ≫ ...)` first so the first `congr 1`
  strips `≫ rest` and the second strips `F.map`.

---


## `lean_goal` does NOT confirm a tactic compiled (CRITICAL)

`lean_goal` on the line *after* a tactic will show a goal state even if the tactic has an error
(e.g., "`simp` made no progress", type mismatch). The goal shown is simply the unchanged state.
This silently passes bad tactics through the feedback loop.

**After every tactic edit**, check `lean_diagnostic_messages` with `start_line`/`end_line`
targeting the edited line(s) **before** checking `lean_goal`. If diagnostics show an error,
revert the edit. Never trust `lean_goal` alone as proof that a tactic worked.

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
| eqToHom through functor | Fold into `F.map(...)`, prove in source cat | Fight bare `eqToHom` in target cat | [eqToHom-casting.md](api/eqToHom-casting.md) |

**When stuck, ask:** "Is the real problem that two things are propositionally but not
definitionally equal?" If yes, restructure to restore definitional equality — or use `erw`/
`convert`/`change` to bridge the gap.

---

## `slice_lhs`/`slice_rhs` for categorical compositions

When the goal is `a ≫ b ≫ c ≫ d = ...` and you need to rewrite a specific pair (e.g.,
fold `b ≫ c` via `← Functor.map_comp`), don't fight `Category.assoc`. Use `slice_lhs i j`
(1-indexed) to isolate morphisms `i` through `j`:

```lean
slice_lhs 2 3 => rw [← Functor.map_comp]   -- targets b ≫ c
slice_rhs 1 2 => rw [show eqToHom _ = F.map ... from (eqToHom_map _ _).symm]
```

This is strictly better than manual `Category.assoc` + `conv` for categorical proofs.

---

## `dsimp` for `def`s, `simp` for `@[simp]` lemmas

`simp` applies rewrite rules (equational lemmas, `@[simp]`-tagged lemmas). It **cannot**
unfold a plain `def` that has no `@[simp]` tag or equational lemma. Use `dsimp [defName]`
for definitional reduction first, then `simp` on the result.

**Symptom**: `simp [Foo]` "made no progress" even though `Foo` appears in the goal.

**Common in this project**: `Fin.succAboveOrderEmb`, `OrderEmbedding.ofStrictMono` need
`dsimp` before `simp` can work on `Fin.succAbove`.

---

## Lemma won't match the goal? Use `conv` + one `enter` at a time (CRITICAL)

If `rw [h]` / `erw [h]` / `simp_rw [h]` fail to apply a lemma at the top level, **STOP
immediately.** Do NOT try `simp_rw [show ∀ ... from ...]`, universe annotations, or
repeated `erw` tweaks. **Do NOT use a global `simp` to normalize the goal** — it blows
up the goal state and makes everything harder to read. These all loop forever.

**Instead**: use `conv` to drill down, one `enter` at a time, then apply the lemma
surgically. Escalate through these levels only as needed:

```
conv_lhs =>
  enter [2, x]    -- one step at a time, check goal after each
  enter [2]
  enter [2, x_1]
  enter [2]
  -- Level 1: try rw directly
  rw [lemma args]
  -- Level 2: if rw fails, try erw (handles more defeq mismatches)
  erw [lemma args]
  -- Level 3: if erw also fails, use tactic => to construct h with
  -- exact bound variables, then simp just h, then rw h
  tactic =>
    have h := lemma arg1 (↑x) x_1
    simp at h
    rw [h]
```

**Why this works:** Inside `conv`, binder variables (`x`, `x_1`) are in scope. At level
3, you pass them explicitly to the lemma — fully instantiated, no metavariables — which
bypasses every possible matching issue (universes, notation, binders).

**Rules:**
1. Add ONE `enter` at a time. Check the conv goal state after each. Do not guess the path.
2. `enter [2, binder]` enters a `Finset.sum` (arg 2 is the lambda).
3. `enter [2]` skips past the left operand of `HSMul.hSMul` (i.e., past `c •`).
4. Always try `rw` → `erw` → `tactic =>` in order. Don't skip to level 3.

**Checking conv goals with `lean_goal` (CRITICAL):**
Inside a `conv` block, the focused subexpression (shown as `| expr` in the IDE) is only
visible via `lean_goal` at the **end-of-line column** of the `enter` or tactic line. Using
a small column (e.g., column 4–6) returns the outer tactic goal, not the conv focus.

```
conv_rhs =>
  enter [1, 1, 2]    -- check goal at this line, column = end of line (e.g., 22)
  rw [some_lemma]     -- check diagnostics to confirm it compiled
```

- After each `enter`, call `lean_goal` at `(line, end_of_line_column)` to see the `| focused_expr`.
- After a `rw`/`erw` inside conv, use `lean_diagnostic_messages` to confirm no errors.
- If unsure about the conv focus, ask the user — they can see it in the IDE infoview.

---


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

### `set` doesn't fold `abbrev` terms reliably

`set K := myAbbrev args` creates a `let` binding, but the goal may still contain the
*elaborated* form of `myAbbrev args` instead of `K`. This happens because `set` uses
syntactic matching, and `abbrev`s can elaborate with different implicit arguments in the
goal vs the `set` expression.

**Symptom**: After `set K := singChain ...`, the goal still shows `(singChain ...).d` instead
of `K.d`. Then `simp_rw [d_shift]` (where `d_shift` is stated about `K`) can't match.

**Fix**: Don't rely on `set` for syntactic folding of `abbrev` terms. Instead:
- State your `have` lemma directly about the full expression (not the `set` variable)
- Use `conv_lhs => rw [show full_expr = ... from ...]` to target the exact subexpression

### `subst` needs a free variable on one side

`subst h` only works when `h : x = expr` or `h : expr = x` where `x` is a **free variable**
in the context. It fails on `h : expr1 = expr2` where both sides are compound (e.g.
`h : p + 1 + (q + 1) = p + q + 1 + 1`).

**Fix**: Use `.symm` on a matching lemma instead of `subst`. For example, if you have a lemma
`eqToHom_comp_d K h` that takes `h : i = i'`, use `(eqToHom_comp_d K hrel).symm` as a proof
term rather than trying to `subst hrel`.

For eliminating `h ▸` transports when `subst` fails, see **[`api/transport-cast.md`](api/transport-cast.md)**
— use `generalize` to create a fresh variable, then `rcases`. If that also fails (due to
successor-indexed defs like `SimplexCategory.δ`), decompose into a transport-only helper lemma.

### `rw`/`erw` can't rewrite under `∑` binders; universe mismatches block `simp_rw`

`rw`/`erw` don't descend into lambda binders (`∑ x, f x` has a lambda). `simp_rw` does,
but silently fails when the lemma's universe doesn't match the goal's (common when the
lemma doesn't reference a section variable pinning `v`). Both symptoms look like "did not
find occurrence" on a visually matching pattern. **Fix: use the `conv` strategy above.**

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
