# Transport / Cast / `h ▸` Patterns

Strategies for eliminating `h ▸` (dependent transport) and `cast` in proofs.

## The `generalize` + `rcases` trick (PRIMARY TOOL)

**Problem**: You have `h : expr₁ = expr₂` where neither side is a free variable, and the
goal contains `h ▸ x`. `subst h` fails, `cases h` fails (dependent elimination), and the
transport blocks every tactic.

**Solution**: `generalize` one side to a fresh variable, making `rcases` possible:

```lean
-- Given: h : p + q = n + 1, goal has h ▸ ...
generalize hm : n + 1 = m at h ⊢   -- now h : p + q = m (m is fresh)
revert f                              -- revert anything that depends on generalized vars
rcases h                              -- eliminates h by substituting m := p + q
intro f
simp                                  -- eqToHom rfl = 𝟙, transport becomes id
```

After `rcases h`, `h ▸ x` becomes `rfl ▸ x = x`, and `eqToHom (congrArg ... rfl) = 𝟙`.

### When this fails: successor-indexed definitions

The `generalize` trick fails when the goal contains a definition that requires a
**successor pattern** in its index. Example:

```lean
SimplexCategory.δ : {n : ℕ} → Fin (n + 2) → ([n] ⟶ [n + 1])
```

After `generalize hm : n + 1 = m`, any `Fin (n + 2)` becomes `Fin (m + 1)`. But `δ`
expects `Fin (?n + 2)`, requiring `m + 1 = ?n + 2`, i.e., `m = ?n + 1`. Lean's unifier
can't decompose a generic `m` as a successor — `generalize` reports "result is not type
correct".

**Even fully unfolding `δ` doesn't help** — the underlying `Fin.succAboveOrderEmb` has
the same successor-indexed type signature.

**Note on `Fin` patterns**: `generalize hm : n + 1 = m` only replaces syntactic
occurrences of `n + 1`. It does NOT replace `n + 2` (which is `HAdd.hAdd n 2`, not
`(n + 1) + 1`). Use `show ∀ (i : Fin ((n + 1) + 1)), _` before `generalize` to
convert `Fin (n + 2)` to `Fin ((n + 1) + 1)` so the replacement hits it.

### Fix: decompose into transport-only + composition lemmas

When `generalize` fails due to successor-indexed definitions, **extract a helper lemma**
that handles only the transport, with no successor-indexed terms in its statement. Then
compose with the successor-indexed part separately.

**Concrete example** (`δ_cast_simplexProdMap`):

```lean
-- Step 1: Helper lemma — handles transport only, no SimplexCategory.δ
-- The generalize trick works here because there's no Fin (n + 2) or δ.
lemma cast_ulift_toSSet_down {p q n : ℕ} (h : p + q = n + 1)
    (X : TopCat) (f : stdSimplex (p + q) ⟶ X) :
    (h ▸ ULift.up f : (toSSet.obj X).obj (op [n+1])).down =
    eqToHom (congrArg (toTop.obj ∘ mk) h.symm) ≫ f := by
  generalize hm : n + 1 = m at h ⊢
  revert f; rcases h; intro f; simp

-- Step 2: Main lemma uses the helper after unfolding δ
lemma δ_cast_simplexProdMap ... := by
  apply ULift.ext
  dsimp only [SimplicialObject.δ]
  dsimp [TopCat.toSSet, Presheaf.restrictedULiftYoneda]
  -- Transport is now exposed as (h ▸ ULift.up f).down
  rw [cast_ulift_toSSet_down h]
  -- Remaining goal is pure composition, no transport
  ...
```

**Why decomposition works**: The transport `h ▸` lives in the "data plumbing" layer
(ULift, functor application). The successor-indexed `δ` lives in the "categorical" layer
(SimplexCategory morphisms). By separating them, each layer can be proved with its
natural technique: `generalize` for transport, categorical lemmas for composition.

## Pattern: push a degree cast through `Finsupp.single` / a structure constructor

When a `▸` over a degree equality `e : p + r = n` wraps a `Finsupp.single` of a
record-valued index (e.g. `BiOpLetter`), and `generalize` is blocked by
successor-indexed defs inside (e.g. `SimplexCategory.σ j : ⦋q+1⦌ ⟶ ⦋q⦌`), extract
**one transport-only helper per layer**, each proved by `subst e; rfl`:

```lean
-- single layer: cast commutes with `Finsupp.single`
private lemma cast_single (e : p + r = n) (l : BiOpLetter m m n n) (c : ℤ) :
    (e ▸ Finsupp.single l c : BiDerivedOp m m (p+r) (p+r))
      = Finsupp.single (e ▸ l) c := by subst e; rfl
-- constructor layer: cast distributes over a struct's fields
private lemma cast_diag (e : p + r = n) (f g : (⦋n⦌:SimplexCategory) ⟶ ⦋m⦌) :
    (e ▸ (⟨f, g⟩ : BiOpLetter m m n n)) = ⟨e ▸ f, e ▸ g⟩ := by subst e; rfl
-- predicate layer: a property (e.g. ¬Mono) transports
private lemma not_mono_cast (e : n = n') (θ : (⦋n⦌:SimplexCategory) ⟶ ⦋m⦌)
    (h : ¬ Mono θ) : ¬ Mono (e ▸ θ : (⦋n'⦌:SimplexCategory) ⟶ ⦋m⦌) := by subst e; exact h
```

Then `rw [hdeg, cast_single, cast_diag]` exposes `⟨e ▸ f, e ▸ g⟩`, and you apply the
target lemma with `θ := e ▸ f` (use `e.symm` for `not_mono_cast` since the morphism's
*domain* index is the one rewritten). **Gotcha**: those `rw`s often leave the degree
equality (`p + r = n`) as deferred `case h.e` motive side-goals — close them with
`all_goals first | exact hp | exact <main_lemma> …`.

## Related Mathlib lemmas

| Lemma | Signature | Use |
|-------|-----------|-----|
| `congrArg_cast_hom_left` | `cast ⋯ (q : Y ⟶ Z) = eqToHom p ≫ q` | Convert `cast` on a morphism's domain into `eqToHom ≫` |
| `congrArg_cast_hom_right` | `cast ⋯ (p : X ⟶ Y) = p ≫ eqToHom ⋯` | Convert `cast` on a morphism's codomain into `≫ eqToHom` |
| `eqToHom_map` | `F.map (eqToHom p) = eqToHom ⋯` | Push `eqToHom` through a functor |

## Prefer `eqToHom` over `subst` in definitions

**Problem**: A definition that uses `subst hn; exact data` to transport data across a
type equality produces opaque `h ▸` terms in every downstream goal. These block `rw`,
`simp`, and `subst` — and the `Eq.rec` form generated by `subst` inside a definition
differs from the `▸` notation form, so even `generalize_proofs` + `rw` can't match it.

**Solution**: When a definition needs to transport data across `(hn : n = expr)` in a
category with functors (e.g., `SSet`, `SimplicialObject`), use `F.map (eqToHom ...).op`
instead of `subst`. This produces a normal functor `map` that composes with other maps
via `← FunctorToTypes.map_comp_apply` and merges via `eqToHom_trans`.

**Key tools for the `eqToHom` approach**:
- `← FunctorToTypes.map_comp_apply`: fold `F.map f (F.map g x)` into `F.map (g ≫ f) x`
- `eqToHom_trans`: merge `eqToHom h₁ ≫ eqToHom h₂` into `eqToHom (h₁.trans h₂)`
- `Prod.ext` + `dsimp [SSet.tensorHom_app_apply]`: split tensor product `map` on pairs

**When `h ▸` still appears** (from an external source, not your definition): unfold the
definition first (so the `▸` becomes a plain transport on data), then use a helper lemma
`sset_transport_eq_map` (proved by `subst; simp`) to convert `▸` into `map (eqToHom)`.
The `rw` only matches *after* unfolding — the raw `subst`-generated `Eq.rec` has a
different form than `▸` notation.

## General principles

1. **`h ▸` is opaque** — it compiles to `Eq.mpr`/`Eq.rec` which blocks `simp`, `rw`, and
   pattern matching. Always try to eliminate it rather than compute through it.

2. **`generalize` before `rcases`/`cases`** — the standard trick for turning compound
   equalities into eliminable ones. Always `revert` dependent variables first.

3. **Decompose when `generalize` fails** — if the goal mixes transport with
   successor-indexed or pattern-matched definitions, extract the transport into a
   standalone helper lemma.

4. **`subst` needs a bare variable** — `subst h` only works for `h : x = expr` where `x`
   is a free variable. For compound equalities, use `generalize` to create a free variable
   first.

5. **Prefer `eqToHom` over `subst` in definitions** — when a definition takes
   `(hn : n = expr)` and needs to transport data, use `X.map (eqToHom ...).op` instead
   of `subst hn; exact ...`. This keeps downstream proofs compositional.
