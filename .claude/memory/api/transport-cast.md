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

## Related Mathlib lemmas

| Lemma | Signature | Use |
|-------|-----------|-----|
| `congrArg_cast_hom_left` | `cast ⋯ (q : Y ⟶ Z) = eqToHom p ≫ q` | Convert `cast` on a morphism's domain into `eqToHom ≫` |
| `congrArg_cast_hom_right` | `cast ⋯ (p : X ⟶ Y) = p ≫ eqToHom ⋯` | Convert `cast` on a morphism's codomain into `≫ eqToHom` |
| `eqToHom_map` | `F.map (eqToHom p) = eqToHom ⋯` | Push `eqToHom` through a functor |

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
