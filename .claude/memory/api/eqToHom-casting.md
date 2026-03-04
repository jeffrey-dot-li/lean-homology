# eqToHom Through Functors — General Principles

When a propositional-but-not-definitional equality (like `Nat.add` associativity) infects a categorical proof, `eqToHom` morphisms appear. These are the general strategies for dealing with them — applicable to any functor `F : C ⥤ D`, not just `SimplexCategory.toTop`.

## Principle 1: Retreat to the simplest category

**`eqToHom` in `D` is harder than `eqToHom` in `C`.**

When your goal has `eqToHom` at the level of `D` (e.g., `TopCat`), convert it to `F.map(eqToHom)` in `C` (e.g., `SimplexCategory`) using:

```lean
(eqToHom_map F h).symm   -- F.map (eqToHom h) = eqToHom (congrArg F.obj h)
```

Then fold adjacent `F.map` applications with `← Functor.map_comp` to consolidate everything into a single `F.map(...)`. Now you only need to prove an equality in `C`, where morphisms are simpler (e.g., `OrderHom`s on `Fin` instead of continuous maps on topological spaces).

**Why this works**: `eqToHom` in `D` is opaque — `simp` can't see through `ConcreteCategory.hom`, `congr` produces `HEq` across different types. But in `C`, morphisms are often data (finite maps, order-preserving functions) where `ext` + `omega` can close things.

**Pitfall — going pointwise in the wrong category**: If you `ext` in `TopCat` (e.g., `ext ⟨x, hx⟩ i`) instead of retreating to `SimplexCategory` first, you enter a world of `ConcreteCategory.hom`, `ContinuousMap.coe_mk`, `FunOnFinite.linearMap`, `Finsupp.mapDomain`, etc. that is nearly impossible to close. Always retreat to the source category *before* going pointwise. Extract a bridge lemma in `SimplexCategory` (where `ext + omega` works cleanly), then use functoriality (`eqToHom_map`) to lift the result. See Principle 9 for the full pattern.

## Principle 2: Absorb `eqToHom` into data at the boundary

Don't let `eqToHom` propagate into the middle of a complex proof. Write small helper lemmas (proved by `subst; simp`) that absorb it at the interface:

```lean
-- Pattern: coprojection ≫ eqToHom = coprojection(transported data)
lemma foo_comp_eqToHom (h : n = m) (s : Data n) :
    foo s ≫ eqToHom (congrArg F h) = foo (h ▸ s) := by subst h; simp

-- Pattern: (h ▸ wrapper(f)).unwrap = eqToHom _ ≫ f
lemma cast_wrapper_unwrap (h : n = m) (f : A n ⟶ B) :
    (h ▸ wrap f).unwrap = eqToHom (...h.symm) ≫ f := by subst h; simp
```

These are trivial to prove (one line each) and they convert the problem from "compute through an opaque transport" to "work with a concrete `eqToHom ≫ f` composition".

**When to write these**: Whenever you see `≫ eqToHom _` or `h ▸ _` in a proof goal, ask: "Can I write a one-line `subst; simp` lemma that eliminates this at the source?"

## Principle 3: `Functor.map_comp` requires both sides in `F.map(...)` form

`← Functor.map_comp` rewrites `F.map f ≫ F.map g` to `F.map (f ≫ g)`. It does **not** match `F.map f ≫ eqToHom _` — the bare `eqToHom` isn't syntactically `F.map(...)`.

**Recipe**: Always convert the `eqToHom` first (Principle 1), then fold:
```lean
rw [show (eqToHom _ : F.obj _ ⟶ _) = F.map (eqToHom (by ...)) from (eqToHom_map _ _).symm]
rw [← Functor.map_comp]
```

**Pitfall**: `← Functor.map_comp (F := MyFunctor)` gives "Invalid argument name `F`" — in Lean 4's Mathlib, the parameter is called `self` (dot notation style). Just write `← Functor.map_comp` and let inference work.

## Principle 4: Use `slice_lhs`/`slice_rhs` to avoid `Category.assoc` fights

When the goal is `a ≫ b ≫ c ≫ d = ...`, targeting a specific pair for `Functor.map_comp` or `eqToHom_map` with bare `rw` is fragile (associativity varies). Use `slice_lhs i j` (1-indexed) to isolate morphisms `i` through `j`:

```lean
slice_lhs 1 2 =>
  rw [show eqToHom _ = F.map (eqToHom ...) from (eqToHom_map _ _).symm, ← Functor.map_comp]
```

## Principle 5: Peeling off functors with `congr 1`

After folding to `F.map(f) ≫ g = F.map(f') ≫ g`:

- **First `congr 1`**: peels off `≫ g`, leaving `F.map(f) = F.map(f')`
- **Second `congr 1`**: peels off `F.map`, leaving `f = f'` in the source category

**Pitfall**: A single `congr 1` on `F.map f = F.map g` (without the trailing `≫ g`) does NOT give `f = g`. For concrete categories like `TopCat`, it goes pointwise through `ConcreteCategory.hom`, producing goals about function application on points. You need the *second* `congr 1` to peel the functor layer.

**Pitfall**: `apply SomeCategory.Hom.ext` on `F.map f = F.map g` fails when the equality is at a different universe than the source category's hom-type. Use `congr 1` instead.

## Principle 6: Closing morphism equalities by descent to `Fin`

For `SimplexCategory` (or any category with `OrderHom`-based morphisms), once you have `f = g` where `f g : [n] ⟶ [m]`:

1. `ext ⟨i, hi⟩` — reduces to showing the underlying functions agree on all `Fin` inputs
2. Unfold layer by layer (composition → eqToHom → face map → if-then-else)
3. `split` on if-then-else conditions, then `omega` or `simp_all` for arithmetic

**Key insight**: `simp` alone can't unfold everything. Some definitions (`Fin.succAboveOrderEmb`, `OrderEmbedding.ofStrictMono`) are `def`s, not `@[simp]` lemmas — they need `dsimp` for definitional reduction before `simp` can work on the result.

**`dsimp` vs `simp` — which tool for which layer (CRITICAL):**

`dsimp` unfolds `def`s by definitional reduction. `simp` applies rewrite rules (theorems with `@[simp]` or supplied explicitly). Using the wrong one silently does nothing.

| Layer | Tool | Why |
|-------|------|-----|
| `SimplexCategory.Hom` composition | `dsimp [SimplexCategory.comp_toOrderHom]` | It's a `def` |
| `eqToHom` in SimplexCategory | **`simp only [SimplexCategory.eqToHom_toOrderHom]`** | It's a **theorem**, not a def — `dsimp` silently fails! |
| `Fin.castOrderIso` | `dsimp [Fin.castOrderIso]` | It's a `def` |
| Face map (`δ`) | `dsimp [SimplexCategory.δ, Fin.succAboveOrderEmb]` | Both are `def`s |
| `Fin.succAbove` | `simp only [Fin.succAbove, Fin.lt_def, Fin.val_castSucc, Fin.val_cast]` | `Fin.succAbove` needs simp to unfold the `if` |
| Final `Fin` values | `simp_all [Fin.val_castSucc, Fin.val_succ, Fin.val_cast]` | Clean up coercions for `omega` |

**Working unfolding recipe** (tested on `δ ≫ eqToHom` compositions):
```lean
-- Step 1: dsimp for defs
dsimp [SimplexCategory.δ, Fin.succAboveOrderEmb, SimplexCategory.comp_toOrderHom]
-- Step 2: simp for the theorem (MUST be simp, not dsimp!)
simp only [SimplexCategory.eqToHom_toOrderHom]
-- Step 3: dsimp for the OrderIso wrapper
dsimp [Fin.castOrderIso]
-- Step 4: simp to unfold succAbove and castSucc/succ
simp only [Fin.succAbove, Fin.lt_def, Fin.val_castSucc, Fin.val_cast]
-- Step 5: split on if-then-else, then close
split_ifs <;> simp_all [Fin.val_castSucc, Fin.val_succ, Fin.val_cast]
```

After fully unfolding, `split_ifs` on the `if` conditions, then `omega` or `simp_all` closes each case.

## Principle 6a: Bridge lemmas for `δ ≫ eqToHom` vs `Fin.succAbove ∘ Fin.cast`

**Problem**: A combinatorial lemma (e.g., `insertLeftStep_face`) is stated using `Fin.succAbove` and `Fin.cast` directly, but the categorical goal has `(SimplexCategory.δ t ≫ eqToHom h).toOrderHom i`. These produce the **same `Fin.val`** but are **syntactically different `Fin` terms** — `Fin.cast (succAbove t i)` vs `succAbove (cast t) (cast i)`.

**Solution**: Write a bridge lemma that translates between the categorical form and the combinatorial form. Pattern:

```lean
private lemma myLemma_comp_δ {p q : ℕ} (ν : ...) (j : ...) (i : Fin (p + q + 1)) :
    f ((SimplexCategory.δ t ≫ eqToHom (by congr 1; omega)).toOrderHom i) =
    <RHS from the combinatorial lemma> := by
  have hface := combinatorial_lemma ν j i
  suffices harg : ∀ (a b : Fin n), a.val = b.val → f a = f b from
    harg _ _ (by
      <unfolding recipe from Principle 6>
    ) |>.trans hface
  exact fun _ _ h => congr_arg _ (Fin.ext h)
```

**Key trick**: The `suffices ∀ a b, a.val = b.val → f a = f b` avoids needing to elaborate the `eqToHom` proof term in a `have` statement (which fails due to metavariable inference). It reduces the problem to showing two `Fin.val`s are equal, which the unfolding recipe + `omega` handles.

**When to use this**: Whenever a proof needs to connect a `SimplexCategory` morphism composition (`δ ≫ eqToHom`) with a `Fin`-level operation (`succAbove`, `cast`), and there's already a combinatorial lemma stated in `Fin` terms.

## Principle 7: Proving the `eqToHom` proof term

When writing `eqToHom (by ...)`, the proof obligation is typically `F.obj X = F.obj Y` where `X` and `Y` differ by a `Nat` equation. For `SimplexCategory.mk`:

- `congr 1` reduces `SimplexCategory.mk n = SimplexCategory.mk m` to `n = m`
- Then `omega` or `rfl` closes it
- Sometimes `congr 1` closes it outright (when the `Nat` equality is definitional). If `omega` then says "No goals to be solved", just remove `omega`.

## Principle 8: `simplexProdMap` goals — full pipeline

When the goal is `toTop.map (δ t) ≫ eqToHom _ ≫ simplexProdMap μ = simplexProdMap ν ≫ prod.map (toTop.map f) g`, use this pipeline:

```lean
-- 1. Left-associate to enable Functor.map_comp matching
simp only [← Category.assoc] at *
-- 2. Convert eqToHom from TopCat to SimplexCategory
rw [← show SimplexCategory.toTop.map (eqToHom _) = eqToHom _ from eqToHom_map _ _]
-- 3. Fold δ ≫ eqToHom into a single toTop.map
rw [← Functor.map_comp]
-- 4. Use simplexProdMap_comp to absorb the toTop.map into the OrderHom
rw [simplexProdMap_comp, simplexProdMap_comp_prod_map_toTop_left]
-- 5. Now the goal is an OrderHom equality — use a bridge lemma pointwise
congr 1; ext : 1; funext i
simp only [OrderHom.comp_coe, Function.comp_apply, OrderHom.coe_mk]
exact myBridgeLemma ν j i
```

**Step 1 is critical**: `← Category.assoc` left-associates the composition so that `toTop.map (δ _) ≫ toTop.map (eqToHom _)` becomes `(toTop.map (δ _) ≫ toTop.map (eqToHom _))`, making `← Functor.map_comp` match.

**`ext : 1; funext i` vs `ext i`**: For `OrderHom` equality, `ext i` goes all the way to `Fin.val` (too deep). Use `ext : 1` to get function equality, then `funext i` to go pointwise at the `Prod` level.

## Principle 9: Re-fold after `dsimp` — the `change F.map _ = _` pattern

**Problem**: You `dsimp` a functor application to access inner structure (e.g., to `rw [prod.lift_snd]` inside a `shuffleStdSimplexMap`). After the rewrite, the goal is a concrete `D`-morphism (e.g., `TopCat.uliftFunctor.map (TopCat.ofHom { toFun := stdSimplex.map ..., ... }) = eqToHom ⋯`). Now you're trapped in the concrete category — `Finsupp.mapDomain`, `FunOnFinite.linearMap`, etc. — and the proof becomes extremely painful.

**Solution**: Immediately re-fold back to functor form with `change`:

```lean
dsimp [shuffleStdSimplexMap, simplexProdMap]  -- expand to access inner structure
rw [CategoryTheory.Limits.prod.lift_snd]       -- apply the rewrite you needed
change SimplexCategory.toTop.map _ = eqToHom _ -- RE-FOLD back to functor form
rw [bridge_lemma_at_SimplexCategory_level]     -- work in the source category
exact eqToHom_map _ _                          -- functoriality closes it
```

**Why `change` works**: Even though `dsimp` expanded `toTop.map f` into its concrete definition, the expanded form is still *definitionally equal* to `toTop.map f`. So `change` can re-introduce the `F.map` wrapper at zero cost.

**When to use this**: Whenever you `dsimp` a `F.map(...)` to access something inside (e.g., a product lift component), and the remaining goal is an equality in the expanded concrete form. The re-fold lets you escape back to functor-level reasoning.

**Companion pattern — bridge lemma for the non-eqToHom side**: The concrete morphism you re-folded into `F.map(f)` may itself need a bridge lemma showing `f = eqToHom(...)` in the source category `C`. For example, `snd_comp_default_shuffle_eq_eqToHom` proves the snd projection of the default `(0,n)`-shuffle is `eqToHom` in `SimplexCategory`. These are proved by `ext + omega` / `dsimp` at the `Fin` level (Principle 6).

## Pitfall: `SimplexCategory.len` is opaque to `omega`

When `ext` destructs `⟨i, hi⟩ : Fin ((SimplexCategory.mk n).len + 1)`, the bound `hi` involves `.len` which `omega` can't reduce. Fix: `simp only [SimplexCategory.len_mk] at hi` to get `hi : i < n + 1`.

## Project-specific helper lemmas

| Lemma | Purpose |
|-------|---------|
| `simplexCoprojection_comp_eqToHom` | Absorbs `eqToHom` on chain group into transport on the simplex |
| `cast_singularSimplex_down` | Converts `(h ▸ ⟪f⟫ₛ).down` into `eqToHom _ ≫ f` |
| `cast_ulift_toSSet_down` | Earlier version of `cast_singularSimplex_down` |
| `snd_comp_default_shuffle_eq_eqToHom` | `snd ∘ default (Shuffle 0 n) = eqToHom` in SimplexCategory |

## Meta-lesson: when one side of a symmetry is trivial and the other isn't

If two cases should be "symmetric" but one is trivial (3 lines) and the other is painful (50+ lines), the cause is almost always a definitional vs. propositional equality gap. Before grinding through the hard case, ask:

1. **Can I redefine to make both sides definitional?** (e.g., change argument order, use a different index form)
2. **Can I prove a general `eqToHom`-absorption lemma** that pays the tax once, making the hard case only slightly longer than the easy case?
3. If neither, follow the functor-retreat recipe above.
