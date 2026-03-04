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

**Simp lemma layers for SimplexCategory → Fin:**

| Layer | Unfolds with |
|-------|-------------|
| `SimplexCategory.Hom` composition | `simp [SimplexCategory.comp_toOrderHom, OrderHom.comp_coe, Function.comp_apply]` |
| `eqToHom` in SimplexCategory | `simp [SimplexCategory.eqToHom_toOrderHom]` (gives `Fin.castOrderIso`) |
| `Fin.castOrderIso` | `simp [Fin.castOrderIso, OrderIso.coe_toOrderEmbedding, RelIso.coe_fn_mk, Equiv.coe_fn_mk, Fin.val_cast]` |
| Face map (`δ`) | `simp [SimplexCategory.δ, SimplexCategory.Hom.toOrderHom_mk]` (gives `succAboveOrderEmb`) |
| `Fin.succAboveOrderEmb` | **`dsimp [Fin.succAboveOrderEmb]`** (not simp!) then `simp [Fin.succAbove, Fin.lt_def, Fin.val_cast]` |
| Final `Fin` values | `simp_all [Fin.val_castSucc, Fin.val_succ]` |

After fully unfolding, `split <;> split` on the `if` conditions, then `omega` closes matching cases and `exact absurd trivial ‹_›` closes contradictory ones (where `simp_all` may leave `¬True`).

## Principle 7: Proving the `eqToHom` proof term

When writing `eqToHom (by ...)`, the proof obligation is typically `F.obj X = F.obj Y` where `X` and `Y` differ by a `Nat` equation. For `SimplexCategory.mk`:

- `congr 1` reduces `SimplexCategory.mk n = SimplexCategory.mk m` to `n = m`
- Then `omega` or `rfl` closes it
- Sometimes `congr 1` closes it outright (when the `Nat` equality is definitional). If `omega` then says "No goals to be solved", just remove `omega`.

## Project-specific helper lemmas

| Lemma | Purpose |
|-------|---------|
| `simplexCoprojection_comp_eqToHom` | Absorbs `eqToHom` on chain group into transport on the simplex |
| `cast_singularSimplex_down` | Converts `(h ▸ ⟪f⟫ₛ).down` into `eqToHom _ ≫ f` |
| `cast_ulift_toSSet_down` | Earlier version of `cast_singularSimplex_down` |

## Meta-lesson: when one side of a symmetry is trivial and the other isn't

If two cases should be "symmetric" but one is trivial (3 lines) and the other is painful (50+ lines), the cause is almost always a definitional vs. propositional equality gap. Before grinding through the hard case, ask:

1. **Can I redefine to make both sides definitional?** (e.g., change argument order, use a different index form)
2. **Can I prove a general `eqToHom`-absorption lemma** that pays the tax once, making the hard case only slightly longer than the easy case?
3. If neither, follow the functor-retreat recipe above.
