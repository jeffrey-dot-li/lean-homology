# SSet yonedaEquiv / ULift patterns

## The problem

`SSet.yonedaEquiv` is defined as `uliftYonedaEquiv`, which wraps everything in `ULift`.
Similarly, `SSet.stdSimplex.objEquiv` is `Equiv.ulift`. This means:

- `rfl` fails on `(yonedaEquiv.symm x).app m (objEquiv.symm f) = X.map f.op x`
  even though it's definitionally true at the Mathlib source level.
- `rw` cannot match `uliftYonedaEquiv_symm_apply_app` because the argument
  `objEquiv.symm f` has type `Δ[n].obj m` while the lemma expects
  `(uliftYoneda.obj n).obj m` — definitionally equal but not syntactically.
- `simp` with `uliftYonedaEquiv_symm_apply_app` also fails for the same reason.
- `erw` works but is fragile: chained `erw [A, B, C]` succeeds where
  separate `erw [A]; rw [B]` fails, because `erw` changes the goal's
  internal type representation and later `rw` can't match.

## The namespace collision

`SSet.stdSimplex` is both a **namespace** and a **term** (the functor
`SimplexCategory ⥤ SSet`). Lean resolves `SSet.stdSimplex.foo` as field
projection on the functor, not as a namespace lookup. So you cannot write
`SSet.stdSimplex.yonedaEquiv_symm_app_objEquiv_symm` even though that
declaration exists in Mathlib's `SimplicialHomotopy.lean`.

## The solution: local `@[simp]` bridge lemma

In `EilenbergZilber.lean` we define:

```lean
@[simp] lemma yonedaEquiv_symm_app {X : SSet.{v}} {n : SimplexCategory}
    (x : X.obj (Opposite.op n)) {m : SimplexCategoryᵒᵖ}
    (f : m.unop ⟶ n) :
    (SSet.yonedaEquiv.symm x).app m (SSet.stdSimplex.objEquiv.symm f) =
      X.map f.op x :=
  rfl
```

This is the same as Mathlib's `SSet.stdSimplex.yonedaEquiv_symm_app_objEquiv_symm`
(from `SimplicialHomotopy.lean`) but in our own namespace, avoiding the collision.

## Usage pattern

When a goal contains `(yonedaEquiv.symm x).app m (Δ[n].map g (objEquiv.symm f))`:

1. `rw [SSet.stdSimplex.map_apply]` — rewrites `Δ[n].map g (objEquiv.symm f)`
   to `objEquiv.symm (f ≫ g.unop)`, putting it in the form our lemma matches.
2. `rw [yonedaEquiv_symm_app]` — collapses to `X.map (f ≫ g.unop).op x`.
3. `simp [SimplexCategory.hom_zero_zero]` or similar to simplify the morphism.

No `erw` needed anywhere.

## Key Mathlib lemmas

| Lemma | What it does |
|-------|-------------|
| `SSet.stdSimplex.map_apply` | `Δ[n].map f x = objEquiv.symm (f.unop ≫ objEquiv x)` — functorial action on standard simplex |
| `SSet.stdSimplex.objEquiv` | `Δ[n].obj m ≃ (m.unop ⟶ ⦋n⦌)` — is `Equiv.ulift` |
| `SSet.yonedaEquiv` | `(Δ[n] ⟶ X) ≃ X.obj (op n)` — is `uliftYonedaEquiv` |
| `uliftYonedaEquiv_symm_apply_app` | `(uliftYonedaEquiv.symm x).app Y y = F.map y.down.op x` — the raw ULift version |
| `FunctorToTypes.map_id_apply` | `F.map (𝟙 X) a = a` — needs `erw` when `F` is `Δ[n]` (type mismatch with `SSet` functor) |
| `SimplexCategory.hom_zero_zero` | Any `⦋0⦌ ⟶ ⦋0⦌` is `𝟙 ⦋0⦌` |

## General principle

When working with `SSet` and encountering `ULift`-related `rw` failures:
- **Don't** try to `erw` through the `ULift` layer.
- **Do** write a `rfl`-proof `@[simp]` lemma that states the desired equality
  directly in terms of the high-level API (`yonedaEquiv`, `objEquiv`), then
  use `rw`/`simp` with that lemma.
- Use `SSet.stdSimplex.map_apply` to normalize `Δ[n].map f (objEquiv.symm g)`
  into `objEquiv.symm (g ≫ f.unop)` before applying the bridge lemma.
