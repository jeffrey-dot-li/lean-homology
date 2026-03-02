# TopCat Limit and Product Operations

## Pointwise evaluation of `TopCat` limit operations

`TopCat` limit operations (`prod.lift`, `prod.fst`, `prod.snd`, `prod.map`, `prod.braiding`,
`prodIsoProd`) are **not** definitionally transparent. `rfl` and `dsimp` cannot see through
`ConcreteCategory.hom prod.fst (...)` to extract the underlying projection.

**Strategy**: alternate between recombining pointwise applications into categorical
compositions, simplifying categorically, and decomposing again:

```lean
-- 1. Decompose the composition into pointwise applications
simp only [ConcreteCategory.comp_apply]
-- 2. Use erw for prodIsoProd (simp can't match due to anonymous TopCat structure)
erw [TopCat.prodIsoProd_hom_apply]
-- 3. Simplify categorical operations that simp CAN handle at the categorical level
simp only [← ConcreteCategory.comp_apply, prod.map_fst, prod.map_snd, Category.assoc]
simp only [ConcreteCategory.comp_apply, ConcreteCategory.id_apply]
-- 4. For prod.lift_fst/snd: explicit rw with named arguments (simp can't drive this)
rw [← ConcreteCategory.comp_apply (prod.lift f g) prod.fst]
rw [prod.lift_fst]
```

**Why `simp` can't automate step 4**: `← ConcreteCategory.comp_apply` rewrites
`g(f(x)) → (f ≫ g)(x)` but is ambiguous about which nested pair to recombine.
`simp` either combines too aggressively (creating compositions the categorical
lemma doesn't match) or not enough. Explicit `rw` with the two morphism arguments
controls exactly which pair is recombined.

See `homotopyMap_eval` in `HomotopyMap.lean` for a complete example.

## Pitfall: `TopCat.prodIsoProd_hom_apply` needs `erw`, not `rw` or `simp`

After `simp only [ConcreteCategory.comp_apply]`, function applications use `ConcreteCategory.hom`.
`TopCat.prodIsoProd_hom_apply` is stated with the `FunLike` coercion `(prodIsoProd X Y).hom x`.
These are definitionally equal but syntactically different, so `rw` and `simp` both fail.

**Symptom**: `simp [TopCat.prodIsoProd_hom_apply]` reports "unused argument";
`rw` reports "did not find an occurrence of the pattern".

**Fix**: Use `erw [TopCat.prodIsoProd_hom_apply]`.

Also: `dsimp [homotopyMap]` over-unfolds `TopCat.of (ULift I)` into an anonymous
structure `{ carrier := ULift ↑I, str := ... }` which blocks `prodIsoProd_hom_apply`
entirely — prefer `unfold homotopyMap` (less aggressive) over `dsimp`.

## Pitfall: `F.map` for `TopCat.toSSet ⋙ eval (op [n])` is NOT definitional

`(F.map g y).down` does NOT reduce by `rfl`/`dsimp` to `y.down ≫ g`.

**Fix**: `simp only [F, Functor.comp_map, evaluation_obj_map]` then `change _ = t ≫ sigmaι f i`.
Or in the reverse direction, `simpa using ht` when the hypothesis already has the concrete form.
