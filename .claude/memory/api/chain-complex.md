# Chain Complex API Patterns

Patterns for working with `HomologicalComplex`, `ChainComplex`, and the alternating face map complex.

## `Nat.add` index mismatch blocks `.d` lemmas (CRITICAL)

`ChainComplex.of` defines `.d i j` via `dite (i = j + 1)`. This means `.d (p+1+(q+1)) (p+q+1)`
does **not** reduce to the face map sum, because `p+1+(q+1) = (p+q+1)+1` is only propositional
(not definitional). Lemmas like `alternatingFaceMapComplex_obj_d` require the syntactic form
`.d ((n+1)) n`.

### The `eqToHom_comp_d` index-shifting pattern

**Problem**: You have `K.d (expr₁) (expr₂)` where `expr₁ = expr₂ + 1` propositionally but not
definitionally. You need to apply a lemma (e.g. `alternatingFaceMapComplex_obj_d`) that requires
`.d ((n+1)) n`.

**Solution**: Use `HomologicalComplex.eqToHom_comp_d` to insert an `eqToHom` that shifts the index:

```lean
-- Local helper (defined in HomotopyInvariance.lean):
lemma HomologicalComplex.eqToHom_comp_d (K : HomologicalComplex A c) {i i' j : ι} (h : i = i') :
    eqToHom (congrArg K.X h) ≫ K.d i' j = K.d i j

-- Usage: shift K.d (p+1+(q+1)) (p+q+1) to eqToHom _ ≫ K.d ((p+q+1)+1) (p+q+1)
have hrel : (p + 1 + (q + 1) : ℕ) = (p + q + 1) + 1 := by omega
have d_shift : K.d (p + 1 + (q + 1)) (p + q + 1) =
    eqToHom (congrArg K.X hrel) ≫ K.d ((p + q + 1) + 1) (p + q + 1) :=
  (HomologicalComplex.eqToHom_comp_d K hrel).symm
```

Now `K.d ((p+q+1)+1) (p+q+1)` is in `(n+1) n` form and `alternatingFaceMapComplex_obj_d` applies.

### Applying the shift inside a complex goal

`simp_rw [d_shift]` may fail if:
- The `.d` term is inside deeply nested compositions or sums
- The expression containing `.d` was unfolded by `dsimp` to a different syntactic form

**Fix**: Use `conv_lhs => rw [show ... from ...]` to target the exact `.d` subexpression:

```lean
conv_lhs => rw [show (singChain (C := C) (R := R) X).d (p + 1 + (q + 1)) (p + q + 1) =
    eqToHom ... ≫ (singChain (C := C) (R := R) X).d ((p + q + 1) + 1) (p + q + 1) from
  (HomologicalComplex.eqToHom_comp_d _ hrel).symm]
```

### Full recipe: expanding `singChain.d` into face maps

1. **Shift index**: `conv_lhs => rw [... (eqToHom_comp_d _ hrel).symm]` — converts
   `.d (p+1+(q+1)) (p+q+1)` to `eqToHom _ ≫ .d ((p+q+1)+1) (p+q+1)`
2. **Apply bridge lemma**: `rw [singChain_d_eq_alternatingFaceMapObjD]` — converts
   `singChain.d ((n+1)) n` to `AlternatingFaceMapComplex.objD (...) n`
3. **Expand objD**: `simp only [AlternatingFaceMapComplex.objD]` — unfolds to
   `∑ i, (-1)^i • δ i`
4. **Distribute**: `simp only [Preadditive.comp_sum, Preadditive.comp_zsmul]`

### `d_comp_eqToHom` — the codomain version

Similarly, `K.d i j ≫ eqToHom (congrArg K.X h) = K.d i j'` where `h : j = j'`.
Useful when you need to shift the *target* index instead of the source.

## Folding `ι s ≫ δⱼ` into `ι(δⱼ s)` via `simplexCoprojection_comp_eqToHom_comp_δ`

When expanding differentials into face map sums, you often get `simplexCoprojection s ≫ δ j` and need to fold it into `simplexCoprojection (δ j s)`. The bridge lemma is `simplexCoprojection_comp_eqToHom_comp_δ`, but it includes an `eqToHom` that needs to be simplified away when the index proof is `rfl`.

**Pattern**:
```lean
rw [show simplexCoprojection (C := C) s ≫
    (((SimplicialObject.whiskering (Type v) C).obj ((sigmaConst (C := C)).obj (𝟙_ C))).obj
      (TopCat.toSSet.obj X)).δ j =
  simplexCoprojection (C := C) ((TopCat.toSSet.obj X).δ j s) from by
  have := simplexCoprojection_comp_eqToHom_comp_δ (C := C) rfl s j
  simp only [eqToHom_refl, Category.id_comp] at this
  exact this]
```

This comes up in cross product Leibniz rule proofs where you need to match `ι(face(s))` on both sides after expanding differentials.

## Avoid `dsimp` before index shifting

`dsimp [SCF, singularChainComplexFunctor, ...]` unfolds `singChain` and `Δ[p]` into their
internal representations (`TopCat.uliftFunctor.obj { carrier := ... }`). This:
- Makes `set K := singChain ...` fail to fold (syntactic mismatch)
- Bloats the goal with implementation details
- Prevents `rw [singChain_d_eq_alternatingFaceMapObjD]` from matching

**Rule**: Do the index shift and `singChain_d_eq_alternatingFaceMapObjD` rewrite **before**
any `dsimp` unfolding. Work at the `singChain` abstraction level as long as possible.
