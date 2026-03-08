# Cleanup for Mathlib submission

Post-refactor cleanup items for `HomotopyInvariance.lean` and `CrossProduct.lean`.
Ordered by priority (high impact + easy first).

## Tier 1: High impact, easy

### 1. Extract duplicated `cast_down` as a named lemma

The identical 4-line `have cast_down` appears inline at:
- `simplexCrossProduct_zero_left` (HomotopyInvariance.lean:601–604)
- `universalSimplexCrossProduct_boundary` right-type case (HomotopyInvariance.lean:965–968)

This is the old `cast_singularSimplex_down` that was removed during the `n`-param refactor.
Restore it as a top-level lemma and use it in both places.

### 2. Extract `Subsingleton Δ[0]` as a standalone instance

The proof that `Δ[0]` is a subsingleton appears twice with slightly different elaborations:
- `simplexCrossProduct_zero_right` (HomotopyInvariance.lean:548–559)
- `simplexCrossProduct_zero_left` (HomotopyInvariance.lean:614–625)

Both are 10+ lines proving the same thing. Extract as:
```lean
instance : Subsingleton Δ[0] := ...
```
Then both call sites collapse to `exact congrArg _ (Subsingleton.elim _ _)`.

### 3. `attribute [simp] CategoryTheory.yoneda` → `local attribute`

Line 398 of HomotopyInvariance.lean adds a global `@[simp]` to a Mathlib definition.
Mathlib will reject this. Change to `local attribute [simp]` or replace with explicit
`simp only [yoneda]` in `shuffleSimplex`.

### 4. Scope notations

For Mathlib, unscoped notation pollutes the global namespace:
- `notation "Δ[" p "]" => stdSimplex p` (HomotopyInvariance.lean:53) → `scoped notation`
- `notation "⟪" f "⟫ₛ" => SingularSimplex.ofΔ f` (HomotopyInvariance.lean:96) → `scoped notation`

### 5. Check if `singChain_X_iso_sigma` is used

`singChain_X_iso_sigma` (HomotopyInvariance.lean:99–110) doesn't appear to be referenced
anywhere in either file. Search the full project; if unused, delete.

### 6. Remove `#print axioms` debugging artifact

CrossProduct.lean:1020 has `#print axioms singularHomology_iso_of_homotopyEquiv`.
Remove before submission.

## Tier 2: Medium impact, medium effort

### 7. Shorten `Unique_Shuffle_n_0` and `Unique_Shuffle_0_n`

Both are ~50 lines (HomotopyInvariance.lean:448–500) following the same pattern:
show a projection is `StrictMono`, then `StrictMono.le_id`/`StrictMono.id_le`.

Opportunities:
- Factor the `StrictMono → id` argument into a small helper (used twice)
- `Unique_Shuffle_0_n` has a convoluted `hcast` step — simplify with `Fin.ext (by omega)`
- Target: ~15–20 lines each

### 8. Consider eliminating `simplexCrossProduct_zero_left`

`simplexCrossProduct_zero_left` (HomotopyInvariance.lean:577–637) is 60 lines of `eqToHom`
manipulation from the `0 + n ≠ n` issue. It's only used once:
`crossProduct_leibniz_left_zero_zero` (CrossProduct.lean:784).

If that special case can be proved directly without `simplexCrossProduct_zero_left`,
then both it and `snd_comp_default_shuffle_eq_eqToHom` (HomotopyInvariance.lean:561–571)
can be deleted. Net savings: ~70 lines.

## Tier 3: Hard but valuable

### 9. Extract right-type case of boundary proof as a standalone lemma

The right-type case of `universalSimplexCrossProduct_boundary`
(HomotopyInvariance.lean:960–1019) is a 60-line `eqToHom` manipulation block.
The `eqToHom` here is *internal* (about `p + (q+1) ≠ (p+1) + q` in `SimplexCategory`,
not chain complex indexing), so the `n`-param refactor doesn't reach it.

Extract as something like:
```lean
private lemma insertRightStep_simplex_eq {p q : ℕ} (ν : Shuffle p q) (k : Fin (q + 2)) ... 
```
This keeps the boundary proof shorter and makes the right-type case independently reviewable.

### 10. Clean up `crossProduct_leibniz` in CrossProduct.lean

The statement (CrossProduct.lean:600–609) still has `crossProduct (p + 1) q _ (by omega)`,
and the proof's `nat2` block (lines 638–651) still does `chainMap_f_comp_eqToHom` gymnastics.

If `crossProduct_tensor_naturality` is generalized to accept different `hn` proofs on
the two sides (source vs target), the `nat2` block and `chainMap_f_comp_eqToHom`
(CrossProduct.lean:588–592) might both become unnecessary.

This is the last remaining `eqToHom` pain point after the `n`-param refactor.

---

## Addendum: Why `eqToHom` still appears after the `n`-param refactor

The `n`-param refactor eliminated `eqToHom` at the **chain complex indexing** layer
(`(...).X n` instead of `(...).X (p+q)`), but a second, independent layer of `eqToHom`
remains in `SimplexCategory` / `TopCat`. These are fundamentally different issues.

### The two layers

| Layer | What's being cast | Status |
|-------|-------------------|--------|
| Chain complex: `(...).X n` | Degree index in the chain complex | **Eliminated** by `n`-param |
| SimplexCategory: `Δ[a]` vs `Δ[b]` | Source/target of simplex maps when `a ≠ b` definitionally | **Still present** |

### Where the remaining `eqToHom` enters

Inside `shuffleSimplex`, the `subst hn` converts the return type from
`SingularSimplex (X ⨯ Y) n` to `SingularSimplex (X ⨯ Y) (p + q)`, builds
the simplex at degree `(p + q)`, then wraps it in a transport `hn ▸ ...`.

When the boundary proof needs to access `.down` on a transported simplex
(e.g., one built with `hn : p + (q+1) = (p+1) + q`), the transport doesn't
vanish — it becomes `eqToHom _ ≫ f`, where `eqToHom` is a `TopCat` morphism
`Δ[p+(q+1)] ⟶ Δ[(p+1)+q]`. This is what the `cast_down` helper computes.

Concretely, the RHS right-type sum calls `simplexCrossProduct` with
`p' = p+1`, `q' = q`, targeting degree `n = p + (q+1)`. Inside, `shuffleSimplex`
builds a map on `Δ[(p+1)+q]` and transports it to degree `p + (q+1)`. Extracting
`.down` produces `eqToHom (Δ[p+(q+1)] ⟶ Δ[(p+1)+q]) ≫ simplexProdMap ...`.

### Why it's unavoidable

`(p+1)+q` and `p+(q+1)` are propositionally but not definitionally equal
(`Nat.add_assoc`). Since `SimplexCategory.mk` takes a literal `ℕ`,
`SimplexCategory.mk ((p+1)+q) ≠ SimplexCategory.mk (p+(q+1))` definitionally,
and therefore `Δ[(p+1)+q] ≠ Δ[p+(q+1)]` as objects of `TopCat`. Any morphism
between them must go through `eqToHom`.

This could only be eliminated by either:
1. Working in a setting where `SimplexCategory.mk` doesn't distinguish
   propositionally-equal `ℕ` values (e.g., a quotient), or
2. Reformulating `shuffleStdSimplexMap_insertRight_face` to avoid the `eqToHom`
   in its statement (hard — it's intrinsic to the `δ ≫ eqToHom` pattern in
   `SimplexCategory`).
