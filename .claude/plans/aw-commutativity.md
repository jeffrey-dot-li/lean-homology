# Alexander-Whitney `comm'` Proof Plan

## Goal

Prove the `comm'` field of `alexanderWhitney`:

```
AW_i ≫ (F₁.obj X).d i j = (F₂.obj X).d i j ≫ AW_j
```

where `(ComplexShape.down ℕ).Rel i j` (i.e., `i = j + 1`).

## Unpacking the sides

- **LHS**: `(∑_p awComponent(p, i-p) ≫ ιTotal) ≫ total.d i j`
  - The AW map at degree `i`, followed by the total complex differential.
- **RHS**: `diag.d i j ≫ (∑_p awComponent(p, j-p) ≫ ιTotal)`
  - The diagonal differential followed by AW at degree `j`.

## Comparison with EZ commutativity

The EZ proof (lines 727–793 of `Bisimplicial.lean`) has a structural advantage:

1. **Reduction to per-summand equality** is immediate via `HomologicalComplex₂.total.hom_ext` — two maps out of the total complex agree iff they agree after precomposing each `ιTotal`.
2. **Simplification** via `ι_totalDesc` collapses `ιTotal ≫ totalDesc(f)` to `f(p, q)` on the LHS.
3. **The key lemma** `ezComponent_boundary` does all the hard combinatorial work. After applying it, the proof just matches the two sides against `d₁` and `d₂` of the total complex.

For AW the situation is **reversed**: the map goes *into* the coproduct (sum of `ιTotal`s), not out of it.

| Aspect | EZ `comm'` | AW `comm'` |
|--------|-----------|-----------|
| Map direction | Out of coproduct (`totalDesc`) | Into coproduct (`∑ ιTotal`) |
| Decomposition tool | `hom_ext` (per-summand) | Distribute sums directly |
| Key lemma | `ezComponent_boundary` (hard, ~400 lines) | `awComponent_boundary` (should be simpler) |
| Combinatorics | Shuffle decomposition, sign tracking | Face map / injection composition |
| Matching step | Match against `d₁`, `d₂` | Reindex sum |

## Proof strategy

### Step 1: Prove `awComponent_boundary`

State and prove a lemma:

```
(F₂.obj X).d (p+q) j ≫ awComponent X p' q' = 
  (vertical face terms) + (horizontal face terms)
```

This decomposes `d_diag ≫ AW_{p',q'}`. The key identities are:
- `δ_k ≫ ι_front = ...` — how face maps compose with the front-face inclusion
- `δ_k ≫ ι_back = ...` — how face maps compose with the back-face inclusion

These are simpler than the EZ case because `ι_front` and `ι_back` are standard injections (no shuffle combinatorics), so compositions with face maps `δ_k` factor cleanly:
- For `k ≤ p`: `δ_k` acts on the front part, giving `ι_front(p-1, q) ≫ δ_k`
- For `k ≥ p`: `δ_k` acts on the back part, giving `ι_back(p, q-1) ≫ δ_{k-p}`

### Step 2: Match sums

Use `awComponent_boundary` to rewrite the RHS `d_diag ≫ AW_j`, then match against the LHS `AW_i ≫ total.d`. The LHS distributes `(∑_p ... ≫ ιTotal) ≫ (D₁ + D₂)` into terms involving `d₁` and `d₂` of the double complex.

### Why AW is simpler than EZ

- `awComponent` is just `ι_front ≫ ι_back` (two standard inclusions), not a sum over shuffles.
- The face map / front-back composition identities are straightforward `SimplexCategory` computations.
- No sign combinatorics beyond the standard alternating signs from the face maps.
- The complexity is mainly in reindexing the sums.

## Supporting lemmas needed

1. **`δ_comp_ι_front`**: How `δ_k` composes with `ι_front p q` in `SimplexCategory`.
2. **`δ_comp_ι_back`**: How `δ_k` composes with `ι_back p q` in `SimplexCategory`.
3. **`awComponent_boundary`**: The main boundary formula for `d_diag ≫ awComponent`.

## Files involved

- `HomologyLean/SingularHomology/Bisimplicial.lean` — main file, `alexanderWhitney` definition and `comm'` proof.
- Potentially `HomologyLean/SingularHomology/EilenbergZilber.lean` — if `ι_front`/`ι_back` lemmas belong there.
