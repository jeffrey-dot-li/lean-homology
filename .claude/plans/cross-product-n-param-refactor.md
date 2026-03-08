# Refactor: Parameterize cross product codomain by `n` instead of `p + q`

## Problem

Currently `universalSimplexCrossProduct`, `simplexCrossProduct`, and `crossProduct` all have their codomain indexed by `p + q`:

```lean
def universalSimplexCrossProduct (p q : ℕ) :
    R ⟶ (singChain (R := R) (X := (Δ[p] ⨯ Δ[q]))).X (p + q)

def simplexCrossProduct {X Y} {p q : ℕ} (s : ...) (t : ...) :
    R ⟶ (singChain (R := R) (X ⨯ Y)).X (p + q)

abbrev crossProduct {X Y} (p q : ℕ) :
    (mSingChain R X).X p ⊗ (mSingChain R Y).X q ⟶ (mSingChain R (X ⨯ Y)).X (p + q)
```

This forces all downstream code to work with `(p + q)` as a concrete Nat expression in the type. Since `Nat.add` recurses on the second argument, expressions like `(p + 1) + (q + 1)` vs `p + q + 2` or `(p + 1) + q` vs `p + (q + 1)` are **not** definitionally equal, generating dozens of `eqToHom` casts throughout:

- `universalSimplexCrossProduct_boundary` (HomotopyInvariance.lean:772–1069) — the biggest theorem, riddled with `eqToHom` to relate `(p+1)+(q+1)` to `(p+q+1)+1`
- `crossProduct_leibniz` (CrossProduct.lean:598–664) — needs `eqToHom (by omega)` because `(p+1)+q ≠ p+(q+1)` definitionally
- `simplexCrossProduct_leibniz` (CrossProduct.lean:501–561) — same issue
- Chain homotopy construction (CrossProduct.lean:847–986) — `crossProduct (n+1) 0 ≫ eqToHom (Nat.add_zero (n+1))`

## Proposed fix

Add `(n : ℕ)` and `(hn : n = p + q)` parameters. The codomain uses `n` instead of `p + q`. Internally, the definition `subst`s `hn` so the body is unchanged. Externally, callers choose `n` to match their context, and the `eqToHom` casts turn into different `hn` proofs (which are all `by omega`).

## Files in scope

Only two files need changes (Shuffle.lean and Working.lean mention these only in comments):

1. **`HomotopyInvariance.lean`** — definitions + `universalSimplexCrossProduct_boundary`
2. **`CrossProduct.lean`** — `ModuleCat`-specialized wrappers + Leibniz + chain homotopy

## Dependency chain (bottom-up)

```
shuffleSimplex                     ← CHANGE: add (n, hn) to produce simplex at degree n
  │
universalSimplexCrossProduct       ← BASE of refactor (no subst needed if shuffleSimplex takes n)
  │
simplexCrossProduct                ← uses universalSimplexCrossProduct
  │
  ├── simplexCrossProduct_zero_right
  ├── simplexCrossProduct_zero_left
  ├── crossProduct_natural_pure_tensor
  │
  ├── universalSimplexCrossProduct_boundary  (BIG theorem)
  │
  │  ── [CrossProduct.lean] ──
  │
  ├── simplexCrossProductElem
  │     └── simplexCrossProductElem_natural
  │           └── simplexCrossProductNat
  │                 └── liftedCrossProductNat
  │                       └── crossProductNat
  │                             └── crossProduct         ← main user-facing def
  │
  ├── crossProductNat_unit
  ├── mι_tensor_tensorCoprodNatIso
  ├── mι_tensor_comp_crossProduct
  ├── simplexCrossProduct_id
  │
  ├── simplexCrossProduct_leibniz
  │     └── crossProduct_leibniz
  │
  ├── crossProduct_normalized
  ├── crossProduct_leibniz_left_zero_zero
  ├── crossProduct_zero_right_boundary
  │     └── singularChain_chainHomotopy_of_homotopy
  │           └── singularHomology_map_eq_of_homotopy
  │                 └── singularHomology_iso_of_homotopyEquiv
  ```

## Detailed change plan

### Phase 1: Base definitions in HomotopyInvariance.lean

#### 1a. `shuffleSimplex` (line 414)

**Before:**
```lean
def shuffleSimplex {X Y} {p q : ℕ}
    (s : SingularSimplex X p) (t : SingularSimplex Y q) (μ : Shuffle p q) :
    SingularSimplex (X ⨯ Y) (p + q) := ...
```

**After:**
```lean
def shuffleSimplex {X Y} {p q n : ℕ} (hn : n = p + q)
    (s : SingularSimplex X p) (t : SingularSimplex Y q) (μ : Shuffle p q) :
    SingularSimplex (X ⨯ Y) n := by
  subst hn; ...same body...
```

Key reason: by absorbing the `subst` here at the leaf, `universalSimplexCrossProduct`
and `simplexCrossProduct` can be defined *without* `subst` — their bodies stay transparent
at `n`, so Lean sees the output type as `...X n` throughout without unfolding to `p + q`.

#### 1b. `universalSimplexCrossProduct` (line 424)

**Before:**
```lean
def universalSimplexCrossProduct (p q : ℕ) :
    R ⟶ (singChain (R := R) (X := (Δ[p] ⨯ Δ[q]))).X (p + q) := ...
```

**After (no subst needed):**
```lean
def universalSimplexCrossProduct (p q n : ℕ) (hn : n = p + q) :
    R ⟶ (singChain (R := R) (X := (Δ[p] ⨯ Δ[q]))).X n :=
  ∑ μ : Shuffle p q, μ.sign • simplexCoprojection
    (shuffleSimplex hn ⟪𝟙 stdSimplex.{v} p ⟫ₛ ⟪𝟙 stdSimplex.{v} q⟫ₛ μ)
```

#### 1c. `simplexCrossProduct` (line 436)

**Before:**
```lean
def simplexCrossProduct {X Y} {p q : ℕ} (s : ...) (t : ...) :
    R ⟶ (singChain (R := R) (X ⨯ Y)).X (p + q) := ...
```

**After (no subst needed):**
```lean
def simplexCrossProduct {X Y} {p q n : ℕ} (hn : n = p + q)
    (s : SingularSimplex X p) (t : SingularSimplex Y q) :
    R ⟶ (singChain (R := R) (X ⨯ Y)).X n :=
  universalSimplexCrossProduct p q n hn ≫
    ((SCF R).map (prod.map s.down t.down)).f n
```

### Phase 2: Lemmas about simplexCrossProduct in HomotopyInvariance.lean

Each of these just needs `hn` threaded through. The statements simplify because `eqToHom` casts that existed to bridge `(p+1)+q ↔ p+(q+1)` become different `hn` proofs.

| Lemma | Line | Change |
|-------|------|--------|
| `simplexCrossProduct_zero_right` | 511 | Add `(hn : n = p + 0)` or specialize to `rfl` |
| `simplexCrossProduct_zero_left` | 587 | Add `hn`, **the trailing `eqToHom (by simp)` in the statement likely disappears** since we can just pick `n = 0 + q` directly |
| `crossProduct_natural_pure_tensor` | 645 | Add `hn` |
| `simplexCoprojection_comp_eqToHom` | 576 | May become unnecessary or simpler — the `eqToHom` it handles is exactly the `n ↔ p + q` bridge |

### Phase 3: `universalSimplexCrossProduct_boundary` (line 772)

This is the biggest win. Currently the statement has:
```lean
    ... (p + 1 + (q + 1)) (p + (q + 1)) = ... ≫ eqToHom (congrArg ... (by omega))
```

With `n`-parameterization, the RHS terms can target the same `n` directly:
- LHS: `universalSimplexCrossProduct (p+1) (q+1) n hn ≫ d n m`
- RHS left sum: `simplexCrossProduct hn' ⟪δ j⟫ₛ ⟪𝟙⟫ₛ` where `hn'` targets `m`
- RHS right sum: `simplexCrossProduct hn'' ⟪𝟙⟫ₛ ⟪δ j⟫ₛ` where `hn''` also targets `m`
- **The `eqToHom (by omega)` on the right sum disappears** because both sums target the same `m`

The proof body also simplifies substantially:
- Lines 790–814 (the `cancel_mono (eqToHom ...)` + `hd_eq` + `eqToHom_comp_d` dance) — eliminated or greatly simplified
- Line 1013 (`simplexCoprojection_comp_eqToHom`) — eliminated since the right-type case directly targets the correct index

### Phase 4: CrossProduct.lean — ModuleCat specializations

#### 4a. Element-level wrappers

| Definition/Lemma | Line | Change |
|-----------------|------|--------|
| `simplexCrossProductElem` | 203 | Add `n, hn` |
| `simplexCrossProductElem_natural` | 211 | Add `n, hn` |
| `simplexCrossProductNat` | 280 | The `NatTrans` targets `chainGroupOnProdFunctor (p + q)` — either parameterize or keep `p + q` here since this is the "unfolded" version |

#### 4b. The cross product NatTrans and its components

These are parameterized by `n` already in a sense (via `crossProductTgtFunctor n`), but the connection to `p + q` happens at composition time:

| Definition | Line | Change |
|-----------|------|--------|
| `liftedCrossProductNat` | 355 | Takes `p + q` → takes `n` |
| `crossProductNat` | 371 | Takes `p + q` → takes `n` |
| `crossProduct` | 377 | **Main API change**: add `n, hn` params |

#### 4c. Key lemmas

| Lemma | Line | Change |
|-------|------|--------|
| `crossProductNat_unit` | 386 | Thread `n, hn` |
| `mι_tensor_tensorCoprodNatIso` | 418 | Thread `n, hn` |
| `mι_tensor_comp_crossProduct` | 460 | Thread `n, hn` |
| `simplexCrossProduct_id` | 488 | Thread `n, hn` |

#### 4d. Leibniz rules (biggest payoff in CrossProduct.lean)

**`simplexCrossProduct_leibniz`** (line 501): The `eqToHom (congrArg ... (by omega))` on line 514 disappears. Both the left sum `crossProduct p (q+1)` and right sum `crossProduct (p+1) q` target the same `n` with different `hn` proofs.

**`crossProduct_leibniz`** (line 598): Same — the `eqToHom (by omega)` on line 608 disappears. The `chainMap_f_comp_eqToHom` dance (line 650) is eliminated.

#### 4e. Chain homotopy (line 847)

The construction uses:
- `crossProduct n 1` at degree `n + 1` — works fine (definitional)
- `crossProduct n 0` at degree `n + 0 = n` — works fine (definitional)
- `crossProduct (n+1) 0 ≫ eqToHom (Nat.add_zero (n+1))` (line 944) — **this eqToHom disappears** since `n + 0 = n` is definitional

### Phase 5: Cleanup

- `HomologicalComplex.d_comp_eqToHom` and `HomologicalComplex.eqToHom_comp_d` (lines 671–684) may become unused in this file after the refactor. Keep if used elsewhere or delete.
- `simplexCoprojection_comp_eqToHom` (line 576) — may become unnecessary.
- `chainMap_f_comp_eqToHom` (CrossProduct.lean:587) — may become unnecessary.
- Various `eqToHom`-related helper lemmas in `universalSimplexCrossProduct_boundary` proof may simplify or disappear.

## Expected reduction

Rough estimate of lines affected / eliminated:

| Area | Current lines of eqToHom pain | Expected after refactor |
|------|------------------------------|------------------------|
| `universalSimplexCrossProduct_boundary` proof | ~50 lines of casting | ~10-15 lines (just `by omega` proofs for `hn`) |
| `crossProduct_leibniz` statement + proof | ~10 lines of eqToHom | ~2 lines |
| `simplexCrossProduct_leibniz` | ~5 lines | ~1 line |
| Chain homotopy `eqToHom` | ~5 lines | 0 |
| Helper lemmas that may be removed | ~20 lines | 0 |

## Execution order

1. ✅ Change `shuffleSimplex`, `universalSimplexCrossProduct`, `simplexCrossProduct` signatures
2. ✅ Fix all callers in HomotopyInvariance.lean — compiles with two sorrys:
   - `simplexCrossProduct_zero_left` — statement simplified (eqToHom removed), proof sorry'd
   - `universalSimplexCrossProduct_boundary` — statement simplified (eqToHom removed), proof sorry'd
3. Fill sorry: `simplexCrossProduct_zero_left`
4. Fill sorry: `universalSimplexCrossProduct_boundary`
5. Move to CrossProduct.lean: update ModuleCat wrappers
6. Restate and reprove `simplexCrossProduct_leibniz` and `crossProduct_leibniz`
7. Update chain homotopy construction
8. Clean up unused helper lemmas
