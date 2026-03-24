# Shuffle.lean Cleanup Analysis

## Overview

`Shuffle.lean` (2984 lines) defines `(p,q)`-shuffles as injective monotone maps
`Index(p+q) →o Index(p) × Index(q)` and provides the combinatorial infrastructure
for the Eilenberg–Zilber cross product in `EilenbergZilber.lean` (1848 lines).

This document analyzes the dependency structure, symmetry opportunities, and
cleanup actions needed for a Mathlib PR.

---

## Task 1: Dependency Analysis

### Complete Dependency Table

Every `Shuffle.`-qualified reference in `EilenbergZilber.lean`:

| Shuffle declaration | EZ lines | Context |
|---|---|---|
| `Shuffle.fstHom` | 89 (def), 107, 123, 144, 147, 151, 189, 190, 194, 214, 215, 219, 236, 237, 241 | Core definition + helper lemmas |
| `Shuffle.sndHom` | 93 (def), 107, 125, 166, 169, 173, 221, 256, 257, 261 | Core definition + helper lemmas |
| `Shuffle.isDiagonalVertex` | 141, 163, 489, 497, 596, 600 | Boundary proof: diagonal classification |
| `Shuffle.isDiagonalVertex_decidable` | 598 | Boundary proof: decidability instance |
| `Shuffle.swapDiagonalSteps` | 615 | Boundary proof: sign-reversing involution |
| `Shuffle.swapDiagonalSteps_apply_ne` | 155, 176 | Boundary proof: fst/sndHom helper lemmas |
| `Shuffle.swapDiagonalSteps_neg_sign` | 621 | Boundary proof: sign negation |
| `Shuffle.swapDiagonalSteps_ne` | 640 | Boundary proof: involution ≠ identity |
| `Shuffle.swapDiagonalSteps_vertex` | 644 | Boundary proof: preserves diagonal |
| `Shuffle.swapDiagonalSteps_involutive` | 649 | Boundary proof: involution² = id |
| `Shuffle.isLeftStep` | 652, 695, 696, 748, 749 | Boundary proof: left/right type classification |
| `Shuffle.isLeftStep_decidable` | 654 | Boundary proof: decidability |
| `Shuffle.insertLeftStep` | 665, 695, 696, 748, 749 | Boundary proof: left bijection |
| `Shuffle.insertLeftIndex` | 666, 674 | Boundary proof: left bijection |
| `Shuffle.insertLeftStep_not_diagonal` | 669 | Boundary proof: left insertion is non-diagonal |
| `Shuffle.insertLeftStep_isLeftType` | 670, 745 | Boundary proof: left insertion is left-type |
| `Shuffle.insertLeftStep_injective` | 677 | Boundary proof: left injection is injective |
| `Shuffle.insertLeftStep_face` | 198, 221 | Helper lemmas for fst/sndHom factorization |
| `Shuffle.sign_insertLeftStep` | 702 | Boundary proof: sign relation |
| `Shuffle.insertRightStep` | 724, 690, 695, 696, 748, 749 | Boundary proof: right bijection |
| `Shuffle.insertRightIndex` | 725, 692, 733 | Boundary proof: right bijection |
| `Shuffle.insertRightStep_not_diagonal` | 728 | Boundary proof: right insertion is non-diagonal |
| `Shuffle.insertRightStep_not_isLeftType` | 690, 729 | Boundary proof: right insertion is not left-type |
| `Shuffle.insertRightStep_injective` | 736 | Boundary proof: right injection is injective |
| `Shuffle.insertRightStep_face` | 243, 263 | Helper lemmas for fst/sndHom factorization |
| `Shuffle.sign_insertRightStep` | 758 | Boundary proof: sign relation |
| `Shuffle.nondiag_mem_insertLeft_or_insertRight` | 683, 742 | Boundary proof: surjectivity of insertion |
| `Shuffle.sign` | 341 | Zero-index lemmas |
| `Shuffle.invCount` | 341 | Zero-index lemmas |
| `Shuffle.sign_default_zero_right` | 819 | `simplexCrossProduct_zero_right` |
| `Shuffle.sign_default_zero_left` | 835 | `simplexCrossProduct_zero_left` |

### Categorization

#### Core definitions (used directly in EilenbergZilber)
- `Shuffle` (type) — the abbrev itself
- `Shuffle.sign` / `Shuffle.invCount`
- `Shuffle.fstHom` / `Shuffle.sndHom` (defined in EZ, but uses `Shuffle` internals)
- `Shuffle.isLeftStep` / `Shuffle.isLeftStep_decidable`
- `Shuffle.isDiagonalVertex` / `Shuffle.isDiagonalVertex_decidable`

#### Used in the boundary proof (`universalSimplexCrossProduct_boundary`, lines 539–780)
- `Shuffle.swapDiagonalSteps` + `_apply_ne`, `_neg_sign`, `_ne`, `_vertex`, `_involutive`
- `Shuffle.insertLeftStep` + `_face`, `_not_diagonal`, `_isLeftType`, `_injective`
- `Shuffle.insertLeftIndex`
- `Shuffle.sign_insertLeftStep`
- `Shuffle.insertRightStep` + `_face`, `_not_diagonal`, `_not_isLeftType`, `_injective`
- `Shuffle.insertRightIndex`
- `Shuffle.sign_insertRightStep`
- `Shuffle.nondiag_mem_insertLeft_or_insertRight`

#### Used elsewhere in EilenbergZilber (outside boundary proof)
- `Shuffle.sign_default_zero_right` (line 819, in `simplexCrossProduct_zero_right`)
- `Shuffle.sign_default_zero_left` (line 835, in `simplexCrossProduct_zero_left`)
- `Shuffle.insertLeftStep_face` (lines 198, 221, in `fstHom_insertLeftStep_comp_δ` / `sndHom_insertLeftStep_comp_δ`)
- `Shuffle.insertRightStep_face` (lines 243, 263, in `fstHom_insertRightStep_comp_δ` / `sndHom_insertRightStep_comp_δ`)
- `Shuffle.swapDiagonalSteps_apply_ne` (lines 155, 176, in `fstHom_swapDiagonalSteps_comp_δ` / `sndHom_swapDiagonalSteps_comp_δ`)

#### Potentially unused from EilenbergZilber (NOT directly referenced)

These declarations in `Shuffle.lean` are **not** referenced by name in `EilenbergZilber.lean`:

| Declaration | Line | Used transitively? |
|---|---|---|
| `Shuffle.left` | 101 | No |
| `Shuffle.right` | 105 | No |
| `Shuffle.instFintype` | 109 | Yes — `Fintype (Shuffle p q)` needed for `∑ μ` |
| `Shuffle.swap` | 132 | Yes — used by `sign_insertRightStep` (via `insertRightStep_eq_swap`) |
| `Shuffle.swap_swap` | 151 | Yes — used by `nondiag_mem_insertLeft_or_insertRight` |
| `Shuffle.swapEquiv` | 158 | No |
| `coordSum_lt` | 167 | Yes — used by `coordSum_eq` |
| `coordSum_eq` | 183 | Yes — used pervasively |
| `shuffle_step` | 205 | Yes — used by many insertion lemmas |
| `shuffle_fst_lt_iff_not_snd_lt` | 220 | Likely used transitively |
| `swap_apply_fst` / `swap_apply_snd` | 226/230 | Yes — used by `invCount_swap_eq` |
| `invCount_swap_eq` | 235 | Yes — used by `invCount_add_invCount_swap` |
| `nat_sum_telescope` | 260 | Yes — used by `invCount_add_invCount_swap` |
| `Shuffle.apply_zero` | 285 | Yes — used by `invCount_add_invCount_swap` |
| `Shuffle.apply_last` | 297 | Yes — used by `invCount_add_invCount_swap`, `insertLeftStep_isLeftType` |
| `Shuffle.invCount_eq_sum_mul_diff` | 306 | Yes — used by `swapDiagonalSteps_invCount_sum_odd` |
| `Shuffle.swap_invCount_eq_sum_mul_diff` | 317 | Yes — used by `invCount_add_invCount_swap` |
| `Shuffle.xy_diff_eq_sum_mixed` | 329 | Yes — used by `invCount_add_invCount_swap` |
| `invCount_add_invCount_swap` | 338 | Yes — used by `sign_eq_negOnePow_mul_swap_sign` |
| `sign_eq_negOnePow_mul_swap_sign` | 358 | Yes — used by `sign_insertRightStep`, `sign_default_zero_left` |
| `unique_0_0` | 373 | No — superseded by `Unique_Shuffle_n_0` |
| `subsingleton_0_0` | 380 | No — superseded by `Unique_Shuffle_n_0` |
| `default_0_0` | 384 | No — superseded by `Unique_Shuffle_n_0` |
| `sign_0_0` | 389 | No — superseded by `sign_default_zero_right` |
| `insertLeftIndex_le` | 447 | Yes — used by `insertLeftStepFun_coordSum`, `invCount_insertLeftStep_add` |
| `insertRightIndex_le` | 463 | Yes — used by `insertRightStepFun_coordSum` |
| `insertLeftIndex_ge` | 479 | Yes — used by `insertLeftStepFun_coordSum`, `invCount_insertLeftStep_add` |
| `insertRightIndex_ge` | 494 | Yes — used by `insertRightStepFun_coordSum` |
| `insertLeftIndex_iff` | 513 | Yes — used by `insertLeftStepFun_coordSum`, `insertLeftStep_invCount_term_skip` |
| `insertRightIndex_iff` | 531 | Yes — used by `insertRightStepFun_coordSum` |
| `shuffle_fst_succ_le` | 549 | Unclear — may be unused |
| `insertLeftStepFun` | 564 | Yes — definition body of `insertLeftStep` |
| `insertLeftStepFun_coordSum` | 581 | Yes — used in `insertLeftStep` monotonicity proof |
| `insertRightStepFun` | 739 | Yes — definition body of `insertRightStep` |
| `insertRightStepFun_coordSum` | 752 | Yes — used in `insertRightStep` monotonicity proof |
| `insertLeftStep_isLeftStep_at` | 993 | Yes — used by `insertLeftStep_isLeftType`, `insertLeft_insertRight_disjoint` |
| `insertLeftStep_snd_at` | 1011 | Yes — used by `insertLeftStep_invCount_term_at` |
| `insertLeftStep_invCount_term_at` | 1019 | Yes — used by `invCount_insertLeftStep_add` |
| `insertLeftStep_invCount_term_skip` | 1054 | Yes — used by `invCount_insertLeftStep_add` |
| `invCount_insertLeftStep_add` | 1142 | Yes — used by `sign_insertLeftStep` |
| `insertRightIndex_eq_swap` | 1294 | Yes — used by `insertRightStep_eq_swap` |
| `insertRightStep_eq_swap` | 1307 | Yes — used by `sign_insertRightStep`, `nondiag_mem_insertLeft_or_insertRight` |
| `isLeftVertex` | 1450 | Yes — used by `removeLeft`, `insertLeft_removeLeft`, etc. |
| `isRightVertex` | 1457 | Yes — used by `removeRight`, `isRightVertex_swap`, etc. |
| `finRemove` | 1468 | Yes — used by `removeLeftFun`, `removeRightFun` |
| `removeLeftFun` / `removeRightFun` | 1477/1485 | Yes — definition bodies of `removeLeft`/`removeRight` |
| `finRemove_succAbove` | 1494 | Yes — used by `insertLeft_removeLeft` |
| `succAbove_finRemove` | 1509 | Yes — used by `insertLeft_removeLeft` |
| `finRemove_strictMono_on` | 1518 | Yes — used by `removeLeft_is_shuffle`, `removeRight_is_shuffle` |
| `ne_fst_of_isLeftVertex` | 1542 | Yes — used by `removeLeft_is_shuffle`, `insertIndex_removeLeft` |
| `ne_snd_of_isRightVertex` | 1566 | Yes — used by `removeRight_is_shuffle`, `insertIndex_removeRight` |
| `removeLeft_is_shuffle` | 1582 | Yes — used by `removeLeft` definition |
| `removeRight_is_shuffle` | 1619 | Yes — used by `removeRight` definition |
| `removeLeft` / `removeRight` | 1648/1653 | Yes — used by `nondiag_mem_insertLeft_or_insertRight` |
| `finRemove_val_lt_iff` | 1659 | Yes — used by `insertIndex_removeLeft`, `insertIndex_removeRight` |
| `insertIndex_removeLeft` | 1666 | Yes — used by `insertLeft_removeLeft` |
| `insertLeft_removeLeft` | 1719 | Yes — used by `nondiag_mem_insertLeft_or_insertRight` |
| `insertIndex_removeRight` | 1825 | Yes — used by `nondiag_mem_insertLeft_or_insertRight` |
| `isRightVertex_swap` | 1869 | Yes — used by `removeRight_eq_swap_removeLeft`, `nondiag_mem_insertLeft_or_insertRight` |
| `removeRight_eq_swap_removeLeft` | 1910 | Yes — used by `nondiag_mem_insertLeft_or_insertRight` |
| `not_diagonal_iff_left_or_right` | 1933 | Yes — used by `nondiag_mem_insertLeft_or_insertRight` |
| `insertRightStep_not_isLeftStep_at` | 2003 | Yes — used by `insertLeft_insertRight_disjoint` |
| `insertLeft_insertRight_disjoint` | 2019 | Not directly referenced but needed for correctness |
| `isDiagonalVertex_bounds` | 2089 | Yes — used by `swapDiagonalSteps_fun` and many lemmas |
| `diagonal_left_fst_pos` | 2097 | Yes — used by `swapDiagonalSteps_fun` |
| `diagonal_right_snd_pos` | 2116 | Yes — used by `swapDiagonalSteps_fun` |
| `swapDiagonalSteps_fun` | 2137 | Yes — definition body of `swapDiagonalSteps` |
| `swapDiagonalSteps_fun_coordSum` | 2191 | Yes — used in monotonicity proof |
| `swapDiagonalSteps_fun_local_bounds` | 2220 | Yes — used in monotonicity proof |
| `swapDiagonalSteps_fun_monotone` | 2339 | Yes — used by `swapDiagonalSteps` |
| `swapDiagonalSteps_fun_injective` | 2362 | Yes — used by `swapDiagonalSteps` |
| `swapDiagonalSteps_apply_r_of_left` | 2401 | Yes — used by `swapDiagonalSteps_invCount_sum_odd` |
| `swapDiagonalSteps_apply_r_of_right` | 2425 | Yes — used by `swapDiagonalSteps_invCount_sum_odd` |
| `swapDiagonalSteps_flip_prev` | 2458 | Yes — used by `swapDiagonalSteps_vertex` |
| `swapDiagonalSteps_flip_curr` | 2515 | Yes — used by `swapDiagonalSteps_vertex` |
| `swapDiagonalSteps_apply_ne_r` | 2581 | Duplicate of `swapDiagonalSteps_apply_ne` (2388) |
| `swapDiagonalSteps_val_r` | 2593 | Yes — used by `swapDiagonalSteps_involutive` |
| `swapDiagonalSteps_isLeftStep_toggle` | 2643 | Yes — used by `swapDiagonalSteps_involutive` |
| `swapDiagonalSteps_same_map` | 2714 | No — not referenced from EZ or other Shuffle lemmas |
| `swapDiagonalSteps_invCount_sum_odd` | 2738 | Yes — used by `swapDiagonalSteps_neg_sign` |
| `Unique_Shuffle_n_0` | 2917 | Yes — needed for `Fintype.sum_unique` in EZ |
| `Unique_Shuffle_0_n` | 2943 | Yes — needed for `Fintype.sum_unique` in EZ |

### Declarations safe to remove entirely

1. **`Shuffle.left`** (line 101) — never referenced
2. **`Shuffle.right`** (line 105) — never referenced
3. **`Shuffle.swapEquiv`** (line 158) — never referenced (swap/swap_swap suffice)
4. **`unique_0_0`** (line 373) — superseded by `Unique_Shuffle_n_0`
5. **`subsingleton_0_0`** (line 380) — superseded by `Unique_Shuffle_n_0`
6. **`default_0_0`** (line 384) — superseded by `Unique_Shuffle_n_0`
7. **`sign_0_0`** (line 389) — superseded by `sign_default_zero_right`
8. **`shuffle_fst_succ_le`** (line 549) — appears unused by any other declaration
9. **`swapDiagonalSteps_apply_ne_r`** (line 2581) — exact duplicate of `swapDiagonalSteps_apply_ne` (line 2388)
10. **`swapDiagonalSteps_same_map`** (line 2714) — never referenced
11. **`insertLeft_insertRight_disjoint`** (line 2019) — not directly used in EZ (the disjointness is handled by the left-type/right-type classification instead)
12. **`#check` statements** (lines 1461–1462, 1864–1865) — debugging artifacts

---

## Task 2: Symmetry Analysis

### Left/Right Symmetry (swap)

#### Current state

The file already has key swap infrastructure:
- `Shuffle.swap : Shuffle p q → Shuffle q p` (line 132)
- `swap_swap : swap (swap μ) = μ` (line 151)
- `insertRightStep_eq_swap : (insertRightStep ν k).swap = insertLeftStep (ν.swap) k` (line 1307)
- `insertRightIndex_eq_swap : (insertRightIndex ν k).val = (insertLeftIndex (ν.swap) k).val` (line 1294)
- `sign_eq_negOnePow_mul_swap_sign : u.sign = (-1)^(p*q) * u.swap.sign` (line 358)
- `isRightVertex_swap : isRightVertex μ r ↔ isLeftVertex μ.swap (r.cast ...)` (line 1869)
- `removeRight_eq_swap_removeLeft` (line 1910)

The file **already derives** several right-side results from left-side via swap:
- `sign_insertRightStep` is proved from `sign_insertLeftStep` + `insertRightStep_eq_swap` + `sign_eq_negOnePow_mul_swap_sign` (lines 1337–1358)
- `ne_snd_of_isRightVertex` is proved from `ne_fst_of_isLeftVertex` via swap (line 1566)
- The right branch of `nondiag_mem_insertLeft_or_insertRight` uses `removeRight_eq_swap_removeLeft` + `insertRightStep_eq_swap` + `insertLeft_removeLeft` (lines 1973–1991)

#### What can still be derived via swap

**Can `insertRightStep` be defined as `swap ∘ insertLeftStep ∘ swap`?**

Almost. The relationship is:
```
(insertRightStep ν k).swap = insertLeftStep (ν.swap) k
```
So `insertRightStep ν k = (insertLeftStep (ν.swap) k).swap`. This is already proved as `insertRightStep_eq_swap` (line 1307). However, `insertRightStep` is currently defined independently with its own `insertRightStepFun` (lines 739–749) and its own monotonicity proof (lines 781–903).

**Obstacles to eliminating `insertRightStepFun`:**
1. **Type mismatch**: `insertLeftStep (ν.swap) k : Shuffle (q + 1) p`, and swapping gives `Shuffle p (q + 1)`. The types match, but the `Fin` arithmetic is different: `(q + 1) + p + 1` vs `p + (q + 1) + 1`. The `swap` definition uses `Fin.castOrderIso` to bridge `q + p ↔ p + q`, so the composition works but involves casts.
2. **Definitional unfolding**: Downstream proofs like `insertRightStep_face` unfold `insertRightStepFun` directly. If `insertRightStep` were redefined via swap, these proofs would need to unfold through swap + insertLeftStepFun + swap, which is more complex.
3. **Performance**: The current direct definition may be faster for the kernel to check than the swap-based one.

**Recommendation**: Keep `insertRightStep` as a separate definition for now, but derive all its **properties** from the left-side via swap. This is already partially done. The remaining candidates:

| Right-side lemma | Can derive from left via swap? | Status |
|---|---|---|
| `insertRightStepFun` (def, 739) | Could redefine as `swap ∘ insertLeftStepFun ∘ swap` | Keep separate (performance) |
| `insertRightStepFun_coordSum` (752) | Yes, from `insertLeftStepFun_coordSum` | Currently independent |
| `insertRightStep` (def, 781) | Could redefine via swap | Keep separate (performance) |
| `insertRightStep_face` (930) | Yes, from `insertLeftStep_face` + swap | Currently independent |
| `insertRightStep_injective` (971) | Yes, from `insertLeftStep_injective` + swap | Currently independent |
| `insertRightStep_not_diagonal` (1420) | Yes, from `insertLeftStep_not_diagonal` + swap | Currently independent |
| `insertRightStep_not_isLeftStep_at` (2003) | Yes, from `insertLeftStep_isLeftStep_at` + swap | Currently independent |
| `insertRightStep_not_isLeftType` (2066) | Yes, from `insertLeftStep_isLeftType` + swap | Currently independent |
| `sign_insertRightStep` (1337) | **Already derived** via swap | ✓ |
| `insertRightIndex_eq_swap` (1294) | Bridge lemma (needed) | ✓ |
| `insertRightStep_eq_swap` (1307) | Bridge lemma (needed) | ✓ |
| `removeRight_is_shuffle` (1619) | Yes, from `removeLeft_is_shuffle` + swap | Currently independent |
| `removeRight` (def, 1653) | Could redefine via swap | Keep separate |
| `insertIndex_removeRight` (1825) | Yes, from `insertIndex_removeLeft` + swap | Currently independent |
| `ne_snd_of_isRightVertex` (1566) | **Already derived** via swap | ✓ |

#### Specific derivation sketches

**`insertRightStep_face` from `insertLeftStep_face`:**
```lean
lemma insertRightStep_face (ν : Shuffle p q) (k : Fin (q + 2)) :
    ∀ (i : Index (p + q)),
      (insertRightStep ν k).1 (Fin.succAbove ...) = ((ν.1 i).1, k.succAbove (ν.1 i).2) := by
  intro i
  -- Use insertRightStep_eq_swap: (insertRightStep ν k).swap = insertLeftStep (ν.swap) k
  -- Apply insertLeftStep_face to ν.swap
  -- Swap back and extract components
  have h := insertLeftStep_face (ν.swap) k (i.cast ...)
  -- h : (insertLeftStep (ν.swap) k).1 (...) = (k.succAbove (ν.swap.1 ...).1, (ν.swap.1 ...).2)
  -- Since (insertRightStep ν k).swap = insertLeftStep (ν.swap) k,
  -- we get the result by swapping coordinates
  sorry -- requires careful Fin.cast management
```

**`insertRightStep_injective` from `insertLeftStep_injective`:**
```lean
lemma insertRightStep_injective (k₁ k₂ : Fin (q + 2)) (ν₁ ν₂ : Shuffle p q)
    (hμ : insertRightStep ν₁ k₁ = insertRightStep ν₂ k₂)
    (hr : insertRightIndex ν₁ k₁ = insertRightIndex ν₂ k₂) :
    k₁ = k₂ ∧ ν₁ = ν₂ := by
  -- From hμ, derive (insertRightStep ν₁ k₁).swap = (insertRightStep ν₂ k₂).swap
  -- By insertRightStep_eq_swap: insertLeftStep (ν₁.swap) k₁ = insertLeftStep (ν₂.swap) k₂
  -- By insertRightIndex_eq_swap: insertLeftIndex (ν₁.swap) k₁ = insertLeftIndex (ν₂.swap) k₂
  -- Apply insertLeftStep_injective to get k₁ = k₂ ∧ ν₁.swap = ν₂.swap
  -- From ν₁.swap = ν₂.swap, apply swap_swap to get ν₁ = ν₂
  have h1 : insertLeftStep (ν₁.swap) k₁ = insertLeftStep (ν₂.swap) k₂ := by
    rw [← insertRightStep_eq_swap, ← insertRightStep_eq_swap, hμ]
  have h2 : insertLeftIndex (ν₁.swap) k₁ = insertLeftIndex (ν₂.swap) k₂ := by
    rw [← insertRightIndex_eq_swap, ← insertRightIndex_eq_swap]; exact hr
  obtain ⟨hk, hν⟩ := insertLeftStep_injective k₁ k₂ (ν₁.swap) (ν₂.swap) h1 h2
  exact ⟨hk, by rw [← swap_swap ν₁, ← swap_swap ν₂, hν]⟩
```

**`insertRightStep_not_isLeftType` from `insertLeftStep_isLeftType`:**
```lean
-- The key insight: if insertRightStep ν k had a left step at the insertion point,
-- then swapping would give insertLeftStep (ν.swap) k with a right step at the
-- insertion point, contradicting insertLeftStep_isLeftType.
-- This requires a lemma: isLeftStep (μ.swap) r ↔ ¬isLeftStep μ (r.cast ...)
-- (i.e., left steps of the swap are right steps of the original)
```

#### New lemmas needed for full swap derivation

1. **`isLeftStep_swap`**: `isLeftStep (μ.swap) r ↔ ¬isLeftStep μ (r.cast ...)` — relates left steps of swap to right steps of original. This is the key missing bridge lemma.
2. **`insertRightStep_not_diagonal_via_swap`**: derive from `insertLeftStep_not_diagonal` + `isLeftStep_swap`.
3. **`removeRight_is_shuffle_via_swap`**: derive from `removeLeft_is_shuffle` + swap.

### First/Last Symmetry (complement)

#### Analysis

Every shuffle path goes from `(0,0)` to `(p,q)` with `coordSum_eq` ensuring
`fst + snd = index` at every step. This suggests a **complement** operation:

```
complement(μ)(r) = (p - μ(p+q - r).fst, q - μ(p+q - r).snd)
```

This reverses the path and reflects it through `(p,q)`. Equivalently, it maps
step `r` to step `p+q-1-r` and swaps left↔right.

**Would this help?**

The complement would give `complement : Shuffle p q → Shuffle p q` (same type, unlike swap).
Properties:
- `complement ∘ complement = id`
- `sign(complement μ) = (-1)^(p+q) * sign(μ)` (reversing all steps flips parity when p+q is odd)
- `isLeftStep (complement μ) r ↔ isLeftStep μ (p+q-1-r)`

However, the file's main structure (insertion/removal of steps, diagonal cancellation)
does not have an obvious complement symmetry. The insertion operations
`insertLeftStep`/`insertRightStep` change `p` or `q`, so complement doesn't
directly relate them. The diagonal involution `swapDiagonalSteps` is already
local (changes only one vertex), not global like complement.

**Verdict**: Complement symmetry is mathematically interesting but would not
simplify the existing proofs. It could be useful for other results (e.g.,
relating the EZ map to the Alexander–Whitney map), but is not a cleanup priority.

---

## Task 3: Cleanup Recommendations

### Priority 1: Remove dead code (~80 lines saved)

| Action | Lines saved |
|---|---|
| Remove `Shuffle.left`, `Shuffle.right` | ~6 |
| Remove `Shuffle.swapEquiv` | ~5 |
| Remove `unique_0_0`, `subsingleton_0_0`, `default_0_0`, `sign_0_0` | ~18 |
| Remove `shuffle_fst_succ_le` | ~5 |
| Remove `swapDiagonalSteps_apply_ne_r` (duplicate of `swapDiagonalSteps_apply_ne`) | ~5 |
| Remove `swapDiagonalSteps_same_map` | ~10 |
| Remove `#check` statements | ~4 |
| Remove `insertLeft_insertRight_disjoint` (if truly unused) | ~25 |
| **Subtotal** | **~78** |

### Priority 2: Derive right-side lemmas from left-side via swap (~400 lines saved)

The following right-side proofs can be replaced with short derivations from
their left-side counterparts using `insertRightStep_eq_swap` and
`insertRightIndex_eq_swap`:

| Right-side lemma | Current lines | Estimated new lines | Savings |
|---|---|---|---|
| `insertRightStepFun_coordSum` (752–776) | 25 | 5 | 20 |
| `insertRightStep` monotonicity proof (783–903) | 120 | 15 | 105 |
| `insertRightStep_face` (930–945) | 16 | 8 | 8 |
| `insertRightStep_injective` (971–981) | 11 | 6 | 5 |
| `insertRightStep_not_diagonal` (1420–1437) | 18 | 8 | 10 |
| `insertRightStep_not_isLeftStep_at` (2003–2013) | 11 | 6 | 5 |
| `insertRightStep_not_isLeftType` (2066–2087) | 22 | 8 | 14 |
| `removeRight_is_shuffle` (1619–1643) | 25 | 8 | 17 |
| `insertIndex_removeRight` (1825–1860) | 36 | 10 | 26 |
| **Subtotal** | **~284** | **~74** | **~210** |

Note: The `insertRightStepFun` definition (739–749) and `insertRightStep` definition
(781–783) should be kept as-is for definitional convenience, but the monotonicity
proof inside `insertRightStep` (the `by` block from 783–903) is the big target.
If `insertRightStep` is redefined as `(insertLeftStep (ν.swap) k).swap`, the
120-line monotonicity proof vanishes. But this changes the definitional behavior.

**Alternative**: Keep the definition, but replace the monotonicity proof with:
```lean
noncomputable def insertRightStep (ν : Shuffle p q) (k : Fin (q + 2)) : Shuffle p (q + 1) :=
  (insertLeftStep (ν.swap) k).swap
```
This is clean, short, and the `insertRightStep_eq_swap` lemma becomes `rfl`.

### Priority 3: Style cleanup (~50 lines saved)

1. **Remove redundant `open` statements**: There are 20+ `open HomologyLean.SingularHomology` scattered throughout the file (lines 283, 295, 304, 315, 327, 1446, 1454, 1464, 1492, 1507, 1516, 1540, 1564, 1580, 1617, 1645, 1657, 1664, 1717, 1823, 1862, 1867, 1908, 1931, etc.). These should be consolidated into a single `open` at the top of the relevant section.

2. **Remove `skip` statements**: Multiple `skip` statements appear as debugging artifacts (lines 1538, 1821, etc.).

3. **Remove empty `section`/`end` pairs and redundant `noncomputable section AristotleLemmas`**: The file has multiple `noncomputable section AristotleLemmas` / `end AristotleLemmas` blocks (lines 278/336, 1444/1948, 1997/2015, 2216/2558, 2381/2674, 2574/2674). These should be consolidated.

4. **Long lines**: Many lines exceed 100 characters (Mathlib style limit). Examples:
   - Line 297: `apply_last` proof is a single 280-character line
   - Line 307: `invCount_eq_sum_mul_diff` statement
   - Lines 1569, 1576–1578: `ne_snd_of_isRightVertex` proof
   - Many Aristotle-generated proofs use very long single-line tactics

5. **Missing docstrings**: Most public definitions and lemmas lack docstrings. Key ones to add:
   - `isLeftStep`, `insertLeftIndex`, `insertRightIndex`
   - `insertLeftStep`, `insertRightStep`
   - `isDiagonalVertex`, `swapDiagonalSteps`
   - `isLeftVertex`, `isRightVertex`, `removeLeft`, `removeRight`
   - `sign_insertLeftStep`, `sign_insertRightStep`
   - `nondiag_mem_insertLeft_or_insertRight`

6. **`exact?` calls left in proofs**: Lines 1688, 1728, 1780, 1804, 1807, 1629, 2556, 2670 contain `exact?` which should be replaced with the actual term.

### Priority 4: Structural improvements

1. **Add `isLeftStep_swap` bridge lemma**: This is the key missing piece for systematic swap derivation:
   ```lean
   lemma isLeftStep_swap (μ : Shuffle p q) (r : Fin (p + q)) :
       isLeftStep (μ.swap) (r.cast (by omega)) ↔ ¬isLeftStep μ r
   ```
   This would enable cleaner proofs of `insertRightStep_not_isLeftType`, `insertRightStep_not_isLeftStep_at`, etc.

2. **Consolidate `finRemove` with Mathlib's `Fin.predAbove`**: The `finRemove` function (line 1468) is essentially `Fin.predAbove` or a variant. Check if Mathlib already has this and use it instead.

3. **Move `Unique_Shuffle_n_0` and `Unique_Shuffle_0_n` earlier**: These are used for the zero-index lemmas in EZ and logically belong right after the `Shuffle` definition, not at the end of the file.

### Estimated total line reduction

| Category | Lines saved |
|---|---|
| Dead code removal | ~78 |
| Swap-based derivation of right-side lemmas | ~210 |
| Style cleanup (redundant opens, skips, sections) | ~50 |
| Redefining `insertRightStep` via swap (eliminates monotonicity proof) | ~120 |
| **Total** | **~458** |

This would bring `Shuffle.lean` from ~2984 lines to ~2526 lines, a **15% reduction**.

If the `insertRightStepFun` definition and its `_coordSum` lemma are also eliminated
(by redefining `insertRightStep` via swap), the savings increase to ~500 lines (**17%**).

### Prioritized action list

1. **Remove dead code** (Priority 1) — safe, no proof changes needed
2. **Consolidate `open` statements and remove `skip`/`#check`** — safe, cosmetic
3. **Add `isLeftStep_swap` bridge lemma** — enables all subsequent swap derivations
4. **Redefine `insertRightStep` as `(insertLeftStep (ν.swap) k).swap`** — biggest single win
5. **Derive `insertRightStep_face`, `_injective`, `_not_diagonal`, `_not_isLeftType` from left-side** — medium effort
6. **Derive `removeRight_is_shuffle`, `insertIndex_removeRight` from left-side** — medium effort
7. **Replace `exact?` calls with actual terms** — requires running Lean
8. **Add docstrings to public declarations** — documentation pass
9. **Fix long lines** — formatting pass
10. **Check if `finRemove` can use Mathlib's `Fin.predAbove`** — research needed

---

## Additional Cleanup Analysis

### 1. Proof Quality

#### 1a. The `insertLeftStep` monotonicity proof (lines 617–733, ~116 lines)

This proof is well-structured but excessively verbose. The core argument is:
- Reduce monotonicity to successor-step monotonicity via `Fin.monotone_iff_le_succ`
- Case-split on whether `castSucc r` and `succ r` are before/at/after the insertion point `t`
- 9 cases for each coordinate (3×3 grid), but 5 are impossible

**Problems:**
- The 5 impossible cases each take a full line (`have := Fin.val_succ r; have := fin_val_castSucc r; omega`). These could be collapsed into a single `all_goals` or `any_goals` block.
- The `snd` monotonicity proof (lines 654–724) is 70 lines for what is essentially the same argument as `fst` (lines 621–653, 33 lines). The `snd` case is harder because it requires `coordSum_eq` reasoning, but the proof could be shortened by extracting the "castSucc = t, succ > t" case (lines 700–721) as a helper lemma.
- The proof uses `fin_val_castSucc` (a private backward-compat shim for `Fin.val_castSucc`) — this should use the standard Mathlib name.

**Estimated shortening:** ~40 lines (from 116 to ~75) by collapsing impossible cases and extracting shared logic.

#### 1b. The `swapDiagonalSteps_fun_local_bounds` proof (lines 2220–2336, ~117 lines)

This is one of the worst proofs in the file. It establishes that the swapped value at the diagonal vertex `r` is sandwiched between `μ(r-1)` and `μ(r+1)`.

**Problems:**
- **Massive `exact?` pollution**: Lines 2246, 2250, 2254, 2255, 2256, 2257, 2261, 2273, 2274, 2275, 2291, 2293, 2298 all contain `exact?` — these are unresolved proof search calls left by the AI assistant (Aristotle). Each one is a bound proof obligation that should be a simple `by omega` or `by linarith`.
- **`skip` statements**: Lines 2259, 2264, 2278, 2286 contain `skip` — a no-op tactic used as a placeholder. These are dead code.
- **`generalize_proofs at *` spam**: Used 15+ times in this proof alone. This tactic generalizes proof terms to named hypotheses, but is used here as a blunt instrument to work around Lean's proof-irrelevance issues with `Fin`. Most of these are unnecessary.
- **`grind` for bound proofs**: Lines 2236, 2251 use `grind` where `omega` or `linarith` would be more appropriate and faster.
- **Deeply nested parenthesized blocks**: The proof has `generalize_proofs at *; (` ... `)` nesting up to 4 levels deep, making it nearly unreadable.

**Estimated shortening:** ~80 lines (from 117 to ~35). The mathematical content is simple: in the LR case, the swapped value `(fst-1, snd+1)` is between `(fst-1, snd)` = `μ(r-1)` and `(fst, snd+1)` = `μ(r+1)`. This should be a 30-line proof.

#### 1c. The `invCount_insertLeftStep_add` proof (lines 1142–1270, ~128 lines)

This proof is actually **well-written** — it's the best-structured proof in the file. It clearly:
1. Extracts the term at the insertion point
2. Bijects the remaining terms with `invCount(ν)` via a skip map `φ`
3. Handles the boundary case separately

**Problems:**
- The boundary case (lines 1206–1270) is a near-duplicate of the main case (lines 1161–1205). The `sum_nbij` arguments are identical except for the target element (`t` vs `s`). This could be extracted as a helper.
- Lines 1149–1158 contain 10 lines of abandoned comments about alternative proof strategies. These should be removed.

**Estimated shortening:** ~40 lines by extracting the shared `sum_nbij` logic and removing dead comments.

#### 1d. The `swapDiagonalSteps_invCount_sum_odd` proof (lines 2738–2875, ~137 lines)

This proof is **well-structured** but has massive code duplication: the LR case (lines 2780–2828) and RL case (lines 2829–2875) are nearly identical, differing only in which coordinate increments/decrements. 

**Problems:**
- The two cases share the same structure: extract `shuffle_step` at `r-1` and `r`, derive `hfst`/`hsnd` equalities, compute the four `Nat.sub` values, simplify.
- Each case is ~48 lines; with a shared helper or `wlog`, this could be ~60 lines total.

**Estimated shortening:** ~40 lines by factoring out the shared structure.

#### 1e. The `insertLeft_removeLeft` proof (lines 1719–1821, ~102 lines)

This is the single worst proof in the file.

**Problems:**
- **`exact?` calls**: Lines 1728, 1780, 1804, 1805, 1807 — unresolved.
- **`skip` statements**: Lines 1773, 1788, 1794, 1801, 1817, 1821 — dead code, with comments like "This line is added to prevent the code from being incomplete. It should be removed in the final version."
- **Deeply nested `generalize_proofs at *; (`...`)` blocks**: Up to 8 levels of nesting (line 1773: `skip)))))));`).
- **Opaque proof structure**: The proof is a single monolithic block that unfolds `insertLeftStep`, `insertLeftStepFun`, `removeLeft`, `removeLeftFun` all at once and then fights with `Fin` proof irrelevance. It should be restructured as: (a) show the insertion index is correct, (b) show the values match at each position.

**Estimated shortening:** ~60 lines (from 102 to ~40) with a clean rewrite.

#### 1f. General patterns across Aristotle-generated proofs

The proofs generated by the Aristotle AI assistant share distinctive patterns:
- **`generalize_proofs at *;`** used as a universal workaround (103 occurrences total!)
- **`simp_all +decide [...]`** as a catch-all (135 occurrences)
- **`aesop`** as a fallback (56 occurrences)
- **`grind`** for arithmetic (33 occurrences)
- **`exact?`** left unresolved (25+ occurrences)
- **`skip`** as dead code (20+ occurrences)
- **`‹_›` anonymous hypothesis references** (29 occurrences) — fragile and unreadable
- **`rename_i`** (20 occurrences) — naming anonymous hypotheses after the fact

These are all anti-patterns for Mathlib:
- `grind` is experimental and not accepted in Mathlib
- `exact?` is a search tactic, not a proof term
- `skip` is a no-op
- `‹_›` is fragile under refactoring
- `generalize_proofs at *` is a sledgehammer that obscures proof structure

### 2. Naming Conventions

#### 2a. Inconsistencies with Mathlib conventions

| Current name | Issue | Suggested name |
|---|---|---|
| `fin_val_castSucc` | Private shim; should use Mathlib's `Fin.val_castSucc` | Remove, use `Fin.val_castSucc` |
| `coordSum_lt` | Not namespaced under `Shuffle` | `Shuffle.coordSum_lt` |
| `coordSum_eq` | Not namespaced under `Shuffle` | `Shuffle.coordSum_eq` |
| `shuffle_step` | Not namespaced, uses `shuffle_` prefix | `Shuffle.step` |
| `shuffle_fst_lt_iff_not_snd_lt` | Too long, not namespaced | `Shuffle.fst_lt_iff_not_snd_lt` |
| `shuffle_fst_succ_le` | Not namespaced | `Shuffle.fst_succ_le` |
| `invCount_add_invCount_swap` | Not namespaced | `Shuffle.invCount_add_swap_invCount` |
| `sign_eq_negOnePow_mul_swap_sign` | Verbose | `Shuffle.sign_swap` or `Shuffle.sign_eq_neg_one_pow_mul_swap_sign` |
| `unique_0_0` / `subsingleton_0_0` / `default_0_0` / `sign_0_0` | Inconsistent with `Unique_Shuffle_n_0` | Remove (dead code) |
| `nat_sum_telescope` | Generic lemma in wrong namespace | Move to a utility file or find Mathlib equivalent |
| `insertLeftStep_isLeftStep_at` | `_at` suffix is non-standard | `insertLeftStep_isLeftStep` |
| `insertRightStep_not_isLeftStep_at` | `_at` suffix | `insertRightStep_not_isLeftStep` |
| `finRemove` | Not namespaced under `Fin` or `Shuffle` | `Shuffle.finRemove` or use `Fin.predAbove` |
| `finRemove_succAbove` | Should be `Shuffle.finRemove_succAbove` | Namespace it |
| `succAbove_finRemove` | Should be `Shuffle.succAbove_finRemove` | Namespace it |
| `finRemove_strictMono_on` | Should be namespaced | `Shuffle.finRemove_strictMono_on` |
| `finRemove_val_lt_iff` | Should be namespaced | `Shuffle.finRemove_val_lt_iff` |
| `ne_fst_of_isLeftVertex` | Reads oddly | `Shuffle.isLeftVertex.fst_ne` |
| `ne_snd_of_isRightVertex` | Reads oddly | `Shuffle.isRightVertex.snd_ne` |
| `removeLeft_is_shuffle` | Should be `removeLeftFun_strictMono` | Rename |
| `removeRight_is_shuffle` | Should be `removeRightFun_strictMono` | Rename |
| `not_diagonal_iff_left_or_right` | Should be `Shuffle.not_isDiagonalVertex_iff` | Rename |
| `nondiag_mem_insertLeft_or_insertRight` | Abbreviation `nondiag` is non-standard | `Shuffle.not_isDiagonalVertex_mem_insertLeft_or_insertRight` or shorter |
| `Unique_Shuffle_n_0` | PascalCase instance name | `Shuffle.instUnique_right_zero` or similar |
| `Unique_Shuffle_0_n` | PascalCase instance name | `Shuffle.instUnique_left_zero` or similar |

#### 2b. `lemma` vs `theorem` usage

The file uses `theorem` for `swap_swap` (line 151) and `sign_eq_negOnePow_mul_swap_sign` (line 358), but `lemma` for everything else. By the project's conventions, `theorem` should be reserved for main results. `swap_swap` is a basic property, not a main result — it should be `lemma`. The sign-swap theorem is arguably a main result and can stay as `theorem`.

### 3. Structure Organization

#### 3a. Current section structure

The file has no coherent section/namespace organization:
- Everything is in `namespace Shuffle` (opened at line 98), but many declarations are outside it (lines 278–368, 1444–1948, 1950–2015, etc.) due to `section AristotleLemmas` blocks.
- The 6 `section AristotleLemmas` blocks (lines 278, 1444, 1997, 2216, 2381, 2574) are **not** logically grouped — they're artifacts of the Aristotle AI assistant's session boundaries. Each block opens `noncomputable section AristotleLemmas` and `open HomologyLean.SingularHomology`, which is why there are 34 redundant `open` statements.

#### 3b. Proposed reorganization

```
namespace Shuffle
  /-! ### Core definitions -/
  -- Shuffle, sign, invCount, swap, swap_swap, swapEquiv
  -- apply_zero, apply_last, coordSum_eq, shuffle_step
  -- isLeftStep, isLeftStep_decidable

  /-! ### Sign and swap -/
  -- invCount_swap_eq, invCount_add_invCount_swap
  -- sign_eq_negOnePow_mul_swap_sign

  /-! ### Unique shuffles -/
  -- Unique_Shuffle_n_0, Unique_Shuffle_0_n
  -- sign_default_zero_right, sign_default_zero_left

  /-! ### Insertion operations -/
  -- insertLeftIndex, insertRightIndex
  -- insertLeftStepFun, insertLeftStep
  -- insertRightStepFun, insertRightStep (or via swap)
  -- insertLeftStep_face, insertRightStep_face
  -- insertLeftStep_injective, insertRightStep_injective

  /-! ### Sign of insertion -/
  -- sign_insertLeftStep, sign_insertRightStep

  /-! ### Diagonal vertices -/
  -- isDiagonalVertex, isDiagonalVertex_decidable
  -- insertLeftStep_not_diagonal, insertRightStep_not_diagonal
  -- insertLeftStep_isLeftType, insertRightStep_not_isLeftType

  /-! ### Removal operations -/
  -- isLeftVertex, isRightVertex
  -- finRemove, removeLeftFun, removeRightFun
  -- removeLeft, removeRight
  -- insertLeft_removeLeft, insertIndex_removeLeft
  -- isRightVertex_swap, removeRight_eq_swap_removeLeft

  /-! ### Classification of non-diagonal vertices -/
  -- not_diagonal_iff_left_or_right
  -- nondiag_mem_insertLeft_or_insertRight

  /-! ### Diagonal involution -/
  -- swapDiagonalSteps_fun, swapDiagonalSteps
  -- swapDiagonalSteps_apply_ne, swapDiagonalSteps_vertex
  -- swapDiagonalSteps_involutive
  -- swapDiagonalSteps_neg_sign, swapDiagonalSteps_ne
end Shuffle
```

#### 3c. Declarations that should move to other files

- `fin_val_castSucc` (line 88): Remove entirely; use Mathlib's `Fin.val_castSucc`.
- `nat_sum_telescope` (line 260): This is a general lemma about telescoping sums over `Finset.range`. Check if Mathlib has `Finset.sum_range_sub` or similar. If not, it belongs in a utility file, not in `Shuffle.lean`.
- `finRemove`, `finRemove_succAbove`, `succAbove_finRemove`, `finRemove_strictMono_on`, `finRemove_val_lt_iff`: These are general `Fin` lemmas. Check if `Fin.predAbove` serves the same purpose. If not, they belong in a `Fin` utility file.

### 4. Missing API

#### 4a. Missing `@[simp]` lemmas

Currently only `swap_swap` has `@[simp]`. The following should also be `@[simp]`:

| Declaration | Why |
|---|---|
| `Shuffle.apply_zero` | Canonical simplification of shuffle at 0 |
| `Shuffle.apply_last` | Canonical simplification of shuffle at last |
| `Shuffle.sign_default_zero_right` | Simplifies sign of unique shuffle |
| `Shuffle.sign_default_zero_left` | Simplifies sign of unique shuffle |
| `swapDiagonalSteps_apply_ne` | Simplifies swapped shuffle at non-diagonal vertex |

#### 4b. Missing ext lemma

There is no `@[ext]` lemma for `Shuffle`. Since `Shuffle p q` is an `abbrev` for a subtype of `OrderHom`, extensionality is inherited, but an explicit ext lemma would be clearer:

```lean
@[ext]
lemma Shuffle.ext {μ ν : Shuffle p q} (h : ∀ i, μ.1 i = ν.1 i) : μ = ν :=
  Subtype.ext (OrderHom.ext (funext h))
```

#### 4c. Missing basic API

- **`Shuffle.swap_fst`**: `(μ.swap.1 x).1 = (μ.1 (x.cast ...)).2` — currently only available as private `swap_apply_fst` at the `val` level.
- **`Shuffle.swap_snd`**: Symmetric.
- **`isLeftStep_swap`**: `isLeftStep (μ.swap) (r.cast ...) ↔ ¬isLeftStep μ r` — identified in the previous analysis as the key missing bridge lemma.
- **`Shuffle.invCount_swap`**: Currently `invCount_swap_eq` gives a complex rewriting; a cleaner statement would be useful.
- **`isDiagonalVertex_iff`**: A cleaner characterization: `isDiagonalVertex μ r ↔ 0 < r.val ∧ r.val < n ∧ (isLeftStep μ (r-1) ↔ ¬isLeftStep μ r)`.

### 5. Mathlib Compatibility

#### 5a. `classical` usage

- Line 110 (`instFintype`): Uses `classical` twice. The outer `classical` is needed for `Finite.of_injective`, but the inner one is redundant.
- Line 133 (`swap`): Uses `classical` for the `Fin.castOrderIso` construction. This is likely unnecessary — `Fin.castOrderIso` should be computable.
- Line 152 (`swap_swap`): Uses `classical`. This is likely unnecessary if `swap` is made computable.

Mathlib reviewers will flag unnecessary `classical` usage. The `swap` definition should be rewritten without `classical`:

```lean
def swap (μ : Shuffle p q) : Shuffle q p :=
  ⟨⟨fun x => (μ.1 (x.cast (by omega))).swap, fun a b hab => ...⟩, fun a b hab => ...⟩
```

#### 5b. `noncomputable` usage

The top-level `noncomputable section` (line 81) makes everything noncomputable. This is too broad. Only `instFintype`, `insertLeftStepFun`, `insertLeftStep`, `insertRightStepFun`, `insertRightStep` genuinely need `noncomputable` (due to `Finset.card` in the insertion index, which uses `DecidableEq`). Everything else — `sign`, `invCount`, `swap`, `isLeftStep`, `isDiagonalVertex`, `swapDiagonalSteps`, etc. — should be computable.

Mathlib reviewers will require removing the blanket `noncomputable section` and marking only the necessary definitions.

#### 5c. `grind` usage (33 occurrences)

`grind` is an experimental tactic that is **not accepted in Mathlib**. Every occurrence must be replaced:
- Most `grind` calls are doing arithmetic that `omega` or `linarith` can handle.
- Some `grind` calls are doing propositional reasoning that `tauto` or `simp` can handle.
- A few `grind +ring` calls need `ring` or `ring_nf` followed by `omega`.

#### 5d. `aesop` usage (56 occurrences)

`aesop` is accepted in Mathlib but discouraged for non-trivial closures. Many of the `aesop` calls here are closing goals that could be closed by `simp`, `exact`, or `omega`. Mathlib reviewers will ask for more explicit proofs for readability.

#### 5e. `decide` in `simp_all +decide` (135 occurrences)

The `+decide` flag tells `simp` to use `decide` as a discharger. This is fine for `Prop`-valued goals over finite types, but it can be slow and opaque. Many of these could be replaced with `omega` or explicit lemma applications.

#### 5f. `sorry` usage

There is no actual `sorry` in the file — only a comment on line 2317 that mentions `sorry` in a comment string. The file compiles without `sorry`.

#### 5g. `refine'` usage (13 occurrences)

`refine'` is the Lean 3 syntax; Lean 4 uses `refine`. Mathlib has been migrating away from `refine'`. All 13 occurrences should be updated to `refine`.

#### 5h. `induction'` usage (1 occurrence, line 343)

`induction'` is the Lean 3 syntax. Should be `induction ... with`.

#### 5i. Import hygiene

The file imports:
- `Mathlib.Tactic` (line 74) — a blanket import that pulls in all tactics. Mathlib PRs require minimal imports.
- `Mathlib.GroupTheory.Perm.Sign` (line 75) — needed for sign-related lemmas.
- `Mathlib.Order.Fin.Basic` (line 76) — needed for `Fin` order lemmas.
- `Mathlib.Tactic.GeneralizeProofs` (line 79) — redundant since `Mathlib.Tactic` already includes it.

The `Mathlib.Tactic` import should be replaced with specific tactic imports.

### 6. The `AristotleLemmas` Sections

#### What they are

The 6 `noncomputable section AristotleLemmas` blocks are artifacts of the **Aristotle** AI proof assistant (by Harmonic). The file header (lines 1–72) explicitly credits Aristotle for proving specific lemmas. Each `section AristotleLemmas` block corresponds to a batch of lemmas that Aristotle proved in a single session.

The sections serve two purposes:
1. **`noncomputable`**: Makes all definitions in the section noncomputable (needed because Aristotle doesn't track computability).
2. **`open HomologyLean.SingularHomology`**: Opens the namespace so Aristotle can refer to declarations without full qualification.

#### Problems

1. **Redundant nesting**: The file already has `noncomputable section` at line 81, so the `noncomputable` on each `section AristotleLemmas` is redundant.
2. **Namespace pollution**: Each section opens `HomologyLean.SingularHomology`, but the file is already inside `namespace HomologyLean.SingularHomology` (line 83). The `open` statements are therefore no-ops (opening a namespace you're already in).
3. **Logical incoherence**: The sections don't group related lemmas. For example:
   - Section 1 (278–336): `apply_zero`, `apply_last`, `invCount_eq_sum_mul_diff`, `xy_diff_eq_sum_mixed`
   - Section 2 (1444–1948): `isLeftVertex`, `isRightVertex`, `finRemove`, `removeLeft`, `removeRight`, `insertLeft_removeLeft`, `isRightVertex_swap`, `removeRight_eq_swap_removeLeft`, `not_diagonal_iff_left_or_right`
   - Section 3 (1997–2015): Just `insertRightStep_not_isLeftStep_at`
   
   These groupings reflect Aristotle's session boundaries, not mathematical structure.

4. **Fully-qualified names in proofs**: Inside the sections, Aristotle still uses fully-qualified names like `HomologyLean.SingularHomology.Shuffle.insertLeftStep` (line 915) instead of just `insertLeftStep`. This is because Aristotle's code generation doesn't track the current namespace context.

#### Cleanup

All 6 `section AristotleLemmas` / `end AristotleLemmas` pairs should be removed. The `open` statements inside them are redundant. The `noncomputable` is redundant. The declarations should be reorganized by mathematical topic (see Section 3b above).

### Summary of Additional Findings

| Category | Count | Severity |
|---|---|---|
| `exact?` (unresolved proof search) | 25+ | **Critical** — must resolve before Mathlib PR |
| `skip` (dead tactic) | 20+ | **Critical** — must remove |
| `grind` (experimental tactic) | 33 | **Critical** — not accepted in Mathlib |
| `generalize_proofs at *` (sledgehammer) | 103 | **High** — obscures proof structure |
| `simp_all +decide` (catch-all) | 135 | **Medium** — many could be more explicit |
| `aesop` (catch-all) | 56 | **Medium** — many could be more explicit |
| `‹_›` (anonymous hyp) | 29 | **Medium** — fragile |
| `refine'` (Lean 3 syntax) | 13 | **Low** — mechanical fix |
| `induction'` (Lean 3 syntax) | 1 | **Low** — mechanical fix |
| Redundant `open` statements | 34 | **Low** — cosmetic |
| Missing `@[simp]` | ~5 | **Low** — API completeness |
| Blanket `noncomputable section` | 1 | **Medium** — Mathlib requires precision |
| Blanket `import Mathlib.Tactic` | 1 | **Medium** — Mathlib requires minimal imports |
| Unnecessary `classical` | 3 | **Medium** — Mathlib flags this |
| `#check` debugging artifacts | 3 | **Low** — remove |
| `sorry` in comments | 1 | **Cosmetic** — misleading |

### Revised Line Count Estimate

With the additional findings, the total cleanup potential is larger than initially estimated:

| Category | Lines saved |
|---|---|
| Dead code removal (Priority 1, original) | ~78 |
| Swap-based derivation of right-side lemmas | ~210 |
| Style cleanup (opens, skips, checks, sections) | ~80 |
| Redefining `insertRightStep` via swap | ~120 |
| Proof shortening (local_bounds, insertLeft_removeLeft, invCount_add) | ~220 |
| Resolving `exact?` / removing `skip` / replacing `grind` | ~50 |
| Deduplicating `swapDiagonalSteps_invCount_sum_odd` LR/RL cases | ~40 |
| **Total** | **~798** |

This would bring `Shuffle.lean` from ~2984 lines to ~2186 lines, a **27% reduction**, while also dramatically improving proof quality and Mathlib compatibility.
