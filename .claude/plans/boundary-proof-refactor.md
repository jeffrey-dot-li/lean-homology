# Refactoring `universalSimplexCrossProduct_boundary`

Analysis of the boundary proof in `HomologyLean/SingularHomology/EilenbergZilber.lean`
and a concrete plan to remove left/right redundancy and fill the sorry'd edge cases.

---

## Goal 1: Remove left/right redundancy

### Current structure

The proof of `universalSimplexCrossProduct_boundary` (lines 539–781) has three phases:

1. **Steps 1–9** (lines 549–606): Expand `d` into face maps, fold shuffleSimplex, unfold
   simplexCrossProduct on the RHS, collapse the double sum, split into diagonal vs
   non-diagonal. This is shared infrastructure — no duplication.

2. **Step 10** (lines 608–649): Cancel diagonal pairs via `Finset.sum_involution` using
   `swapDiagonalSteps`. Also shared — no duplication.

3. **Step 11** (lines 650–659): Split non-diagonal into left-type and right-type vertices.
   Shared.

4. **Step 12** (lines 661–719): Left bijection via `insertLeftStep`. ~58 lines.

5. **Step 13** (lines 720–780): Right bijection via `insertRightStep`. ~60 lines.

Steps 12 and 13 are the duplicated parts. They each call `Finset.sum_nbij` with four
proof obligations: (a) membership, (b) injectivity, (c) surjectivity, (d) summand equality.

### How the left and right branches differ

#### (a) Membership obligation

| Left (line 667–670) | Right (line 726–729) |
|---|---|
| `insertLeftStep_not_diagonal ν j` | `insertRightStep_not_diagonal ν k` |
| `insertLeftStep_isLeftType ν j` | `fun h => insertRightStep_not_isLeftType ν k h` |

The left branch proves `isDiag ∧ isLeftType`; the right branch proves `isDiag ∧ ¬isLeftType`.
The negation wrapper `fun h => ...` is the only structural difference.

#### (b) Injectivity

| Left (lines 671–678) | Right (lines 730–737) |
|---|---|
| `insertLeftStep_injective` | `insertRightStep_injective` |
| `insertLeftIndex` | `insertRightIndex` |

Structurally identical: extract `hμ, hr` from `Sigma.mk.inj_iff`, build the index equality
from `eq_of_heq`, apply the injective lemma, produce `Prod.ext`.

#### (c) Surjectivity

| Left (lines 679–698) | Right (lines 738–754) |
|---|---|
| Match left case → produce witness | Match right case → produce witness |
| Match right case → `exfalso` via `insertRightStep_not_isLeftType` | Match left case → `exfalso` via `insertLeftStep_isLeftType` |

The two branches are mirror images: the "good" case and "contradiction" case swap.

#### (d) Summand equality

| Left (lines 699–719) | Right (lines 755–780) |
|---|---|
| `sign_insertLeftStep` | `sign_insertRightStep` |
| `fstHom_insertLeftStep_comp_δ` → `congrArg objEquiv.symm` | `fstHom_insertRightStep_comp_δ` → needs extra `eqToHom_comp_δ` rewrite |
| `sndHom_insertLeftStep_comp_δ` → `congrArg objEquiv.symm` | `sndHom_insertRightStep_comp_δ` → needs extra `eqToHom_comp_δ` rewrite |

**This is the key asymmetry.** The left helper lemmas have the form:
```
δ_{insertLeftIndex} ≫ eqToHom(p+q+1 = (p+1)+q) ≫ fstHom(insertLeftStep ν j) = fstHom ν ≫ δ j
δ_{insertLeftIndex} ≫ eqToHom(p+q+1 = (p+1)+q) ≫ sndHom(insertLeftStep ν j) = sndHom ν
```
The eqToHom dimension is `p + q + 1 = (p+1) + q`, which matches the LHS dimension exactly.

The right helper lemmas have:
```
δ_{insertRightIndex} ≫ eqToHom(p+q+1 = p+(q+1)) ≫ fstHom(insertRightStep ν k) = fstHom ν
δ_{insertRightIndex} ≫ eqToHom(p+q+1 = p+(q+1)) ≫ sndHom(insertRightStep ν k) = sndHom ν ≫ δ k
```
The eqToHom dimension is `p + q + 1 = p + (q+1)`, which does NOT match the LHS dimension
`(p+1) + (q+1) - 1 = p + (q+1)`. There's an extra dimension mismatch that requires
`SimplexCategory.eqToHom_comp_δ` to commute the eqToHom past the δ. This is why the right
summand equality proof (lines 765–780) needs `slice_lhs` + `eqToHom_comp_δ` while the left
one (lines 712–719) can close with a direct `congrArg`.

### Can we use a WLOG argument via `Shuffle.swap`?

**In principle, yes.** The Shuffle file already has:

- `Shuffle.swap : Shuffle p q → Shuffle q p` (swaps the two coordinates)
- `sign_eq_negOnePow_mul_swap_sign`: `μ.sign = (-1)^(p*q) * μ.swap.sign`
- `insertRightStep_eq_swap`: `(insertRightStep ν k).swap = insertLeftStep (ν.swap) k`
- `insertRightIndex_eq_swap`: `(insertRightIndex ν k).val = (insertLeftIndex (ν.swap) k).val`
- `sign_insertRightStep` is already proved via `sign_insertLeftStep` + swap

So the shuffle-level combinatorics already factor through swap. The question is whether
the **SSet-level** proof (the `fstHom`/`sndHom` lemmas and the `Finset.sum_nbij` argument)
can also be factored.

**The obstacle is the eqToHom mismatch.** The left case works with
`eqToHom(p+q+1 = (p+1)+q)` and the right case with `eqToHom(p+q+1 = p+(q+1))`.
These are different `SimplexCategory` morphisms. A swap-based WLOG would need to
relate `fstHom(μ.swap)` to `sndHom(μ)` and vice versa, and show that the eqToHom
dimensions transform correctly under swap. This is doable but requires new lemmas:

```lean
lemma fstHom_swap (μ : Shuffle p q) :
    eqToHom (...) ≫ Shuffle.fstHom μ.swap = Shuffle.sndHom μ ≫ eqToHom (...)
lemma sndHom_swap (μ : Shuffle p q) :
    eqToHom (...) ≫ Shuffle.sndHom μ.swap = Shuffle.fstHom μ ≫ eqToHom (...)
```

These would need to navigate the `Fin.castOrderIso` / `OrderHom.comp` layers, similar
to the existing `fstHom_swapDiagonalSteps_comp_δ` proofs. Feasible but not trivial.

**Verdict: WLOG via swap is possible but the eqToHom plumbing makes it non-trivial.
A parameterized bijection lemma is cleaner.**

### Recommended approach: parameterized bijection lemma

Extract a single lemma that handles both the left and right bijection arguments,
parameterized by the "side". The key insight is that the `Finset.sum_nbij` argument
has the same shape in both cases — only the specific Shuffle API calls differ.

#### Proposed helper: `insertStep_bijection_sum`

```lean
/-- Bijection argument for one side of the non-diagonal split.
Parameterized by:
- `insertStep`: the insertion function (insertLeftStep or insertRightStep)
- `insertIndex`: the insertion index function
- `signRel`: the sign relation for this side
- `fstRel`, `sndRel`: the face factorization lemmas for fst/snd components
- `membershipPred`: whether this side is "left-type" or "not left-type"
- `injective`: injectivity of the insertion
- `surjective_case`: which case of nondiag_mem_insertLeft_or_insertRight is the "good" one
-/
private lemma insertStep_bijection_sum
    {p q : ℕ}
    (faceCount : ℕ)  -- p + 2 for left, q + 2 for right
    (shuffleType : Type)  -- Shuffle p (q+1) for left, Shuffle (p+1) q for right
    [Fintype shuffleType]
    (insertStep : shuffleType → Fin faceCount → Shuffle (p+1) (q+1))
    (insertIndex : shuffleType → Fin faceCount → Fin (p + (q+1) + 2))
    ... (many parameters) ... :
    ∑ x : Fin faceCount × shuffleType, ... = ∑ ⟨μ, r⟩ in ..., ... := by
  ...
```

**Problem:** This approach requires abstracting over too many parameters. The types
of `shuffleType` differ (`Shuffle p (q+1)` vs `Shuffle (p+1) q`), the sign relations
have different forms, and the summand equality proofs have genuinely different eqToHom
plumbing. The abstraction would be more complex than the duplication it removes.

### Better approach: extract the four sub-obligations as lemmas

Instead of one mega-lemma, extract the four `Finset.sum_nbij` obligations as
separate lemmas. The injectivity and surjectivity proofs are mechanical and nearly
identical — these benefit most from extraction.

#### Concrete plan for Goal 1

**Step 1: Extract injectivity lemma (saves ~14 lines × 2 = 28 lines)**

```lean
private lemma insertStep_sigma_injective
    {α β : Type*} [DecidableEq α] [DecidableEq β]
    (step : α → β → γ) (idx : α → β → δ)
    (inj : ∀ a₁ a₂ b₁ b₂, step b₁ a₁ = step b₂ a₂ → idx b₁ a₁ = idx b₂ a₂ → a₁ = a₂ ∧ b₁ = b₂)
    (x₁ x₂ : β × α) (h : Sigma.mk (step x₁.2 x₁.1) (idx x₁.2 x₁.1) = ...) :
    x₁ = x₂ := by
  ...
```

Actually, the injectivity proofs are only ~7 lines each and differ only in the names
`insertLeftStep_injective` vs `insertRightStep_injective` and `insertLeftIndex` vs
`insertRightIndex`. The savings are modest.

**Step 2: Extract summand equality into two lemmas (saves ~20 lines each)**

The summand equality is the most complex part and where the real asymmetry lives.
Extract:

```lean
/-- Summand equality for the left bijection: the signed coprojection of
`insertLeftStep ν j` at face index `insertLeftIndex ν j` equals the
left-face cross product term. -/
private lemma insertLeftStep_summand_eq (p q : ℕ) (ν : Shuffle p (q+1)) (j : Fin (p+2)) :
    (insertLeftStep ν j).sign * (-1)^(insertLeftIndex ν j).val •
      simplexCoprojection (shuffleSimplex (idSimplex (p+1)) (idSimplex (q+1))
        (insertLeftStep ν j) ...) =
    (-1)^j.val * ν.sign •
      simplexCoprojection (shuffleSimplex (faceSimplex j) (idSimplex (q+1)) ν ...) := by
  ...
```

And similarly for `insertRightStep_summand_eq`. These would encapsulate the
`fstHom`/`sndHom` rewriting and the eqToHom plumbing.

**Step 3: Extract surjectivity into a shared lemma**

The surjectivity argument in both cases uses `nondiag_mem_insertLeft_or_insertRight`
and then either produces a witness or derives a contradiction. This can be factored:

```lean
/-- Given a non-diagonal `(μ, r)` that is left-type, it came from insertLeftStep. -/
private lemma surj_left (μ : Shuffle (p+1) (q+1)) (r : Fin (p+(q+1)+2))
    (hnd : ¬isDiag μ r) (hlt : isLeftType μ r) :
    ∃ j ν, μ = insertLeftStep ν j ∧ (insertLeftIndex ν j).val = r.val := by
  rcases nondiag_mem_insertLeft_or_insertRight ...
  · exact ⟨j, ν, ...⟩
  · exfalso; exact insertRightStep_not_isLeftType ...

/-- Given a non-diagonal `(μ, r)` that is NOT left-type, it came from insertRightStep. -/
private lemma surj_right ... := by
  rcases nondiag_mem_insertLeft_or_insertRight ...
  · exfalso; exact ... insertLeftStep_isLeftType ...
  · exact ⟨k, ν, ...⟩
```

### Summary for Goal 1

The left/right branches cannot be fully unified via WLOG because of genuine eqToHom
asymmetry in the summand equality. However, extracting the four sub-obligations as
named lemmas would:

1. Reduce the main proof from ~120 lines (Steps 12+13) to ~20 lines (two `Finset.sum_nbij`
   calls referencing the extracted lemmas).
2. Make each sub-obligation independently readable and testable.
3. The `fstHom`/`sndHom` helper lemmas (lines 139–269) are already extracted — the
   summand equality lemmas would compose them.

**Estimated savings: ~80 lines from the main proof, at the cost of ~60 lines of new
helper lemmas. Net: ~20 lines shorter, but much more readable.**

The real win is not line count but **readability**: the main proof becomes a clear
sequence of "expand → cancel diagonal → left bijection → right bijection" with each
step being a single lemma application.

---

## Goal 2: Inline the edge cases `(0, q+1)` and `(p+1, 0)`

### What makes the edge cases different

The current `universalSimplexCrossProduct_boundary` only works for `(p+1, q+1)` because:

1. **The diagonal cancellation (Step 10) requires `(p+1, q+1)`.** The `swapDiagonalSteps`
   involution is defined only for shuffles with both dimensions ≥ 1. A diagonal vertex
   requires both a left and right step adjacent to it, which needs room in both dimensions.

2. **The left/right split (Step 11) requires `(p+1, q+1)`.** The predicate `isLeftType`
   and the decomposition `nondiag_mem_insertLeft_or_insertRight` are stated for
   `Shuffle (p+1) (q+1)`.

3. **The `leftFace`/`rightFace` definitions vanish at the boundary.** Looking at lines
   510–526:
   - `leftFace p q j` matches on `p`: when `p = 0`, it returns `0`.
   - `rightFace p q j` matches on `q`: when `q = 0`, it returns `0`.

   So for `(0, q+1)`: `leftFace 0 (q+1) j = 0` for all `j`, and the LHS of the
   boundary formula becomes `∑ j, (-1)^j • 0 + (-1)^0 • ∑ j, (-1)^j • rightFace ...`.
   The left sum vanishes, leaving only the right sum.

   For `(p+1, 0)`: `rightFace (p+1) 0 j = 0` for all `j`, and the right sum vanishes.

4. **The universal cross product simplifies.** For `(0, q+1)` there is a unique
   `(0, q+1)`-shuffle (the identity), so `universalSimplexCrossProduct 0 (q+1)` is a
   single coprojection. Similarly for `(p+1, 0)`.

### How `eilenbergZilber_comm_case` handles edge cases

Looking at lines 1266–1379, `eilenbergZilber_comm_case` handles all `(p, q)` by:

1. Reducing to the universal case via `crossProduct_boundary_naturality` (line 1294).
2. Splitting into left-face (D₁) and right-face (D₂) summands (line 1296).
3. Case-splitting `p` for the left summand and `q` for the right summand **independently**
   (lines 1300 and 1309).
4. When `p = 0`: D₁ vanishes (`d₁_eq_zero` since there's no predecessor of 0), and
   `leftFace 0 _ = 0`, so both sides are 0. Closed by `simp`.
5. When `q = 0`: D₂ vanishes similarly.
6. The `p+1` and `q+1` cases share a common tail via `all_goals` (lines 1342–1378).

**Key insight:** `eilenbergZilber_comm_case` never needs the full
`universalSimplexCrossProduct_boundary` for edge cases. It only needs
`universalSimplexCrossProduct_boundary'` (which uses `leftFace`/`rightFace`), and the
edge cases are handled by the vanishing of `leftFace`/`rightFace` at `p=0`/`q=0`.

### Strategy for filling the sorry'd cases

The sorry'd cases in `universalSimplexCrossProduct_boundary'` (lines 796–798) are:

**Case `(0, q+1)`:** Need to show:
```
universalSimplexCrossProduct 0 (q+1) ≫ d = ∑ j, (-1)^j • leftFace 0 (q+1) j +
  (-1)^0 • ∑ j, (-1)^j • rightFace 0 (q+1) j
```
Since `leftFace 0 _ = 0`, the left sum vanishes. The RHS simplifies to
`∑ j, (-1)^j • rightFace 0 (q+1) j`. The LHS is a single coprojection (unique shuffle)
composed with `d`. This should be provable by:
1. `simp [leftFace]` to kill the left sum.
2. Expand `universalSimplexCrossProduct 0 (q+1)` using `Fintype.sum_unique` (unique shuffle).
3. Expand `d` as the alternating face map sum.
4. Match term-by-term: each face `δ_j` applied to the unique shuffle simplex gives
   exactly `rightFace 0 (q+1) j`.

**Case `(p+1, 0)`:** Symmetric. `rightFace _ 0 = 0`, the right sum vanishes, and
the LHS expands into the left face sum.

### Can the main proof handle all `(p, q)` without case-splitting?

**No, not easily.** The diagonal cancellation fundamentally requires `(p+1, q+1)` because
`swapDiagonalSteps` needs both dimensions to be positive. For `(0, q)` or `(p, 0)`,
there are no diagonal vertices at all (every vertex of a `(0, q)`-shuffle is a right
step), so the diagonal cancellation step is vacuously true — but the current proof
structure doesn't express this.

To make the proof work for all `(p, q)`, you would need to:
1. Show that for `p = 0` or `q = 0`, the diagonal set is empty (so the diagonal sum is 0).
2. Show that for `p = 0`, all non-diagonal vertices are right-type (so the left sum is empty).
3. Show that for `q = 0`, all non-diagonal vertices are left-type (so the right sum is empty).

This is doable but would require generalizing `nondiag_mem_insertLeft_or_insertRight` and
the `isLeftType`/`isLeftStep` predicates to work for `Shuffle p q` (not just `Shuffle (p+1) (q+1)`).
The Shuffle file would need significant changes.

**Verdict: Filling the sorry's directly is much easier than generalizing the main proof.**

### Concrete plan for Goal 2

**Option A (recommended): Fill the sorry's directly.**

Each sorry is a ~15-20 line proof:

```lean
· -- (0, q+1): leftFace 0 _ = 0, only rightFace contributes.
  simp only [leftFace, Finset.sum_const_zero, zero_add, smul_zero, pow_zero, one_smul]
  -- universalSimplexCrossProduct 0 (q+1) is a single coprojection (unique (0,q+1)-shuffle)
  simp only [universalSimplexCrossProduct, Fintype.sum_unique,
    Shuffle.sign_default_zero_left, one_smul]
  -- Expand d as alternating face map sum
  rw [singChain_d_eq_alternatingFaceMapObjD ...]
  simp only [AlternatingFaceMapComplex.objD, Preadditive.comp_sum, Preadditive.comp_zsmul]
  -- Each summand: coprojection ≫ δ_j = coprojection(δ_j applied)
  simp_rw [simplexCoprojection_comp_eqToHom_comp_δ ...]
  -- Match with rightFace definition
  congr 1; ext j
  simp only [rightFace]
  -- Show δ_j of the unique shuffle simplex = shuffleSimplex (idSimplex 0) (faceSimplex j)
  ...
```

The `(p+1, 0)` case is symmetric.

**Option B: Derive edge cases from `simplexCrossProduct_zero_left`/`_zero_right`.**

The file already has `simplexCrossProduct_zero_right` (line 813) and
`simplexCrossProduct_zero_left` (line 829), which show that the cross product
with a 0-simplex collapses to a single coprojection. These could be used to
simplify the universal cross product in the edge cases, but the boundary expansion
still needs to be done manually.

**Option C: Use `eilenbergZilber_comm_case`'s approach.**

Note that `eilenbergZilber_comm_case` already handles all cases correctly. However,
it proves a different statement (the chain map condition, not the boundary formula).
The boundary formula `universalSimplexCrossProduct_boundary'` is used *inside*
`crossProduct_boundary_naturality`, which is used inside `eilenbergZilber_comm_case`.
So there's a dependency: we can't use `eilenbergZilber_comm_case` to fill the sorry's
in `universalSimplexCrossProduct_boundary'` without creating a circular dependency.

**Recommendation: Option A.** Fill the sorry's directly. Each is a straightforward
calculation that expands the unique shuffle and matches face maps.

---

## Goal 3: Concrete refactoring plan

### Phase 1: Extract bijection sub-obligations (Goal 1)

**New lemmas to add** (in EilenbergZilber.lean, before the main theorem):

1. **`insertLeftStep_surj`** (~15 lines): Given non-diagonal left-type `(μ, r)`,
   produce `(j, ν)` with `μ = insertLeftStep ν j` and index match.

2. **`insertRightStep_surj`** (~15 lines): Given non-diagonal non-left-type `(μ, r)`,
   produce `(k, ν)` with `μ = insertRightStep ν k` and index match.

3. **`insertLeftStep_summand_eq`** (~25 lines): The sign × coprojection equality for
   the left bijection. Encapsulates `sign_insertLeftStep` + `fstHom`/`sndHom` rewriting.

4. **`insertRightStep_summand_eq`** (~30 lines): Same for right. Slightly longer due
   to eqToHom plumbing.

**Changes to the main proof:**

Replace Steps 12–13 (lines 661–780, ~120 lines) with:

```lean
· -- Step 12: Left bijection
  rw [← Fintype.sum_prod_type', Finset.sum_sigma']
  exact Finset.sum_nbij (fun x => ⟨insertLeftStep x.2 x.1, (insertLeftIndex x.2 x.1).cast ..⟩)
    (fun ⟨j, ν⟩ _ => ⟨insertLeftStep_not_diagonal ν j, insertLeftStep_isLeftType ν j⟩)
    (fun ⟨j₁, ν₁⟩ _ ⟨j₂, ν₂⟩ _ h => ... insertLeftStep_injective ...)
    (fun ⟨μ, r⟩ hmem => insertLeftStep_surj ...)
    (fun ⟨j, ν⟩ _ => insertLeftStep_summand_eq p q ν j)
· -- Step 13: Right bijection
  rw [← Fintype.sum_prod_type', Finset.sum_sigma']
  exact Finset.sum_nbij (fun x => ⟨insertRightStep x.2 x.1, (insertRightIndex x.2 x.1).cast ..⟩)
    (fun ⟨k, ν⟩ _ => ⟨insertRightStep_not_diagonal ν k, fun h => insertRightStep_not_isLeftType ν k h⟩)
    (fun ⟨k₁, ν₁⟩ _ ⟨k₂, ν₂⟩ _ h => ... insertRightStep_injective ...)
    (fun ⟨μ, r⟩ hmem => insertRightStep_surj ...)
    (fun ⟨k, ν⟩ _ => insertRightStep_summand_eq p q ν k)
```

This reduces Steps 12+13 from ~120 lines to ~20 lines in the main proof.

### Phase 2: Fill the sorry'd edge cases (Goal 2)

**Fill `(0, q+1)` case** (~20 lines):
- `simp [leftFace]` to eliminate the vanishing left sum.
- Expand `universalSimplexCrossProduct 0 (q+1)` via `Fintype.sum_unique` + `Shuffle.sign_default_zero_left`.
- Expand `d` via `singChain_d_eq_alternatingFaceMapObjD`.
- Match each face map term with `rightFace 0 (q+1) j`.
- The key identity: `δ_j` applied to the unique `(0, q+1)`-shuffle simplex equals
  `shuffleSimplex (idSimplex 0) (faceSimplex j) default`.

**Fill `(p+1, 0)` case** (~20 lines):
- Symmetric: `simp [rightFace]`, expand unique shuffle, match with `leftFace`.

**May need a new helper lemma:**

```lean
/-- Face map on the unique (0, n+1)-shuffle simplex gives the (0, n)-shuffle simplex
composed with δ_j on the second component. -/
private lemma δ_unique_shuffle_zero_left (q : ℕ) (j : Fin (q + 2)) :
    (Δ[0] ⊗ₛ Δ[q + 1]).δ j
      (shuffleSimplex (idSimplex 0) (idSimplex (q + 1)) default ...) =
    shuffleSimplex (idSimplex 0) (faceSimplex j) default ... := by
  ...
```

And the symmetric version for `(n+1, 0)`.

### Phase 3: Consider whether the theorem statement should change

The current split into `universalSimplexCrossProduct_boundary` (for `(p+1, q+1)`) and
`universalSimplexCrossProduct_boundary'` (for all `(p, q)`) is reasonable. The primed
version uses `leftFace`/`rightFace` which handle the vanishing cleanly.

**No change to the theorem statements is needed.** The `leftFace`/`rightFace` abstraction
is the right one — it encapsulates the case split on whether `p` or `q` is zero.

### Phase 4: Possible further cleanup of helper lemmas

The four `fstHom`/`sndHom` helper lemmas (lines 139–269) come in left/right pairs:

| Left | Right |
|---|---|
| `fstHom_swapDiagonalSteps_comp_δ` (lines 139–159) | `sndHom_swapDiagonalSteps_comp_δ` (lines 161–180) |
| `fstHom_insertLeftStep_comp_δ` (lines 186–207) | `sndHom_insertLeftStep_comp_δ` (lines 211–229) |
| `fstHom_insertRightStep_comp_δ` (lines 233–249) | `sndHom_insertRightStep_comp_δ` (lines 253–269) |

Each pair differs only in projecting `.1` vs `.2`. These could potentially be unified
by parameterizing over the projection, but the savings would be minimal (each is ~20 lines)
and the abstraction would obscure the mathematical content. **Leave these as-is.**

### Execution order

1. **First:** Fill the two sorry's in `universalSimplexCrossProduct_boundary'` (Phase 2).
   This is independent and unblocks downstream proofs.

2. **Second:** Extract the four sub-obligation lemmas (Phase 1). This is a pure refactor
   that doesn't change any theorem statements.

3. **Optional:** Clean up the helper lemma pairs (Phase 4) if the refactored code
   still feels redundant.

### Risk assessment

- **Phase 1 (extract lemmas):** Low risk. Pure refactoring, no new math.
- **Phase 2 (fill sorry's):** Medium risk. The `(0, q+1)` and `(p+1, 0)` cases
  require matching face maps through the unique shuffle, which involves eqToHom
  plumbing. The `δ_unique_shuffle_*` helper lemma may need careful Fin arithmetic.
- **Phase 3 (no change):** No risk.

### Estimated effort

- Phase 1: ~2 hours (extract 4 lemmas, rewrite main proof, verify compilation)
- Phase 2: ~3 hours (fill 2 sorry's, possibly with new helper lemmas)
- Total: ~5 hours
