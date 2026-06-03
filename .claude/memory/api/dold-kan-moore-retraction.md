# Dold–Kan / Moore-complex retraction (`PInfty`, normalized Moore) patterns

Patterns for killing degenerate operators against the normalized Moore retraction
`PInftyToNormalizedMooreComplex`, used heavily in the bi-normalized Eilenberg–Zilber proof
(`BisimplicialNormalized.lean`, the `ezComponent_awComponent_comp_retraction` scaffold).

## Key Mathlib facts

- `degeneracy_comp_PInfty (X : SimplicialObject C) (n) (θ : ⦋n⦌ ⟶ Δ') (hθ : ¬Mono θ) :`
  `X.map θ.op ≫ PInfty.f n = 0`. Lives in `Mathlib/AlgebraicTopology/DoldKan/Degeneracies.lean`.
  **This module is NOT imported by `DoldKan/Normalized`** — add
  `import Mathlib.AlgebraicTopology.DoldKan.Degeneracies` explicitly.
- `PInftyToNormalizedMooreComplex_comp_inclusionOfMooreComplexMap X :`
  `PInftyToNormalizedMooreComplex X ≫ inclusionOfMooreComplexMap X = PInfty`.
- `inclusionOfMooreComplexMap_f X n : (inclusionOfMooreComplexMap X).f n = (NormalizedMooreComplex.objX X n).arrow`.
  The whole chain map has a `Mono` instance, but the **componentwise** `Mono ((inclusionOfMooreComplexMap X).f n)`
  is NOT an instance — derive it via `rw [inclusionOfMooreComplexMap_f]; infer_instance` (subobject arrows are mono).
- `PInftyToNormalizedMooreComplex_naturality (f : X ⟶ Y) :`
  `AlternatingFaceMapComplex.map f ≫ PInftyToNormalizedMooreComplex Y = PInftyToNormalizedMooreComplex X ≫ NormalizedMooreComplex.map f`.
- `AlternatingFaceMapComplex.map_f (f) (n) : (AlternatingFaceMapComplex.map f).f n = f.app (op ⦋n⦌)` (`rfl`).

## Pattern 1: inner dual glue (degenerate vertical op killed by Moore retraction)

Goal `Y.map g.op ≫ (PInftyToNormalizedMooreComplex Y).f n = 0` for `g : ⦋n⦌ ⟶ ⦋n⦌` non-mono:

```lean
have h := degeneracy_comp_PInfty Y n g hg
rw [← PInftyToNormalizedMooreComplex_comp_inclusionOfMooreComplexMap Y,
  HomologicalComplex.comp_f, ← Category.assoc] at h
haveI : Mono ((inclusionOfMooreComplexMap Y).f n) := by
  rw [inclusionOfMooreComplexMap_f]; infer_instance
exact zero_of_comp_mono _ h
```

Factor `PInfty.f n = PInftyToNorm.f n ≫ inclusion.f n`, then cancel the mono inclusion component with
`zero_of_comp_mono`.

## Pattern 2: GENERALIZE the glue lemma to an arbitrary abelian category — it fires at the *outer* level too

A bisimplicial object `X : BisimplicialObject C` is a `SimplicialObject (SimplicialObject C)`. The
*outer* simplicial structure lives in the abelian category `A = SimplicialObject C`. So the **same**
inner-glue statement, stated polymorphically, kills outer degeneracies:

```lean
private lemma map_op_comp_PInftyToNormalizedMooreComplex_eq_zero {A : Type*} [Category A]
    [Abelian A] (Y : SimplicialObject A) {n : ℕ} (g : (⦋n⦌ : SimplexCategory) ⟶ ⦋n⦌) (hg : ¬ Mono g) :
    Y.map g.op ≫ (PInftyToNormalizedMooreComplex Y).f n = 0 := ...
```

- Inner use: `... (X _⦋r⦌) β hβ`     (A = C).
- Outer use: `... X α hα`           (A = SimplicialObject C, Y = the bisimplicial object itself).

**Lesson**: when a `SimplicialObject C` lemma is really about "any abelian category", state it that way;
the bisimplicial outer direction reuses it for free instead of re-proving a dual.

## Pattern 3: decomposing the bi-graded retraction `R'` at bidegree `(r, m)`

`R'` = `(((NatTrans.mapHomologicalComplex mooreRetraction _).app (AFMC.obj X) ≫`
`((normalizedMooreComplex C).mapHomologicalComplex _).map (PInftyToNormalizedMooreComplex X)).f r).f m`.
Recall `mooreRetraction.app Y = PInftyToNormalizedMooreComplex Y` (definitional). Decompose with:

```lean
simp only [HomologicalComplex.comp_f, NatTrans.mapHomologicalComplex_app_f, mooreRetraction,
  Functor.mapHomologicalComplex_map_f, alternatingFaceMapComplex_obj_X]
-- ⟹  (PInftyToNormalizedMooreComplex (X _⦋r⦌)).f m              -- INNER leg
--      ≫ ((normalizedMooreComplex C).map ((PInftyToNormalizedMooreComplex X).f r)).f m  -- OUTER leg
```

`alternatingFaceMapComplex_obj_X` is essential: it rewrites `((AFMC.obj X).X r)` to `X _⦋r⦌` so the inner
leg's object matches `X _⦋r⦌.map β.op` syntactically (they are defeq but `rw` needs syntactic match).

## Pattern 4: killing the OUTER degeneracy in `R'`

Goal `(X.map α.op).app (op ⦋m⦌) ≫ R' = 0`, `α : ⦋r⦌ ⟶ ⦋r⦌` non-mono. After Pattern-3 decomposition,
commute the outer op past the inner `PInfty` leg, fold the two outer `NormMoore.map`s, then Pattern-2:

```lean
have hnat := HomologicalComplex.congr_hom
  (PInftyToNormalizedMooreComplex_naturality (X.map α.op)) m
simp only [HomologicalComplex.comp_f, AlternatingFaceMapComplex.map_f] at hnat
slice_lhs 1 2 => rw [hnat]
slice_lhs 2 3 => rw [← HomologicalComplex.comp_f, ← normalizedMooreComplex_map,
  ← Functor.map_comp, map_op_comp_PInftyToNormalizedMooreComplex_eq_zero X α hα,
  Functor.map_zero, HomologicalComplex.zero_f]
rw [comp_zero]
```

Gotchas:
- **Functor-spelling mismatch**: `PInftyToNormalizedMooreComplex_naturality` produces the *bare*
  `NormalizedMooreComplex.map f`, but the decomposed `R'` has `(normalizedMooreComplex C).map (...)`.
  `← Functor.map_comp` needs both as `Functor.map (normalizedMooreComplex C)` — unify first with
  `← normalizedMooreComplex_map` (rewrites `NormalizedMooreComplex.map f` → `(normalizedMooreComplex C).map f`).
- Use `slice_lhs 2 3`, not `1 2`: after `rw [hnat]` the goal has 3 factors
  `[innerP, NormMoore.map α, NormMoore.map (outerRetr.f r)]`; you want to fold/kill the LAST two.

## Pattern 5: the 4-map EZ∘AW summand merge (bifunctor naturality)

`X _⦋r⦌.map (sndHom x).op ≫ (X.map (fstHom x).op).app ⦋r+m⦌ ≫ (X.map ι_front.op).app ⦋r+m⦌ ≫ X _⦋r⦌.map ι_back.op`
collapses to `X _⦋r⦌.map (ι_back ≫ sndHom x).op ≫ (X.map (ι_front ≫ fstHom x).op).app ⦋m⦌`:

```lean
slice_lhs 2 3 => rw [← NatTrans.comp_app, ← Functor.map_comp, ← op_comp]      -- fuse 2 outer maps
slice_lhs 2 3 => rw [← (X.map (ι_front r m ≫ shuffleFstHom x).op).naturality (ι_back r m).op]  -- push inner left
slice_lhs 1 2 => rw [← Functor.map_comp, ← op_comp]                            -- fuse 2 inner maps
```

(See also `api/eqToHom-casting.md` Principle 10 for the general "fuse verticals + naturality" recipe.)

### Mismatched-split twin: `ezawSummand_offDiag_merge`

When the Alexander–Whitney split `(b, c)` differs from the shuffle's bidegree `(r, s)` (with
`b + c = r + s`), the merge gets a C-level **diagonal cast** `eqToHom` wedged between the two outer
operators (ez lands at `⦋r+s⦌`, aw starts at `⦋b+c⦌`). The merged legs become *non-endo*:
outer `A = ι_front b c ≫ eqToHom ≫ shuffleFstHom μ : ⦋b⦌ ⟶ ⦋r⦌`, inner
`B = ι_back b c ≫ eqToHom ≫ shuffleSndHom μ : ⦋c⦌ ⟶ ⦋s⦌`. The cast changes **both** simplicial
indices, so you must first decompose it into two single-variable casts (`have hcast`) and then run the
3-step skeleton **twice**. Full recipe + gotchas: `api/eqToHom-casting.md` **Principle 11**.

The non-endo `A`, `B` are then killed by the **generalized** `outer_/inner_map_op_comp_retraction_eq_zero`
(Patterns 2/4 relaxed from `⦋n⦌ ⟶ ⦋n⦌` to `⦋b⦌ ⟶ ⦋r⦌`): `degeneracy_comp_PInfty` already allows
arbitrary codomain `θ : ⦋n⦌ ⟶ Δ'`, so the generalization is free. Dimension count picks the dead leg:
`b > r ⟹ A` non-mono (via `SimplexCategory.le_of_mono`); `b < r ⟹ c = n-b > s ⟹ B` non-mono.

## Pattern 6: naturality of the Dold–Kan contraction homotopy operator `homotopyPToId`/`homotopyPInftyToId`

To get *naturality in the simplicial object* of the homotopy operator
`homotopyPInftyToId.hom i j` (e.g. as the `hnat` input when lifting the Dold–Kan contraction through
`mapHomologicalComplex`/`flip`), don't fight the operator directly — reduce and induct:

1. `homotopyEquivNormalizedMooreComplexAlternatingFaceMapComplex.homotopyInvHomId` simps (via the
   `@[simps]` lemma `…_homotopyInvHomId`, then `Homotopy.trans_hom`, `Homotopy.ofEq_hom`,
   `Pi.add_apply`, `Pi.zero_apply`, `zero_add`, `homotopyPInftyToId_hom`) down to
   `(homotopyPToId · (j+1)).hom i j`.
2. Extract the general lemma over **all** `q i j` (not just `j+1`) and **induct on `q`**:
   - `zero`: `homotopyPToId · 0 = Homotopy.refl`, `simp [homotopyPToId]` closes (operator is `0`).
   - `succ q`: unfold with
     `simp only [homotopyPToId, homotopyHσToZero, Homotopy.trans_hom, Homotopy.ofEq_hom,`
     `Pi.zero_apply, Homotopy.add_hom, Homotopy.compLeft_hom, Homotopy.nullHomotopy'_hom,`
     `Pi.add_apply, add_zero, zero_add]`
     giving `(homotopyPToId · q).hom i j + (P q).f i ≫ dite ((down ℕ).Rel j i) (hσ' q i j) 0`.
     Then `rw [Preadditive.comp_add, Preadditive.add_comp, ih]; congr 1; split_ifs with h`:
     - `pos`: `rw [← Category.assoc, P_f_naturality, Category.assoc, hσ'_naturality, Category.assoc]`.
     - `neg`: `simp` (the `dite` is `0`).

Key Mathlib naturalities: **`P_f_naturality`** (projections `P q` are natural, `Projections.lean`)
and **`hσ'_naturality`** (homotopy operators `hσ'` are natural, `Homotopies.lean`). Both are
`f.app ⦋n⦌.op ≫ _ = _ ≫ f.app ⦋m⦌.op`. Use `alternatingFaceMapComplex_map_f` to turn
`((alternatingFaceMapComplex C).map f).f n` into `f.app ⦋n⦌.op` so they fire. Gotcha: in this repo
the bare `comp_add`/`add_comp`/`assoc` are *not* in scope — use `Preadditive.comp_add`,
`Preadditive.add_comp`, `Category.assoc`.

## Pattern 7: bridging a `DerivedOp` to the `F₂ = diag ⋙ alternatingFaceMapComplex` chain data

Used in `BisimplicialDerivedOp.lean` (`realize_faceOp`, `realize_boundaryOp`) to identify the
*realization* of a formal EM operator with the actual differential / faces of `F₂.obj X`.

**(a) A single face letter realizes to the diagonal face — a naturality square.**
`faceOp q i = single ⟨δ i, δ i⟩ 1`, so `(faceOp q i).realize X` is the *vertical-then-horizontal*
leg `(X.obj ⦋q+1⦌).map (δ i).op ≫ (X.map (δ i).op).app ⦋q⦌`, while `(diag.obj X).δ i` (after
`SimplicialObject.δ`, `diag_obj_map`) is the *horizontal-then-vertical* leg
`(X.map (δ i).op).app ⦋q+1⦌ ≫ (X.obj ⦋q⦌).map (δ i).op`. These are the two sides of the naturality
square of the natural transformation `X.map (δ i).op` (since `X : BisimplicialObject C` makes
`X.map g` a `NatTrans` between `SimplexCategoryᵒᵖ ⥤ C` functors):

```lean
lemma realize_faceOp (X) (q) (i : Fin (q + 2)) :
    (faceOp q i).realize X = (diag.obj X).δ i := by
  rw [faceOp, realize_single, one_smul, OpLetter.realize, SimplicialObject.δ, diag_obj_map]
  exact (X.map (SimplexCategory.δ i).op).naturality (SimplexCategory.δ i).op
```

`diag_obj_map : (diag.obj X).map f = (X.map f).app _ ≫ (X.obj _).map f` is the key splitter.

**(b) Realize the whole boundary = the chain differential, termwise.**
- Expand `(F₂.obj X).d (n+1) n` with **`AlternatingFaceMapComplex.obj_d_eq`**
  (`= ∑ i, (-1)^↑i • X.δ i`). It is stated about `AlternatingFaceMapComplex.obj`, but the goal has
  `(alternatingFaceMapComplex C).obj` — bridge with a defeq `show ... = (AlternatingFaceMapComplex.obj
  (diag.obj X)).d _ _ from rfl` (the functor's `.obj` is definitionally the bare `.obj`).
- Distribute `realize` over the `Finset.sum`/`zsmul` defining `boundaryOp` via the bundled
  `realizeAddMonoidHom X` (`map_sum`, `map_zsmul`); convert `DerivedOp.realize X M ↔
  realizeAddMonoidHom X M` with `show ... from rfl` (defeq), then `Finset.sum_congr` + `realize_faceOp`.

**General lesson** (recurs across (1c)/(1e)): to push a `Finsupp`-linear operation (`realize`,
`prime`) through a `Finset.sum`/`zsmul`, **bundle it as an `AddMonoidHom`** (mirroring
`realizeAddMonoidHom`) so `map_sum`/`map_zsmul` apply, and use `show lhs = hom x from rfl` to expose
the bare function as the bundled hom where `rw` needs a syntactic match.
