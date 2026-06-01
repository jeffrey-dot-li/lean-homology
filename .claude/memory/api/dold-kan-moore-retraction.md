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
