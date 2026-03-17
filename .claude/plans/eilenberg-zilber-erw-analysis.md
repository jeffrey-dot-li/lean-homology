# `erw` analysis for `EilenbergZilber.lean`

I checked all 11 `erw` occurrences in `HomologyLean/SingularHomology/EilenbergZilber.lean`
with Lean MCP goal states and tactic probes.

## High-level conclusion

Most of the `erw`s are not hiding missing Mathlib lemmas. They mostly fall into two
categories:

1. `erw` was used where plain `rw` or `simp` already works.
2. The goal is in the "wrong shape", and `erw` is compensating for that shape mismatch.

Only one site really looks like a genuine bridge issue, and even there the existing local
lemma is already enough: the proof just needs to instantiate it explicitly instead of asking
`rw` to see through the `ULift` wrapper on its own.

## Bucket 1: `Sigma.ι_comp_map'` does not need `erw`

Occurrences:

- line 343
- line 358
- line 421

What is happening:

- `CategoryTheory.Limits.Sigma.ι_comp_map'` rewrites
  `Sigma.ι _ a ≫ Sigma.map' p q`
  to
  `q a ≫ Sigma.ι _ (p a)`.
- In these proofs, `q a` is always `𝟙 _`, so after the rewrite the goal becomes
  `𝟙 _ ≫ ... = ...`.

What Lean MCP showed:

- At 358 and 421, `simp [CategoryTheory.Limits.Sigma.ι_comp_map']` closes the step directly.
- At 343, plain `rw [CategoryTheory.Limits.Sigma.ι_comp_map']` succeeds, and the next
  simplification step handles the resulting identity morphism.

Diagnosis:

- These are not real `erw`-only sites.
- The issue is not coercions or dependent rewriting.
- `erw` is just doing an ordinary rewrite and leaving an identity-composition goal that
  `simp` or the following `simp only [Category.id_comp]` already solves.

Likely cleanup:

- Replace with `rw` or `simp [CategoryTheory.Limits.Sigma.ι_comp_map']`.

## Bucket 2: `yonedaEquiv_symm_objEquiv_symm_app`

Occurrences:

- line 657
- line 665
- line 1101

### The easy two: lines 657 and 665

What is happening:

- The goal already contains an argument of the form
  `SSet.stdSimplex.objEquiv.symm (...)`.
- Your local lemma
  `yonedaEquiv_symm_objEquiv_symm_app`
  matches that shape exactly.

What Lean MCP showed:

- `rw [yonedaEquiv_symm_objEquiv_symm_app]` works at both 657 and 665.
- So does the more explicit normalization route
  `rw [SSet.stdSimplex.map_apply, yonedaEquiv_symm_app]`.

Diagnosis:

- These two are not genuine `erw` cases.
- Plain `rw` already works.

### The real one: line 1101

What is happening:

- The goal is
  `(SSet.yonedaEquiv.symm (SSet.stdSimplex.objEquiv.symm (𝟙 ⦋n⦌))).app d x = ...`
  with `x : Δ[n].obj d`.
- Your lemma expects the second argument in the syntactic form
  `SSet.stdSimplex.objEquiv.symm g`.
- But `x` is only definitionally equal to such a term, via the `ULift`-based
  `SSet.stdSimplex.objEquiv`.

What Lean MCP showed:

- `rw [yonedaEquiv_symm_objEquiv_symm_app]` fails here.
- `erw [yonedaEquiv_symm_objEquiv_symm_app]` succeeds.
- But an explicit instantiation also succeeds:

```lean
simpa using
  (yonedaEquiv_symm_objEquiv_symm_app (f := 𝟙 ⦋n⦌) (g := x.down))
```

Diagnosis:

- This is the one place where `erw` is actually bridging a syntactic/definitional gap.
- The root cause is the `ULift`/`objEquiv` representation of `Δ[n].obj d`, not a missing
  simp lemma about the Yoneda equivalence itself.

Best cleanup:

- Replace the `erw` with the explicit `simpa using ... (g := x.down)` proof term.

Possible helper lemma:

- If this pattern recurs, a tiny local helper for the identity case could be useful, e.g.
  a lemma specialized to arbitrary `x : Δ[n].obj d`.
- I do not think a new global Mathlib lemma is needed.

## Bucket 3: naturality of `forgetIso.hom`

Occurrences:

- line 779
- line 885
- line 942
- line 949

These are the most interesting ones.

### Lines 942 and 949: `rw` already works

What Lean MCP showed:

- `rw [hnat2]; dsimp [coyoneda]` works at 942.
- `rw [hnat3]; dsimp [coyoneda]` works at 949.

Diagnosis:

- These are not actually `erw`-only.
- The naturality lemmas are already matching the goal well enough for ordinary rewriting.

### Lines 779 and 885: plain `rw` fails, but `change` fixes the goal shape

What is happening:

- After `simp only [types_comp_apply]` and `dsimp [coyoneda] at hnat`, the naturality lemma
  is an equality between an explicit `map` expression and an explicit composition.
- The target looks like the composition side, but `rw [← hnat]` still fails.

What Lean MCP showed:

- `rw [← hnat]` fails at 779 and 885.
- But the following works in both cases:

```lean
change MonoidalUnitorRepresentable.forgetIso.hom.app ... ≫ φ = _
rw [← hnat]
```

and

```lean
change MonoidalUnitorRepresentable.forgetIso.hom.app ... ≫ δ = _
rw [← hnat]
```

Diagnosis:

- These two are not missing-lemma cases.
- They are goal-shape cases: the target is not syntactically in the form needed by `rw`
  until you restate it with `change`.
- The likely blockers are reducible wrappers such as:
  `Free`,
  `.app ... .inv` / `.hom.app ...`,
  and related elaboration choices around the isomorphism/naturality expression.

Best cleanup:

- Replace `erw [← hnat]` with a short `change` exposing the `... ≫ φ` / `... ≫ δ` shape,
  then `rw [← hnat]`.

This looks like a style cleanup problem, not a library-gap problem.

## Bucket 4: `map_id` / `id_f` inside `slice_lhs`

Occurrence:

- line 1105

What Lean MCP showed:

- `slice_lhs 3 4 => rw [(SCF (C := C)).map_id, HomologicalComplex.id_f]` works.
- `slice_lhs 3 4 => simp` also works and simplifies even further.

Diagnosis:

- This is definitely not a real `erw` site.
- The slice is already precise enough; no dependent rewriting is needed.

Likely cleanup:

- Replace with `rw` or just `simp` inside the slice.

## Summary by site

### Can be replaced directly by `rw`/`simp`

- 343: `Sigma.ι_comp_map'`
- 358: `Sigma.ι_comp_map'`
- 421: `Sigma.ι_comp_map'`
- 657: `yonedaEquiv_symm_objEquiv_symm_app`
- 665: `yonedaEquiv_symm_objEquiv_symm_app`
- 942: `hnat2`
- 949: `hnat3`
- 1105: `(SCF.map_id, HomologicalComplex.id_f)` inside `slice_lhs`

### Needs goal reshaping, but not a new lemma

- 779: use `change ... ≫ φ = _` then `rw [← hnat]`
- 885: use `change ... ≫ δ = _` then `rw [← hnat]`

### Genuine "bridge" case, but existing local lemma is enough

- 1101: instantiate `yonedaEquiv_symm_objEquiv_symm_app` explicitly with `g := x.down`

## Overall takeaway

I do **not** think the file has a broad missing-`[simp]`-lemma problem.

The recurring patterns are instead:

1. Ordinary rewrites were written as `erw` even though `rw`/`simp` already works.
2. Naturality lemmas sometimes need a `change` first so that the target is in the exact
   composition shape expected by `rw`.
3. The only truly nontrivial `erw` is the `ULift`/`objEquiv` case at line 1101, where
   explicit instantiation is cleaner than asking `rw` to see through definitional equality.

So if the goal is "remove `erw` in mathlib style", my current guess is:

- no new Mathlib lemmas are needed for most of the file;
- one or two tiny local helper lemmas might improve readability;
- the main cleanup is tactical: prefer `rw`, `simp`, and occasionally `change` before
  reaching for `erw`.
