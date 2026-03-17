# Refactor ideas for `EilenbergZilber.lean`

This note records the main refactor opportunities that still stand out in
`HomologyLean/SingularHomology/EilenbergZilber.lean` after the recent `erw`,
non-terminal `simp`, and linter cleanup.

These are **refactor** ideas, not warning fixes: the file already compiles, and the goal here is
to make the proofs shorter, more local, and easier to review before a Mathlib PR.

## High-level priorities

If only one or two follow-ups are worth doing, the best order seems to be:

1. factor the duplicated zero-left / zero-right cross-product proofs;
2. extract one or two helpers from the duplicated Leibniz summand arguments;
3. package the repeated Yoneda / standard-simplex pointwise calculations;
4. compress the bookkeeping in the three `eilenbergZilber_comm_case_*` lemmas.

## 1. Factor `simplexCrossProduct_zero_right` / `simplexCrossProduct_zero_left`

The proofs of

- `simplexCrossProduct_zero_right`
- `simplexCrossProduct_zero_left`

have almost the same shape:

1. expand `simplexCrossProduct` / `universalSimplexCrossProduct`;
2. collapse the shuffle sum to the default shuffle;
3. prove the default shuffle has sign `1`;
4. rewrite with `simplexCoprojection_comp_SCF_map`;
5. finish the pointwise tensor argument with the same `Prod.ext` proof.

The only real differences are:

- whether the unique shuffle is of type `Shuffle n 0` or `Shuffle 0 n`;
- whether the triviality proof uses `Unique_Shuffle_n_0` or `Unique_Shuffle_0_n`;
- a tiny asymmetry in the `split_ifs` proof of the sign calculation.

### Why this is worth doing

- These lemmas are long enough that their duplication is noticeable in review.
- They are mathematically the same "cross product with a 0-simplex collapses to the default
  shuffle" argument.
- The pointwise endpoint proof is already identical.

### Likely refactor shape

Keep the two public lemmas, but extract one or two private helpers:

- a helper proving the default-shuffle sign is `1` in the zero-left / zero-right cases;
- a helper for the common final `Prod.ext` proof after `simplexCoprojection_comp_SCF_map`.

The public lemmas would then read as short wrappers specialized to `Shuffle n 0` and
`Shuffle 0 n`.

### Caution

Do **not** force both lemmas through a single over-general helper if that introduces more casts,
transport equalities, or `eqToHom` bookkeeping than it removes. The best version is probably:

- one shared endpoint lemma;
- one or two short sign lemmas;
- two still-readable theorem bodies.

## 2. Extract helpers from the duplicated Leibniz summand proofs

Inside the simplex-level Leibniz proof, the left-face and right-face summand arguments still
repeat the same proof skeleton with only left/right tensor asymmetry:

- expand the differential into `AlternatingFaceMapComplex.objD`;
- rewrite `faceSimplex j` as a `δ j` applied to `idSimplex`;
- move scalar factors across tensor whiskering;
- fold the result back with
  `simplexCoprojection_comp_eqToHom_comp_δ`.

The duplicated blocks are the two sum arguments currently proved under the comments

- `Goal 1: left face sum`
- `Goal 2: right face sum`

### Why this is worth doing

- This is one of the densest parts of the file.
- The proof is correct, but the main theorem is currently obscured by tactical plumbing.
- A reviewer has to compare two large blocks by eye to see that they are the same argument.

### Likely refactor shape

There are at least two natural extraction points.

#### Option A: extract the `faceSimplex` normalization

Both branches use the same local rewrite:

```lean
show faceSimplex j = (Δ[_] : SSet).δ j (idSimplex _) from ...
```

This wants to become a small lemma, something morally like:

```lean
private lemma faceSimplex_eq_delta_idSimplex ...
```

That would remove one noisy `conv_lhs` micro-proof from each branch.

#### Option B: extract the full summand identity

A stronger refactor would isolate the repeated "one summand of the differential agrees with one
summand of the Leibniz sum" argument into a private lemma with parameters:

- the side (`left` vs `right`);
- the degree parameter;
- the face index `j`.

This would make the main Leibniz proof much shorter, but only if the helper statement can be kept
clean. If the helper needs a huge list of explicit morphisms, then the extraction is not worth it.

### Recommended approach

Start with Option A. It is low-risk and almost certainly improves readability. Only attempt the
full summand extraction if the helper statement stays short.

## 3. Add a tiny local API for Yoneda / standard-simplex pointwise calculations

There is still a recurring local pattern where proofs reduce tensor or face-map identities to
pointwise calculations involving:

- `SSet.yonedaEquiv.symm`
- `SSet.stdSimplex.objEquiv.symm`
- `SSet.stdSimplex.map_apply`
- `Equiv.ulift`
- `SSet.tensorObj_map_fst` / `SSet.tensorObj_map_snd`

This appears, for example, in:

- the zero-left / zero-right cross-product lemmas;
- several of the shuffle / face-map compatibility arguments.

### Why this is worth doing

- These subproofs are short, but they are visually noisy.
- They repeatedly expose low-level implementation details of `stdSimplex.objEquiv`.
- They make simple "first projection" / "second projection" arguments look harder than they are.

### Likely refactor shape

The top of the file already has good local `@[simp]` lemmas:

- `yonedaEquiv_symm_app`
- `yonedaEquiv_symm_objEquiv_symm_app`
- `yonedaEquiv_symm_comp`
- `SSet.tensorObj_map_fst`
- `SSet.tensorObj_map_snd`

What is probably missing is one more thin layer of local helpers specialized to the recurring
endpoint computations, for example:

- a helper for the first projection of the tensor-simplex calculation;
- a helper for the second projection;
- possibly a helper that hides the final `simp [Equiv.ulift]`.

The goal is not to build a large abstraction, only to turn repeated 4-6 line local proofs into
single-line invocations.

## 4. Package the bookkeeping in `eilenbergZilber_comm_case_pq/p0/0q`

The three dispatch lemmas

- `eilenbergZilber_comm_case_pq`
- `eilenbergZilber_comm_case_p0`
- `eilenbergZilber_comm_case_0q`

already have the right high-level structure: each reduces a chain-map condition on one summand to
an already-proved Leibniz lemma.

What still feels heavy is the amount of repeated bookkeeping before the final `convert`:

- rewriting `HomologicalComplex.mapBifunctor.d_eq`;
- expanding `d₁` / `d₂` or proving one side vanishes;
- discharging `ComplexShape.down_Rel`;
- normalizing `MonoidalCategory.curriedTensor`;
- simplifying the sign term to `1`.

### Why this is worth doing

- These lemmas should read as "reduce to the already-proved simplex-level statement".
- Right now, the reduction is correct but still cluttered by standard normalizations.
- The three cases are clearly related, but the similarity is spread across many lines.

### Likely refactor shape

The best target is probably not one giant helper, but a few tiny "bookkeeping" lemmas such as:

- a local wrapper for the common `ComplexShape.down_Rel` obligations;
- a local rewrite lemma for the relevant `ε₁` / `ε₂` values in the three cases;
- possibly a helper that packages the standard `MonoidalCategory.curriedTensor` simplification.

This would leave each `eilenbergZilber_comm_case_*` lemma with a clearer narrative:

1. normalize indices;
2. rewrite the bifunctor differential;
3. invoke the appropriate Leibniz lemma.

## 5. What I would *not* refactor aggressively

Some parts of the file are already near the right abstraction level, and pushing harder would
likely make them worse.

### Do not over-generalize the shuffle-specific proofs

The file has several proofs where the real content lives in very explicit finite combinatorics on
shuffles. Those are naturally tactical and case-heavy. It is fine for them to stay somewhat
concrete if extracting helpers would just move the same complexity into opaque local lemmas.

### Do not hide all `conv` / `slice` usage

Recent cleanup showed that several proofs genuinely benefit from `conv_lhs`, `conv_rhs`, and
`slice_lhs` because they target exact subexpressions cleanly. Replacing those with restated `have`
lemmas would likely increase brittleness rather than reduce it.

## Suggested next step

If doing exactly one refactor pass, the best target is:

`simplexCrossProduct_zero_right` / `simplexCrossProduct_zero_left`

They offer the clearest readability win for the lowest risk. After that, the next best step is a
small helper for the repeated `faceSimplex = δ(idSimplex)` rewrite inside the Leibniz proof.
