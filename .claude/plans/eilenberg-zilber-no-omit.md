# Remove `omit`s from `EilenbergZilber.lean`

## Goal

Refactor `HomologyLean/SingularHomology/EilenbergZilber.lean` so that:

1. There are **no `omit ... in` declarations** in the file.
2. There are **no `unusedSectionVars` warnings** left in the file.
3. The file still compiles with **no Lean errors** after each structural step.

This is a structural refactor, not a warning-cleanup pass in general. Do **not** chase unrelated
`simp`-arg or long-line warnings unless they are forced by the section reorganization.

## Design decisions

### Section strategy

Use **nested sections** as the default pattern.

Reason:

- The assumption sets in this file are mostly cumulative.
- Sections are **not namespaces**, so nesting does not create extra qualification burden.
- A later inner section naturally expresses "same assumptions as before, plus more".

Use **sibling sections only as exceptions** if the dependency graph is not monotone.

### Outlier declarations

If one or two declarations in an otherwise stronger section need fewer assumptions, prefer:

- moving them earlier into a weaker section, or
- giving them **explicit instance binders on the declaration**

rather than introducing `omit ... in`.

Do **not** use `include` for this cleanup. The preferred pattern is explicit instance binders
directly on the declaration when needed.

## Current state to clean up

### Remaining `omit`s

At the time this plan was written, the file contains these `omit`s:

- `freeGen_chainGroupIsoFree`
- `freeGen_δ`
- `chainTensorHomEquiv_apply`
- `crossProduct_normalized`
- `crossProduct_natural`
- `coprojection_tensorHom_chainCrossProduct`

### Remaining `unusedSectionVars` warnings

At the time this plan was written, the remaining unnecessary-assumption warnings are on:

- `ι_eilenbergZilber_f`
- `eilenbergZilber_comm_case_pq`
- `eilenbergZilber_comm_case_p0`
- `eilenbergZilber_comm_case_0q`
- `eilenbergZilber_comm`
- `eilenbergZilber_natural`

## High-level strategy

The cleanup should proceed by **weakening the section ladder**, not by sprinkling more local fixes.

### Principle

For each declaration currently protected by `omit ... in`:

1. Identify the weakest assumptions it really needs.
2. Move it upward into the earliest compatible section, or give it explicit binders.
3. Only then introduce stronger assumptions for later declarations.

### Concrete direction

The file currently has a good cumulative structure:

- `BasicChainComplex`
- `FreeForgetful`
- `MonoidalCoherence`
- `EilenbergZilberAssembly`

Keep that overall nested-section shape unless a specific cluster forces an exception.

## Recommended section refinement

### 1. Split the current free/forgetful layer more finely

The current `FreeForgetful` / `MonoidalCoherence` transition is still too coarse.

Refine it into a dependency ladder closer to:

1. A weak free/adjunction section containing declarations that do **not** need
   `[(forget C).leftAdjoint.Monoidal]`.
2. A later section that introduces `[(forget C).leftAdjoint.Monoidal]` for declarations that use
   `Functor.Monoidal.μIso Free ...`.
3. A later section that introduces `[(forget C).LaxMonoidal]`,
   `[(Adjunction.ofIsRightAdjoint (forget C)).IsMonoidal]`,
   `NatTrans.IsMonoidal ...`, and `MonoidalLinear ℤ C`.

### 2. Move declarations earlier when possible

In particular, `freeGen_chainGroupIsoFree` is a prime candidate to move earlier into a weaker
section instead of keeping:

```lean
omit [(forget C).leftAdjoint.Monoidal] in
```

The guiding test is: if a declaration only references `Free`, `freeGen`, `chainGroupIsoFree`,
adjunction data, and `MonoidalUnitorRepresentable`, then it likely belongs in an earlier section.

### 3. Use declaration-level instance binders for isolated outliers

If a declaration is isolated and only needs a slightly different assumption set than its neighbors,
prefer explicit binders like:

```lean
lemma foo {C : Type u} [Category.{v} C] [A C] : ... := by
  ...
```

This is preferable to:

- creating a whole sibling section for one declaration, or
- keeping an `omit ... in` patch.

## Specific targets

### A. Remove all six existing `omit`s

Handle each by moving declarations upward or adding explicit binders:

- `freeGen_chainGroupIsoFree`
- `freeGen_δ`
- `chainTensorHomEquiv_apply`
- `crossProduct_normalized`
- `crossProduct_natural`
- `coprojection_tensorHom_chainCrossProduct`

### B. Then remove the six remaining unnecessary-assumption warnings

These all live in the late Eilenberg-Zilber assembly area:

- `ι_eilenbergZilber_f`
- `eilenbergZilber_comm_case_pq`
- `eilenbergZilber_comm_case_p0`
- `eilenbergZilber_comm_case_0q`
- `eilenbergZilber_comm`
- `eilenbergZilber_natural`

These likely require a finer split inside the current late assembly region, especially separating:

- declarations that only need the previously-built cross product infrastructure, from
- declarations that really need the stronger assembly-level assumptions.

## Shell-first editing workflow

Because this is mostly declaration reordering, prefer shell-assisted reconstruction over large
manual edits.

### Workflow

1. Build a temporary reordered file from line ranges of the current source.
2. Insert new section headers and variable blocks manually where needed.
3. Move declarations upward by copying exact ranges, not by retyping proofs.
4. After each structural step, run Lean diagnostics before continuing.
5. Once the temporary file is stable, copy it back onto `EilenbergZilber.lean`.

### Verification rule

After **every** meaningful structural move:

- run `lean_diagnostic_messages severity="error"` on the target file
- if errors appear, fix or revert immediately before continuing

Do not batch multiple risky structural moves before verifying.

## Practical execution order

Recommended order:

1. Eliminate the early `omit` on `freeGen_chainGroupIsoFree` by moving it upward.
2. Re-check compilation.
3. Eliminate `freeGen_δ`.
4. Re-check compilation.
5. Eliminate `chainTensorHomEquiv_apply`.
6. Re-check compilation.
7. Eliminate `crossProduct_normalized`, `crossProduct_natural`, and
   `coprojection_tensorHom_chainCrossProduct`.
8. Re-check compilation.
9. Finally refine the late assembly block to remove the six remaining `unusedSectionVars` warnings.
10. Re-run full diagnostics and confirm:
   - no Lean errors
   - no `omit`s
   - no `unusedSectionVars` warnings

## Non-goals

This plan is **not** for:

- shortening long lines
- removing unrelated `simp`-arg warnings
- proof simplification unrelated to assumption scoping
- renaming declarations

Only do those if they become necessary collateral changes of the section refactor.
