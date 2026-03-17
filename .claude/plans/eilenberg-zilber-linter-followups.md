# `runLinter` follow-ups for `EilenbergZilber`

Current command checked:

```bash
lake build HomologyLean.SingularHomology.EilenbergZilber && \
lake exe runLinter HomologyLean.SingularHomology.EilenbergZilber
```

After a fresh rebuild, the module linter reports **7 remaining errors**.

## High-level status

There are now **no remaining linter errors** in:

- `HomologyLean/SingularHomology/EilenbergZilber.lean`
- `HomologyLean/SingularHomology/Representable.lean`

All **7** remaining errors come from:

- `HomologyLean/SingularHomology/Shuffle.lean`

So to make `lake exe runLinter HomologyLean.SingularHomology.EilenbergZilber` happy, the only
remaining work is in `Shuffle.lean`.

## Remaining linter errors

## Remaining linter errors

## 1. `Shuffle.lean`: duplicated namespaces

File:

- `HomologyLean/SingularHomology/Shuffle.lean`

Declarations flagged:

- `Shuffle.apply_zero`
- `Shuffle.apply_last`
- `Shuffle.invCount_eq_sum_mul_diff`
- `Shuffle.swap_invCount_eq_sum_mul_diff`
- `Shuffle.xy_diff_eq_sum_mixed`

Linter:

- `dupNamespace`

What needs to be done:

- Rename these declarations so the namespace is not duplicated in the final name.

Likely pattern:

- if they are inside `namespace Shuffle`, rename from `Shuffle.foo` to just `foo`;
- or move them out of the duplicated namespace if that is the reason the full name becomes
  `...Shuffle.Shuffle.foo`.

## 2. `Shuffle.lean`: unused arguments

File:

- `HomologyLean/SingularHomology/Shuffle.lean`

Declarations flagged:

- `left`
- `right`

Linter:

- `unusedArguments`

What needs to be done:

- Remove or underscore-prefix the unused `Shuffle p q` argument if it is not semantically needed.
- If it is intentionally present for API shape, consider whether the declaration should be rewritten
  so the parameter is used definitionally rather than passed and ignored.

## Suggested order

1. Fix `Shuffle.lean` duplicated namespaces.
   These are clear naming issues and should not affect proof content.
2. Fix `Shuffle.left` / `Shuffle.right` unused arguments.
   Also local and low-risk.

## Important workflow note

For `simpNF` work, rebuild before trusting the result:

```bash
lake build HomologyLean.SingularHomology.EilenbergZilber
lake exe runLinter HomologyLean.SingularHomology.EilenbergZilber
```

This mattered for the `yonedaEquiv_symm_objEquiv_symm_app` cleanup: the linter output only became
reliable after a fresh build of the target module.

## Not part of the 7 linter errors

The build output also shows additional warnings in `Shuffle.lean`, including:

- deprecated imports
- long lines
- discouraged `refine'`
- flexible `simp` / `simp_all`
- unused simp arguments

These do **not** account for the current 7 blocking linter errors from `runLinter`, but they are
good follow-up cleanup once the blockers above are gone.
