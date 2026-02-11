# Mathlib API Notes

Useful Mathlib lemmas and APIs discovered during proof work.
Record the declaration name, its type signature, and when/why it's useful.

<!-- Example entry:
## CategoryTheory.ShortComplex.Exact
- `ShortComplex.exact_iff_mono` — useful when proving exactness via injectivity
- Found at: .lake/packages/mathlib/Mathlib/Algebra/Homology/ShortComplex/Exact.lean:42
-->

## Mono of chain maps (singular chains)
- `HomologicalComplex.mono_of_mono_f` — chain map is mono iff degreewise mono
- `CategoryTheory.Limits.MonoCoprod.mono_map'_of_injective` — `Sigma.map' ι (fun j => 𝟙 _)` is mono when `ι` is injective. Needs `import Mathlib.CategoryTheory.Limits.MonoCoprod`.
- `Presheaf.restrictedULiftYoneda_map_app` — unfolds `TopCat.toSSet.map` to `uliftYoneda.map`
- After `dsimp [uliftYoneda]`, hypothesis becomes `{ down := σ₁.down ≫ i } = { down := σ₂.down ≫ i }`.
- Close with `ULift.ext _ _ ((cancel_mono i).mp (congrArg ULift.down h))`.

## Naturality of connecting homomorphism δ
- `HomologicalComplex.HomologySequence.δ_naturality` — naturality of δ for short exact sequences of chain complexes. Takes a `ShortComplex.homMk` morphism between the two SES's.
- `ShortComplex.homMk τ₁ τ₂ τ₃ comm₁₂ comm₂₃` — constructs morphism of short complexes.
- `ShortComplex.homMk_τ₁`, `homMk_τ₃` — simp lemmas to extract components.
