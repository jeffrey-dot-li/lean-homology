# Homology, ShortComplex, and Chain Maps

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

## ShortComplex homology functor and AB4

- `AB4OfSize.ofShape ι` — gives `HasExactColimitsOfShape (Discrete ι) C` from `[AB4 C]`. Takes `ι : Type w`, NOT `Discrete ι`.
- `Functor.preservesHomology_of_preservesEpis_and_kernels` — proves `F.PreservesHomology` when `F` preserves epis and kernels (colim has both from AB4).
- `NatTrans.app_homology τ S` — KEY LEMMA. For `τ : F ⟶ G` where both preserve homology, and `S : ShortComplex (J ⥤ C)`: `τ.app S.homology = (S.mapHomologyIso F).inv ≫ homologyMap (S.mapNatTrans τ) ≫ (S.mapHomologyIso G).hom`. Found at `.lake/packages/mathlib/Mathlib/Algebra/Homology/ShortComplex/PreservesHomology.lean:871`.
- `ShortComplex.homologyFunctorIso F` — nat iso: `F.mapShortComplex ⋙ homologyFunctor D ≅ homologyFunctor C ⋙ F` when `F.PreservesHomology`.
- `ShortComplex.functorEquivalence J C` — equivalence `ShortComplex (J ⥤ C) ≌ J ⥤ ShortComplex C`.
- `ShortComplex.colimitCocone K` / `isColimitColimitCocone K` — degreewise colimit cocone for `K : J ⥤ ShortComplex C`.
- `preservesColimitsOfShape_of_natIso` — transfer `PreservesColimitsOfShape` along natural iso.
