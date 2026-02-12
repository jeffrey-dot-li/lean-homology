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

## Coproduct preservation / comparison
- `PreservesCoproduct.iso F X` — `F.obj (∐ X) ≅ ∐ (F.obj ∘ X)` when `F` has `PreservesColimitsOfShape (Discrete ι)`.
- `PreservesCoproduct.inv_hom` — the `.inv` of the above iso equals `sigmaComparison F X`.
- `ι_comp_sigmaComparison G f i` — `Sigma.ι (G.obj ∘ f) i ≫ sigmaComparison G f = G.map (Sigma.ι f i)`.
- `HomologicalComplex.preservesColimitsOfShape_of_eval` — to show `G : D ⥤ HomologicalComplex C c` preserves colimits of shape J, suffice to show `G ⋙ eval n` preserves for each n.
- `comp_preservesColimitsOfShape` — composition of colimit-preserving functors preserves colimits (instance).

## ShortComplex homology functor and AB4
- `AB4OfSize.ofShape ι` — gives `HasExactColimitsOfShape (Discrete ι) C` from `[AB4 C]`. Takes `ι : Type w`, NOT `Discrete ι`.
- `Functor.preservesHomology_of_preservesEpis_and_kernels` — proves `F.PreservesHomology` when `F` preserves epis and kernels (colim has both from AB4).
- `NatTrans.app_homology τ S` — KEY LEMMA. For `τ : F ⟶ G` where both preserve homology, and `S : ShortComplex (J ⥤ C)`: `τ.app S.homology = (S.mapHomologyIso F).inv ≫ homologyMap (S.mapNatTrans τ) ≫ (S.mapHomologyIso G).hom`. Found at `.lake/packages/mathlib/Mathlib/Algebra/Homology/ShortComplex/PreservesHomology.lean:871`.
- `ShortComplex.homologyFunctorIso F` — nat iso: `F.mapShortComplex ⋙ homologyFunctor D ≅ homologyFunctor C ⋙ F` when `F.PreservesHomology`.
- `ShortComplex.functorEquivalence J C` — equivalence `ShortComplex (J ⥤ C) ≌ J ⥤ ShortComplex C`.
- `ShortComplex.colimitCocone K` / `isColimitColimitCocone K` — degreewise colimit cocone for `K : J ⥤ ShortComplex C`.
- `preservesColimitsOfShape_of_natIso` — transfer `PreservesColimitsOfShape` along natural iso.

## Connectivity and sigma types
- `Continuous.exists_lift_sigma` — a continuous map `f : X → Σ_i Y_i` from a connected space factors: `∃ i g, Continuous g ∧ f = Sigma.mk i ∘ g`.
- Access via `σ.hom'.continuous_toFun.exists_lift_sigma` for TopCat morphisms.
- Close the equality with `TopCat.ext (congr_fun hfg)`.

## Discrete diagram normalization
- `Discrete.natIsoFunctor : K ≅ Discrete.functor (K.obj ∘ Discrete.mk)` — canonical iso for any `K : Discrete ι ⥤ C`.
- `preservesColimit_of_iso_diagram F Discrete.natIsoFunctor.symm` — transfer `PreservesColimit (Discrete.functor f) F` to `PreservesColimit K F`.

## Sigma type injection
- `Sigma.mk.inj_iff.mp h` — from `⟨i, x⟩ = ⟨j, y⟩` get `.1 : i = j` and `.2 : HEq x y`.
- `eq_of_heq` — convert `HEq` to `Eq` (after indices match).
- Custom `@[simp] TopCat.sigmaι_apply k x : (sigmaι f k) x = ⟨k, x⟩` — defined in Additivity.lean.
