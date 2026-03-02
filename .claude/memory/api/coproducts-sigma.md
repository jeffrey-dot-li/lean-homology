# Coproducts, Sigma Types, and Discrete Diagrams

## Functorial coproduct iso naturality

When proving `F.map (Sigma.ι X i) = Sigma.ι _ i ≫ (PreservesCoproduct.iso F X).inv`:
```lean
rw [PreservesCoproduct.inv_hom]
exact (ι_comp_sigmaComparison _ _ i).symm
```
For composed isos (e.g., `mapIso chain_iso ≪≫ PreservesCoproduct.iso homFunctor _`):
1. `simp only [..., Iso.trans_inv, PreservesCoproduct.inv_hom, Functor.mapIso_inv]`
2. `change` to resolve definitional mismatches in `Sigma.ι` types (e.g., `singularHomologyFunctor` vs explicit `chainFunctor ⋙ homologyFunctor`)
3. `rw [chainLevel_iso_ι, Functor.map_comp, ← Category.assoc, ι_comp_sigmaComparison]`

Key insight: when `F = G ⋙ H` definitionally but Lean shows them differently in `Sigma.ι` types, use `change` to rewrite to the explicit composition form so that `ι_comp_sigmaComparison` matches.

## Colimit in Type via concrete sigma factoring

When showing `F : TopCat ⥤ Type v` preserves coproducts (`PreservesColimitsOfShape (Discrete ι)`):

**Reduction pattern:**
```lean
constructor; intro K
let f := K.obj ∘ Discrete.mk
haveI : PreservesColimit (Discrete.functor f) F := by
  apply preservesColimit_of_preserves_colimit_cocone (TopCat.sigmaCofanIsColimit f)
  refine ⟨desc, fac, uniq⟩
exact preservesColimit_of_iso_diagram F Discrete.natIsoFunctor.symm
```

**desc**: Use PSigma (`Σ'`) not `∃` — `obtain` can't eliminate `∃` into `Type`.
**fac**: Evaluate `σ ≫ sigmaι f i` at a point, use `Sigma.mk.inj_iff.mp` for index equality, `eq_of_heq` for the second component.
**uniq**: Factor `p` through summand, `conv_lhs => rw [hp]`, then `congr_fun (hm ⟨i⟩) ⟨t⟩`.

**Sigma injection from TopCat morphism equality:**
```lean
-- From ht' : y.down ≫ sigmaι f j.as = t ≫ sigmaι f i, evaluate at point p:
have := congrArg
  (fun (φ : A ⟶ TopCat.of (Σ k, f k)) => (TopCat.Hom.hom φ) p) ht'
simpa using this  -- gives ⟨j.as, y.down p⟩ = ⟨i, t p⟩
-- Then: Sigma.mk.inj_iff.mp for fst/snd, eq_of_heq for Eq from HEq
```

## Relating categorical Coproducts to DirectSum and Finsupp

When proving properties about isomorphisms between a categorical coproduct of free modules (`∐ fun _ : A => Rmod R`) and Mathlib's `ModuleCat.free R` (which is based on `Finsupp`), follow this standard sequence to reduce the goal to evaluating elements on `Finsupp.single`:

```lean
-- 1. Reduce equality of morphisms out of a coproduct to components
apply CategoryTheory.Limits.Sigma.hom_ext
intro a

-- 2. Clean up functor/colimit mappings (exposes `Sigma.ι` composing with `Sigma.desc`)
simp only [CategoryTheory.Limits.colimit.ι_desc_assoc, CategoryTheory.Limits.Cofan.mk_pt, CategoryTheory.Limits.Cofan.mk_ι_app]

-- 3. Element extensionality: reduce to evaluating the module morphism at `1 : R`
ext

-- 4. Translate the categorical `coprodIsoDirectSum` into the algebraic `DirectSum.lof`
simp [ModuleCat.coprodIsoDirectSum, ModuleCat.coproductCocone]

-- 5. Translate `DirectSum.lof` to `Finsupp.single a 1` using the equivalence
erw [finsuppLEquivDirectSum_symm_lof, finsuppLEquivDirectSum_symm_lof]

-- 6. Evaluate the Finsupp maps (like `Finsupp.lmapDomain` inside `(ModuleCat.free R).map f`)
erw [Finsupp.lmapDomain_apply, Finsupp.mapDomain_single]
```
This is the canonical path for traversing `CategoryTheory.Limits.Sigma` ↔ `DirectSum` ↔ `Finsupp`.

## Pitfall: `Sigma.hom_ext` introduces `Sigma.ι (fun x ↦ R) τ` not `mι τ`

After `apply Sigma.hom_ext; intro τ`, the coprojection is `Sigma.ι (fun x ↦ Rmod R) τ`,
which does NOT syntactically match `mι τ` even though they're definitionally equal.

**Symptom**: `rw [some_lemma_about_mι]` fails with "did not find occurrence of pattern".

**Fix**: Add `have hτ : Sigma.ι (fun x ↦ Rmod R) τ = mι (R := R) τ := rfl` then `rw [hτ]`
before the rewrite that needs `mι`.

## Coproduct preservation / comparison lemmas

- `PreservesCoproduct.iso F X` — `F.obj (∐ X) ≅ ∐ (F.obj ∘ X)` when `F` has `PreservesColimitsOfShape (Discrete ι)`.
- `PreservesCoproduct.inv_hom` — the `.inv` of the above iso equals `sigmaComparison F X`.
- `ι_comp_sigmaComparison G f i` — `Sigma.ι (G.obj ∘ f) i ≫ sigmaComparison G f = G.map (Sigma.ι f i)`.
- `HomologicalComplex.preservesColimitsOfShape_of_eval` — to show `G : D ⥤ HomologicalComplex C c` preserves colimits of shape J, suffice to show `G ⋙ eval n` preserves for each n.
- `comp_preservesColimitsOfShape` — composition of colimit-preserving functors preserves colimits (instance).

## Discrete diagram normalization

- `Discrete.natIsoFunctor : K ≅ Discrete.functor (K.obj ∘ Discrete.mk)` — canonical iso for any `K : Discrete ι ⥤ C`.
- `preservesColimit_of_iso_diagram F Discrete.natIsoFunctor.symm` — transfer `PreservesColimit (Discrete.functor f) F` to `PreservesColimit K F`.

## Sigma type injection

- `Sigma.mk.inj_iff.mp h` — from `⟨i, x⟩ = ⟨j, y⟩` get `.1 : i = j` and `.2 : HEq x y`.
- `eq_of_heq` — convert `HEq` to `Eq` (after indices match).
- `TopCat.sigmaι_comp_fst_eq` — if `σ ≫ sigmaι X i = τ ≫ sigmaι X j` and domain nonempty, then `i = j`. Defined in Additivity.lean.
- `TopCat.sigmaι_cancel` — if `σ ≫ sigmaι X i = τ ≫ sigmaι X i`, then `σ = τ` (mono). Defined in Additivity.lean.

## Connectivity and sigma types

- `Continuous.exists_lift_sigma` — a continuous map `f : X → Σ_i Y_i` from a connected space factors: `∃ i g, Continuous g ∧ f = Sigma.mk i ∘ g`.
- Access via `σ.hom'.continuous_toFun.exists_lift_sigma` for TopCat morphisms.
- Close the equality with `TopCat.ext (congr_fun hfg)`.
