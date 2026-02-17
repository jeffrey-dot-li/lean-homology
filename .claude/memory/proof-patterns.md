# Proof Patterns

Reusable strategies for recurring proof shapes in this project.

## Quotients

```lean
have h := Quotient.mk_out q          -- extract representative
exact Quotient.exact (some_equality)  -- quotient equality → relation
exact Quotient.sound (some_relation)  -- relation → quotient equality
```

## Homotopies

```lean
-- Path.Homotopic ≈ ContinuousMap.HomotopyRel ... {0, 1}
refine ⟨{
  toFun := fun ⟨s, t⟩ => ...
  continuous_toFun := by continuity / fun_prop
  map_zero_left := by ...
  map_one_left := by ...
  prop' := by ...
}⟩
```

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

## NatIso.ofComponents naturality for tensor/free-module isos

When proving naturality for `NatIso.ofComponents` whose components are compositions like
`(α.app X ⊗ₘ β.app Y) ≫ freeTensorProductIso.hom`:

1. Unfold functor maps: `dsimp only [myFunctor, Functor.comp_map, Functor.prod_map]`
2. Convert to tensor notation: `simp only [MonoidalCategory.tensor_map]`
3. Combine tensors: `rw [← Category.assoc ..., MonoidalCategory.tensorHom_comp_tensorHom]`
4. Apply component naturality: `erw [nat_iso.hom.naturality f, ...]`
   - Use `erw` (not `rw`) when `.hom.app X` vs `.app X).hom` causes syntactic mismatch
5. Split tensor back: `rw [← MonoidalCategory.tensorHom_comp_tensorHom, Category.assoc, ...]`
6. Use `congr 1` to reduce to the `freeTensorProductIso` naturality piece

Key lemma: `MonoidalCategory.tensorHom_comp_tensorHom` (in `MonoidalCategory` namespace):
`(f₁ ⊗ₘ f₂) ≫ (g₁ ⊗ₘ g₂) = (f₁ ≫ g₁) ⊗ₘ (f₂ ≫ g₂)`

## freeTensorProductIso naturality via monoidal functor

`freeTensorProductIso.hom` is definitionally equal to `Functor.LaxMonoidal.μ (ModuleCat.free R)`.
So naturality comes from:
```lean
have := (Functor.Monoidal.μNatIso (ModuleCat.free R)).hom.naturality
  (show (A, B) ⟶ (A', B') from (f, g))
simp only [Functor.Monoidal.μNatIso_hom_app] at this
convert this using 1  -- handles definitional mismatches in tensor/Prod.map
```

The `show ... from ...` annotation is needed because `(f, g)` must be typed as a
morphism in the product category `Type u × Type u`, not just a bare pair.

## Covering Maps

```lean
set lift := cov.liftPath γ e γ_0
have h_lifts := cov.liftPath_lifts γ e γ_0
have h_mono := cov.liftPath_apply_one_eq_of_homotopicRel h e₁ e₂
```
