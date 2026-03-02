# Monoidal Categories, Tensor Products, and Free Modules

## `NatIso.ofComponents` vs Functor-Level Composition

**Problem**: When building a `NatIso` by composing functor-level operations (`≪≫`, `isoWhiskerLeft`, `isoWhiskerRight`, `NatIso.prod`, `Functor.associator`), the resulting `.hom.app X` does NOT reduce to a simple component — it contains `𝟙` identity morphisms from `Functor.associator` (because `⋙` is not definitionally associative). This blocks element-level proofs.

**Symptom**: After `simp` with all relevant lemmas, goals still contain `ModuleCat.Hom.hom (𝟙 M)` or similar identity morphisms that won't simplify away, requiring 20+ lines of workarounds.

**Solution**: Use `NatIso.ofComponents` instead. It makes `.hom.app X` definitionally equal to the component iso you provide. Trade-off: you must prove naturality manually (often a `sorry` initially).

```lean
-- BAD: functor-level composition
def myNatIso : F ≅ G :=
  isoWhiskerRight (step1NatIso) H ≪≫ step2NatIso

-- GOOD: ofComponents
def myNatIso : F ≅ G :=
  NatIso.ofComponents
    (fun X => step1Iso X ≪≫ step2Iso X)
    (by sorry) -- naturality, fill later
```

**Key simp lemma**: `NatIso.ofComponents_hom_app` — reduces `.hom.app X` to the component.

## Typical Proof Pattern for Element-Level NatIso Reasoning

```lean
-- 1. Unfold ofComponents
simp only [myNatIso, NatIso.ofComponents_hom_app, Iso.trans_hom,
  MonoidalCategory.tensorIso_hom, ModuleCat.hom_comp,
  LinearMap.coe_comp, Function.comp_apply]
-- 2. Distribute tensor with erw (simp can't match ConcreteCategory.hom)
erw [ModuleCat.MonoidalCategory.leftUnitor_inv_apply,
  ModuleCat.MonoidalCategory.tensorHom_tmul]
-- 3. Clean up with change if tuple projections don't reduce
change ...
-- 4. Unfold remaining component isos
simp only [innerIso, NatIso.ofComponents_hom_app, ...]
-- 5. Apply element-level lemmas
erw [component_lemma_1, component_lemma_2]
exact final_lemma
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

## Extensionality for tensor of free modules (coproducts)

When proving `f = g` for morphisms `f g : (∐ A) ⊗ (∐ B) ⟶ M` from a tensor product of coproducts in `ModuleCat`, you cannot directly apply `TensorProduct.ext` combined with `Sigma.hom_ext` cleanly. Instead, use the monoidal closed adjunction to curry out the tensor product:

```lean
-- Curry the tensor to extract `b : B` via Sigma.hom_ext on the right
apply Equiv.injective ((ihom.adjunction (∐ fun _ : B => Rmod R)).homEquiv _ M)
apply CategoryTheory.Limits.Sigma.hom_ext
intro b

-- Uncurry and simplify to expose the tensor structure
apply Equiv.injective ((ihom.adjunction (∐ fun _ : B => Rmod R)).homEquiv _ M).symm
simp only [Adjunction.homEquiv_naturality_left_symm, Equiv.symm_apply_apply]

-- Compose out the right unitor and extract `a : A` via Sigma.hom_ext on the left
rw [← cancel_epi (ρ_ _).inv]
apply CategoryTheory.Limits.Sigma.hom_ext
intro a

-- Reassociate the tensored morphism and repackage `(Sigma.ι a ▷ _) ≫ (_ ◁ Sigma.ι b)`
simp only [Category.assoc]
rw [CategoryTheory.MonoidalCategory.rightUnitor_inv_naturality_assoc (Sigma.ι _ a)]
have hf : (ρ_ _).inv ≫ (Sigma.ι _ a ▷ 𝟙_ _) ≫ (tensorLeft _).map (Sigma.ι _ b) ≫ f =
          (ρ_ _).inv ≫ (Sigma.ι _ a ⊗ₘ Sigma.ι _ b) ≫ f := by
  change (ρ_ _).inv ≫ (Sigma.ι _ a ⊗ₘ Sigma.ι _ b) ≫ f = _
  rfl
```
This reduces the goal to matching `(Sigma.ι a ⊗ₘ Sigma.ι b) ≫ f`, allowing you to apply hypotheses directly.

## Pitfall: `ConcreteCategory.hom` vs `ModuleCat.Hom.hom`

These are **definitionally equal** but `simp` cannot match across them. Many Mathlib lemmas (especially monoidal category ones) state results using `ConcreteCategory.hom`, while our goals have `ModuleCat.Hom.hom`.

**Symptom**: `simp [tensorHom_tmul]` says "made no progress" even though the goal visually matches.

**Fix**: Use `erw` instead of `simp`/`rw` for these lemmas:
```lean
erw [ModuleCat.MonoidalCategory.tensorHom_tmul]
erw [ModuleCat.MonoidalCategory.leftUnitor_inv_apply]
```
Or use `change` to rewrite the goal to use `ModuleCat.Hom.hom` explicitly before `simp`.

## Pitfall: Product Tuples Don't Auto-Reduce

`(1 : R × R).1` does NOT automatically reduce to `(1 : R)`. This appears when `tensorHom` distributes over a product.

**Fix**: Use `change` to manually specify the cleaned-up form:
```lean
change (ModuleCat.Hom.hom (f.hom))
  ((ModuleCat.Hom.hom g) (1 : R) ⊗ₜ[R] (ModuleCat.Hom.hom h) (1 : R)) = _
```

## Key Monoidal Category Simp Lemmas

| Lemma | Reduces |
|-------|---------|
| `MonoidalCategory.tensorIso_hom` | `(A ≪⊗≫ B).hom` → `A.hom ⊗ₘ B.hom` |
| `MonoidalCategory.tensor_map` | `tensor.map f` → `tensorHom f.1 f.2` |
| `ModuleCat.MonoidalCategory.tensorHom_tmul` | `(f ⊗ₘ g)(a ⊗ₜ b)` → `f(a) ⊗ₜ g(b)` (needs `erw`) |
| `ModuleCat.MonoidalCategory.leftUnitor_inv_apply` | `(λ_ M).inv m` → `1 ⊗ₜ m` (needs `erw`) |

## Correct Simp Lemma Names (Common Mistakes)

| Wrong | Correct |
|-------|---------|
| `whiskerLeft_app` | `Functor.whiskerLeft_app` |
| `whiskerRight_app` | `Functor.whiskerRight_app` |
| `NatTrans.prod_app` | `NatTrans.prod_app_fst` / `NatTrans.prod_app_snd` |
| `tensorIso` | `MonoidalCategory.tensorIso` (full namespace needed) |

## Key monoidal functor lemmas

- `MonoidalCategory.tensorHom_comp_tensorHom f₁ f₂ g₁ g₂` — `(f₁ ⊗ₘ f₂) ≫ (g₁ ⊗ₘ g₂) = (f₁ ≫ g₁) ⊗ₘ (f₂ ≫ g₂)`. In `MonoidalCategory` namespace (need `open MonoidalCategory` or qualify).
- `Functor.Monoidal.μNatIso F` — natural iso `(F.prod F ⋙ tensor D) ≅ (tensor C ⋙ F)` for monoidal functor `F`. Naturality gives `(F.map f ⊗ₘ F.map g) ≫ μ = μ ≫ F.map (tensor.map (f, g))`.
- `Functor.Monoidal.μNatIso_hom_app F (X, Y)` — `μNatIso.hom.app (X, Y) = μ X Y`.
- `ModuleCat.instMonoidalFree R` — `(ModuleCat.free R).Monoidal` instance. Makes `μ` available.
- `freeTensorProductIso.hom = Functor.LaxMonoidal.μ (ModuleCat.free R) A B` by `rfl`.
