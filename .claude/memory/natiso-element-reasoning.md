# NatIso Construction & Element-Level Reasoning

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

## `ConcreteCategory.hom` vs `ModuleCat.Hom.hom`

These are **definitionally equal** but `simp` cannot match across them. Many Mathlib lemmas (especially monoidal category ones) state results using `ConcreteCategory.hom`, while our goals have `ModuleCat.Hom.hom`.

**Symptom**: `simp [tensorHom_tmul]` says "made no progress" even though the goal visually matches.

**Fix**: Use `erw` instead of `simp`/`rw` for these lemmas:
```lean
erw [ModuleCat.MonoidalCategory.tensorHom_tmul]
erw [ModuleCat.MonoidalCategory.leftUnitor_inv_apply]
```

Or use `change` to rewrite the goal to use `ModuleCat.Hom.hom` explicitly before `simp`.

## Product Tuples Don't Auto-Reduce

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
