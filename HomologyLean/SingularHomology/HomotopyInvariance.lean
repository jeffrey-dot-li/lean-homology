/-
  Homotopy Invariance of singular homology — Cross Product approach.

  Homotopic maps f, g : X → Y induce equal maps on singular homology:
    H_n(f) = H_n(g) : H_n(X; R) → H_n(Y; R)

  The proof uses the Eilenberg-Zilber cross product:
  1. Define the cross product × : C_p(X;R) ⊗ C_q(Y;R) → C_{p+q}(X×Y;R)
     as a signed sum over (p,q)-shuffles.
  2. Show × is natural, satisfies the Leibniz rule (chain map condition),
     and is normalized on 0-simplices.
  3. Construct a chain homotopy between C_*(f) and C_*(g) using the
     cross product with the unit interval.
-/
import Mathlib.AlgebraicTopology.SingularHomology.Basic
import Mathlib.Topology.Homotopy.Basic
import Mathlib.Algebra.Homology.Homotopy
import Mathlib.Topology.UnitInterval
import Mathlib.CategoryTheory.Monoidal.Category
import Mathlib.CategoryTheory.Monoidal.Preadditive
import Mathlib.CategoryTheory.Monoidal.Linear
import HomologyLean.CategoryTheory.SubTensorHom
import HomologyLean.SingularHomology.HomotopyMap
import Mathlib.CategoryTheory.Monoidal.Closed.Basic
import Mathlib.CategoryTheory.Monoidal.Limits.Preserves
import Mathlib.CategoryTheory.Monoidal.Mon_
import Mathlib.CategoryTheory.Monoidal.Types.Coyoneda
import Mathlib.GroupTheory.Perm.Sign
import Mathlib.Topology.Category.TopCat.Limits.Products
import HomologyLean.SingularHomology.Shuffle
import HomologyLean.SingularHomology.SumInvolution
import HomologyLean.SingularHomology.Representable
import Mathlib.Algebra.Homology.Monoidal

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicTopology unitInterval
open scoped MonoidalCategory
open Representable

universe u v

variable {C : Type u} [Category.{v} C] [HasCoproducts C] [Preadditive C] [CategoryWithHomology C]
   [MonoidalCategory C] [SymmetricCategory C] [MonoidalPreadditive C] [MonoidalClosed C]
   [HasForget.{v} C] [MonoidalUnitorRepresentable (C := C)]
   [(forget C).IsRightAdjoint] [(forget C).leftAdjoint.Monoidal]
   [(forget C).LaxMonoidal] [(Adjunction.ofIsRightAdjoint (forget C)).IsMonoidal]
   -- `forgetIso : forget C ≅ Hom(𝟙_ C, -)` is a monoidal natural iso, i.e. it intertwines
   -- `μ (forget C)` with `μ Hom(𝟙_ C, -)`. For ModuleCat R, this says the pure tensor map
   -- `M × N → M ⊗_R N` is compatible with `Hom(R, -)`'s monoidal structure `(f,g) ↦ (λ_ R).inv ≫ (f ⊗ g)`.
   [NatTrans.IsMonoidal (MonoidalUnitorRepresentable.forgetIso (C := C)).hom]
   [MonoidalLinear ℤ C]



namespace HomologyLean.SingularHomology

-- All constructions use the monoidal unit 𝟙_ C as the coefficient object.
-- For ModuleCat R, this is R itself (the ring as a module over itself).

/-! ### Abbreviations -/

/-- The free functor left adjoint to `forget C`. -/
abbrev Free : Type v ⥤ C := (forget C).leftAdjoint

/-- The standard topological `p`-simplex. -/
abbrev stdSimplex (p : ℕ) : TopCat.{v} :=
  SimplexCategory.toTop.obj (SimplexCategory.mk p)

/-!
Convenience notation for the standard simplex:
- `Δ[p]` (no whitespace ambiguity).
-/
notation "Δ[" p "]" => stdSimplex p
abbrev SCF (C : Type u) [Category.{v} C] [HasCoproducts C] [Preadditive C]
    [MonoidalCategory C] : TopCat ⥤ ChainComplex C ℕ :=
  (singularChainComplexFunctor C).obj (𝟙_ C)

/-- The singular chain complex of X with coefficients in 𝟙_ C. -/
abbrev singChain (C : Type u) [Category.{v} C] [HasCoproducts C] [Preadditive C]
    [MonoidalCategory C] (X : TopCat.{v}) : ChainComplex C ℕ :=
  (SCF C).obj X

/-- A singular n-simplex in X: an n-simplex of the singular simplicial set.
Definitionally `ULift (SimplexCategory.toTop.obj [n] ⟶ X)`. -/
abbrev SingularSimplex (X : TopCat.{v}) (n : ℕ) :=
  (TopCat.toSSet.obj X).obj (Opposite.op (SimplexCategory.mk n))


/-- Equivalence between singular `n`-simplices in `X` and morphisms `Δ[n] ⟶ X`.

This is essentially just removing the `ULift` wrapper in the definition of `TopCat.toSSet`. -/
noncomputable abbrev singularSimplexEquivΔ (X : TopCat.{v}) (n : ℕ) :
    SingularSimplex X n ≃ (Δ[n] ⟶ X) := by
  classical
  -- `TopCat.toSSet` is a restricted (ULift-)Yoneda construction, so the `n`-simplices are
  -- definitionally `ULift (Δ[n] ⟶ X)`.
  simpa [SingularSimplex, TopCat.toSSet, stdSimplex] using
    (Equiv.ulift : ULift (Δ[n] ⟶ X) ≃ (Δ[n] ⟶ X))

@[simp] lemma singularSimplexEquivΔ_apply {X : TopCat.{v}} {n : ℕ} (s : SingularSimplex X n) :
    (singularSimplexEquivΔ (X := X) n) s = s.down := by
  rfl

@[simp] lemma singularSimplexEquivΔ_symm_apply {X : TopCat.{v}} {n : ℕ} (f : Δ[n] ⟶ X) :
    (singularSimplexEquivΔ (X := X) n).symm f = ULift.up f := by
  rfl

/-- Convenience constructor: turn a map `Δ[n] ⟶ X` into the corresponding `SingularSimplex X n`. -/
noncomputable abbrev SingularSimplex.ofΔ {X : TopCat.{v}} {n : ℕ} (f : Δ[n] ⟶ X) :
    SingularSimplex X n :=
  (singularSimplexEquivΔ (X := X) n).symm f

@[simp] lemma SingularSimplex.ofΔ_down {X : TopCat.{v}} {n : ℕ} (f : Δ[n] ⟶ X) :
    (SingularSimplex.ofΔ (X := X) (n := n) f).down = f := by
  -- `SingularSimplex.ofΔ` is definitionally `ULift.up f`.
  rfl

notation "⟪" f "⟫ₛ" => SingularSimplex.ofΔ f

/-- The `n`-chains of `X` are the coproduct of copies of `𝟙_ C` indexed by maps `Δ[n] ⟶ X`. -/
noncomputable def singChain_X_iso_sigma (X : TopCat.{v}) (n : ℕ) :
    (singChain C X).X n ≅ (∐ fun _f : (Δ[n] ⟶ X) => 𝟙_ C) := by
  classical
  -- The chain group is definitionally a coproduct indexed by `SingularSimplex X n`;
  -- we reindex it using `singularSimplexEquivΔ`.
  change (∐ fun _s : SingularSimplex X n => 𝟙_ C) ≅ (∐ fun _f : (Δ[n] ⟶ X) => 𝟙_ C)
  exact
    Sigma.whiskerEquiv (C := C)
      (f := fun _s : SingularSimplex X n => 𝟙_ C)
      (g := fun _f : (Δ[n] ⟶ X) => 𝟙_ C)
      (singularSimplexEquivΔ (X := X) n)
      (fun _ => Iso.refl (𝟙_ C))

/-- Functor `TopCat ⥤ Type` sending `X` to its `p`-simplices (`SingularSimplex X p`). -/
noncomputable def singularSimplexFunctor (p : ℕ) : TopCat.{v} ⥤ Type v where
  obj X := SingularSimplex X p
  map {X X'} f s := ⟪s.down ≫ f⟫ₛ
  map_id X := by funext s; cases s; rfl
  map_comp {X Y Z} f g := by funext s; cases s; simp [Category.assoc]

/-- The degreewise chain group functor `SCF C ⋙ eval p` is naturally isomorphic to
`singularSimplexFunctor p ⋙ Limits.sigmaConst.obj (𝟙_ C)`.

Both send `X` to `∐ (fun _ : SingularSimplex X p => 𝟙_ C)` and push forward simplices
along continuous maps, but are constructed through different code paths
(`singularChainComplexFunctor` vs `Sigma.map'`). -/
noncomputable def chainGroupIsoCoprodFree (p : ℕ) :
    SCF C ⋙ HomologicalComplex.eval C (ComplexShape.down ℕ) p ≅
      singularSimplexFunctor p ⋙ Limits.sigmaConst.obj (𝟙_ C) :=
  NatIso.ofComponents
    (fun X => Iso.refl _)
    (fun {X Y} f => by
      dsimp
      simp only [Category.comp_id, Category.id_comp]
      dsimp [SCF, singularChainComplexFunctor, SSet.singularChainComplexFunctor]
      apply CategoryTheory.Limits.Sigma.hom_ext
      intro a
      simp only [CategoryTheory.Limits.Sigma.ι_comp_map', Category.id_comp]
      congr 1
    )

/-- The degree-`p` chain group `(singChain C X).X p` is naturally isomorphic to
`Free.obj (SingularSimplex X p)`, the free object on the set of `p`-simplices.

Composed from `chainGroupIsoCoprodFree` (chain group ≅ coproduct-based free)
and `sigmaConstIsoFree` (sigmaConst-based free ≅ abstract free). -/
noncomputable def chainGroupIsoFree (p : ℕ) :
    SCF C ⋙ HomologicalComplex.eval C (ComplexShape.down ℕ) p ≅
      singularSimplexFunctor p ⋙ Free (C := C) :=
  chainGroupIsoCoprodFree p ≪≫ (singularSimplexFunctor p).isoWhiskerLeft sigmaConstIsoFree

/-- The coprojection (basis inclusion) for a singular simplex: given a singular
n-simplex `s` in `X`, produce the corresponding "basis element" morphism
`𝟙_ C ⟶ C_n(X; 𝟙_ C)` via the coproduct structure of the chain group.

The chain group `(singChain C X).X n` is definitionally `∐_{σ} 𝟙_ C` where
σ ranges over all singular n-simplices in X. -/
abbrev simplexCoprojection {X : TopCat.{v}} {n : ℕ}
    (s : SingularSimplex X n) : 𝟙_ C ⟶ (singChain C X).X n :=
  Sigma.ι (fun _ : SingularSimplex X n ↦ 𝟙_ C) s

/-- The product of two singular n-simplices: given `s : Δⁿ → X` and `t : Δⁿ → Y`,
form the n-simplex `(s, t) : Δⁿ → X × Y` via the categorical product. -/
def prodSimplex {X Y : TopCat.{v}} {n : ℕ}
    (s : SingularSimplex X n) (t : SingularSimplex Y n) :
    SingularSimplex (X ⨯ Y) n :=
  .up (prod.lift s.down t.down)

/-! ### Simplex-level cross product -/


/-!
### Shuffles as maps between standard simplices

Given a `(p,q)`-shuffle, we will later build the corresponding continuous map
\( \Delta^{p+q} \to \Delta^p \times \Delta^q \).
-/

/-- The map of standard simplices associated to a shuffle:
`Δ[p+q] ⟶ Δ[p] × Δ[q]`. -/
-- Index (p + q) →o (Index p × Index q)
def simplexProdMap {p q r : ℕ} (μ : Index (r) →o (Index p × Index q)) :
    Δ[r] ⟶ (Δ[p] ⨯ Δ[q]) :=
  prod.lift
    (SimplexCategory.toTop.map (SimplexCategory.Hom.mk (OrderHom.fst.comp μ)))
    (SimplexCategory.toTop.map (SimplexCategory.Hom.mk (OrderHom.snd.comp μ)))

@[simp]
lemma simplexProdMap_comp {p q r s : ℕ}
    (f : SimplexCategory.mk s ⟶ SimplexCategory.mk r)
    (μ : Index r →o (Index p × Index q)) :
    SimplexCategory.toTop.map f ≫ simplexProdMap μ =
      simplexProdMap (μ.comp f.toOrderHom) := by
  simp only [simplexProdMap]
  rw [prod.comp_lift]
  congr 1 <;> rw [← Functor.map_comp] <;> rfl

/-- The transport `h ▸ ULift.up f` through `TopCat.toSSet` unwraps to
`eqToHom _ ≫ f`: the cast on the ULift becomes precomposition with an identity-like map. -/
lemma cast_ulift_toSSet_down {p q n : ℕ} (h : p + q = n + 1)
    (X : TopCat.{v})
    (f : stdSimplex.{v} (p + q) ⟶ X) :
    (show (TopCat.toSSet.obj X).obj (Opposite.op (SimplexCategory.mk (n + 1))) from
      h ▸ (ULift.up f : (TopCat.toSSet.obj X).obj
        (Opposite.op (SimplexCategory.mk (p + q))))).down =
    eqToHom (congrArg (SimplexCategory.toTop.obj ∘ SimplexCategory.mk) h.symm) ≫ f := by
  generalize hm : n + 1 = m at h ⊢
  revert f
  rcases h
  intro f
  simp

/-- Moving `SimplicialObject.δ` through a cast and `simplexProdMap`:
the face map acts by precomposition (via `eqToHom` and the face `OrderHom`). -/
lemma δ_cast_simplexProdMap {p q n : ℕ} (h : p + q = n + 1)
    (μ : Index (p + q) →o (Index p × Index q))
    (i : Fin (n + 2)) :
    SimplicialObject.δ (TopCat.toSSet.obj (stdSimplex.{v} p ⨯ stdSimplex.{v} q)) i
      (h ▸ .up (simplexProdMap μ ≫
        prod.map (𝟙 (stdSimplex.{v} p)) (𝟙 (stdSimplex.{v} q)))) =
    .up (simplexProdMap (μ.comp
      (SimplexCategory.δ i ≫
        eqToHom (congrArg SimplexCategory.mk h.symm)).toOrderHom)) := by
  simp only [prod.map_id_id, Category.comp_id]
  apply ULift.ext
  dsimp only [SimplicialObject.δ]
  dsimp [TopCat.toSSet, Presheaf.restrictedULiftYoneda]
  -- LHS: toTop.map (δ i) ≫ (h ▸ ULift.up (simplexProdMap μ)).down
  -- Use cast_ulift_toSSet_down to rewrite the transport into eqToHom ≫ simplexProdMap μ
  rw [cast_ulift_toSSet_down h]
  -- Remaining: toTop.map (δ i) ≫ eqToHom _ ≫ simplexProdMap μ
  --          = simplexProdMap (μ.comp (δ i ≫ eqToHom _).toOrderHom)
  -- Both sides are TopCat morphisms; reduce to pointwise equality on the product
  -- eqToHom in TopCat = toTop.map (eqToHom in SimplexCategory)
  rw [show (eqToHom _ : stdSimplex.{v} (n + 1) ⟶ stdSimplex.{v} (p + q)) =
    SimplexCategory.toTop.map (eqToHom (congrArg SimplexCategory.mk h.symm))
    from (eqToHom_map SimplexCategory.toTop _).symm]
  -- toTop.map (eqToHom _) ≫ simplexProdMap μ = simplexProdMap (μ.comp (eqToHom _).toOrderHom)
  simp only [simplexProdMap_comp]
  -- The LHS still has an unfolded toTop.map (δ i); fold and apply simplexProdMap_comp again
  change SimplexCategory.toTop.map (SimplexCategory.δ i) ≫ _ = _
  rw [simplexProdMap_comp]
  congr 1

/-- Postcomposing `simplexProdMap μ` with `prod.map (toTop.map f) (𝟙 _)` yields another
`simplexProdMap` where `f` is applied to the first projection. -/
@[simp]
lemma simplexProdMap_comp_prod_map_toTop_left {p p' q r : ℕ}
    (μ : Index r →o (Index p × Index q))
    (f : SimplexCategory.mk p ⟶ SimplexCategory.mk p') :
    simplexProdMap μ ≫ prod.map (SimplexCategory.toTop.map f) (𝟙 _) =
    simplexProdMap (⟨fun i => (f.toOrderHom (μ i).1, (μ i).2),
      fun _ _ h => ⟨f.toOrderHom.monotone (μ.monotone h).1, (μ.monotone h).2⟩⟩ :
      Index r →o (Index p' × Index q)) := by
  simp only [simplexProdMap, prod.lift_map, Category.comp_id, ← Functor.map_comp]
  congr 1

/-- Postcomposing `simplexProdMap μ` with `prod.map (𝟙 _) (toTop.map g)` yields another
`simplexProdMap` where `g` is applied to the second projection. -/
@[simp]
lemma simplexProdMap_comp_prod_map_toTop_right {p q q' r : ℕ}
    (μ : Index r →o (Index p × Index q))
    (g : SimplexCategory.mk q ⟶ SimplexCategory.mk q') :
    simplexProdMap μ ≫ prod.map (𝟙 _) (SimplexCategory.toTop.map g) =
    simplexProdMap (⟨fun i => ((μ i).1, g.toOrderHom (μ i).2),
      fun _ _ h => ⟨(μ.monotone h).1, g.toOrderHom.monotone (μ.monotone h).2⟩⟩ :
      Index r →o (Index p × Index q')) := by
  simp only [simplexProdMap, prod.lift_map, Category.comp_id, ← Functor.map_comp]
  congr 1

/-- Postcomposing a `(p, q+1)`-shuffle simplex with `δⱼ × id` and wrapping in `⟪·⟫ₛ`
yields a singular simplex whose underlying map applies `δⱼ` to the first component
of the shuffle. -/
@[simp]
lemma ofΔ_simplexProdMap_comp_prod_map_toTop_left {p q : ℕ}
    (s : Shuffle p (q + 1)) (j : Fin (p + 2)) :
    (⟪simplexProdMap s.1 ≫
        prod.map (SimplexCategory.toTop.map (SimplexCategory.δ j))
          (𝟙 (stdSimplex (q + 1)))⟫ₛ : SingularSimplex (Δ[p + 1] ⨯ Δ[q + 1]) _) =
    ⟪simplexProdMap (⟨fun i => ((SimplexCategory.δ j).toOrderHom (s.1 i).1, (s.1 i).2),
      fun _ _ h => ⟨(SimplexCategory.δ j).toOrderHom.monotone (s.1.monotone h).1,
        (s.1.monotone h).2⟩⟩ :
      Index (p + q + 1) →o (Index (p + 1) × Index (q + 1)))⟫ₛ := by
  congr 1; exact simplexProdMap_comp_prod_map_toTop_left s.1 (SimplexCategory.δ j)

/-- Postcomposing a `(p+1, q)`-shuffle simplex with `id × δⱼ` and wrapping in `⟪·⟫ₛ`
yields a singular simplex whose underlying map applies `δⱼ` to the second component
of the shuffle. -/
@[simp]
lemma ofΔ_simplexProdMap_comp_prod_map_toTop_right {p q : ℕ}
    (s : Shuffle (p + 1) q) (j : Fin (q + 2)) :
    (⟪simplexProdMap s.1 ≫
        prod.map (𝟙 (stdSimplex (p + 1)))
          (SimplexCategory.toTop.map (SimplexCategory.δ j))⟫ₛ :
      SingularSimplex (Δ[p + 1] ⨯ Δ[q + 1]) _) =
    ⟪simplexProdMap (⟨fun i => ((s.1 i).1, (SimplexCategory.δ j).toOrderHom (s.1 i).2),
      fun _ _ h => ⟨(s.1.monotone h).1,
        (SimplexCategory.δ j).toOrderHom.monotone (s.1.monotone h).2⟩⟩ :
      Index ((p + 1) + q) →o (Index (p + 1) × Index (q + 1)))⟫ₛ := by
  congr 1; exact simplexProdMap_comp_prod_map_toTop_right s.1 (SimplexCategory.δ j)

abbrev shuffleStdSimplexMap {p q : ℕ} (μ : Shuffle p q) :
    Δ[p + q] ⟶ (Δ[p] ⨯ Δ[q]) := simplexProdMap μ.1



/-- Precomposing `insertLeftStep ν j` with `δ_{insertLeftIndex} ≫ eqToHom` gives the
same result as applying `ν` with `succAbove j` on fst.  This bridges the categorical
`δ ≫ eqToHom` composition with the `Fin`-level `insertLeftStep_face`. -/
private lemma insertLeftStep_comp_δ {p q : ℕ} (ν : Shuffle p q) (j : Fin (p + 2))
    (i : Fin (p + q + 1)) :
    (ν.insertLeftStep j).1
      ((SimplexCategory.δ (ν.insertLeftIndex j) ≫
        eqToHom (show SimplexCategory.mk (p + q + 1) = SimplexCategory.mk ((p + 1) + q)
          from by congr 1; omega)).toOrderHom i) =
    (j.succAbove (ν.1 i).1, (ν.1 i).2) := by
  have hface := Shuffle.insertLeftStep_face ν j i
  -- Bridge: the argument (δ t ≫ eqToHom _).toOrderHom i has the same Fin.val
  -- as ⟨t.val, _⟩.succAbove (i.cast _), so insertLeftStep gives the same result.
  suffices harg : ∀ (a b : Fin ((p + 1) + q + 1)), a.val = b.val →
      (ν.insertLeftStep j).1 a = (ν.insertLeftStep j).1 b from
    harg _ _ (by
      -- Unfold (δ t ≫ eqToHom _).toOrderHom to Fin.cast ∘ Fin.succAbove
      dsimp [SimplexCategory.δ, Fin.succAboveOrderEmb, SimplexCategory.comp_toOrderHom]
      simp only [SimplexCategory.eqToHom_toOrderHom]
      dsimp [Fin.castOrderIso]
      simp only [Fin.succAbove, Fin.lt_def, Fin.val_castSucc, Fin.val_cast]
      split_ifs <;>
        simp_all [Fin.val_castSucc, Fin.val_succ, Fin.val_cast]) |>.trans hface
  exact fun _ _ h => congr_arg _ (Fin.ext h)

/-- Symmetric: precomposing `insertRightStep ν k` with `δ_{insertRightIndex} ≫ eqToHom`
gives `ν` with `succAbove k` on snd. -/
private lemma insertRightStep_comp_δ {p q : ℕ} (ν : Shuffle p q) (k : Fin (q + 2))
    (i : Fin (p + q + 1)) :
    (ν.insertRightStep k).1
      ((SimplexCategory.δ (ν.insertRightIndex k) ≫
        eqToHom (show SimplexCategory.mk (p + q + 1) = SimplexCategory.mk (p + (q + 1))
          from by congr 1)).toOrderHom i) =
    ((ν.1 i).1, k.succAbove (ν.1 i).2) := by
  have hface := Shuffle.insertRightStep_face ν k i
  suffices harg : ∀ (a b : Fin (p + (q + 1) + 1)), a.val = b.val →
      (ν.insertRightStep k).1 a = (ν.insertRightStep k).1 b from
    harg _ _ (by
      dsimp [SimplexCategory.δ, Fin.succAboveOrderEmb, SimplexCategory.comp_toOrderHom]
      rfl) |>.trans hface
  exact fun _ _ h => congr_arg _ (Fin.ext h)

/-- Face-shuffle factorization (left insertion):
Inserting a left step into a `(p, q)`-shuffle `ν` at face index `j` and then
removing the inserted vertex via `δ` recovers `ν ≫ prod.map (δⱼ) id`.

That is: `δ_{insertLeftIndex ν j} ≫ shuffleStdSimplexMap (insertLeftStep ν j)
         = shuffleStdSimplexMap ν ≫ (δⱼ × id)`.

In the boundary formula this is used with `q := q' + 1` to match the first
RHS sum. -/
lemma shuffleStdSimplexMap_insertLeft_face {p q : ℕ}
    (ν : Shuffle p q) (j : Fin (p + 2)) :
    SimplexCategory.toTop.map (SimplexCategory.δ (n := p + q)
      (Shuffle.insertLeftIndex ν j)) ≫
      eqToHom (by simp [show p + q + 1 = (p + 1) + q from by omega]) ≫
      shuffleStdSimplexMap (p := p + 1) (q := q) (Shuffle.insertLeftStep ν j) =
    shuffleStdSimplexMap (p := p) (q := q) ν ≫
      prod.map
        (SimplexCategory.toTop.map (SimplexCategory.δ j))
        (𝟙 _) := by
  -- Fold eqToHom from TopCat into SimplexCategory, then reduce to OrderHom equality
  simp only [← Category.assoc] at *
  rw [← show SimplexCategory.toTop.map (eqToHom _) = eqToHom _ from eqToHom_map _ _]
  rw [← Functor.map_comp]
  rw [simplexProdMap_comp, simplexProdMap_comp_prod_map_toTop_left]
  -- OrderHom equality: use insertLeftStep_comp_δ pointwise
  congr 1; ext : 1; funext i
  simp only [OrderHom.comp_coe, Function.comp_apply, OrderHom.coe_mk]
  exact insertLeftStep_comp_δ ν j i

/-- Face-shuffle factorization (right insertion):
`δ_{insertRightIndex ν k} ≫ shuffleStdSimplexMap (insertRightStep ν k)
 = shuffleStdSimplexMap ν ≫ (id × δₖ)`.

In the boundary formula this is used with `p := p' + 1` to match the second
RHS sum. -/
lemma shuffleStdSimplexMap_insertRight_face {p q : ℕ}
    (ν : Shuffle p q) (k : Fin (q + 2)) :
    SimplexCategory.toTop.map (SimplexCategory.δ (n := p + q)
      (Shuffle.insertRightIndex ν k)) ≫
      eqToHom (by simp [show p + q + 1 = p + (q + 1) from by omega]) ≫
      shuffleStdSimplexMap (p := p) (q := q + 1) (Shuffle.insertRightStep ν k) =
    shuffleStdSimplexMap (p := p) (q := q) ν ≫
      prod.map
        (𝟙 _)
        (SimplexCategory.toTop.map (SimplexCategory.δ k)) := by
  simp only [← Category.assoc] at *
  rw [← show SimplexCategory.toTop.map (eqToHom _) = eqToHom _ from eqToHom_map _ _]
  · rw [← Functor.map_comp, simplexProdMap_comp, simplexProdMap_comp_prod_map_toTop_right]
    congr 1; ext : 1; funext i
    simp only [OrderHom.comp_coe, Function.comp_apply, OrderHom.coe_mk]
    exact insertRightStep_comp_δ ν k i

attribute [simp] CategoryTheory.yoneda

/-- Given a p-simplex σ in X, a q-simplex τ in Y, and a (p,q)-shuffle μ,
produce an n-simplex in X × Y (where n = p + q) by combining σ and τ according to μ.

Geometrically: μ determines a maximal simplex in the standard triangulation
of Δ^p × Δ^q; this maps it into X × Y using σ on the first factor and τ
on the second.

The `n` parameter with proof `hn : n = p + q` allows callers to work at a
chosen index without `eqToHom` casts. The `subst` is confined here at the leaf. -/
def shuffleSimplex {X Y : TopCat.{v}} {p q n : ℕ}
    (s : SingularSimplex X p) (t : SingularSimplex Y q) (μ : Shuffle p q)
    (hn : n = p + q := by omega) :
    SingularSimplex (X ⨯ Y) n := by
  subst hn
  unfold SingularSimplex
  refine .up ?_
  simp only [yoneda, Functor.op_obj, SimplexCategory.toTop_obj, SimplexCategory.len_mk]
  change Δ[p + q] ⟶ _
  refine shuffleStdSimplexMap (p := p) (q := q) μ ≫ ?_
  apply prod.map s.down t.down

/-- The universal simplex-level cross product on the standard simplices.

The `n` parameter with proof `hn : n = p + q` lets downstream code (especially
the Leibniz rule) work at a chosen chain-complex index without `eqToHom` casts. -/
def universalSimplexCrossProduct (p q : ℕ) {n : ℕ} (hn : n = p + q := by omega) :
    𝟙_ C ⟶ (singChain C (Δ[p] ⨯ Δ[q])).X n :=
  ∑ μ : Shuffle p q, μ.sign • simplexCoprojection
    (shuffleSimplex ⟪𝟙 stdSimplex.{v} p ⟫ₛ ⟪𝟙 stdSimplex.{v} q⟫ₛ μ hn)

/-- The simplex-level cross product: the signed formal sum over all shuffles.

Given a p-simplex s in X and a q-simplex t in Y, produce a morphism
`𝟙_ C ⟶ C_n(X × Y; 𝟙_ C)` (where `n = p + q`) as the signed sum
`∑_μ sign(μ) · ι(shuffleSimplex s t μ)` where ι denotes the coprojection
into the free module.

The `n` parameter with proof `hn : n = p + q` avoids `eqToHom` casts
when `p + q` is not definitionally equal to the desired index. -/
def simplexCrossProduct {X Y : TopCat.{v}} {p q n : ℕ}
    (s : SingularSimplex X p) (t : SingularSimplex Y q)
    (hn : n = p + q := by omega) :
    𝟙_ C ⟶ ((singChain C (X ⨯ Y)).X n) :=
  universalSimplexCrossProduct p q hn ≫
    ((SCF C).map (prod.map s.down t.down)).f n

/-- Variant of `simplexCrossProduct` as an explicit set-level map:
takes a pair `(s, t)` of singular simplices and returns an element of
`Hom(𝟙_ C, C_n(X × Y; 𝟙_ C))` (where `n = p + q`). -/
def simplexCrossProduct' {X Y : TopCat.{v}} {p q n : ℕ}
    (hn : n = p + q := by omega) :
    SingularSimplex X p × SingularSimplex Y q →
    Hom[𝟙_ C |-].obj ((singChain C (X ⨯ Y)).X n) :=
  fun ⟨s, t⟩ => simplexCrossProduct s t hn

/-- Precomposition by an iso gives an equivalence on hom-sets (contravariant). -/
noncomputable def precompEquiv {D : Type*} [Category D] {X Y : D} (α : X ≅ Y) (Z : D) :
    (Y ⟶ Z) ≃ (X ⟶ Z) where
  toFun f := α.hom ≫ f
  invFun g := α.inv ≫ g
  left_inv f := by simp
  right_inv g := by simp

/-- The hom-set equivalence for tensors of free objects: morphisms
`Free.obj A ⊗ Free.obj B ⟶ M` in `C` correspond bijectively to set-level maps
`A × B → Hom(𝟙_ C, M)`.

Composed from three equivalences:
1. `(Free A ⊗ Free B ⟶ M) ≃ (Free (A × B) ⟶ M)` via `μIso` (monoidal structure of Free)
2. `(Free (A × B) ⟶ M) ≃ (A × B → forget C .obj M)` via the free-forget adjunction `homEquiv`
3. `(A × B → forget C .obj M) ≃ (A × B → Hom(𝟙_ C, M))` via `forgetIso` -/
noncomputable def freeTensorHomEquiv (A B : Type v) (M : C) :
    (Free.obj A ⊗ Free.obj B ⟶ M) ≃
    (A × B → Hom[𝟙_ C |-].obj M) :=
  -- (Free A ⊗ Free B ⟶ M) ≃ (Free (A × B) ⟶ M) via μIso
  precompEquiv (Functor.Monoidal.μIso Free A B).symm M |>.trans
  -- (Free (A × B) ⟶ M) ≃ (A × B → (forget C).obj M) via adjunction homEquiv
  ((Adjunction.ofIsRightAdjoint (forget C)).homEquiv (A × B) M) |>.trans
  -- (A × B → (forget C).obj M) ≃ (A × B → Hom(𝟙_ C, M)) via forgetIso
  (Equiv.arrowCongr (Equiv.refl _)
    ((MonoidalUnitorRepresentable.forgetIso (C := C)).app M).toEquiv)

/-- The hom-set equivalence for the tensor of chain groups: morphisms
`C_p(X) ⊗ C_q(Y) ⟶ M` in `C` correspond bijectively to set-level maps
`SingularSimplex X p × SingularSimplex Y q → Hom(𝟙_ C, M)`.

Obtained by transporting `freeTensorHomEquiv` along `chainGroupIsoFree`,
which identifies `C_p(X) ≅ Free(SingularSimplex X p)`. -/
noncomputable def chainTensorHomEquiv {X Y : TopCat.{v}} {p q : ℕ} (M : C) :
    ((singChain C X).X p ⊗ (singChain C Y).X q ⟶ M) ≃
    (SingularSimplex X p × SingularSimplex Y q →
      Hom[𝟙_ C |-].obj M) :=
  -- (C_p(X) ⊗ C_q(Y) ⟶ M) ≃ (Free(Sing_p X) ⊗ Free(Sing_q Y) ⟶ M)
  precompEquiv (MonoidalCategory.tensorIso ((chainGroupIsoFree (C := C) p).app X)
    ((chainGroupIsoFree (C := C) q).app Y)).symm M |>.trans
  -- (Free(Sing_p X) ⊗ Free(Sing_q Y) ⟶ M) ≃ (Sing_p X × Sing_q Y → Hom(𝟙_ C, M))
  (freeTensorHomEquiv (SingularSimplex X p) (SingularSimplex Y q) M)

/-- The cross product on chain groups:
`C_p(X; 𝟙_ C) ⊗ C_q(Y; 𝟙_ C) ⟶ C_n(X × Y; 𝟙_ C)` (where `n = p + q`).

Defined by lifting the simplex-level cross product `simplexCrossProduct'` via
`chainTensorHomEquiv`. -/
def chainCrossProduct {X Y : TopCat.{v}} {p q n : ℕ}
    (hn : n = p + q := by omega) :
    (singChain C X).X p ⊗ (singChain C Y).X q ⟶
    (singChain C (X ⨯ Y)).X n :=
  (chainTensorHomEquiv _).symm (simplexCrossProduct' hn)

/-- Applying `chainTensorHomEquiv` to `chainCrossProduct` recovers
`simplexCrossProduct'`: the chain-level cross product is the unique lift of
the simplex-level cross product. -/
lemma chainCrossProduct.spec {X Y : TopCat.{v}} {p q n : ℕ}
    (hn : n = p + q := by omega) :
    chainTensorHomEquiv (X := X) (Y := Y) _
      (chainCrossProduct (C := C) hn) = simplexCrossProduct' hn :=
  (chainTensorHomEquiv _).right_inv (simplexCrossProduct' hn)

/-- Two morphisms out of `C_p(X) ⊗ C_q(Y)` are equal iff they agree on all pairs
of simplex coprojections. This is the tensor analogue of `Sigma.hom_ext`. -/
lemma chainCrossProduct.ext {X Y : TopCat.{v}} {p q : ℕ} {M : C}
    {f g : (singChain C X).X p ⊗ (singChain C Y).X q ⟶ M}
    (h : chainTensorHomEquiv M f = chainTensorHomEquiv M g) : f = g :=
  (chainTensorHomEquiv M).injective h

/-- The "free generator" morphism: for `a : A`, the morphism `𝟙_ C ⟶ Free.obj A`
obtained by applying `forgetIso` to the adjunction unit at `a`.
Represents the inclusion of the generator `a` into the free object. -/
private noncomputable abbrev freeGen {A : Type v} (a : A) : 𝟙_ C ⟶ Free.obj A :=
  (MonoidalUnitorRepresentable.forgetIso (C := C)).hom.app (Free.obj A)
    ((Adjunction.ofIsRightAdjoint (forget C)).unit.app A a)

/-- The free generator at `s`, mapped through `(chainGroupIsoFree p).inv.app X`,
equals the coproduct injection `simplexCoprojection s`. -/
private lemma freeGen_chainGroupIsoFree {X : TopCat.{v}} {p : ℕ}
    (s : SingularSimplex X p) :
    freeGen (C := C) s ≫ (chainGroupIsoFree (C := C) p).inv.app X =
    simplexCoprojection s := by
  simp only [chainGroupIsoFree, Iso.trans_inv, NatTrans.comp_app, Functor.isoWhiskerLeft_inv]
  simp only [chainGroupIsoCoprodFree, NatIso.ofComponents_inv_app, Iso.refl_inv]
  erw [Category.comp_id]
  simp only [Functor.whiskerLeft_app]
  simp only [sigmaConstIsoFree, Adjunction.leftAdjointUniq_inv_app]
  dsimp only [freeGen]
  -- Use forgetIso naturality: forgetIso.hom.app _ x ≫ f = forgetIso.hom.app _ ((forget C).map f x)
  set φ := ((Adjunction.ofIsRightAdjoint (forget C)).leftAdjointUniq
      ((sigmaConstAdj (𝟙_ C)).ofNatIsoRight MonoidalUnitorRepresentable.forgetIso.symm)).hom.app
      ((singularSimplexFunctor p).obj X)
  have hnat := congr_fun (MonoidalUnitorRepresentable.forgetIso (C := C) |>.hom.naturality φ)
    ((Adjunction.ofIsRightAdjoint (forget C)).unit.app (SingularSimplex X p) s)
  simp only [types_comp_apply] at hnat
  dsimp [coyoneda] at hnat
  erw [← hnat]; clear hnat
  -- (forget C).map φ (adj_free.unit.app A s) = (adj_free.unit ≫ (forget C).whiskerRight φ).app A s
  -- which by unit_leftAdjointUniq_hom_app equals adj2.unit.app A s
  change MonoidalUnitorRepresentable.forgetIso.hom.app _ (((Adjunction.ofIsRightAdjoint (forget C)).unit.app _ ≫ (forget C).map φ) s) = _
  rw [Adjunction.unit_leftAdjointUniq_hom_app]
  -- Unfold adj2.unit = (sigmaConstAdj.ofNatIsoRight forgetIso.symm).unit
  simp only [Adjunction.ofNatIsoRight, Adjunction.mkOfHomEquiv_unit_app]
  simp only [Equiv.trans_apply, Adjunction.equivHomsetRightOfNatIso]
  dsimp only [Equiv.coe_fn_mk]
  rw [Adjunction.homEquiv_unit]
  simp only [Functor.map_id, types_id_apply, types_comp_apply]
  -- Cancel coyoneda.map (𝟙 _) and forgetIso.hom ∘ forgetIso.symm.hom
  dsimp [coyoneda]
  simp only [Category.comp_id]
  change (MonoidalUnitorRepresentable.forgetIso (C := C)).hom.app _ ((MonoidalUnitorRepresentable.forgetIso (C := C)).inv.app _ ((sigmaConstAdj (𝟙_ C)).unit.app _ s)) = _
  simp only [← types_comp_apply (MonoidalUnitorRepresentable.forgetIso.inv.app _) (MonoidalUnitorRepresentable.forgetIso.hom.app _)]
  simp only [← NatTrans.comp_app, Iso.inv_hom_id, NatTrans.id_app, types_id_apply]
  rfl

/-- `OplaxMonoidal.δ` sends the free generator at `(a, b)` to the left unitor inverse
composed with the tensor of free generators at `a` and `b`. -/
private lemma freeGen_δ (A B : Type v) (a : A) (b : B) :
    freeGen (C := C) (a, b) ≫ Functor.OplaxMonoidal.δ Free A B =
    (λ_ (𝟙_ C)).inv ≫ (freeGen (C := C) a ⊗ₘ freeGen (C := C) b) := by
  dsimp only [freeGen]
  -- Use forgetIso naturality to absorb ≫ δ
  set δ := Functor.OplaxMonoidal.δ (Free (C := C)) A B
  have hnat := congr_fun (MonoidalUnitorRepresentable.forgetIso (C := C) |>.hom.naturality δ)
    ((Adjunction.ofIsRightAdjoint (forget C)).unit.app (A × B) (a, b))
  simp only [types_comp_apply] at hnat
  dsimp [coyoneda] at hnat
  erw [← hnat]; clear hnat
  -- Rewrite unit ≫ (forget C).map δ using IsMonoidal
  change MonoidalUnitorRepresentable.forgetIso.hom.app _ (((Adjunction.ofIsRightAdjoint (forget C)).unit.app _ ≫ (forget C).map δ) (a, b)) = _
  rw [Adjunction.unit_app_tensor_comp_map_δ]
  simp only [types_comp_apply]
  dsimp
  -- Goal: forgetIso.hom.app _ (μ (forget C) _ _ (unit a, unit b)) = (λ_ 𝟙_C).inv ≫ (freeGen a ⊗ₘ freeGen b)
  -- Use NatTrans.IsMonoidal.tensor: μ (forget C) ≫ forgetIso.hom.app _ = (forgetIso.hom.app _ ⊗ₘ forgetIso.hom.app _) ≫ μ Hom(𝟙_C, -)
  rw [← types_comp_apply (Functor.LaxMonoidal.μ (forget C) _ _)
    (MonoidalUnitorRepresentable.forgetIso.hom.app _),
    NatTrans.IsMonoidal.tensor (τ := MonoidalUnitorRepresentable.forgetIso.hom)]
  simp only [types_comp_apply]
  dsimp
  rfl

/-- Evaluating `chainTensorHomEquiv` on coprojection pairs: the forward map
sends `f` at `(s, t)` to `(λ_ (𝟙_ C)).inv ≫ (ι s ⊗ₘ ι t) ≫ f`. -/
lemma chainTensorHomEquiv_apply {X Y : TopCat.{v}} {p q : ℕ} {M : C}
    (f : (singChain C X).X p ⊗ (singChain C Y).X q ⟶ M)
    (s : SingularSimplex X p) (t : SingularSimplex Y q) :
    chainTensorHomEquiv M f (s, t) =
    (λ_ (𝟙_ C)).inv ≫
      MonoidalCategory.tensorHom (simplexCoprojection s) (simplexCoprojection t) ≫ f := by
  -- Unfold the composed equivalence to expose forgetIso, adj.homEquiv, μIso, chainGroupIsoFree
  simp only [chainTensorHomEquiv, freeTensorHomEquiv, precompEquiv, Equiv.trans_apply]
  change ((MonoidalUnitorRepresentable.forgetIso (C := C)).app M).hom
    (((Adjunction.ofIsRightAdjoint (forget C)).homEquiv _ M)
      ((Functor.Monoidal.μIso Free _ _).symm.hom ≫
        ((chainGroupIsoFree (C := C) p).app X ⊗ᵢ
          (chainGroupIsoFree (C := C) q).app Y).symm.hom ≫ f)
      (s, t)) =
    (λ_ (𝟙_ C)).inv ≫ (simplexCoprojection s ⊗ₘ simplexCoprojection t) ≫ f
  -- Reassociate and peel off f using naturality of homEquiv and forgetIso
  have hassoc : (Functor.Monoidal.μIso Free _ _).symm.hom ≫
      ((chainGroupIsoFree (C := C) p).app X ⊗ᵢ
        (chainGroupIsoFree (C := C) q).app Y).symm.hom ≫ f =
    ((Functor.Monoidal.μIso Free _ _).symm.hom ≫
      ((chainGroupIsoFree (C := C) p).app X ⊗ᵢ
        (chainGroupIsoFree (C := C) q).app Y).symm.hom) ≫ f :=
    (Category.assoc _ _ _).symm
  simp_rw [hassoc, Adjunction.homEquiv_naturality_right]
  simp only [types_comp_apply]
  -- Use forgetIso naturality to factor out ≫ f, then ≫ tensor_inv
  set y := (forget C).map ((chainGroupIsoFree p).app X ⊗ᵢ
      (chainGroupIsoFree q).app Y).symm.hom
    (((Adjunction.ofIsRightAdjoint (forget C)).homEquiv _ _)
      (Functor.Monoidal.μIso Free _ _).symm.hom (s, t))
  have hnat := congr_fun (MonoidalUnitorRepresentable.forgetIso (C := C) |>.hom.naturality f) y
  simp only [types_comp_apply] at hnat
  change (MonoidalUnitorRepresentable.forgetIso (C := C)).hom.app M ((forget C).map f y) =
    (λ_ (𝟙_ C)).inv ≫ (simplexCoprojection s ⊗ₘ simplexCoprojection t) ≫ f
  rw [hnat]; dsimp [coyoneda]; rw [← Category.assoc ((λ_ (𝟙_ C)).inv)]; congr 1
  -- Reduced to f-free goal:
  --   forgetIso.hom.app (C_p ⊗ C_q) y = (λ_ (𝟙_ C)).inv ≫ (ι s ⊗ₘ ι t)
  -- Use forgetIso naturality to absorb (forget C).map tensor_inv
  simp only [y]; clear y hnat hassoc f M
  have hnat2 := congr_fun ((MonoidalUnitorRepresentable.forgetIso (C := C)).hom.naturality
    ((chainGroupIsoFree (C := C) p).app X ⊗ᵢ
      (chainGroupIsoFree (C := C) q).app Y).symm.hom)
    (((Adjunction.ofIsRightAdjoint (forget C)).homEquiv _ _)
      (Functor.Monoidal.μIso Free _ _).symm.hom (s, t))
  simp only [types_comp_apply] at hnat2
  erw [hnat2]; dsimp [coyoneda]
  -- Goal: freeGen(s,t)-like ≫ δ ≫ (CGF.inv ⊗ₘ CGF.inv) = (λ_ 𝟙_C).inv ≫ (ι s ⊗ₘ ι t)
  -- Unfold adj.homEquiv to unit ≫ forget.map, then apply forgetIso naturality for δ
  rw [Adjunction.homEquiv_unit]
  simp only [types_comp_apply]
  have hnat3 := congr_fun ((MonoidalUnitorRepresentable.forgetIso (C := C)).hom.naturality
    (Functor.OplaxMonoidal.δ Free _ _))
    ((Adjunction.ofIsRightAdjoint (forget C)).unit.app _ (s, t))
  simp only [types_comp_apply] at hnat3
  erw [hnat3]; dsimp [coyoneda]
  -- Now: (freeGen(s,t) ≫ δ) ≫ (CGF.inv ⊗ₘ CGF.inv) = (λ_ 𝟙_C).inv ≫ (ι s ⊗ₘ ι t)
  rw [Category.assoc]
  simp only [types_tensorObj_def] at *
  rw [← Category.assoc, freeGen_δ, Category.assoc,
    MonoidalCategory.tensorHom_comp_tensorHom,
    freeGen_chainGroupIsoFree, freeGen_chainGroupIsoFree]

/-- On 0-simplices, `simplexCrossProduct x y` is just `simplexCoprojection (prodSimplex x y)`:
there is a unique (0,0)-shuffle with sign 1, so the shuffle sum collapses. -/
lemma simplexCrossProduct_zero_zero {X Y : TopCat.{v}}
    (x : SingularSimplex X 0) (y : SingularSimplex Y 0) :
    simplexCrossProduct (C := C) x y = simplexCoprojection (prodSimplex x y) := by
  simp only [simplexCrossProduct, universalSimplexCrossProduct, shuffleSimplex]
  rw [Fintype.sum_subsingleton _ default]
  have : (default : Shuffle 0 0).sign = 1 := by simp [Shuffle.sign, Shuffle.invCount]
  rw [this, one_smul]
  dsimp [simplexCoprojection, SCF, singularChainComplexFunctor, SSet.singularChainComplexFunctor]
  erw [CategoryTheory.Limits.Sigma.ι_comp_map']
  simp only [Category.id_comp]
  congr 1
  show ⟪(shuffleStdSimplexMap default ≫ prod.map ⟪𝟙 Δ[0]⟫ₛ.down ⟪𝟙 Δ[0]⟫ₛ.down) ≫
    prod.map x.down y.down⟫ₛ = prodSimplex x y
  have h1 : ⟪𝟙 Δ[0]⟫ₛ.down = 𝟙 Δ[0] := SingularSimplex.ofΔ_down _
  rw [h1, prod.map_id_id, Category.comp_id]
  simp only [ shuffleStdSimplexMap,
    SimplexCategory.hom_zero_zero, SimplexCategory.toTop.map_id,
     prod.lift_map, prodSimplex, simplexProdMap]
  simp


theorem crossProduct_normalized' {X Y : TopCat.{v}}
    (x : SingularSimplex X 0) (y : SingularSimplex Y 0) :
    MonoidalCategory.tensorHom (simplexCoprojection (C := C) x)
      (simplexCoprojection y) ≫ chainCrossProduct (C := C) =
    (λ_ (𝟙_ C)).hom ≫ simplexCoprojection (prodSimplex x y) := by
  rw [← Iso.inv_comp_eq (λ_ (𝟙_ C))]
  rw [← chainTensorHomEquiv_apply]
  rw [congrFun (chainCrossProduct.spec (C := C)) (x, y)]
  exact simplexCrossProduct_zero_zero x y

@[simp] lemma SimplexCategory.default_mk0_eq_id :
    (default : SimplexCategory.mk 0 ⟶ SimplexCategory.mk 0) = 𝟙 _ := by
  ext ⟨j, hj⟩; simp [default, SimplexCategory.Hom.toOrderHom]

@[simp] lemma SimplexCategory.δ_comp_default_mk1 (i : Fin 2) :
    SimplexCategory.δ i ≫ (default : SimplexCategory.mk 1 ⟶ SimplexCategory.mk 0) = 𝟙 _ := by
  ext ⟨j, hj⟩; simp [default, SimplexCategory.Hom.toOrderHom, SimplexCategory.δ]

lemma simplexCrossProduct_zero_right {X Y : TopCat.{v}} {n : ℕ}
    (s : SingularSimplex X n) (c : SingularSimplex Y 0) :
    simplexCrossProduct (C := C) s c =
    simplexCoprojection
      ⟪prod.lift s.down (SimplexCategory.toTop.map default ≫ c.down)⟫ₛ := by
  simp [simplexCrossProduct, universalSimplexCrossProduct, shuffleSimplex]
  have hd : (default : Shuffle n 0).sign = 1 := by
    dsimp [Shuffle.sign, Shuffle.invCount]
    have hz : (∑ r : Fin (n + 0), if ((default : Shuffle n 0).1 (Fin.castSucc r)).1 < ((default : Shuffle n 0).1 (Fin.succ r)).1 then ((default : Shuffle n 0).1 (Fin.castSucc r)).2.val else 0) = 0 := by
      apply Finset.sum_eq_zero
      intro i _
      split_ifs
      · rfl
      · rfl
    exact congrArg (fun x => (-1 : ℤ) ^ x) hz
  rw [hd]
  simp
  dsimp [simplexCoprojection, SCF, singularChainComplexFunctor, SSet.singularChainComplexFunctor]
  erw [CategoryTheory.Limits.Sigma.ι_comp_map']
  simp
  apply congrArg
  apply ULift.ext
  dsimp [TopCat.toSSet]
  apply CategoryTheory.Limits.prod.hom_ext
  ·
    have H : shuffleStdSimplexMap (p := n) (q := 0) default ≫ prod.fst = eqToHom (by rfl) := by
      dsimp [shuffleStdSimplexMap, simplexProdMap]
      rw [CategoryTheory.Limits.prod.lift_fst]
      ext ⟨⟨i, hi⟩⟩
      simp only [ConcreteCategory.id_apply]
      apply ULift.ext
      change stdSimplex.map _ ⟨i, hi⟩ = ⟨i, hi⟩
      convert stdSimplex.map_id_apply ⟨i, hi⟩
    erw [Category.assoc, CategoryTheory.Limits.prod.map_fst, ← Category.assoc, H]
    simp
  · erw [Category.assoc, CategoryTheory.Limits.prod.map_snd, ← Category.assoc]
    simp
    ext x
    have h_sub : Subsingleton ↑(Opposite.unop (SimplexCategory.toTop.op.obj (Opposite.op (SimplexCategory.mk 0)))) := by
      dsimp [SimplexCategory.toTop]
      constructor
      rintro ⟨⟨a, ha⟩⟩ ⟨⟨b, hb⟩⟩
      apply ULift.ext
      apply Subtype.ext
      funext i
      have hz : i = 0 := Fin.eq_zero i
      have h1 : a 0 = 1 := by simpa using ha.2
      have h2 : b 0 = 1 := by simpa using hb.2
      change a i = b i
      rw [hz, h1, h2]
    exact congrArg (ConcreteCategory.hom c.down) (Subsingleton.elim _ _)
/-- The snd projection of the unique `(0, n)`-shuffle is `eqToHom` (i.e., the identity
up to `0 + n = n`). Proved in `SimplexCategory` where `ext + omega` closes it. -/
private lemma snd_comp_default_shuffle_eq_eqToHom (n : ℕ) :
    (SimplexCategory.Hom.mk (OrderHom.snd.comp (default : Shuffle 0 n).1) :
      SimplexCategory.mk (0 + n) ⟶ SimplexCategory.mk n) =
    eqToHom (by change SimplexCategory.mk (0 + n) = SimplexCategory.mk n; congr 1; omega) := by
  apply SimplexCategory.Hom.ext
  ext ⟨i, hi⟩
  simp only [SimplexCategory.eqToHom_toOrderHom]
  dsimp [Fin.castOrderIso, SimplexCategory.Hom.toOrderHom, OrderHom.snd,
    default, Unique_Shuffle_0_n]

/-- For `p = 0`, the cross product of a `0`-simplex `c` in `X` with an `n`-simplex `s`
in `Y` reduces to a single product simplex `t ↦ (c(*), s(t))`.

There is a unique `(0, n)`-shuffle with sign `1`, so the shuffle sum collapses. -/
lemma simplexCrossProduct_zero_left {X Y : TopCat.{v}} {n : ℕ}
    (c : SingularSimplex X 0) (s : SingularSimplex Y n) :
    simplexCrossProduct (C := C) c s =
    simplexCoprojection
      ⟪prod.lift (SimplexCategory.toTop.map default ≫ c.down) s.down⟫ₛ := by
  simp [simplexCrossProduct, universalSimplexCrossProduct, shuffleSimplex]
  have hd : (default : Shuffle 0 n).sign = 1 := by
    dsimp [Shuffle.sign, Shuffle.invCount]
    have hz : (∑ r : Fin (0 + n), if ((default : Shuffle 0 n).1 (Fin.castSucc r)).1 < ((default : Shuffle 0 n).1 (Fin.succ r)).1 then ((default : Shuffle 0 n).1 (Fin.castSucc r)).2.val else 0) = 0 := by
      apply Finset.sum_eq_zero
      intro i _
      split_ifs with h
      · exact absurd h (lt_irrefl _)
      · rfl
    exact congrArg (fun x => (-1 : ℤ) ^ x) hz
  rw [hd]
  simp
  dsimp [simplexCoprojection, SCF, singularChainComplexFunctor, SSet.singularChainComplexFunctor]
  erw [CategoryTheory.Limits.Sigma.ι_comp_map']
  simp
  apply congrArg
  apply ULift.ext
  dsimp [TopCat.toSSet]
  -- Variant of cast_singularSimplex_down matching the anonymous-constructor form in the goal
  have cast_down : ∀ {Z : TopCat.{v}} {a b : ℕ} (h : a = b) (f : Δ[b] ⟶ Z),
      (h ▸ ({ down := f } : SingularSimplex Z b) : SingularSimplex Z a).down =
      eqToHom (congrArg (SimplexCategory.toTop.obj ∘ SimplexCategory.mk) h) ≫ f := by
    intro Z a b h f; subst h; simp
  rw [cast_down (show n = 0 + n from by omega)
    (shuffleStdSimplexMap (p := 0) (q := n) default)]
  apply CategoryTheory.Limits.prod.hom_ext
  · -- fst component
    simp only [Category.assoc]
    rw [prod.map_fst, prod.lift_fst]
    rw [← Category.assoc, ← Category.assoc]
    congr 1
    ext x
    have h_sub : Subsingleton ↑(TopCat.uliftFunctor.obj
        { carrier := ↑(_root_.stdSimplex ℝ (Fin 1)), str := instTopologicalSpaceSubtype }) := by
      constructor
      rintro ⟨⟨a, ha⟩⟩ ⟨⟨b, hb⟩⟩
      apply ULift.ext
      apply Subtype.ext
      funext i
      have hz : i = 0 := Fin.eq_zero i
      have h1 : a 0 = 1 := by simpa using ha.2
      have h2 : b 0 = 1 := by simpa using hb.2
      change a i = b i
      rw [hz, h1, h2]
    exact Subsingleton.elim _ _
  · -- snd component
    simp only [Category.assoc]
    rw [prod.map_snd, prod.lift_snd]
    slice_lhs 2 3 => tactic =>
      change shuffleStdSimplexMap default ≫ prod.snd = eqToHom (by simp)
      dsimp [shuffleStdSimplexMap, simplexProdMap]
      rw [CategoryTheory.Limits.prod.lift_snd]
      change SimplexCategory.toTop.map _ = eqToHom _
      rw [snd_comp_default_shuffle_eq_eqToHom]
      exact eqToHom_map _ _
    rw [← Category.assoc, eqToHom_trans, eqToHom_refl, Category.id_comp]

/-- Naturality of `simplexCoprojection` w.r.t. the singular chain functor:
pushing a continuous map `f : X ⟶ Y` through the coprojection reindexes the
simplex by postcomposition, `σ ↦ σ ≫ f`. -/
@[simp] lemma simplexCoprojection_comp_SCF_map {X Y : TopCat.{v}} {n : ℕ}
    (s : SingularSimplex X n) (f : X ⟶ Y) :
    simplexCoprojection (C := C) s ≫ ((SCF C).map f).f n =
    simplexCoprojection ⟪s.down ≫ f⟫ₛ := by
  dsimp [simplexCoprojection, SCF, singularChainComplexFunctor,
    SSet.singularChainComplexFunctor]
  erw [CategoryTheory.Limits.Sigma.ι_comp_map']
  simp only [Category.id_comp]; congr 1

/-- Factoring a coprojection through the identity simplex: `ι s` equals
`ι ⟪𝟙 Δ[n]⟫ₛ` composed with the chain map induced by `s.down`.
Named separately from `simplexCoprojection_comp_SCF_map` because the Leibniz rule
needs to factor `ι s ⊗ₘ ι t` into `(ι ⟪𝟙⟫ₛ ⊗ₘ ι ⟪𝟙⟫ₛ) ≫ (s_* ⊗ₘ t_*)`,
which requires rewriting the LHS of `_comp_SCF_map` rather than the RHS. -/
lemma simplexCoprojection_factor {X : TopCat.{v}} {n : ℕ} (s : SingularSimplex X n) :
    simplexCoprojection (C := C) s =
    simplexCoprojection ⟪𝟙 Δ[n]⟫ₛ ≫ ((SCF C).map s.down).f n := by
  dsimp [simplexCoprojection, SCF, singularChainComplexFunctor,
    SSet.singularChainComplexFunctor]
  rw [CategoryTheory.Limits.Sigma.ι_comp_map', Category.id_comp]
  rfl

lemma crossProduct_natural_pure_tensor {X X' Y Y' : TopCat.{v}} [MonObj (𝟙_ C)]
    (f : X ⟶ X') (g : Y ⟶ Y') {p q n : ℕ}
    (s : Δ[p] ⟶ X) (t : Δ[q] ⟶ Y)
    (hn : n = p + q := by omega) :
    simplexCrossProduct  ⟪s⟫ₛ ⟪t⟫ₛ hn ≫
      ((SCF C).map (prod.map f g)).f n =
    simplexCrossProduct  ⟪s ≫ f⟫ₛ ⟪t ≫ g⟫ₛ hn := by
  subst hn
  classical
  unfold simplexCrossProduct
  -- Reduce to functoriality of the induced map on chains.
  simp [Category.assoc]
  -- The composite map on products is `prod.map (s ≫ f) (t ≫ g)`.
  have hprod :
      (prod.map s t) ≫ (prod.map f g) = prod.map (s ≫ f) (t ≫ g) := by
    ext <;> simp
  -- Convert componentwise composition into the component of a composite chain map.
  have hmap :
      ((SCF C).map (prod.map s t)).f (p + q) ≫
        ((SCF C).map (prod.map f g)).f (p + q) =
      ((SCF C).map ((prod.map s t) ≫ (prod.map f g))).f (p + q) := by
    have := congrArg (fun φ => φ.f (p + q))
      (Functor.map_comp (SCF C) (prod.map s t) (prod.map f g)).symm
    simpa [HomologicalComplex.comp_f] using this
  -- Finish by rewriting the LHS using `hmap` and `hprod`.
  simp [hmap, hprod]

/-- Naturality of the chain-level cross product: given continuous maps `f : X ⟶ X'`
and `g : Y ⟶ Y'`, the cross product commutes with the induced chain maps:
`chainCrossProduct ≫ (prod.map f g)_* = (f_* ⊗ g_*) ≫ chainCrossProduct`.

This lifts `crossProduct_natural_pure_tensor` from the simplex level to the chain level
using `chainCrossProduct.ext` (injectivity of `chainTensorHomEquiv`). -/
theorem crossProduct_natural {X X' Y Y' : TopCat.{v}}
    (f : X ⟶ X') (g : Y ⟶ Y') {p q n : ℕ}
    (hn : n = p + q := by omega) :
    chainCrossProduct (C := C) hn ≫ ((SCF C).map (prod.map f g)).f n =
    (((SCF C).map f).f p ⊗ₘ ((SCF C).map g).f q) ≫ chainCrossProduct (C := C) hn := by
  apply chainCrossProduct.ext
  ext ⟨s, t⟩
  simp only [chainTensorHomEquiv_apply]
  -- RHS: rewrite (ι s ⊗ₘ ι t) ≫ (f_* ⊗ₘ g_*) = (ι s ≫ f_*) ⊗ₘ (ι t ≫ g_*)
  rw [MonoidalCategory.tensorHom_comp_tensorHom_assoc]
  rw [simplexCoprojection_comp_SCF_map, simplexCoprojection_comp_SCF_map]
  -- LHS: (λ_.inv ≫ (ι s ⊗ₘ ι t) ≫ chainCrossProduct ≫ (prod.map f g)_*)
  -- Reassociate so ← chainTensorHomEquiv_apply can match on LHS
  rw [show (λ_ (𝟙_ C)).inv ≫
    (simplexCoprojection s ⊗ₘ simplexCoprojection t) ≫ chainCrossProduct hn ≫
      ((SCF C).map (prod.map f g)).f n =
    ((λ_ (𝟙_ C)).inv ≫
      (simplexCoprojection s ⊗ₘ simplexCoprojection t) ≫ chainCrossProduct hn) ≫
      ((SCF C).map (prod.map f g)).f n from by simp [Category.assoc]]
  rw [← chainTensorHomEquiv_apply]
  rw [congrFun (chainCrossProduct.spec (C := C) hn) (s, t)]
  -- RHS: (λ_.inv ≫ (ι ⟪s.down ≫ f⟫ₛ ⊗ₘ ι ⟪t.down ≫ g⟫ₛ) ≫ chainCrossProduct)
  rw [← chainTensorHomEquiv_apply]
  rw [congrFun (chainCrossProduct.spec (C := C) hn) (⟪s.down ≫ f⟫ₛ, ⟪t.down ≫ g⟫ₛ)]
  exact crossProduct_natural_pure_tensor f g s.down t.down hn

/-- The boundary map of `singChain` equals the alternating face map differential.
This avoids unfolding `singChain`/`SCF` through deep functor composition. -/
lemma singChain_d_eq_alternatingFaceMapObjD (X : TopCat.{v}) (n : ℕ) {m : ℕ} (hm : m = n + 1) :
    (singChain C X).d m n =
    eqToHom (congrArg (singChain C X).X hm) ≫
    AlternatingFaceMapComplex.objD
      (((SimplicialObject.whiskering (Type v) C).obj
        ((sigmaConst (C := C)).obj (𝟙_ C))).obj (TopCat.toSSet.obj X)) n := by
  subst hm
  simp only [eqToHom_refl, Category.id_comp, singChain]
  dsimp [SCF, singularChainComplexFunctor, SSet.singularChainComplexFunctor]
  rw [alternatingFaceMapComplex_obj_d]
  rfl


/-! ### Universal Leibniz rule for the simplex-level cross product

**Proof sketch** (after expanding ∂ into face maps):

The LHS is `∑ μ, μ.sign • ∑ r, (-1)^r • coprojection(μ ∘ δ_r)` (double sum over
all `(p+1,q+1)`-shuffles and face indices).

The RHS is two sums: one over `(j, ν)` with `ν : Shuffle p (q+1)`, one over
`(k, ν)` with `ν : Shuffle (p+1) q`.

**Strategy: inject the RHS into the LHS, then cancel the remainder.**

1. **Functoriality** (already done above): rewrite `coprojection(σ) ≫ δ_r` as
   `coprojection(δ_r ≫ σ)`.

2. **Inject RHS left terms into LHS**: For each `(j, ν)` on the RHS, use
   `insertLeftStep ν j` to construct a `(p+1,q+1)`-shuffle `μ` and vertex
   `r = insertLeftIndex ν j`.  By `shuffleStdSimplexMap_insertLeft_face`,
   `δ_r ≫ μ = ν ≫ (δⱼ × id)`, so the RHS term equals the LHS term at `(μ, r)`.
   By `sign_insertLeftStep`, the signs match.

3. **Inject RHS right terms into LHS**: Analogous via `insertRightStep`.

4. **Show injectivity**: The maps `(j, ν) ↦ (insertLeftStep ν j, insertLeftIndex ν j)`
   and `(k, ν) ↦ (insertRightStep ν k, insertRightIndex ν k)` are injective with
   disjoint images (via `insertLeftStep_injective`, `insertRightStep_injective`).

5. **Cancel diagonal remainder**: The LHS terms `(μ, r)` not in either image are
   **diagonal terms** — vertex `r` has one adjacent left step and one adjacent
   right step.  These cancel pairwise via `swapDiagonalSteps`, a sign-reversing
   involution that swaps the two steps around `r`:
   - same map after vertex removal (`swapDiagonalSteps_same_map`)
   - opposite sign (`swapDiagonalSteps_neg_sign`)
   - involutive (`swapDiagonalSteps_involutive`)
-/

/-- Functoriality of `simplexCoprojection`: the face map acts by precomposition
on singular simplices through the coproduct structure. -/
lemma simplexCoprojection_comp_eqToHom_comp_δ {X : TopCat.{v}} {n m : ℕ} (h : n = m + 1)
    (s : SingularSimplex X n) (i : Fin (m + 2)) :
    simplexCoprojection (C := C) s ≫
      eqToHom (congrArg (singChain C X).X h) ≫
      (((SimplicialObject.whiskering (Type v) C).obj ((sigmaConst (C := C)).obj (𝟙_ C))).obj
        (TopCat.toSSet.obj X)).δ i =
    simplexCoprojection (C := C)      ((TopCat.toSSet.obj X).δ i (h ▸ s)) := by
  subst h
  simp only [eqToHom_refl, Category.id_comp]
  dsimp [simplexCoprojection, singChain, SCF, singularChainComplexFunctor,
    SSet.singularChainComplexFunctor, SimplicialObject.δ, SimplicialObject.whiskering]
  erw [CategoryTheory.Limits.Sigma.ι_comp_map']
  simp

/-- The boundary of the universal simplex cross product decomposes as a signed sum
of face-map cross products (the "universal Leibniz rule"):
```
  universalSimplexCrossProduct (p+1) (q+1) ≫ ∂ =
    ∑ j, (-1)^j · simplexCrossProduct (δ_j) (id) +
    (-1)^{p+1} · ∑ j, (-1)^j · simplexCrossProduct (id) (δ_j)
```
Both RHS sums target the same chain-complex degree `p + (q + 1)` via different `hn` proofs,
eliminating the `eqToHom` cast that was needed when the codomain was fixed at `p + q`. -/
theorem universalSimplexCrossProduct_boundary (p q : ℕ) :
    universalSimplexCrossProduct (C := C) (p + 1) (q + 1) ≫
      (singChain C (Δ[p + 1] ⨯ Δ[q + 1])).d
        ((p + 1) + (q + 1)) (p + (q + 1)) =
    ∑ j : Fin (p + 2),
      ((-1 : ℤ) ^ (j : ℕ)) •
        simplexCrossProduct (C := C)          ⟪SimplexCategory.toTop.map (SimplexCategory.δ j)⟫ₛ
          ⟪𝟙 Δ[q + 1]⟫ₛ +
    ((-1 : ℤ) ^ (p + 1)) •
      ∑ j : Fin (q + 2),
        ((-1 : ℤ) ^ (j : ℕ)) •
          simplexCrossProduct (C := C)            ⟪𝟙 Δ[p + 1]⟫ₛ
            ⟪SimplexCategory.toTop.map (SimplexCategory.δ j)⟫ₛ := by
  simp only [universalSimplexCrossProduct, Preadditive.sum_comp, Preadditive.zsmul_comp]
  have hrel : (p + 1 + (q + 1) : ℕ) = (p + (q + 1)) + 1 := by omega
  rw [singChain_d_eq_alternatingFaceMapObjD _ _ hrel]
  simp only [AlternatingFaceMapComplex.objD]
  simp only [Preadditive.comp_sum, Preadditive.comp_zsmul]
  -- Step 1: Functoriality — rewrite coprojection ≫ eqToHom ≫ δ as coprojection(δ ∘ σ)
  simp_rw [simplexCoprojection_comp_eqToHom_comp_δ hrel]
  unfold shuffleSimplex
  unfold shuffleStdSimplexMap
  dsimp only [id]
  simp only [SingularSimplex.ofΔ_down]
  -- Step 2: Rewrite δᵢ(simplexProdMap μ) ↦ simplexProdMap(μ ∘ δᵢ) — the face map acts on a
  -- shuffle simplex by precomposition, absorbing it into the OrderHom.
  -- simp_rw can't match under the ∑ binders; drill down with conv + erw instead.
  conv_lhs =>
    enter [2, x]
    enter [2]
    enter [2, x_1]
    enter [2]
    erw [δ_cast_simplexProdMap hrel]
  -- Fold { down := simplexProdMap ... } back to ⟪simplexProdMap ...⟫ₛ for readability
  conv_lhs =>
    enter [2, x, 2, 2, x_1, 2, 1]
    change ⟪simplexProdMap _⟫ₛ
  -- Step 3: Use naturality to absorb δ j into the shuffle simplex arguments
  unfold simplexCrossProduct
  unfold universalSimplexCrossProduct
  -- Distribute ≫ ((SCF C).map ...).f into the ∑
  simp_rw [Preadditive.sum_comp, Preadditive.zsmul_comp,
    simplexCoprojection_comp_SCF_map]
  -- Simplify (shuffleSimplex ⟪𝟙⟫ₛ ⟪𝟙⟫ₛ μ).down ≫ prod.map (toTop.map (δ j)) 𝟙
  simp only [shuffleSimplex, SingularSimplex.ofΔ_down, shuffleStdSimplexMap,
    id, Category.assoc]
  simp only [prod.map_map, Category.comp_id]
  conv_rhs =>
    -- First sum: 𝟙 ≫ toTop.map (δ x) → toTop.map (δ x) in left face
    enter [1, 2, x, 2, 2, x_1, 2, 1, 1, 2, 1]
    erw [Category.id_comp]
  -- (Previously rewrote 𝟙 ≫ δ x in the second sum's prod.map, but after the n-param
  -- refactor the 𝟙 is inside the ▸-transport and no longer composes with δ x directly.)
  -- Step 4: Collapse LHS double sum ∑ μ, μ.sign • ∑ r, (-1)^r • ... into ∑ (μ,r), (μ.sign * (-1)^r) • ...
  simp_rw [Finset.smul_sum, smul_smul]
  -- Step 4: Split inner sum into diagonal + non-diagonal vertices.
  -- The inner sum is over Fin (p+q+1+2) but isDiagonalVertex expects Index ((p+1)+(q+1)),
  -- so we cast via Fin.cast.
  let isDiag := fun (μ : Shuffle (p + 1) (q + 1)) (r : Fin (p + (q + 1) + 2)) =>
    Shuffle.isDiagonalVertex μ (r.cast (show p + (q + 1) + 2 = (p + 1) + (q + 1) + 1 from by omega))
  haveI isDiag_dec : ∀ μ, DecidablePred (isDiag μ) :=
    fun μ r => Shuffle.isDiagonalVertex_decidable μ _
  conv_lhs =>
    enter [2, x]
    rw [show ∑ r, _ = _ from
      (Finset.sum_filter_add_sum_filter_not Finset.univ (isDiag x) _).symm]
  -- Step 5: Distribute ∑ x over the diagonal + non-diagonal split
  simp_rw [Finset.sum_add_distrib]
  -- Step 6: Cancel the diagonal sum (first summand) via sign-reversing involution.
  -- swapDiagonalSteps swaps the two steps adjacent to a diagonal vertex,
  -- negating the sign while preserving the topological map. The paired terms cancel.
  convert (zero_add _) using 2
  · exact SumInvolution.sum_sum_involution_zero isDiag _
      (fun μ r h => Shuffle.swapDiagonalSteps μ (r.cast (by omega)) h)
      (fun μ r h => Shuffle.swapDiagonalSteps_vertex μ (r.cast (by omega)) h)
      (fun μ r h => Shuffle.swapDiagonalSteps_involutive μ (r.cast (by omega)) h)
      (fun μ r h => by
        dsimp only
        have hsign := Shuffle.swapDiagonalSteps_neg_sign μ (r.cast (by omega)) h
        rw [hsign, neg_mul, neg_smul]
        -- Map part: the swap doesn't change the underlying map away from
        -- the diagonal vertex. δ r avoids r, so the compositions agree.
        congr 1; congr 1; congr 1; congr 1; congr 1
        exact Shuffle.swapDiagonalSteps_same_map μ (r.cast (by omega)) h _
          (fun k h_eq => by
            have h_val := congr_arg Fin.val h_eq
            simp only [SimplexCategory.comp_toOrderHom, SimplexCategory.δ,
              SimplexCategory.mkHom, SimplexCategory.Hom.toOrderHom_mk,
              SimplexCategory.eqToHom_toOrderHom, SimplexCategory.len_mk,
              Fin.val_cast] at h_val
            exact absurd (Fin.ext h_val) (Fin.succAbove_ne r k)))
      (fun μ r h => Shuffle.swapDiagonalSteps_ne μ (r.cast (by omega)) h)
  · -- Split non-diagonal sum into left-type + right-type vertices.
    -- isLeftType checks whether the step at (or just before) vertex r is a left step.
    let isLeftType := fun (μ : Shuffle (p + 1) (q + 1)) (r : Fin (p + q + 1 + 2)) =>
      Shuffle.isLeftStep μ ⟨min r.val ((p + 1) + (q + 1) - 1), by omega⟩
    haveI isLeftType_dec : ∀ μ, DecidablePred (isLeftType μ) :=
      fun μ r => Shuffle.isLeftStep_decidable μ _
    conv_rhs =>
      enter [2, x]
      rw [(Finset.sum_filter_add_sum_filter_not
        (Finset.univ.filter (fun r => ¬isDiag x r)) (isLeftType x) _).symm]
    simp_rw [Finset.sum_add_distrib]
    congr 1
    · rw [← Fintype.sum_prod_type']
      rw [Finset.sum_sigma']
      apply Finset.sum_nbij
        (fun x => ⟨Shuffle.insertLeftStep x.2 x.1,
          (Shuffle.insertLeftIndex x.2 x.1).cast (by omega)⟩)
      · intro ⟨j, ν⟩ _
        simp only [Finset.mem_sigma, Finset.mem_univ, Finset.mem_filter, true_and]
        exact ⟨Shuffle.insertLeftStep_not_diagonal ν j,
               Shuffle.insertLeftStep_isLeftType ν j⟩
      · intro ⟨j₁, ν₁⟩ _ ⟨j₂, ν₂⟩ _ h
        rw [Sigma.mk.inj_iff] at h
        obtain ⟨hμ, hr⟩ := h
        have hr' : Shuffle.insertLeftIndex ν₁ j₁ = Shuffle.insertLeftIndex ν₂ j₂ := by
          have heq := eq_of_heq hr
          exact Fin.ext (by simp [Fin.ext_iff] at heq; exact heq)
        obtain ⟨hj, hν⟩ := Shuffle.insertLeftStep_injective j₁ j₂ ν₁ ν₂ hμ hr'
        exact Prod.ext hj hν
      · intro ⟨μ, r⟩ hmem
        simp only [Finset.mem_coe, Finset.mem_sigma, Finset.mem_univ, Finset.mem_filter,
          true_and] at hmem
        obtain ⟨hnd, hlt⟩ := hmem
        rcases Shuffle.nondiag_mem_insertLeft_or_insertRight μ (r.cast (by omega)) hnd with
          ⟨j, ν, hμ_eq, hr_eq⟩ | ⟨k, ν, hμ_eq, hr_eq⟩
        · refine ⟨(j, ν), Finset.mem_univ _, ?_⟩
          apply Sigma.ext hμ_eq.symm
          apply heq_of_eq; apply Fin.ext
          simp [Fin.val_cast] at hr_eq ⊢; omega
        · exfalso
          have hnotleft := Shuffle.insertRightStep_not_isLeftType ν k
          apply hnotleft
          have hrv : r.val = (Shuffle.insertRightIndex ν k).val := by
            simp [Fin.val_cast] at hr_eq; omega
          subst hμ_eq
          have : isLeftType (Shuffle.insertRightStep ν k) r = Shuffle.isLeftStep
            (Shuffle.insertRightStep ν k) ⟨min r.val ((p + 1) + (q + 1) - 1), by omega⟩ := rfl
          rw [this] at hlt
          convert hlt using 2; congr 1
      · intro ⟨j, ν⟩ _
        dsimp only
        have hsign := Shuffle.sign_insertLeftStep ν j
        congr 1
        · -- Coefficient: use sign_insertLeftStep after showing Fin.cast doesn't change val
          simp only [Fin.val_cast]
          linarith
        · -- Map: follows from shuffleStdSimplexMap_insertLeft_face
          congr 1; congr 1
          -- Goal: simplexProdMap ↑ν ≫ prod.map (δ j) 𝟙
          --     = simplexProdMap ((insertLeftStep ν j).1.comp (δ (Fin.cast ...) ≫ eqToHom ...).toOrderHom)
          -- RHS is definitionally toTop.map (δ _ ≫ eqToHom _) ≫ simplexProdMap (insertLeftStep ν j).1
          conv_rhs => rw [← @simplexProdMap_comp _ _ _ _
            (SimplexCategory.δ (Fin.cast _ (ν.insertLeftIndex j)) ≫ eqToHom _)
            (ν.insertLeftStep j).1]
          rw [Functor.map_comp, Category.assoc,
            show SimplexCategory.toTop.map (eqToHom _) = eqToHom _ from eqToHom_map _ _]
          exact (shuffleStdSimplexMap_insertLeft_face ν j).symm
    · -- Right-type case: analogous to left-type via insertRightStep/insertRightIndex
      rw [← Fintype.sum_prod_type']
      rw [Finset.sum_sigma']
      apply Finset.sum_nbij
        (fun x => ⟨Shuffle.insertRightStep x.2 x.1,
          (Shuffle.insertRightIndex x.2 x.1).cast (by omega)⟩)
      · -- hi: image lands in the sigma finset
        intro ⟨k, ν⟩ _
        simp only [Finset.mem_sigma, Finset.mem_univ, Finset.mem_filter, true_and]
        exact ⟨Shuffle.insertRightStep_not_diagonal ν k,
               fun h => Shuffle.insertRightStep_not_isLeftType ν k h⟩
      · -- i_inj: injective on source
        intro ⟨k₁, ν₁⟩ _ ⟨k₂, ν₂⟩ _ h
        rw [Sigma.mk.inj_iff] at h
        obtain ⟨hμ, hr⟩ := h
        have hr' : Shuffle.insertRightIndex ν₁ k₁ = Shuffle.insertRightIndex ν₂ k₂ := by
          have heq := eq_of_heq hr
          exact Fin.ext (by simp [Fin.ext_iff] at heq; exact heq)
        obtain ⟨hk, hν⟩ := Shuffle.insertRightStep_injective k₁ k₂ ν₁ ν₂ hμ hr'
        exact Prod.ext hk hν
      · -- i_surj: surjective onto target
        intro ⟨μ, r⟩ hmem
        simp only [Finset.mem_coe, Finset.mem_sigma, Finset.mem_univ, Finset.mem_filter,
          true_and] at hmem
        obtain ⟨hnd, hnlt⟩ := hmem
        rcases Shuffle.nondiag_mem_insertLeft_or_insertRight μ (r.cast (by omega)) hnd with
          ⟨j, ν, hμ_eq, hr_eq⟩ | ⟨k, ν, hμ_eq, hr_eq⟩
        · exfalso
          have hleft := Shuffle.insertLeftStep_isLeftType ν j
          apply hnlt
          subst hμ_eq
          have : isLeftType (Shuffle.insertLeftStep ν j) r = Shuffle.isLeftStep
            (Shuffle.insertLeftStep ν j) ⟨min r.val ((p + 1) + (q + 1) - 1), by omega⟩ := rfl
          rw [this]
          convert hleft using 2; congr 1
          simp [Fin.val_cast] at hr_eq ⊢; omega
        · exact ⟨(k, ν), Finset.mem_univ _,
            Sigma.ext hμ_eq.symm (heq_of_eq (Fin.ext (by simp [Fin.val_cast] at hr_eq ⊢; omega)))⟩
      · -- h: summands agree
        intro ⟨k, ν⟩ _
        dsimp only
        have hsign := Shuffle.sign_insertRightStep ν k
        congr 1
        · -- Coefficient
          simp only [Fin.val_cast]; linarith
        · -- Map: show the two simplices are equal
          congr 1
          apply ULift.ext
          simp only [SingularSimplex.ofΔ_down]
          -- Rewrite (h ▸ { down := f }).down to eqToHom _ ≫ f
          have cast_down : ∀ {Z : TopCat.{v}} {a b : ℕ} (h : a = b) (f : Δ[b] ⟶ Z),
              (h ▸ ({ down := f } : SingularSimplex Z b) : SingularSimplex Z a).down =
              eqToHom (congrArg (SimplexCategory.toTop.obj ∘ SimplexCategory.mk) h) ≫ f := by
            intro Z a b h f; subst h; simp
          rw [cast_down] <;> [skip; omega]
          -- Simplify prod.map 𝟙 𝟙 ≫ prod.map 𝟙 (δ k) → prod.map 𝟙 (δ k) and reassociate
          simp only [Category.assoc, prod.map_map, Category.id_comp, Category.comp_id]
          -- Unfold RHS via simplexProdMap_comp to match the face lemma pattern
          conv_rhs => rw [← @simplexProdMap_comp _ _ _ _
            (SimplexCategory.δ (Fin.cast _ (ν.insertRightIndex k)) ≫ eqToHom _)
            (ν.insertRightStep k).1]
          rw [Functor.map_comp, Category.assoc,
            show SimplexCategory.toTop.map (eqToHom _) = eqToHom _ from eqToHom_map _ _]
          -- Use the face lemma to rewrite LHS
          have hface := shuffleStdSimplexMap_insertRight_face ν k
          change eqToHom _ ≫ shuffleStdSimplexMap ν ≫
            prod.map (𝟙 Δ[p + 1]) (SimplexCategory.toTop.map (SimplexCategory.δ k)) =
            SimplexCategory.toTop.map (SimplexCategory.δ (Fin.cast _ (ν.insertRightIndex k))) ≫
            eqToHom _ ≫ shuffleStdSimplexMap (ν.insertRightStep k)
          rw [hface.symm]
          -- Goal: eqToHom ≫ δ idx ≫ eqToHom ≫ shuffle = δ (Fin.cast idx) ≫ eqToHom ≫ shuffle
          -- All are the same underlying face map, just routed through different types.
          -- Convert the leading TopCat eqToHom to toTop.map(eqToHom), fold with Functor.map_comp
          erw [show (eqToHom _ : SimplexCategory.toTop.obj _ ⟶ SimplexCategory.toTop.obj _) =
            SimplexCategory.toTop.{v}.map (eqToHom (by congr 1; omega :
              SimplexCategory.mk (p + (q + 1)) = SimplexCategory.mk ((p + 1) + q)))
            from (eqToHom_map _ _).symm]
          conv_lhs => rw [← Category.assoc (SimplexCategory.toTop.{v}.map (eqToHom _))
            (SimplexCategory.toTop.{v}.map (SimplexCategory.δ _)) _,
            ← Functor.map_comp]
          -- Convert LHS middle eqToHom to toTop.map(eqToHom) and fold
          slice_lhs 1 2 =>
            rw [show (eqToHom _ : SimplexCategory.toTop.obj _ ⟶ _) =
              SimplexCategory.toTop.{v}.map (eqToHom (by rfl))
              from (eqToHom_map _ _).symm, ← Functor.map_comp]
          -- Convert RHS eqToHom to toTop.map(eqToHom) and fold
          slice_rhs 1 2 =>
            rw [show (eqToHom _ : SimplexCategory.toTop.obj _ ⟶ _) =
              SimplexCategory.toTop.{v}.map (eqToHom (by congr 1; omega))
              from (eqToHom_map _ _).symm, ← Functor.map_comp]
          -- Both sides: toTop.map(f) = toTop.map(g). Peel off toTop.map, then ext in SimplexCategory.
          congr 1; congr 1; ext ⟨i, hi⟩
          simp only [SimplexCategory.comp_toOrderHom, SimplexCategory.Hom.toOrderHom_mk,
            SimplexCategory.eqToHom_toOrderHom, SimplexCategory.δ, OrderHom.comp_coe,
            OrderEmbedding.toOrderHom_coe, Function.comp_apply, SimplexCategory.mkHom]
          -- Unfold castOrderIso, then succAboveOrderEmb to succAbove
          simp only [Fin.castOrderIso, OrderIso.coe_toOrderEmbedding, Fin.val_cast,
            RelIso.coe_fn_mk, Equiv.coe_fn_mk]
          -- succAbove(idx, cast(i)) = succAbove(cast(idx), i)
          -- Both give the same Nat value since cast doesn't change .val
          dsimp [Fin.succAboveOrderEmb]
          simp only [Fin.succAbove, Fin.lt_def, Fin.val_cast]
          split <;> split <;>
            simp_all only [Fin.val_castSucc, Fin.val_succ] <;>
            first | omega | exact absurd trivial ‹_›
/-! ### Chain-level Leibniz rule -/

/-- Pushing `(f_* ⊗ₘ g_*) ≫ (α₁ ⊗ₘ β₁)` past `chainCrossProduct`:
fuse the tensor products via `tensorHom_comp_tensorHom` using the commutativity
hypotheses, then apply `crossProduct_natural` to commute past `chainCrossProduct`. -/
lemma chainCrossProduct_tensor_naturality
    {X₁ X₂ Y₁ Y₂ : TopCat.{v}} {f : X₁ ⟶ X₂} {g : Y₁ ⟶ Y₂}
    {p₁ p₂ q₁ q₂ n : ℕ}
    {α₁ : (singChain C X₂).X p₁ ⟶ (singChain C X₂).X p₂}
    {β₁ : (singChain C Y₂).X q₁ ⟶ (singChain C Y₂).X q₂}
    {α₂ : (singChain C X₁).X p₁ ⟶ (singChain C X₁).X p₂}
    {β₂ : (singChain C Y₁).X q₁ ⟶ (singChain C Y₁).X q₂}
    (hα : ((SCF C).map f).f p₁ ≫ α₁ = α₂ ≫ ((SCF C).map f).f p₂)
    (hβ : ((SCF C).map g).f q₁ ≫ β₁ = β₂ ≫ ((SCF C).map g).f q₂)
    (hn : n = p₂ + q₂ := by omega) :
    (((SCF C).map f).f p₁ ⊗ₘ ((SCF C).map g).f q₁) ≫
      (α₁ ⊗ₘ β₁) ≫ chainCrossProduct (C := C) hn =
    (α₂ ⊗ₘ β₂) ≫ chainCrossProduct (C := C) hn ≫
      ((SCF C).map (prod.map f g)).f n := by
  subst hn
  rw [← Category.assoc, MonoidalCategory.tensorHom_comp_tensorHom, hα, hβ,
      ← MonoidalCategory.tensorHom_comp_tensorHom, Category.assoc]
  congr 1
  exact (crossProduct_natural (C := C) f g).symm

/-- The universal Leibniz rule lifted to the coprojection/`chainCrossProduct` level:
`(ι ⟪𝟙⟫ₛ ⊗ₘ ι ⟪𝟙⟫ₛ) ≫ chainCrossProduct ≫ d` decomposes as
`(ι ⟪𝟙⟫ₛ ⊗ₘ ι ⟪𝟙⟫ₛ) ≫ (d ⊗ₘ 𝟙) ≫ chainCrossProduct + (-1)^(p+1) · ... ≫ (𝟙 ⊗ₘ d) ≫ chainCrossProduct`.

Proof strategy: precompose `universalSimplexCrossProduct_boundary` with `(λ_ (𝟙_ C)).inv`,
fold each `simplexCrossProduct` term back into `chainTensorHomEquiv` form via `spec`,
then re-fold the face-map sums into `d ⊗ₘ 𝟙` and `𝟙 ⊗ₘ d`. -/
private lemma universalSimplexCrossProduct_coprojection_boundary (p q : ℕ) :
    ((simplexCoprojection (C := C) ⟪𝟙 Δ[p + 1]⟫ₛ ⊗ₘ
        simplexCoprojection ⟪𝟙 Δ[q + 1]⟫ₛ) ≫
      chainCrossProduct (C := C) (show (p + 1) + (q + 1) = (p + 1) + (q + 1) from rfl)) ≫
      (singChain C (Δ[p + 1] ⨯ Δ[q + 1])).d ((p + 1) + (q + 1)) (p + (q + 1)) =
    ((simplexCoprojection ⟪𝟙 Δ[p + 1]⟫ₛ ⊗ₘ simplexCoprojection ⟪𝟙 Δ[q + 1]⟫ₛ) ≫
        ((singChain C Δ[p + 1]).d (p + 1) p ⊗ₘ
          𝟙 ((singChain C Δ[q + 1]).X (q + 1)))) ≫
      chainCrossProduct (C := C) (show p + (q + 1) = p + (q + 1) from rfl) +
    ((-1 : ℤ) ^ (p + 1)) •
      ((simplexCoprojection ⟪𝟙 Δ[p + 1]⟫ₛ ⊗ₘ simplexCoprojection ⟪𝟙 Δ[q + 1]⟫ₛ) ≫
          (𝟙 ((singChain C Δ[p + 1]).X (p + 1)) ⊗ₘ
            (singChain C Δ[q + 1]).d (q + 1) q)) ≫
        chainCrossProduct (C := C) (show p + (q + 1) = (p + 1) + q from by omega) := by
  -- General key: (ι s ⊗ₘ ι t) ≫ chainCrossProduct = (λ_).hom ≫ simplexCrossProduct s t
  have gen_key : ∀ {X Y : TopCat.{v}} {a b n : ℕ} (hn : n = a + b)
      (s : SingularSimplex X a) (t : SingularSimplex Y b),
      (simplexCoprojection (C := C) s ⊗ₘ simplexCoprojection t) ≫
        chainCrossProduct (C := C) hn =
      (λ_ (𝟙_ C)).hom ≫ simplexCrossProduct (C := C) s t hn := by
    intro X Y a b n hn s t
    rw [← Iso.inv_comp_eq (λ_ (𝟙_ C))]
    rw [← chainTensorHomEquiv_apply]
    exact congrFun (chainCrossProduct.spec (C := C) hn) (s, t)
  -- Rewrite LHS: (ι ⊗ₘ ι) ≫ chainCrossProduct = (λ_).hom ≫ simplexCrossProduct ⟪𝟙⟫ ⟪𝟙⟫
  rw [gen_key]
  -- simplexCrossProduct ⟪𝟙⟫ ⟪𝟙⟫ = universalSimplexCrossProduct ≫ (prod.map 𝟙 𝟙)_*
  simp only [simplexCrossProduct, SingularSimplex.ofΔ_down, Category.assoc]
  -- Simplify prod.map 𝟙 𝟙 = 𝟙, (SCF C).map 𝟙 = 𝟙
  rw [show prod.map (𝟙 Δ[p + 1]) (𝟙 Δ[q + 1]) = 𝟙 _ from Limits.prod.map_id_id]
  slice_lhs 3 4 => erw [(SCF C).map_id, HomologicalComplex.id_f, Category.id_comp]
  rw [universalSimplexCrossProduct_boundary, Preadditive.comp_add, Preadditive.comp_zsmul]
  congr 1
  · -- Goal 1: (λ_).hom ≫ Σ_j (-1)^j • simplexCrossProduct(δ_j, 𝟙) =
    --          (ι ⊗ₘ ι) ≫ (d ⊗ₘ 𝟙) ≫ chainCrossProduct
    -- Fold each simplexCrossProduct term back to (ι ⊗ₘ ι) ≫ chainCrossProduct via ← gen_key
    simp only [Preadditive.comp_sum, Preadditive.comp_zsmul, ← gen_key]
    -- LHS: Σ_j (-1)^j • (ι(δ_j) ⊗ₘ ι(𝟙)) ≫ chainCrossProduct
    -- RHS: (ι(𝟙) ⊗ₘ ι(𝟙)) ≫ (d ⊗ₘ 𝟙) ≫ chainCrossProduct
    -- Work on RHS: fuse (ι ⊗ₘ ι) ≫ (d ⊗ₘ 𝟙) via tensorHom_comp_tensorHom
    rw [MonoidalCategory.tensorHom_comp_tensorHom_assoc, Category.comp_id]
    -- RHS: ((ι ≫ d) ⊗ₘ ι) ≫ chainCrossProduct
    -- Expand ι ⟪𝟙⟫ ≫ d into face map sum on the RHS
    conv_rhs =>
      enter [1, 1, 2]
      rw [singChain_d_eq_alternatingFaceMapObjD (C := C) Δ[p + 1] p rfl]
    simp only [eqToHom_refl, Category.id_comp, AlternatingFaceMapComplex.objD,
      Preadditive.comp_sum, Preadditive.comp_zsmul,
      sum_tensor, Preadditive.sum_comp]
    apply Finset.sum_congr rfl; intro j _
    -- LHS: (-1)^j • (ι ⟪δ_j⟫ ⊗ₘ ι ⟪𝟙⟫) ≫ chainCrossProduct
    -- RHS: ((-1)^j • (ι ⟪𝟙⟫ ≫ δ_j) ⊗ₘ ι ⟪𝟙⟫) ≫ chainCrossProduct
    conv_lhs =>
      enter [2, 1, 1, 1]
      rw [show ⟪SimplexCategory.toTop.map (SimplexCategory.δ j)⟫ₛ =
        (TopCat.toSSet.obj Δ[p + 1]).δ j ⟪𝟙 Δ[p + 1]⟫ₛ from rfl]
    rw [← Preadditive.zsmul_comp]
    rw [← Preadditive.zsmul_comp]
    congr 1
    conv_rhs => enter [1]; rw [Preadditive.zsmul_comp]
    conv_rhs => rw [MonoidalCategory.tensorHom_def, MonoidalLinear.smul_whiskerRight,
      Preadditive.zsmul_comp, ← MonoidalCategory.tensorHom_def]
    congr 1
    congr 1
    rw [← simplexCoprojection_comp_eqToHom_comp_δ (C := C) rfl ⟪𝟙 Δ[p + 1]⟫ₛ j,
        eqToHom_refl, Category.id_comp]
  · -- Goal 2: (-1)^(p+1) • (λ_).hom ≫ Σ_j (-1)^j • simplexCrossProduct(𝟙, δ_j) =
    --          (-1)^(p+1) • (ι ⊗ₘ ι) ≫ (𝟙 ⊗ₘ d) ≫ chainCrossProduct
    congr 1
    simp only [Preadditive.comp_sum, Preadditive.comp_zsmul, ← gen_key]
    rw [MonoidalCategory.tensorHom_comp_tensorHom_assoc, Category.comp_id]
    conv_rhs =>
      enter [1, 2]
      rw [singChain_d_eq_alternatingFaceMapObjD (C := C) Δ[q + 1] q rfl]
    simp only [eqToHom_refl, Category.id_comp, AlternatingFaceMapComplex.objD,
      Preadditive.comp_sum, Preadditive.comp_zsmul,
      tensor_sum, Preadditive.sum_comp]
    apply Finset.sum_congr rfl; intro j _
    conv_lhs =>
      enter [2, 1, 2]
      rw [show ⟪SimplexCategory.toTop.map (SimplexCategory.δ j)⟫ₛ =
        (TopCat.toSSet.obj Δ[q + 1]).δ j ⟪𝟙 Δ[q + 1]⟫ₛ from rfl]
    rw [← Preadditive.zsmul_comp]
    conv_rhs =>
      enter [1, 2]
      rw [← Preadditive.zsmul_comp]
    conv_rhs =>
      enter [1]
      rw [MonoidalCategory.tensorHom_def', Preadditive.zsmul_comp,
        MonoidalLinear.whiskerLeft_smul, Preadditive.zsmul_comp,
        ← MonoidalCategory.tensorHom_def']
    congr 1
    congr 1
    congr 1
    rw [← simplexCoprojection_comp_eqToHom_comp_δ (C := C) rfl ⟪𝟙 Δ[q + 1]⟫ₛ j,
        eqToHom_refl, Category.id_comp]

/-- Simplex-level Leibniz rule for `chainCrossProduct`: the cross product of
`(s, t)` composed with the boundary equals the signed sum of face-map cross products.

This lifts `universalSimplexCrossProduct_boundary` from the standard simplices to
arbitrary simplices `s : SingularSimplex X (p+1)`, `t : SingularSimplex Y (q+1)`,
by factoring through `ι ⟪𝟙⟫ₛ ≫ s.down_*` and using naturality + chain map condition.

Both summands target degree `p + (q + 1)` via the `hn` parameter of `chainCrossProduct`,
avoiding `eqToHom` casts (note `(p+1) + q = p + (q+1)` is not definitional). -/
lemma simplexCrossProduct_boundary {X Y : TopCat.{v}} (p q : ℕ)
    (s : SingularSimplex X (p + 1)) (t : SingularSimplex Y (q + 1)) :
    (simplexCoprojection (C := C) s ⊗ₘ simplexCoprojection t) ≫
      chainCrossProduct (C := C) (show (p + 1) + (q + 1) = (p + 1) + (q + 1) from rfl) ≫
      (singChain C (X ⨯ Y)).d ((p + 1) + (q + 1)) (p + (q + 1)) =
    (simplexCoprojection s ⊗ₘ simplexCoprojection t) ≫
      ((singChain C X).d (p + 1) p ⊗ₘ
          𝟙 ((singChain C Y).X (q + 1))) ≫
        chainCrossProduct (C := C) (show p + (q + 1) = p + (q + 1) from rfl) +
    ((-1 : ℤ) ^ (p + 1)) •
      ((simplexCoprojection s ⊗ₘ simplexCoprojection t) ≫
        (𝟙 ((singChain C X).X (p + 1)) ⊗ₘ
            (singChain C Y).d (q + 1) q) ≫
          chainCrossProduct (C := C) (show p + (q + 1) = (p + 1) + q from by omega)) := by
  -- Factor ι s = ι ⟪𝟙⟫ₛ ≫ s_* and ι t = ι ⟪𝟙⟫ₛ ≫ t_*
  rw [simplexCoprojection_factor s, simplexCoprojection_factor t,
      ← MonoidalCategory.tensorHom_comp_tensorHom]
  -- LHS: push (s_* ⊗ₘ t_*) past chainCrossProduct via crossProduct_natural
  simp only [Category.assoc]
  slice_lhs 2 3 => rw [(crossProduct_natural (C := C) s.down t.down).symm]
  -- LHS: commute (prod.map s t)_* past d via chain map condition
  simp only [Category.assoc]
  rw [((SCF C).map (prod.map s.down t.down)).comm
    ((p + 1) + (q + 1)) (p + (q + 1))]
  -- RHS: use chainCrossProduct_tensor_naturality to push (s_* ⊗ₘ t_*) past each summand
  have nat1 := chainCrossProduct_tensor_naturality (C := C)
    (((SCF C).map s.down).comm (p + 1) p)
    (by simp [Category.comp_id, Category.id_comp] :
      ((SCF C).map t.down).f (q + 1) ≫ 𝟙 _ = 𝟙 _ ≫ ((SCF C).map t.down).f (q + 1))
    (show p + (q + 1) = p + (q + 1) from rfl)
  have nat2 := chainCrossProduct_tensor_naturality (C := C)
    (by simp [Category.comp_id, Category.id_comp] :
      ((SCF C).map s.down).f (p + 1) ≫ 𝟙 _ = 𝟙 _ ≫ ((SCF C).map s.down).f (p + 1))
    (((SCF C).map t.down).comm (q + 1) q)
    (show p + (q + 1) = (p + 1) + q from by omega)
  simp only [Category.assoc] at nat1 nat2
  rw [nat1, nat2]
  -- Both sides now end with ≫ (prod.map s t)_*. Left-associate and factor it out.
  simp only [← Category.assoc]
  rw [← Preadditive.zsmul_comp, ← Preadditive.add_comp]
  congr 1
  -- Remaining: the universal Leibniz rule on Δ[p+1] ⨯ Δ[q+1] with coprojection prefix.
  exact universalSimplexCrossProduct_coprojection_boundary p q

/-- **Leibniz rule** (chain map condition): The chain-level cross product is compatible
with the boundary operators.
```
  ∂(σ × τ) = (∂σ) × τ + (-1)^{p+1} · σ × (∂τ)
```
Stated with shifted indices `(p+1, q+1)` to avoid natural number subtraction.
Both summands target degree `p + (q + 1)` via the `hn` parameter.

This lifts `universalSimplexCrossProduct_boundary` to the chain level using
`chainCrossProduct.ext` and `simplexCrossProduct_boundary`. -/
theorem chainCrossProduct_leibniz {X Y : TopCat.{v}} (p q : ℕ) :
    chainCrossProduct (C := C) (show (p + 1) + (q + 1) = (p + 1) + (q + 1) from rfl) ≫
      (singChain C (X ⨯ Y)).d ((p + 1) + (q + 1)) (p + (q + 1)) =
    ((singChain C X).d (p + 1) p ⊗ₘ
        𝟙 ((singChain C Y).X (q + 1))) ≫
      chainCrossProduct (C := C) (show p + (q + 1) = p + (q + 1) from rfl) +
    ((-1 : ℤ) ^ (p + 1)) •
      ((𝟙 ((singChain C X).X (p + 1)) ⊗ₘ
          (singChain C Y).d (q + 1) q) ≫
        chainCrossProduct (C := C) (show p + (q + 1) = (p + 1) + q from by omega)) := by
  apply chainCrossProduct.ext
  ext ⟨s, t⟩
  simp only [chainTensorHomEquiv_apply, Category.assoc]
  rw [Preadditive.comp_add, Preadditive.comp_zsmul]
  congr 1
  exact simplexCrossProduct_boundary (C := C) p q s t

/-! ## Chain homotopy from topological homotopy -/

/-- The boundary of the identity 1-simplex in `Δ[1]`:
`simplexCoprojection ⟪𝟙 Δ[1]⟫ₛ ≫ d₁₀ = simplexCoprojection δ₀ - simplexCoprojection δ₁`,
where `δ₀` and `δ₁` are the two vertex inclusions `Δ[0] → Δ[1]`. -/
lemma boundary_identity_1simplex_generic :
    simplexCoprojection (C := C) ⟪𝟙 Δ[1]⟫ₛ ≫ (singChain C Δ[1]).d 1 0 =
    simplexCoprojection (C := C) ⟪SimplexCategory.toTop.map (SimplexCategory.δ 0)⟫ₛ -
    simplexCoprojection ⟪SimplexCategory.toTop.map (SimplexCategory.δ 1)⟫ₛ := by
  simp only [singChain]
  dsimp [SCF, singularChainComplexFunctor, SSet.singularChainComplexFunctor]
  simp only [alternatingFaceMapComplex_obj_d, AlternatingFaceMapComplex.objD]
  simp only [Preadditive.comp_sum, Preadditive.comp_zsmul]
  rw [Fin.sum_univ_two]
  simp only [Fin.val_zero, pow_zero, one_smul, Fin.val_one, pow_one, neg_smul, sub_eq_add_neg]
  simp only [simplexCoprojection]
  erw [Sigma.ι_comp_map', Sigma.ι_comp_map']
  simp only [Category.id_comp, sub_eq_add_neg]
  congr 1 <;> congr 1 <;> {ext; rfl}

/-- Evaluating the cross product on a 0-simplex on the right and pushing forward
along a map recovers the chain map, generically.

Given `Hmap : X ⨯ Δ[1] ⟶ Y`, a 0-simplex `c` in `Δ[1]`, and `h : X ⟶ Y`
such that `prod.lift s c ≫ Hmap = s ≫ h` for all simplices `s`, we get
`(ρ⁻¹ ≫ (𝟙 ⊗ ι c) ≫ chainCrossProduct) ≫ Hmap_* = h_*` at each degree. -/
lemma chainCrossProduct_zero_right_boundary {X Y : TopCat.{v}}
    (Hmap : X ⨯ Δ[1] ⟶ Y) (c : SingularSimplex Δ[1] 0) (h : X ⟶ Y)
    (heval : ∀ {n : ℕ} (s : SingularSimplex X n),
      prod.lift s.down (SimplexCategory.toTop.map default ≫ c.down) ≫ Hmap = s.down ≫ h)
    (n : ℕ) :
    (ρ_ ((singChain C X).X n)).inv ≫
      (𝟙 ((singChain C X).X n) ⊗ₘ simplexCoprojection c) ≫
      chainCrossProduct (C := C) (show n + 0 = n from by omega) ≫ ((SCF C).map Hmap).f n =
    ((SCF C).map h).f n := by
  apply Sigma.hom_ext; intro s
  slice_lhs 1 2 => erw [MonoidalCategory.rightUnitor_inv_naturality]
  simp only [Category.assoc]
  rw [← MonoidalCategory.tensorHom_id]
  rw [← Category.assoc (Sigma.ι _ s ⊗ₘ _)]
  erw [MonoidalCategory.tensorHom_comp_tensorHom, Category.comp_id]
  rw [Category.id_comp]
  have key : (simplexCoprojection s ⊗ₘ simplexCoprojection c) ≫ chainCrossProduct (C := C)
      (show n + 0 = n from by omega) =
      (λ_ (𝟙_ C)).hom ≫ simplexCrossProduct' (show n + 0 = n from by omega) (s, c) := by
    rw [← Iso.inv_comp_eq (λ_ (𝟙_ C))]
    rw [← chainTensorHomEquiv_apply]
    exact congrFun (chainCrossProduct.spec (C := C) _) (s, c)
  rw [← Category.assoc (Sigma.ι _ s ⊗ₘ _), key]
  simp only [simplexCrossProduct']
  rw [simplexCrossProduct_zero_right]
  rw [Category.assoc, ← Category.assoc (ρ_ (𝟙_ C)).inv (λ_ (𝟙_ C)).hom]
  rw [show (ρ_ (𝟙_ C)).inv ≫ (λ_ (𝟙_ C)).hom = 𝟙 _ from by
    erw [MonoidalCategory.unitors_equal]; exact (ρ_ _).inv_hom_id]
  rw [Category.id_comp]
  rw [simplexCoprojection_comp_SCF_map, simplexCoprojection_comp_SCF_map]
  congr 1; apply ULift.ext; simp only [SingularSimplex.ofΔ_down]; exact heval s

--# TODO: Get rid of this and just derive from the other one
/-- Special case of the Leibniz rule for degree `(0, 1)`:
the cross product `chainCrossProduct (0, 1)` composed with the boundary `d` equals
`(𝟙 ⊗ d) ≫ chainCrossProduct (0, 0)`. -/
lemma chainCrossProduct_leibniz_left_zero_zero {X Y : TopCat.{v}} :
    chainCrossProduct (C := C) (X := X) (Y := Y) (show 0 + 1 = 0 + 1 from rfl) ≫
      (singChain C (X ⨯ Y)).d (0 + 1) 0 =
    (𝟙 ((singChain C X).X 0) ⊗ₘ (singChain C Y).d 1 0) ≫
      chainCrossProduct (C := C) (show 0 + 0 = 0 from by omega) := by
  apply chainCrossProduct.ext; ext ⟨s, t⟩
  simp only [chainTensorHomEquiv_apply, Category.assoc]
  congr 1
  -- LHS: (ι s ⊗ₘ ι t) ≫ chainCrossProduct ≫ d
  -- Use key: (ι s ⊗ₘ ι t) ≫ chainCrossProduct = (λ_).hom ≫ simplexCrossProduct s t
  rw [← Category.assoc (simplexCoprojection s ⊗ₘ _)]
  rw [show (simplexCoprojection s ⊗ₘ simplexCoprojection t) ≫ chainCrossProduct (C := C)
      (show 0 + 1 = 0 + 1 from rfl) =
      (λ_ (𝟙_ C)).hom ≫ simplexCrossProduct' (show 0 + 1 = 0 + 1 from rfl) (s, t) from by
    rw [← Iso.inv_comp_eq (λ_ (𝟙_ C)), ← chainTensorHomEquiv_apply]
    exact congrFun (chainCrossProduct.spec (C := C) _) (s, t)]
  -- RHS: (ι s ⊗ₘ (ι t ≫ d)) ≫ chainCrossProduct
  conv_rhs =>
    rw [← Category.assoc, MonoidalCategory.tensorHom_comp_tensorHom, Category.comp_id]
  conv_rhs =>
    arg 1; arg 2
    rw [simplexCoprojection_factor t, Category.assoc,
        ((SCF C).map t.down).comm 1 0, ← Category.assoc]
    erw [boundary_identity_1simplex_generic (C := C)]
  conv_rhs =>
    arg 1; arg 2
    rw [Preadditive.sub_comp, simplexCoprojection_comp_SCF_map,
        simplexCoprojection_comp_SCF_map]
  open HomologyLean.CategoryTheory in
  rw [tensorHom_sub, Preadditive.sub_comp]
  rw [show (simplexCoprojection s ⊗ₘ simplexCoprojection
      ⟪⟪SimplexCategory.toTop.map (SimplexCategory.δ 0)⟫ₛ.down ≫ t.down⟫ₛ) ≫
      chainCrossProduct (C := C) (show 0 + 0 = 0 from by omega) =
      (λ_ (𝟙_ C)).hom ≫ simplexCrossProduct' (show 0 + 0 = 0 from by omega)
        (s, ⟪⟪SimplexCategory.toTop.map (SimplexCategory.δ 0)⟫ₛ.down ≫ t.down⟫ₛ) from by
    rw [← Iso.inv_comp_eq (λ_ (𝟙_ C)), ← chainTensorHomEquiv_apply]
    exact congrFun (chainCrossProduct.spec (C := C) _) _]
  rw [show (simplexCoprojection s ⊗ₘ simplexCoprojection
      ⟪⟪SimplexCategory.toTop.map (SimplexCategory.δ 1)⟫ₛ.down ≫ t.down⟫ₛ) ≫
      chainCrossProduct (C := C) (show 0 + 0 = 0 from by omega) =
      (λ_ (𝟙_ C)).hom ≫ simplexCrossProduct' (show 0 + 0 = 0 from by omega)
        (s, ⟪⟪SimplexCategory.toTop.map (SimplexCategory.δ 1)⟫ₛ.down ≫ t.down⟫ₛ) from by
    rw [← Iso.inv_comp_eq (λ_ (𝟙_ C)), ← chainTensorHomEquiv_apply]
    exact congrFun (chainCrossProduct.spec (C := C) _) _]
  simp only [simplexCrossProduct']
  rw [Category.assoc, ← Preadditive.comp_sub]
  congr 1
  rw [simplexCrossProduct_zero_right, simplexCrossProduct_zero_right]
  rw [simplexCrossProduct_zero_left]
  rw [simplexCoprojection_factor ⟪prod.lift (SimplexCategory.toTop.map default ≫ s.down) t.down⟫ₛ,
      Category.assoc, ((SCF C).map _).comm 1 0, ← Category.assoc]
  erw [boundary_identity_1simplex_generic (C := C)]
  rw [Preadditive.sub_comp, simplexCoprojection_comp_SCF_map, simplexCoprojection_comp_SCF_map]
  congr 1 <;> congr 1 <;> {
    apply ULift.ext
    simp only [singularSimplexFunctor, SingularSimplex.ofΔ_down]
    rw [prod.comp_lift]
    apply CategoryTheory.Limits.prod.hom_ext
    · rw [prod.lift_fst, prod.lift_fst, ← Category.assoc,
          ← SimplexCategory.toTop.map_comp, SimplexCategory.δ_comp_default_mk1,
          SimplexCategory.toTop.map_id, Category.id_comp]
    · rw [prod.lift_snd, prod.lift_snd, ← Category.assoc,
          ← SimplexCategory.toTop.map_comp, SimplexCategory.default_mk0_eq_id, Category.id_comp]
  }

/-- **Leibniz rule, right-zero case** `(p+1, 0)`:
The cross product `chainCrossProduct (p+1, 0)` composed with the boundary `d` equals
`(d_X ⊗ 𝟙) ≫ chainCrossProduct (p, 0)`.

There is a unique `(p+1, 0)`-shuffle with sign `1`, so the cross product reduces
to `simplexCrossProduct_zero_right`. The `d₂` term vanishes because `Y` has
no differential from degree `0`. -/
lemma chainCrossProduct_leibniz_right_zero {X Y : TopCat.{v}} (p : ℕ) :
    (chainCrossProduct (C := C) (X := X) (Y := Y) (p := p + 1) (q := 0) :
        _ ⟶ (singChain C (X ⨯ Y)).X (p + 1)) ≫
      (singChain C (X ⨯ Y)).d (p + 1) p =
    ((singChain C X).d (p + 1) p ⊗ₘ
        𝟙 ((singChain C Y).X 0)) ≫
      (chainCrossProduct (C := C) (p := p) (q := 0) :
        _ ⟶ (singChain C (X ⨯ Y)).X p) := by
  apply chainCrossProduct.ext; ext ⟨s, t⟩
  simp only [chainTensorHomEquiv_apply, Category.assoc]
  congr 1
  have gen_key : ∀ {X' Y' : TopCat.{v}} {a b n : ℕ} (hn : n = a + b)
      (s' : SingularSimplex X' a) (t' : SingularSimplex Y' b),
      (simplexCoprojection (C := C) s' ⊗ₘ simplexCoprojection t') ≫
        chainCrossProduct (C := C) hn =
      (λ_ (𝟙_ C)).hom ≫ simplexCrossProduct' (C := C) hn (s', t') := by
    intro X' Y' a b n hn s' t'
    rw [← Iso.inv_comp_eq (λ_ (𝟙_ C))]
    rw [← chainTensorHomEquiv_apply]
    exact congrFun (chainCrossProduct.spec (C := C) hn) (s', t')
  -- LHS: unfold crossProduct(p+1,0) via gen_key and simplexCrossProduct_zero_right
  rw [← Category.assoc (simplexCoprojection s ⊗ₘ _)]
  rw [gen_key]
  simp only [simplexCrossProduct']
  rw [simplexCrossProduct_zero_right (C := C)]
  -- LHS: expand d(X⨯Y) into face map sum
  rw [Category.assoc, singChain_d_eq_alternatingFaceMapObjD (C := C) (X ⨯ Y) p rfl]
  simp only [eqToHom_refl, Category.id_comp, AlternatingFaceMapComplex.objD,
    Preadditive.comp_sum, Preadditive.comp_zsmul, Category.assoc]
  -- RHS: fuse (ι s ⊗ ι t) ≫ (d_X ⊗ 𝟙) into ((ι s ≫ d_X) ⊗ ι t)
  conv_rhs =>
    rw [← Category.assoc, MonoidalCategory.tensorHom_comp_tensorHom, Category.comp_id]
  -- RHS: expand d_X
  conv_rhs =>
    enter [1, 1]
    rw [singChain_d_eq_alternatingFaceMapObjD (C := C) X p rfl]
    simp only [eqToHom_refl, Category.id_comp, AlternatingFaceMapComplex.objD,
      Preadditive.comp_sum, Preadditive.comp_zsmul]
  -- Distribute ⊗ₘ over the sum, then ≫ over the sum
  rw [sum_tensor, Preadditive.sum_comp]
  -- Match term by term
  apply Finset.sum_congr rfl; intro j _
  -- Pull (-1)^j out of the tensor on the RHS
  conv_rhs => enter [1]; rw [MonoidalCategory.tensorHom_def]
  rw [MonoidalLinear.smul_whiskerRight, Preadditive.zsmul_comp,
      ← MonoidalCategory.tensorHom_def]
  rw [Preadditive.zsmul_comp]
  congr 1
  -- LHS: fold ι(prod.lift s.down (default ≫ t.down)) ≫ δⱼ as ι(δⱼ(prod.lift ...))
  rw [show simplexCoprojection (C := C)
      ⟪prod.lift s.down (SimplexCategory.toTop.map default ≫ t.down)⟫ₛ ≫
      (((SimplicialObject.whiskering (Type v) C).obj ((sigmaConst (C := C)).obj (𝟙_ C))).obj
        (TopCat.toSSet.obj (X ⨯ Y))).δ j =
    simplexCoprojection (C := C)
      ((TopCat.toSSet.obj (X ⨯ Y)).δ j
        ⟪prod.lift s.down (SimplexCategory.toTop.map default ≫ t.down)⟫ₛ) from by
    have := simplexCoprojection_comp_eqToHom_comp_δ (C := C) rfl
      ⟪prod.lift s.down (SimplexCategory.toTop.map default ≫ t.down)⟫ₛ j
    simp only [eqToHom_refl, Category.id_comp] at this
    exact this]
  -- RHS: fold ι s ≫ δⱼ as ι(δⱼ(s))
  conv_rhs =>
    enter [1, 1]
    rw [show simplexCoprojection (C := C) s ≫
        (((SimplicialObject.whiskering (Type v) C).obj ((sigmaConst (C := C)).obj (𝟙_ C))).obj
          (TopCat.toSSet.obj X)).δ j =
      simplexCoprojection (C := C) ((TopCat.toSSet.obj X).δ j s) from by
      have := simplexCoprojection_comp_eqToHom_comp_δ (C := C) rfl s j
      simp only [eqToHom_refl, Category.id_comp] at this
      exact this]
  -- RHS: use gen_key and simplexCrossProduct_zero_right
  rw [gen_key]
  simp only [simplexCrossProduct']
  rw [simplexCrossProduct_zero_right (C := C)]
  -- Both sides: (λ_).hom ≫ ι(prod.lift ? (default ≫ t.down))
  -- Show δⱼ(X⨯Y)(prod.lift(s, default ≫ t)) = prod.lift(δⱼ(X) s, default ≫ t)
  congr 2
  apply ULift.ext
  simp only [SingularSimplex.ofΔ_down, SimplicialObject.δ, TopCat.toSSet]
  change SimplexCategory.toTop.map (SimplexCategory.δ j) ≫
    prod.lift s.down (SimplexCategory.toTop.map default ≫ t.down) =
    prod.lift (SimplexCategory.toTop.map (SimplexCategory.δ j) ≫ s.down)
      (SimplexCategory.toTop.map default ≫ t.down)
  rw [prod.comp_lift]; congr 1
  -- δⱼ.toTop ≫ default.toTop ≫ t.down = default.toTop ≫ t.down
  -- since δⱼ ≫ default = default (unique map to [0])
  rw [← Category.assoc, ← SimplexCategory.toTop.map_comp]; congr 1

/-- **Leibniz rule, left-zero case** `(0, q+1)`:
The cross product `chainCrossProduct (0, q+1)` composed with the boundary `d` equals
`(𝟙 ⊗ d_Y) ≫ chainCrossProduct (0, q)`.

There is a unique `(0, q+1)`-shuffle with sign `1`, so the cross product reduces
to `simplexCrossProduct_zero_left`. The `d₁` term vanishes because `X` has
no differential from degree `0`. -/
lemma chainCrossProduct_leibniz_left_zero {X Y : TopCat.{v}} (q : ℕ) :
    (chainCrossProduct (C := C) (X := X) (Y := Y) (p := 0) (q := q + 1) :
        _ ⟶ (singChain C (X ⨯ Y)).X (q + 1)) ≫
      (singChain C (X ⨯ Y)).d (q + 1) q =
    (𝟙 ((singChain C X).X 0) ⊗ₘ
        (singChain C Y).d (q + 1) q) ≫
      (chainCrossProduct (C := C) (p := 0) (q := q) :
        _ ⟶ (singChain C (X ⨯ Y)).X q) := by
  apply chainCrossProduct.ext; ext ⟨s, t⟩
  simp only [chainTensorHomEquiv_apply, Category.assoc]
  congr 1
  -- gen_key: (ι s' ⊗ ι t') ≫ crossProduct = (λ_).hom ≫ simplexCrossProduct'(s', t')
  have gen_key : ∀ {X' Y' : TopCat.{v}} {a b n : ℕ} (hn : n = a + b)
      (s' : SingularSimplex X' a) (t' : SingularSimplex Y' b),
      (simplexCoprojection (C := C) s' ⊗ₘ simplexCoprojection t') ≫
        chainCrossProduct (C := C) hn =
      (λ_ (𝟙_ C)).hom ≫ simplexCrossProduct' (C := C) hn (s', t') := by
    intro X' Y' a b n hn s' t'
    rw [← Iso.inv_comp_eq (λ_ (𝟙_ C))]
    rw [← chainTensorHomEquiv_apply]
    exact congrFun (chainCrossProduct.spec (C := C) hn) (s', t')
  -- LHS: unfold crossProduct(0,q+1) via gen_key and simplexCrossProduct_zero_left
  rw [← Category.assoc (simplexCoprojection s ⊗ₘ _)]
  rw [gen_key]
  simp only [simplexCrossProduct']
  rw [simplexCrossProduct_zero_left (C := C)]
  -- LHS: expand d(X⨯Y) into face map sum
  rw [Category.assoc, singChain_d_eq_alternatingFaceMapObjD (C := C) (X ⨯ Y) q rfl]
  simp only [eqToHom_refl, Category.id_comp, AlternatingFaceMapComplex.objD,
    Preadditive.comp_sum, Preadditive.comp_zsmul, Category.assoc]
  -- RHS: fuse (ι s ⊗ ι t) ≫ (𝟙 ⊗ d_Y) into (ι s ⊗ (ι t ≫ d_Y))
  conv_rhs =>
    rw [← Category.assoc, MonoidalCategory.tensorHom_comp_tensorHom, Category.comp_id]
  -- RHS: expand d_Y
  conv_rhs =>
    enter [1, 2]
    rw [singChain_d_eq_alternatingFaceMapObjD (C := C) Y q rfl]
    simp only [eqToHom_refl, Category.id_comp, AlternatingFaceMapComplex.objD,
      Preadditive.comp_sum, Preadditive.comp_zsmul]
  -- Distribute ⊗ₘ over the sum, then ≫ over the sum
  rw [tensor_sum, Preadditive.sum_comp]
  -- Match term by term
  apply Finset.sum_congr rfl; intro j _
  -- Pull (-1)^j out of the tensor on the RHS
  conv_rhs => enter [1]; rw [MonoidalCategory.tensorHom_def']
  rw [MonoidalLinear.whiskerLeft_smul, Preadditive.zsmul_comp,
      ← MonoidalCategory.tensorHom_def']
  rw [Preadditive.zsmul_comp]
  congr 1
  -- LHS: fold ι(f) ≫ δⱼ as ι(δⱼ(f)) using the simplexCoprojection_comp_eqToHom_comp_δ
  rw [show simplexCoprojection (C := C)
      ⟪prod.lift (SimplexCategory.toTop.map default ≫ s.down) t.down⟫ₛ ≫
      (((SimplicialObject.whiskering (Type v) C).obj ((sigmaConst (C := C)).obj (𝟙_ C))).obj
        (TopCat.toSSet.obj (X ⨯ Y))).δ j =
    simplexCoprojection (C := C)
      ((TopCat.toSSet.obj (X ⨯ Y)).δ j
        ⟪prod.lift (SimplexCategory.toTop.map default ≫ s.down) t.down⟫ₛ) from by
    have := simplexCoprojection_comp_eqToHom_comp_δ (C := C) rfl
      ⟪prod.lift (SimplexCategory.toTop.map default ≫ s.down) t.down⟫ₛ j
    simp only [eqToHom_refl, Category.id_comp] at this
    exact this]
  -- RHS: fold ι t ≫ δⱼ as ι(δⱼ(t))
  conv_rhs =>
    enter [1, 2]
    rw [show simplexCoprojection (C := C) t ≫
        (((SimplicialObject.whiskering (Type v) C).obj ((sigmaConst (C := C)).obj (𝟙_ C))).obj
          (TopCat.toSSet.obj Y)).δ j =
      simplexCoprojection (C := C) ((TopCat.toSSet.obj Y).δ j t) from by
      have := simplexCoprojection_comp_eqToHom_comp_δ (C := C) rfl t j
      simp only [eqToHom_refl, Category.id_comp] at this
      exact this]
  -- RHS: use gen_key and simplexCrossProduct_zero_left
  rw [gen_key]
  simp only [simplexCrossProduct']
  rw [simplexCrossProduct_zero_left (C := C)]
  -- Now both sides: (λ_).hom ≫ ι(prod.lift(default ≫ s, ?))
  -- Show δⱼ(X⨯Y)(prod.lift(default ≫ s, t)) = prod.lift(default ≫ s, (δⱼ(Y) t).down)
  congr 2
  -- Simplex equality: δⱼ(prod.lift(default ≫ s, t)) = prod.lift(default ≫ s, δⱼ(t))
  apply ULift.ext
  simp only [SingularSimplex.ofΔ_down, SimplicialObject.δ, TopCat.toSSet]
  -- Unfold the .map action (which is precomposition with δⱼ.toTop)
  change SimplexCategory.toTop.map (SimplexCategory.δ j) ≫
    prod.lift (SimplexCategory.toTop.map default ≫ s.down) t.down =
    prod.lift (SimplexCategory.toTop.map default ≫ s.down)
      (SimplexCategory.toTop.map (SimplexCategory.δ j) ≫ t.down)
  rw [prod.comp_lift]
  congr 1
  rw [← Category.assoc, ← SimplexCategory.toTop.map_comp]; congr 1

/-- A topological homotopy `H : f ∼ g` between continuous maps `f g : X → Y`
induces a chain homotopy between the chain maps `C_*(f)` and `C_*(g)`.

The proof uses the cross product with the unit interval: the homotopy
`H : I × X → Y` composed with the cross product `C_1(Δ[1]) ⊗ C_n(X) → C_{n+1}(X × Δ[1])`
gives the chain homotopy operator, using the fundamental class of `Δ[1]` as a
1-chain connecting the two endpoints. -/
noncomputable def singularChain_chainHomotopy_of_homotopy {X Y : TopCat.{v}} {f g : X ⟶ Y}
    (H : ContinuousMap.Homotopy f.hom' g.hom') :
    Homotopy
      ((SCF C).map g)
      ((SCF C).map f) := by
  let Hmap : X ⨯ Δ[1] ⟶ Y := homotopyMap H
  let chainH := (SCF C).map Hmap
  let ι₁ : SingularSimplex (Δ[1] : TopCat.{v}) 1 := ⟪𝟙 Δ[1]⟫ₛ
  let tensorι₁ := fun n =>
    (ρ_ (((SCF C).obj X).X n)).inv ≫
      (𝟙 (((SCF C).obj X).X n) ⊗ₘ simplexCoprojection (C := C) ι₁)
  let P := fun n => (-1 : ℤ) ^ n •
    (tensorι₁ n ≫ chainCrossProduct (C := C) (show n + 1 = n + 1 from rfl) ≫ chainH.f (n + 1))
  refine Homotopy.mk
    (fun i j => if h : j = i + 1 then h ▸ P i else 0)
    (by intro i j h; dsimp; rw [dif_neg]; rw [ComplexShape.down_Rel] at h; omega)
    ?_
  intro i
  rw [prevD_eq _ (show (ComplexShape.down ℕ).Rel (i + 1) i by simp [ComplexShape.down_Rel])]
  simp only [dif_pos trivial]
  have hBoundary₀ : ∀ n,
      (ρ_ (((SCF C).obj X).X n)).inv ≫
        (𝟙 (((SCF C).obj X).X n) ⊗ₘ
          simplexCoprojection (C := C) (⟪SimplexCategory.toTop.map (SimplexCategory.δ 0)⟫ₛ :
            SingularSimplex Δ[1] 0)) ≫
        chainCrossProduct (C := C) (show n + 0 = n from by omega) ≫ chainH.f n =
       ((SCF C).map g).f n :=
    chainCrossProduct_zero_right_boundary (C := C) Hmap _ g fun s => homotopyMap_comp_delta0 H s.down
  have hBoundary₁ : ∀ n,
      (ρ_ (((SCF C).obj X).X n)).inv ≫
        (𝟙 (((SCF C).obj X).X n) ⊗ₘ
          simplexCoprojection (C := C) (⟪SimplexCategory.toTop.map (SimplexCategory.δ 1)⟫ₛ :
            SingularSimplex Δ[1] 0)) ≫
        chainCrossProduct (C := C) (show n + 0 = n from by omega) ≫ chainH.f n =
        ((SCF C).map f).f n :=
    chainCrossProduct_zero_right_boundary (C := C) Hmap _ f fun s => homotopyMap_comp_delta1 H s.down
  open HomologyLean.CategoryTheory in
  match i with
  | 0 =>
    rw [dNext_eq_zero _ 0 (by simp [ComplexShape.down_Rel])]
    simp
    conv_rhs => lhs; rw [show P 0 = tensorι₁ 0 ≫
        chainCrossProduct (C := C) (show 0 + 1 = 0 + 1 from rfl) ≫ chainH.f 1 from by
      simp [P]]
    simp only [Category.assoc]
    rw [chainH.comm 1 0]
    rw [← Category.assoc (chainCrossProduct (C := C) (show 0 + 1 = 0 + 1 from rfl)),
        chainCrossProduct_leibniz_left_zero_zero (C := C)]
    simp only [tensorι₁, Category.assoc]
    rw [← Category.assoc (𝟙 _ ⊗ₘ simplexCoprojection (C := C) ι₁),
      MonoidalCategory.tensorHom_comp_tensorHom, Category.comp_id]
    erw [boundary_identity_1simplex_generic (C := C)]
    rw [tensorHom_sub, Preadditive.sub_comp, Preadditive.comp_sub]
    rw [hBoundary₀ 0, hBoundary₁ 0]
    abel
  | n + 1 =>
    rw [dNext_eq _ (show (ComplexShape.down ℕ).Rel (n + 1) n by simp [ComplexShape.down_Rel])]
    simp
    simp only [P, Preadditive.zsmul_comp, Preadditive.comp_zsmul, Category.assoc]
    rw [chainH.comm (n + 2) (n + 1)]
    rw [← Category.assoc (chainCrossProduct (C := C) (show (n + 1) + 1 = (n + 1) + 1 from rfl)),
        chainCrossProduct_leibniz (C := C) n 0]
    simp only [Preadditive.add_comp, Preadditive.comp_add, Preadditive.comp_zsmul,
      Preadditive.zsmul_comp, Category.assoc]
    simp only [smul_add, smul_smul, ← pow_add, ← two_mul,
      pow_mul, neg_one_pow_two, one_pow, one_smul]
    conv_rhs => lhs; rw [← add_assoc]
    let Xbdy := tensorι₁ (n + 1) ≫
      ((singChain C X).d (n + 1) n ⊗ₘ 𝟙 ((singChain C Δ[1]).X (0 + 1))) ≫
        chainCrossProduct (C := C) (show n + (0 + 1) = n + (0 + 1) from rfl) ≫ chainH.f (n + 1)
    let Δbdy := tensorι₁ (n + 1) ≫
      (𝟙 ((singChain C X).X (n + 1)) ⊗ₘ (singChain C Δ[1]).d (0 + 1) 0) ≫
        chainCrossProduct (C := C) (show (n + 1) + 0 = n + 1 from by omega) ≫
          chainH.f (n + 1)
    change _ = (-1) ^ n • (((SCF C).obj X).d (n + 1) n ≫
        tensorι₁ n ≫ chainCrossProduct (C := C) (show n + 1 = n + 1 from rfl) ≫
          chainH.f (n + 1)) +
      (-1) ^ (n + 1) • Xbdy + Δbdy + ((SCF C).map f).f (n + 1)
    have hΔbdy : Δbdy = ((SCF C).map g).f (n + 1) - ((SCF C).map f).f (n + 1) := by
      simp only [Δbdy, tensorι₁, Category.assoc]
      rw [← Category.assoc (𝟙 _ ⊗ₘ simplexCoprojection (C := C) ι₁),
        MonoidalCategory.tensorHom_comp_tensorHom, Category.comp_id]
      erw [boundary_identity_1simplex_generic (C := C)]
      rw [tensorHom_sub, Preadditive.sub_comp, Preadditive.comp_sub]
      rw [hBoundary₀ (n + 1), hBoundary₁ (n + 1)]
    rw [hΔbdy]
    abel
    simp only [Xbdy]
    have htensor_nat : tensorι₁ (n + 1) ≫
        ((singChain C X).d (n + 1) n ⊗ₘ 𝟙 ((singChain C Δ[1]).X (0 + 1))) =
        ((SCF C).obj X).d (n + 1) n ≫ tensorι₁ n := by
      simp only [tensorι₁, Category.assoc]
      rw [MonoidalCategory.tensorHom_comp_tensorHom, Category.id_comp, Category.comp_id]
      conv_rhs =>
        rw [← Category.assoc, MonoidalCategory.rightUnitor_inv_naturality, Category.assoc]
      congr 1
      rw [← MonoidalCategory.tensorHom_id,
        MonoidalCategory.tensorHom_comp_tensorHom, Category.comp_id, Category.id_comp]
    simp only [← Category.assoc (tensorι₁ (n + 1)), htensor_nat, Category.assoc]
    norm_num
    rw [pow_succ, mul_neg_one, neg_smul]
    abel

/-- Homotopic maps induce equal maps on singular homology. -/
theorem singularHomology_map_eq_of_homotopy {X Y : TopCat.{v}} {f g : X ⟶ Y}
    (H : ContinuousMap.Homotopy f.hom' g.hom') (n : ℕ) :
    ((singularHomologyFunctor C n).obj (𝟙_ C)).map f =
      ((singularHomologyFunctor C n).obj (𝟙_ C)).map g :=
  ((singularChain_chainHomotopy_of_homotopy (C := C) H).homologyMap_eq n).symm

/-- Homotopy equivalent spaces have isomorphic singular homology. -/
noncomputable def singularHomology_iso_of_homotopyEquiv {X Y : TopCat.{v}}
    (f : X ⟶ Y) (g : Y ⟶ X)
    (hfg : ContinuousMap.Homotopy (f ≫ g : X ⟶ X).hom' (𝟙 X : X ⟶ X).hom')
    (hgf : ContinuousMap.Homotopy (g ≫ f : Y ⟶ Y).hom' (𝟙 Y : Y ⟶ Y).hom')
    (n : ℕ) :
    ((singularHomologyFunctor C n).obj (𝟙_ C)).obj X ≅
      ((singularHomologyFunctor C n).obj (𝟙_ C)).obj Y where
  hom := ((singularHomologyFunctor C n).obj (𝟙_ C)).map f
  inv := ((singularHomologyFunctor C n).obj (𝟙_ C)).map g
  hom_inv_id := by
    rw [← Functor.map_comp, singularHomology_map_eq_of_homotopy (C := C) hfg n]; simp
  inv_hom_id := by
    rw [← Functor.map_comp, singularHomology_map_eq_of_homotopy (C := C) hgf n]; simp

#print axioms singularHomology_iso_of_homotopyEquiv

/-! ### Tensor product of chain complexes: instances

`HasTensor (singChain C X) (singChain C Y)` requires two instances not automatically
derived from the existing hypotheses:
1. `(curriedTensor C).Additive` — the bifunctor `C ⥤ (C ⥤ C)` respects addition.
   Follows from `MonoidalPreadditive.add_whiskerRight`.
2. `HasCoproducts.{0} C` — the degree-`n` object of the tensor product is a coproduct
   indexed by `{(p,q) : ℕ × ℕ | p + q = n}` (a `Type 0`), so we resize from `HasCoproducts.{v} C`.
-/

instance curriedTensor_additive :
    (MonoidalCategory.curriedTensor C).Additive where
  map_add {X Y} f g := by
    apply NatTrans.ext; funext Z
    exact MonoidalPreadditive.add_whiskerRight f g

instance hasCoproducts_zero_of_v : HasCoproducts.{0} C :=
  hasCoproducts_shrink.{0, v}

/-! ### Eilenberg–Zilber cross product chain map

The cross product `chainCrossProduct` at each bidegree `(p, q)` assembles into a
chain map from the tensor product of singular chain complexes to the singular
chain complex of the product space:
```
  eilenbergZilber : (singChain C X).tensorObj (singChain C Y) ⟶ singChain C (X ⨯ Y)
```
The degree-`n` component maps `⨁_{p+q=n} C_p(X) ⊗ C_q(Y) ⟶ C_n(X × Y)` by
applying `chainCrossProduct` on each summand. The chain map condition follows
from the Leibniz rules (`chainCrossProduct_leibniz`, `_right_zero`, `_left_zero`).
-/

section EilenbergZilber

-- Selective open: `open HomologicalComplex` would bring the `Monoidal` namespace prefix
-- into scope, shadowing `Functor.Monoidal` and breaking `[(forget C).leftAdjoint.Monoidal]`.
open HomologicalComplex (ιTensorObj mapBifunctorDesc ι_mapBifunctorDesc)

/-- The degree-`n` component of the Eilenberg–Zilber map: it is the unique morphism
out of the coproduct `⨁_{p+q=n} C_p(X) ⊗ C_q(Y)` that restricts to `chainCrossProduct`
on each summand. -/
noncomputable def eilenbergZilber_f (X Y : TopCat.{v}) (n : ℕ) :
    ((singChain C X).tensorObj (singChain C Y)).X n ⟶
    (singChain C (X ⨯ Y)).X n :=
  mapBifunctorDesc (fun p q (h : p + q = n) =>
    chainCrossProduct (C := C) h.symm)

/-- Inclusion of the `(p, q)` summand followed by `eilenbergZilber_f` equals
`chainCrossProduct`. -/
lemma ι_eilenbergZilber_f (X Y : TopCat.{v}) (p q n : ℕ) (h : p + q = n) :
    ιTensorObj (singChain C X) (singChain C Y) p q n h ≫
      eilenbergZilber_f (C := C) X Y n =
    chainCrossProduct (C := C) h.symm :=
  ι_mapBifunctorDesc _ _ _ h

/-- The chain map condition for `eilenbergZilber`, on the `(p+1, q+1)` summand.
Dispatches to `chainCrossProduct_leibniz`. -/
lemma eilenbergZilber_comm_case_pq {X Y : TopCat.{v}} (p q n m : ℕ)
    (hpq : (p + 1) + (q + 1) = n) (hnm : n = m + 1) :
    ιTensorObj (singChain C X) (singChain C Y) (p + 1) (q + 1) n hpq ≫
      eilenbergZilber_f (C := C) X Y n ≫ (singChain C (X ⨯ Y)).d n m =
    ιTensorObj (singChain C X) (singChain C Y) (p + 1) (q + 1) n hpq ≫
      ((singChain C X).tensorObj (singChain C Y)).d n m ≫
      eilenbergZilber_f (C := C) X Y m := by
  have hm : m = p + (q + 1) := by omega
  subst hpq; subst hm
  rw [reassoc_of% (ι_eilenbergZilber_f (C := C) X Y (p + 1) (q + 1)
    ((p + 1) + (q + 1)))]
  rw [HomologicalComplex.mapBifunctor.d_eq, Preadditive.add_comp,
    Preadditive.comp_add,
    HomologicalComplex.mapBifunctor.ι_D₁_assoc, HomologicalComplex.mapBifunctor.ι_D₂_assoc]
  rw [HomologicalComplex.mapBifunctor.d₁_eq _ _ _ _ (show (ComplexShape.down ℕ).Rel (p + 1) p
    from by simp [ComplexShape.down_Rel]) (q + 1) (p + (q + 1)) (by simp)]
  rw [HomologicalComplex.mapBifunctor.d₂_eq _ _ _ _ _ (show (ComplexShape.down ℕ).Rel (q + 1) q
    from by simp [ComplexShape.down_Rel]) (p + (q + 1))
    (show (p + 1) + q = p + (q + 1) by omega)]
  simp only [Category.assoc, ι_eilenbergZilber_f,
    show (ComplexShape.down ℕ).ε₁ (ComplexShape.down ℕ) (ComplexShape.down ℕ) (p + 1, q + 1) = 1
    from rfl, one_smul, Preadditive.zsmul_comp, Preadditive.comp_zsmul]
  convert chainCrossProduct_leibniz (C := C) (X := X) (Y := Y) p q using 1
  congr 1
  · simp [MonoidalCategory.curriedTensor]
  · rw [Units.smul_def, Preadditive.zsmul_comp, Category.assoc, ι_eilenbergZilber_f]
    congr 1
    simp [ComplexShape.ε₂, ComplexShape.ε]

/-- The chain map condition for `eilenbergZilber`, on the `(p+1, 0)` summand.
Dispatches to `chainCrossProduct_leibniz_right_zero`. -/
lemma eilenbergZilber_comm_case_p0 {X Y : TopCat.{v}} (p n m : ℕ)
    (hpq : (p + 1) + 0 = n) (hnm : n = m + 1) :
    ιTensorObj (singChain C X) (singChain C Y) (p + 1) 0 n hpq ≫
      eilenbergZilber_f (C := C) X Y n ≫ (singChain C (X ⨯ Y)).d n m =
    ιTensorObj (singChain C X) (singChain C Y) (p + 1) 0 n hpq ≫
      ((singChain C X).tensorObj (singChain C Y)).d n m ≫
      eilenbergZilber_f (C := C) X Y m := by
  have hm : m = p := by omega
  subst hpq; subst hm
  rw [reassoc_of% (ι_eilenbergZilber_f (C := C) X Y (m + 1) 0 (m + 1))]
  rw [HomologicalComplex.mapBifunctor.d_eq, Preadditive.add_comp,
    Preadditive.comp_add,
    HomologicalComplex.mapBifunctor.ι_D₁_assoc, HomologicalComplex.mapBifunctor.ι_D₂_assoc]
  have hd₂ : HomologicalComplex.mapBifunctor.d₂ (singChain C X) (singChain C Y)
      (MonoidalCategory.curriedTensor C) (ComplexShape.down ℕ) (m + 1) 0 m = 0 :=
    HomologicalComplex.mapBifunctor.d₂_eq_zero _ _ _ _ _ _ _
      (fun h => by simp [ComplexShape.down_Rel] at h)
  simp only [hd₂, zero_comp, add_zero]
  rw [HomologicalComplex.mapBifunctor.d₁_eq _ _ _ _ (show (ComplexShape.down ℕ).Rel (m + 1) m
    from by simp [ComplexShape.down_Rel]) 0 m (by simp)]
  change chainCrossProduct _ ≫ _ = (_ • _) ≫ _
  rw [show (ComplexShape.down ℕ).ε₁ (ComplexShape.down ℕ) (ComplexShape.down ℕ) (m + 1, 0) = 1
    from rfl, one_smul, Category.assoc, ι_eilenbergZilber_f]
  convert chainCrossProduct_leibniz_right_zero (C := C) (X := X) (Y := Y) m using 1
  simp [MonoidalCategory.curriedTensor]

/-- The chain map condition for `eilenbergZilber`, on the `(0, q+1)` summand.
Dispatches to `chainCrossProduct_leibniz_left_zero`. -/
lemma eilenbergZilber_comm_case_0q {X Y : TopCat.{v}} (q n m : ℕ)
    (hpq : 0 + (q + 1) = n) (hnm : n = m + 1) :
    ιTensorObj (singChain C X) (singChain C Y) 0 (q + 1) n hpq ≫
      eilenbergZilber_f (C := C) X Y n ≫ (singChain C (X ⨯ Y)).d n m =
    ιTensorObj (singChain C X) (singChain C Y) 0 (q + 1) n hpq ≫
      ((singChain C X).tensorObj (singChain C Y)).d n m ≫
      eilenbergZilber_f (C := C) X Y m := by
  have hm : m = q := by omega
  have hn : n = q + 1 := by omega
  subst hm; subst hn
  rw [reassoc_of% (ι_eilenbergZilber_f (C := C) X Y 0 (m + 1) (m + 1))]
  rw [HomologicalComplex.mapBifunctor.d_eq, Preadditive.add_comp,
    Preadditive.comp_add,
    HomologicalComplex.mapBifunctor.ι_D₁_assoc, HomologicalComplex.mapBifunctor.ι_D₂_assoc]
  have hd₁ : HomologicalComplex.mapBifunctor.d₁ (singChain C X) (singChain C Y)
      (MonoidalCategory.curriedTensor C) (ComplexShape.down ℕ) 0 (m + 1) m = 0 :=
    HomologicalComplex.mapBifunctor.d₁_eq_zero _ _ _ _ _ _ _
      (fun h => by simp [ComplexShape.down_Rel] at h)
  simp only [hd₁, zero_comp, zero_add]
  rw [HomologicalComplex.mapBifunctor.d₂_eq _ _ _ _ _ (show (ComplexShape.down ℕ).Rel (m + 1) m
    from by simp [ComplexShape.down_Rel]) m (by simp)]
  change chainCrossProduct _ ≫ _ = (_ • _) ≫ _
  rw [show (ComplexShape.down ℕ).ε₂ (ComplexShape.down ℕ) (ComplexShape.down ℕ) (0, m + 1) = 1
    from by simp [ComplexShape.ε₂, ComplexShape.ε], one_smul, Category.assoc, ι_eilenbergZilber_f]
  convert chainCrossProduct_leibniz_left_zero (C := C) (X := X) (Y := Y) m using 1
  simp [MonoidalCategory.curriedTensor]

/-- The Eilenberg–Zilber chain map condition: `eilenbergZilber_f` commutes with
the differentials. Proved by case-splitting on the `(p, q)` summand — since
`n = m + 1 ≥ 1` and `p + q = n`, at least one of `p, q` is positive. -/
lemma eilenbergZilber_comm (X Y : TopCat.{v}) (n m : ℕ) (hnm : n = m + 1) :
    eilenbergZilber_f (C := C) X Y n ≫ (singChain C (X ⨯ Y)).d n m =
    ((singChain C X).tensorObj (singChain C Y)).d n m ≫
      eilenbergZilber_f (C := C) X Y m := by
  apply HomologicalComplex.mapBifunctor.hom_ext
  intro p q hpq
  -- hpq : π(p,q) = n, which is definitionally p + q = n
  change p + q = n at hpq
  rcases p with _ | p <;> rcases q with _ | q
  · omega
  · exact eilenbergZilber_comm_case_0q q n m hpq hnm
  · exact eilenbergZilber_comm_case_p0 p n m hpq hnm
  · exact eilenbergZilber_comm_case_pq p q n m hpq hnm

/-- **Eilenberg–Zilber cross product chain map.**

The cross product of singular chains, packaged as a chain map from the tensor
product of singular chain complexes to the singular chain complex of the product:
```
  eilenbergZilber : (singChain C X).tensorObj (singChain C Y) ⟶ singChain C (X ⨯ Y)
```

Degree-`n` component: `⨁_{p+q=n} C_p(X) ⊗ C_q(Y) → C_n(X × Y)` via the
shuffle cross product `chainCrossProduct` on each summand. -/
noncomputable def eilenbergZilber (X Y : TopCat.{v}) :
    (singChain C X).tensorObj (singChain C Y) ⟶ singChain C (X ⨯ Y) where
  f n := eilenbergZilber_f (C := C) X Y n
  comm' n m hnm := by
    have h : n = m + 1 := by rw [ComplexShape.down_Rel] at hnm; omega
    exact eilenbergZilber_comm (C := C) X Y n m h

#print axioms eilenbergZilber
end EilenbergZilber

end HomologyLean.SingularHomology
