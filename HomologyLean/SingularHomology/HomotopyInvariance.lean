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
import Mathlib.CategoryTheory.Monoidal.Closed.Basic
import Mathlib.CategoryTheory.Monoidal.Limits.Preserves
import Mathlib.CategoryTheory.Monoidal.Mon_
import Mathlib.GroupTheory.Perm.Sign
import Mathlib.Topology.Category.TopCat.Limits.Products
import HomologyLean.SingularHomology.Shuffle
import HomologyLean.SingularHomology.SumInvolution

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicTopology unitInterval
open scoped MonoidalCategory

universe u v

variable {C : Type u} [Category.{v} C] [HasCoproducts C] [Preadditive C] [CategoryWithHomology C]
   [MonoidalCategory C] [SymmetricCategory C] [MonoidalPreadditive C] [MonoidalClosed C]

namespace HomologyLean.SingularHomology

variable {R : C}

/-! ### Abbreviations -/

/-- The standard topological `p`-simplex. -/
abbrev stdSimplex (p : ℕ) : TopCat.{v} :=
  SimplexCategory.toTop.obj (SimplexCategory.mk p)

/-!
Convenience notation for the standard simplex:
- `Δ[p]` (no whitespace ambiguity).
-/
notation "Δ[" p "]" => stdSimplex p
abbrev SCF (R : C) : TopCat ⥤ ChainComplex C ℕ :=
  (singularChainComplexFunctor C).obj R

/-- The singular chain complex of X with coefficients in R. -/
abbrev singChain (X : TopCat.{v}) : ChainComplex C ℕ :=
  ((singularChainComplexFunctor C).obj R).obj X

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

/-- The `n`-chains of `X` are the coproduct of copies of `R` indexed by maps `Δ[n] ⟶ X`. -/
noncomputable def singChain_X_iso_sigma (X : TopCat.{v}) (n : ℕ) :
    (singChain (C := C) (R := R) X).X n ≅ (∐ fun _f : (Δ[n] ⟶ X) => R) := by
  classical
  -- The chain group is definitionally a coproduct indexed by `SingularSimplex X n`;
  -- we reindex it using `singularSimplexEquivΔ`.
  change (∐ fun _s : SingularSimplex X n => R) ≅ (∐ fun _f : (Δ[n] ⟶ X) => R)
  exact
    Sigma.whiskerEquiv (C := C)
      (f := fun _s : SingularSimplex X n => R)
      (g := fun _f : (Δ[n] ⟶ X) => R)
      (singularSimplexEquivΔ (X := X) n)
      (fun _ => Iso.refl R)

/-- Functor `TopCat ⥤ Type` sending `X` to its `p`-simplices (`SingularSimplex X p`). -/
noncomputable def singularSimplexFunctor (p : ℕ) : TopCat.{v} ⥤ Type v where
  obj X := SingularSimplex X p
  map {X X'} f s := ⟪s.down ≫ f⟫ₛ
  map_id X := by funext s; cases s; rfl
  map_comp {X Y Z} f g := by funext s; cases s; simp [Category.assoc]

/-- The "coproduct-based free" functor `Type v ⥤ C`, sending `A ↦ ∐ (fun _ : A => R)`.
Functorial action sends `f : A → B` to the map induced by `Sigma.desc`/`Sigma.ι`. -/
noncomputable def coprodFreeFunctor : Type v ⥤ C where
  obj A := ∐ fun _ : A => R
  map {A B} f := Sigma.desc (fun a => Sigma.ι (fun _ : B => R) (f a))
  map_id A := by ext a : 1; simp
  map_comp {A B D} f g := by ext a : 1; simp

/-- The degreewise chain group functor `SCF R ⋙ eval p` is naturally isomorphic to
`singularSimplexFunctor p ⋙ coprodFreeFunctor`.

Both send `X` to `∐ (fun _ : SingularSimplex X p => R)` and push forward simplices
along continuous maps, but are constructed through different code paths
(`singularChainComplexFunctor` vs direct `Sigma.desc`/`Sigma.ι`). -/
noncomputable def chainGroupIsoCoprodFree (p : ℕ) :
    SCF R ⋙ HomologicalComplex.eval C (ComplexShape.down ℕ) p ≅
      singularSimplexFunctor p ⋙ coprodFreeFunctor (R := R) :=
  NatIso.ofComponents
    (fun X => Iso.refl _)
    (fun {X Y} f => by
      dsimp
      simp only [Category.comp_id, Category.id_comp]
      dsimp [SCF, singularChainComplexFunctor, SSet.singularChainComplexFunctor, coprodFreeFunctor]
      apply CategoryTheory.Limits.Sigma.hom_ext
      intro a
      simp only [CategoryTheory.Limits.Sigma.ι_comp_map', Category.id_comp]
      erw [CategoryTheory.Limits.Sigma.ι_desc]
      rfl
    )

/-- The coprojection (basis inclusion) for a singular simplex: given a singular
n-simplex `s` in `X`, produce the corresponding "basis element" morphism
`R ⟶ C_n(X; R)` via the coproduct structure of the chain group.

The chain group `(singChain (C := C) (R := R) X).X n` is definitionally `∐_{σ} R` where
σ ranges over all singular n-simplices in X. -/
abbrev simplexCoprojection {X : TopCat.{v}} {n : ℕ}
    (s : SingularSimplex X n) : R ⟶ (singChain (C := C) (R := R) X).X n :=
  Sigma.ι (fun _ : SingularSimplex X n ↦ R) s

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
def shuffleSimplex {X Y : TopCat.{v}} {p q n : ℕ} (hn : n = p + q)
    (s : SingularSimplex X p) (t : SingularSimplex Y q) (μ : Shuffle p q) :
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
def universalSimplexCrossProduct (p q : ℕ) {n : ℕ} (hn : n = p + q) :
    R ⟶ (singChain (R := R) (X := (Δ[p] ⨯ Δ[q]))).X n :=
  ∑ μ : Shuffle p q, μ.sign • simplexCoprojection
    (shuffleSimplex hn ⟪𝟙 stdSimplex.{v} p ⟫ₛ ⟪𝟙 stdSimplex.{v} q⟫ₛ μ)

/-- The simplex-level cross product: the signed formal sum over all shuffles.

Given a p-simplex s in X and a q-simplex t in Y, produce a morphism
`R ⟶ C_n(X × Y; R)` (where `n = p + q`) as the signed sum
`∑_μ sign(μ) · ι(shuffleSimplex s t μ)` where ι denotes the coprojection
into the free module.

The `n` parameter with proof `hn : n = p + q` avoids `eqToHom` casts
when `p + q` is not definitionally equal to the desired index. -/
def simplexCrossProduct {X Y : TopCat.{v}} {p q n : ℕ} (hn : n = p + q)
    (s : SingularSimplex X p) (t : SingularSimplex Y q) :
    R ⟶ (singChain (R := R) (X ⨯ Y)).X n :=
  universalSimplexCrossProduct p q hn ≫
    ((SCF R).map (prod.map s.down t.down)).f n

/-- For `q = 0`, the cross product of an `n`-simplex `s` in `X` with a `0`-simplex `c`
in `Y` reduces to a single product simplex `t ↦ (s(t), c(*))`.

There is a unique `(n, 0)`-shuffle with sign `1`, so the shuffle sum collapses. -/
instance Unique_Shuffle_n_0 {n : ℕ} : Unique (Shuffle n 0) where
  default := ⟨⟨fun i => (i, 0), fun i j h => ⟨h, by simp⟩⟩, fun i j h => by simpa using h⟩
  uniq := fun ⟨⟨f, hf⟩, hinj⟩ => by
    apply Subtype.ext
    apply OrderHom.ext
    funext i
    ext
    · have hmono : StrictMono (fun i => (f i).1) := by
        intro a b hab
        have h_le := hf hab.le
        have h_neq : f a ≠ f b := fun h => hab.ne (hinj h)
        have h_le_1 : (f a).1 ≤ (f b).1 := h_le.1
        cases eq_or_lt_of_le h_le_1 with
        | inl heq =>
          exfalso
          apply h_neq
          ext
          · exact congrArg Fin.val heq
          · simp
        | inr hlt => exact hlt
      have heq : ∀ i, (f i).1 = i := by
        intro i
        exact le_antisymm (StrictMono.le_id hmono i) (StrictMono.id_le hmono i)
      exact congrArg Fin.val (heq i)
    · simp

instance Unique_Shuffle_0_n {n : ℕ} : Unique (Shuffle 0 n) where
  default := ⟨⟨fun i => (0, i.cast (by omega)),
    fun i j h => ⟨by simp, by simpa using h⟩⟩,
    fun i j h => by ext; simpa using congrArg (Fin.val ∘ Prod.snd) h⟩
  uniq := fun ⟨⟨f, hf⟩, hinj⟩ => by
    apply Subtype.ext; apply OrderHom.ext; funext i
    have hmono : StrictMono (fun i => (f i).2) := by
      intro a b hab
      have h_neq : f a ≠ f b := fun h => hab.ne (hinj h)
      cases eq_or_lt_of_le (hf hab.le).2 with
      | inl heq =>
        exact absurd (Prod.ext (by simp [Fin.eq_zero])
          (Fin.ext (congrArg Fin.val heq))) h_neq
      | inr hlt => exact hlt
    let g : Fin (n + 1) → Fin (n + 1) := fun j => (f (j.cast (by omega))).2
    have hg : StrictMono g := fun a b h =>
      hmono (show a.cast _ < b.cast _ by exact_mod_cast h)
    have hg_eq : ∀ j, g j = j :=
      fun j => le_antisymm (StrictMono.le_id hg j) (StrictMono.id_le hg j)
    have hcast : ∀ i : Fin (0 + n + 1),
        (i.cast (show 0 + n + 1 = n + 1 by omega)).cast
          (show n + 1 = 0 + n + 1 by omega) = i :=
      fun i => Fin.ext (by simp)
    have h2 : (f i).2 = i.cast (by omega) := by
      have := hg_eq (i.cast (by omega))
      simp only [g, hcast] at this; exact this
    exact Prod.ext (Fin.eq_zero _) h2

@[simp] lemma SimplexCategory.default_mk0_eq_id :
    (default : SimplexCategory.mk 0 ⟶ SimplexCategory.mk 0) = 𝟙 _ := by
  ext ⟨j, hj⟩; simp [default, SimplexCategory.Hom.toOrderHom]

@[simp] lemma SimplexCategory.δ_comp_default_mk1 (i : Fin 2) :
    SimplexCategory.δ i ≫ (default : SimplexCategory.mk 1 ⟶ SimplexCategory.mk 0) = 𝟙 _ := by
  ext ⟨j, hj⟩; simp [default, SimplexCategory.Hom.toOrderHom, SimplexCategory.δ]

lemma simplexCrossProduct_zero_right {X Y : TopCat.{v}} {n : ℕ}
    (s : SingularSimplex X n) (c : SingularSimplex Y 0) :
    simplexCrossProduct (C := C) (R := R) rfl s c =
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
    simplexCrossProduct (C := C) (R := R) (show n = 0 + n by omega) c s =
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

lemma crossProduct_natural_pure_tensor {X X' Y Y' : TopCat.{v}} [MonObj R]
    (f : X ⟶ X') (g : Y ⟶ Y') {p q n : ℕ} (hn : n = p + q)
    (s : Δ[p] ⟶ X) (t : Δ[q] ⟶ Y) :
    simplexCrossProduct (R := R) hn ⟪s⟫ₛ ⟪t⟫ₛ ≫
      ((SCF R).map (prod.map f g)).f n =
    simplexCrossProduct (R := R) hn ⟪s ≫ f⟫ₛ ⟪t ≫ g⟫ₛ := by
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
      ((SCF R).map (prod.map s t)).f (p + q) ≫
        ((SCF R).map (prod.map f g)).f (p + q) =
      ((SCF R).map ((prod.map s t) ≫ (prod.map f g))).f (p + q) := by
    have := congrArg (fun φ => φ.f (p + q))
      (Functor.map_comp (SCF R) (prod.map s t) (prod.map f g)).symm
    simpa [HomologicalComplex.comp_f] using this
  -- Finish by rewriting the LHS using `hmap` and `hprod`.
  simp [hmap, hprod]

/-- The boundary map of `singChain` equals the alternating face map differential.
This avoids unfolding `singChain`/`SCF` through deep functor composition. -/
lemma singChain_d_eq_alternatingFaceMapObjD (X : TopCat.{v}) (n : ℕ) {m : ℕ} (hm : m = n + 1) :
    (singChain (C := C) (R := R) X).d m n =
    eqToHom (congrArg (singChain (C := C) (R := R) X).X hm) ≫
    AlternatingFaceMapComplex.objD
      (((SimplicialObject.whiskering (Type v) C).obj
        ((sigmaConst (C := C)).obj R)).obj (TopCat.toSSet.obj X)) n := by
  subst hm
  simp only [eqToHom_refl, Category.id_comp, singChain]
  dsimp [singularChainComplexFunctor, SSet.singularChainComplexFunctor]
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
    simplexCoprojection (C := C) (R := R) s ≫
      eqToHom (congrArg (singChain (C := C) (R := R) X).X h) ≫
      (((SimplicialObject.whiskering (Type v) C).obj ((sigmaConst (C := C)).obj R)).obj
        (TopCat.toSSet.obj X)).δ i =
    simplexCoprojection (C := C) (R := R)
      ((TopCat.toSSet.obj X).δ i (h ▸ s)) := by
  subst h
  simp only [eqToHom_refl, Category.id_comp]
  dsimp [simplexCoprojection, singChain, SCF, singularChainComplexFunctor,
    SSet.singularChainComplexFunctor, SimplicialObject.δ, SimplicialObject.whiskering]
  erw [CategoryTheory.Limits.Sigma.ι_comp_map']
  simp

/-- Naturality of `simplexCoprojection` w.r.t. the singular chain functor:
pushing a continuous map `f : X ⟶ Y` through the coprojection reindexes the
simplex by postcomposition, `σ ↦ σ ≫ f`. -/
@[simp] lemma simplexCoprojection_comp_SCF_map {X Y : TopCat.{v}} {n : ℕ}
    (s : SingularSimplex X n) (f : X ⟶ Y) :
    simplexCoprojection (C := C) (R := R) s ≫ ((SCF R).map f).f n =
    simplexCoprojection ⟪s.down ≫ f⟫ₛ := by
  dsimp [simplexCoprojection, SCF, singularChainComplexFunctor,
    SSet.singularChainComplexFunctor]
  erw [CategoryTheory.Limits.Sigma.ι_comp_map']
  simp only [Category.id_comp]; congr 1

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
    universalSimplexCrossProduct (C := C) (R := R) (p + 1) (q + 1) (hn := rfl) ≫
      (singChain (C := C) (R := R) (Δ[p + 1] ⨯ Δ[q + 1])).d
        ((p + 1) + (q + 1)) (p + (q + 1)) =
    ∑ j : Fin (p + 2),
      ((-1 : ℤ) ^ (j : ℕ)) •
        simplexCrossProduct (C := C) (R := R) rfl
          ⟪SimplexCategory.toTop.map (SimplexCategory.δ j)⟫ₛ
          ⟪𝟙 Δ[q + 1]⟫ₛ +
    ((-1 : ℤ) ^ (p + 1)) •
      ∑ j : Fin (q + 2),
        ((-1 : ℤ) ^ (j : ℕ)) •
          simplexCrossProduct (C := C) (R := R) (by omega)
            ⟪𝟙 Δ[p + 1]⟫ₛ
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
  -- Distribute ≫ ((SCF R).map ...).f into the ∑
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
/-! The chain-level cross product and homotopy invariance theorems
are in `HomologyLean.SingularHomology.CrossProduct`, specialized to `ModuleCat R`. -/


end HomologyLean.SingularHomology
