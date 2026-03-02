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

For now we introduce it as a placeholder; we will implement it next.
-/

/-- The map of standard simplices associated to a shuffle:
`Δ[p+q] ⟶ Δ[p] × Δ[q]`. -/
def shuffleStdSimplexMap {p q : ℕ} (μ : Shuffle p q) :
    Δ[p + q] ⟶ (Δ[p] ⨯ Δ[q]) :=
  prod.lift
    (SimplexCategory.toTop.map (SimplexCategory.Hom.mk (OrderHom.fst.comp μ.1)))
    (SimplexCategory.toTop.map (SimplexCategory.Hom.mk (OrderHom.snd.comp μ.1)))



attribute [simp] CategoryTheory.yoneda

/-- Given a p-simplex σ in X, a q-simplex τ in Y, and a (p,q)-shuffle μ,
produce a (p+q)-simplex in X × Y by combining σ and τ according to μ.

Geometrically: μ determines a maximal simplex in the standard triangulation
of Δ^p × Δ^q; this maps it into X × Y using σ on the first factor and τ
on the second. -/
def shuffleSimplex {X Y : TopCat.{v}} {p q : ℕ}
    (s : SingularSimplex X p) (t : SingularSimplex Y q) (μ : Shuffle p q) :
    SingularSimplex (X ⨯ Y) (p + q) := by
  unfold SingularSimplex
  refine .up ?_
  simp only [yoneda, Functor.op_obj, SimplexCategory.toTop_obj, SimplexCategory.len_mk]
  change Δ[p + q] ⟶ _
  refine shuffleStdSimplexMap (p := p) (q := q) μ ≫ ?_
  apply prod.map s.down t.down

def universalSimplexCrossProduct (p q : ℕ) :
    R ⟶ (singChain (R := R) (X := (Δ[p] ⨯ Δ[q]))).X (p + q) := by
  -- simp [singularSimplexEquivΔ]
  have id_p  := ⟪𝟙 stdSimplex.{v} p ⟫ₛ
  have id_q :=  ⟪𝟙 stdSimplex.{v} q⟫ₛ
  exact ∑ μ : Shuffle p q, μ.sign • simplexCoprojection (shuffleSimplex id_p id_q μ)

/-- The simplex-level cross product: the signed formal sum over all shuffles.

Given a p-simplex s in X and a q-simplex t in Y, produce a morphism
`R ⟶ C_{p+q}(X × Y; R)` (i.e., a "chain" in the abstract categorical sense)
as the signed sum `∑_μ sign(μ) · ι(shuffleSimplex s t μ)` where ι denotes
the coprojection into the free module. -/
def simplexCrossProduct {X Y : TopCat.{v}} {p q : ℕ}
    (s : SingularSimplex X p) (t : SingularSimplex Y q) :
    R ⟶ (singChain (R := R) (X ⨯ Y)).X (p + q) := by
  -- simp [singularSimplexEquivΔ]
  refine universalSimplexCrossProduct p q ≫ ?_
  -- Push the chain on `Δ[p] ⨯ Δ[q]` forward along the map induced by `s` and `t`.
  -- The map `Δ[p] ⨯ Δ[q] ⟶ X ⨯ Y` is `prod.map s.down t.down`.
  exact ((SCF R).map (prod.map s.down t.down)).f (p + q)

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

@[simp] lemma SimplexCategory.default_mk0_eq_id :
    (default : SimplexCategory.mk 0 ⟶ SimplexCategory.mk 0) = 𝟙 _ := by
  ext ⟨j, hj⟩; simp [default, SimplexCategory.Hom.toOrderHom]

@[simp] lemma SimplexCategory.δ_comp_default_mk1 (i : Fin 2) :
    SimplexCategory.δ i ≫ (default : SimplexCategory.mk 1 ⟶ SimplexCategory.mk 0) = 𝟙 _ := by
  ext ⟨j, hj⟩; simp [default, SimplexCategory.Hom.toOrderHom, SimplexCategory.δ]

lemma simplexCrossProduct_zero_right {X Y : TopCat.{v}} {n : ℕ}
    (s : SingularSimplex X n) (c : SingularSimplex Y 0) :
    simplexCrossProduct (C := C) (R := R) s c =
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
      dsimp [shuffleStdSimplexMap]
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

/-- For `p = 0`, the cross product of a `0`-simplex `c` in `X` with an `n`-simplex `s`
in `Y` reduces to a single product simplex `t ↦ (c(*), s(t))`.

There is a unique `(0, n)`-shuffle with sign `1`, so the shuffle sum collapses. -/
lemma simplexCrossProduct_zero_left {X Y : TopCat.{v}} {n : ℕ}
    (c : SingularSimplex X 0) (s : SingularSimplex Y n) :
    simplexCrossProduct (C := C) (R := R) c s =
    simplexCoprojection
      ⟪prod.lift (SimplexCategory.toTop.map default ≫ c.down) s.down⟫ₛ ≫
    eqToHom (by simp) := by
  sorry

lemma crossProduct_natural_pure_tensor {X X' Y Y' : TopCat.{v}} [MonObj R]
    (f : X ⟶ X') (g : Y ⟶ Y') (p q : ℕ) (s : Δ[p] ⟶ X) (t : Δ[q] ⟶ Y) :
    simplexCrossProduct (R := R) (p := p) (q := q)
        ⟪s⟫ₛ ⟪t⟫ₛ ≫
      ((SCF R).map (prod.map f g)).f (p + q) =
    simplexCrossProduct (R := R) (X := X') (Y := Y') (p := p) (q := q)
      ⟪s ≫ f⟫ₛ ⟪t ≫ g⟫ₛ := by
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

/-! The chain-level cross product and homotopy invariance theorems
are in `HomologyLean.SingularHomology.CrossProduct`, specialized to `ModuleCat R`. -/


end HomologyLean.SingularHomology
