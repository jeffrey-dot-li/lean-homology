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

variable (C : Type u) [Category.{v} C] [HasCoproducts C] [Preadditive C]
  [CategoryWithHomology C] [MonoidalCategory C] [SymmetricCategory C]

namespace HomologyLean.SingularHomology

/-! ### Abbreviations -/

/-- The standard topological `p`-simplex. -/
abbrev stdSimplex (p : ℕ) : TopCat :=
  SimplexCategory.toTop.obj (SimplexCategory.mk p)

/-!
Convenience notation for the standard simplex:
- `Δ[p]` (no whitespace ambiguity).
-/
notation "Δ[" p "]" => stdSimplex p

/-- The singular chain complex of X with coefficients in R. -/
abbrev singChain (R : C) (X : TopCat.{v}) : ChainComplex C ℕ :=
  ((singularChainComplexFunctor C).obj R).obj X

/-- A singular n-simplex in X: an n-simplex of the singular simplicial set.
Definitionally `ULift (SimplexCategory.toTop.obj [n] ⟶ X)`. -/
abbrev SingularSimplex (X : TopCat.{v}) (n : ℕ) :=
  (TopCat.toSSet.obj X).obj (Opposite.op (SimplexCategory.mk n))

/-- The coprojection (basis inclusion) for a singular simplex: given a singular
n-simplex `s` in `X`, produce the corresponding "basis element" morphism
`R ⟶ C_n(X; R)` via the coproduct structure of the chain group.

The chain group `(singChain C R X).X n` is definitionally `∐_{σ} R` where
σ ranges over all singular n-simplices in X. -/
def simplexCoprojection (R : C) {X : TopCat.{v}} {n : ℕ}
    (s : SingularSimplex X n) : R ⟶ (singChain C R X).X n :=
  Sigma.ι (fun _ : SingularSimplex X n ↦ R) s

/-- The product of two singular n-simplices: given `s : Δⁿ → X` and `t : Δⁿ → Y`,
form the n-simplex `(s, t) : Δⁿ → X × Y` via the categorical product. -/
def prodSimplex {X Y : TopCat.{v}} {n : ℕ}
    (s : SingularSimplex X n) (t : SingularSimplex Y n) :
    SingularSimplex (X ⨯ Y) n :=
  .up (prod.lift s.down t.down)

/-! ### Simplex-level cross product -/

variable {C}

/-!
### Shuffles as maps between standard simplices

Given a `(p,q)`-shuffle, we will later build the corresponding continuous map
\( \Delta^{p+q} \to \Delta^p \times \Delta^q \).

For now we introduce it as a placeholder; we will implement it next.
-/

/-- The map of standard simplices associated to a shuffle:
`Δ[p+q] ⟶ Δ[p] × Δ[q]`. -/
def shuffleStdSimplexMap {p q : ℕ} (μ : Shuffle p q) :
    Δ[p + q] ⟶ (Δ[p] ⨯ Δ[q]) := by
  sorry



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

/-- The simplex-level cross product: the signed formal sum over all shuffles.

Given a p-simplex s in X and a q-simplex t in Y, produce a morphism
`R ⟶ C_{p+q}(X × Y; R)` (i.e., a "chain" in the abstract categorical sense)
as the signed sum `∑_μ sign(μ) · ι(shuffleSimplex s t μ)` where ι denotes
the coprojection into the free module. -/
def simplexCrossProduct (R : C) {X Y : TopCat.{v}} {p q : ℕ}
    (s : SingularSimplex X p) (t : SingularSimplex Y q) :
    R ⟶ (singChain C R (X ⨯ Y)).X (p + q) :=
  ∑ μ : Shuffle p q, μ.sign • simplexCoprojection C R (shuffleSimplex s t μ)

variable (C)

/-! ### Chain-level cross product -/

variable [MonoidalPreadditive C] [MonoidalClosed C]

/-- The cross product on singular chains:
  `crossProduct R p q : C_p(X; R) ⊗ C_q(Y; R) → C_{p+q}(X × Y; R)`

Defined as the bilinear extension of the simplex-level cross product.
Since it is a morphism out of `⊗` in a monoidal category, bilinearity
is built into the type — the tensor product universally encodes bilinear maps. -/
def crossProduct {X Y : TopCat.{v}} (R : C) [MonObj R] (p q : ℕ) :
    (singChain C R X).X p ⊗ (singChain C R Y).X q ⟶
      (singChain C R (X ⨯ Y)).X (p + q) := by
  let A : SingularSimplex X p → C := fun _ => R
  let B : SingularSimplex Y q → C := fun _ => R
  let leftIso :
      (∐ A) ⊗ (∐ B) ≅
        ∐ fun _s : SingularSimplex X p => R ⊗ (∐ B) :=
    PreservesCoproduct.iso (MonoidalCategory.tensorRight (∐ B)) A
  let rightIso :
        R ⊗ (∐ B) ≅ ∐ fun _t : SingularSimplex Y q => R ⊗ R :=
    PreservesCoproduct.iso (MonoidalCategory.tensorLeft R) B
  exact
    leftIso.hom ≫
      Sigma.desc (fun s =>
        rightIso.hom ≫
          Sigma.desc (fun t => by
          -- R ⊗ R ⟶ (singChain C R (X ⨯ Y)).X (p + q)
            refine MonObj.mul ≫ ?_
            apply simplexCrossProduct (C := C)
              (R := R) (X := X) (Y := Y) (p := p) (q := q) s t
          )
      )

/-! ### Properties of the cross product -/

/-- **Naturality**: The cross product commutes with maps induced on chains.
For `f : X ⟶ X'` and `g : Y ⟶ Y'`, the following diagram commutes:
```
  C_p(X) ⊗ C_q(Y) --×--> C_{p+q}(X × Y)
       |                        |
  f_* ⊗ g_*                (f × g)_*
       |                        |
  C_p(X') ⊗ C_q(Y') --×--> C_{p+q}(X' × Y')
```
-/
theorem crossProduct_natural {X X' Y Y' : TopCat.{v}} (R : C) [MonObj R]
    (f : X ⟶ X') (g : Y ⟶ Y') (p q : ℕ) :
    crossProduct C R p q ≫
      (((singularChainComplexFunctor C).obj R).map (prod.map f g)).f (p + q) =
    ((((singularChainComplexFunctor C).obj R).map f).f p ⊗ₘ
      (((singularChainComplexFunctor C).obj R).map g).f q) ≫
    crossProduct C R p q := by
  let A : SingularSimplex X p → C := fun _ => R
  let B : SingularSimplex Y q → C := fun _ => R
  let leftIso :
      (∐ A) ⊗ (∐ B) ≅
        ∐ fun _s : SingularSimplex X p => R ⊗ (∐ B) :=
    PreservesCoproduct.iso (MonoidalCategory.tensorRight (∐ B)) A
  let rightIso :
      R ⊗ (∐ B) ≅ ∐ fun _t : SingularSimplex Y q => R ⊗ R :=
    PreservesCoproduct.iso (MonoidalCategory.tensorLeft R) B
  -- Extensionality: compare after precomposing with coproduct generators.
  apply (cancel_epi leftIso.inv).1
  refine Sigma.hom_ext _ _ ?_
  intro a
  apply (cancel_epi rightIso.inv).1
  refine Sigma.hom_ext _ _ ?_
  intro b

  -- ⨯ (f(a) ⨂ g(b)) = ⨯(f, g) (⨯ (a ⨂ b))

  -- Remaining goal is the pure-generator (`a`,`b`) naturality statement.
  sorry

/-- **Leibniz rule** (chain map condition): The cross product is compatible
with the boundary operators. For the cross product to assemble into a chain
map from the tensor product complex to the singular complex of the product:
```
  ∂(σ × τ) = (∂σ) × τ + (-1)^{p+1} · σ × (∂τ)
```
Stated with shifted indices `(p+1, q+1)` to avoid natural number subtraction. -/
theorem crossProduct_leibniz {X Y : TopCat.{v}} (R : C) [MonObj R] (p q : ℕ) :
    crossProduct C R (X := X) (Y := Y) (p + 1) (q + 1) ≫
      (singChain C R (X ⨯ Y)).d ((p + 1) + (q + 1)) (p + (q + 1)) =
    ((singChain C R X).d (p + 1) p ⊗ₘ 𝟙 ((singChain C R Y).X (q + 1))) ≫
      crossProduct C R p (q + 1) +
    ((-1 : ℤ) ^ (p + 1)) •
      ((𝟙 ((singChain C R X).X (p + 1)) ⊗ₘ (singChain C R Y).d (q + 1) q) ≫
        crossProduct C R (p + 1) q ≫
        eqToHom (congrArg (singChain C R (X ⨯ Y)).X (by omega))) := sorry

/-- **Normalization**: On 0-simplices (points), the cross product sends
`[x] ⊗ [y]` to `[(x, y)]`. That is, the cross product of two point-simplices
is the point-simplex at the product point.

Requires `R` to be a monoid object (`[MonObj R]`) so that the multiplication
`μ : R ⊗ R → R` mediates between the tensor of coprojections (source `R ⊗ R`)
and the target coprojection (source `R`). In practice, `R` is a ring object
(e.g., `ℤ` in `Ab`), so this is always satisfied. -/
theorem crossProduct_normalized {X Y : TopCat.{v}} (R : C) [MonObj R]
    (x : SingularSimplex X 0) (y : SingularSimplex Y 0) :
    (simplexCoprojection C R x ⊗ₘ simplexCoprojection C R y) ≫
      crossProduct C R 0 0 =
    MonObj.mul ≫ simplexCoprojection C R (prodSimplex x y) := sorry

/-! ## Chain homotopy from the cross product -/

/-- A topological homotopy `H : f ∼ g` between continuous maps `f g : X → Y`
induces a chain homotopy between the chain maps `C_*(f)` and `C_*(g)`.

**Proof sketch**: Use the cross product with the unit interval. The homotopy
H : I × X → Y composed with the cross product C_0(I) ⊗ C_n(X) → C_n(I × X)
gives the chain homotopy operator, using the fundamental class of I as a
1-chain connecting the two endpoints. -/
def singularChain_chainHomotopy_of_homotopy {X Y : TopCat.{v}} {f g : X ⟶ Y}
    (R : C) [MonObj R] (H : ContinuousMap.Homotopy f.hom' g.hom') :
    Homotopy
      (((singularChainComplexFunctor C).obj R).map f)
      (((singularChainComplexFunctor C).obj R).map g) := by
  sorry

/-! ## Homotopy invariance of singular homology -/

/-- Homotopic maps induce equal maps on singular homology.

This follows from `singularChain_chainHomotopy_of_homotopy` via
`Homotopy.homologyMap_eq`. -/
theorem singularHomology_map_eq_of_homotopy {X Y : TopCat.{v}} {f g : X ⟶ Y}
    (R : C) [MonObj R] (H : ContinuousMap.Homotopy f.hom' g.hom') (n : ℕ) :
    ((singularHomologyFunctor C n).obj R).map f =
      ((singularHomologyFunctor C n).obj R).map g := by
  exact (singularChain_chainHomotopy_of_homotopy C R H).homologyMap_eq n

/-! ## Homotopy equivalences induce isomorphisms -/

/-- Homotopy equivalent spaces have isomorphic singular homology.

**Proof sketch**: `H_n(f) ∘ H_n(g) = H_n(g ≫ f) = H_n(𝟙 Y) = 𝟙` by
homotopy invariance and functoriality, and similarly for the other composite. -/
def singularHomology_iso_of_homotopyEquiv {X Y : TopCat.{v}} (R : C) [MonObj R]
    (f : X ⟶ Y) (g : Y ⟶ X)
    (hfg : ContinuousMap.Homotopy (f ≫ g : X ⟶ X).hom' (𝟙 X : X ⟶ X).hom')
    (hgf : ContinuousMap.Homotopy (g ≫ f : Y ⟶ Y).hom' (𝟙 Y : Y ⟶ Y).hom')
    (n : ℕ) :
    ((singularHomologyFunctor C n).obj R).obj X ≅
      ((singularHomologyFunctor C n).obj R).obj Y where
  hom := ((singularHomologyFunctor C n).obj R).map f
  inv := ((singularHomologyFunctor C n).obj R).map g
  hom_inv_id := by
    rw [← Functor.map_comp, singularHomology_map_eq_of_homotopy C R hfg n]; simp
  inv_hom_id := by
    rw [← Functor.map_comp, singularHomology_map_eq_of_homotopy C R hgf n]; simp

end HomologyLean.SingularHomology
