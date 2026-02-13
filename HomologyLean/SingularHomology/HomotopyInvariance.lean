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

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicTopology unitInterval
open scoped MonoidalCategory

universe u v

variable (C : Type u) [Category.{v} C] [HasCoproducts C] [Preadditive C]
  [CategoryWithHomology C] [MonoidalCategory C] [SymmetricCategory C]

namespace HomologyLean.SingularHomology

/-! ### Abbreviations -/

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

/-! ### Shuffles -/

/-- A (p,q)-shuffle: a way to interleave `Fin p` and `Fin q` into `Fin (p + q)`
while preserving the relative order within each factor. Shuffles parametrize
the terms in the Eilenberg-Zilber cross product.

Mathematically, a shuffle is a permutation σ of {0,...,p+q-1} such that
σ(0) < ⋯ < σ(p-1) and σ(p) < ⋯ < σ(p+q-1). We encode this as a pair
of strictly monotone injections whose ranges partition `Fin (p + q)`. -/
structure Shuffle (p q : ℕ) where
  /-- The positions in `Fin (p + q)` assigned to the first factor -/
  left : Fin p → Fin (p + q)
  /-- The positions assigned to the second factor -/
  right : Fin q → Fin (p + q)
  /-- First factor positions are strictly increasing -/
  left_strictMono : StrictMono left
  /-- Second factor positions are strictly increasing -/
  right_strictMono : StrictMono right
  /-- The two sets of positions cover all of `Fin (p + q)` -/
  cover : ∀ i : Fin (p + q), i ∈ Set.range left ∨ i ∈ Set.range right
  /-- The two sets of positions don't overlap -/
  disjoint : Disjoint (Set.range left) (Set.range right)

/-- There are finitely many (p,q)-shuffles: exactly `Nat.choose (p + q) p`. -/
instance Shuffle.instFintype (p q : ℕ) : Fintype (Shuffle p q) := by
  classical
  refine Fintype.ofInjective (fun μ : Shuffle p q => (μ.left, μ.right)) ?_
  intro μ ν h
  cases μ with
  | mk left₁ right₁ left_strictMono₁ right_strictMono₁ cover₁ disjoint₁ =>
    cases ν with
    | mk left₂ right₂ left_strictMono₂ right_strictMono₂ cover₂ disjoint₂ =>
      have hleft : left₁ = left₂ := congrArg Prod.fst h
      have hright : right₁ = right₂ := congrArg Prod.snd h
      subst hleft
      subst hright
      have hleft_strictMono : left_strictMono₁ = left_strictMono₂ := Subsingleton.elim _ _
      have hright_strictMono : right_strictMono₁ = right_strictMono₂ := Subsingleton.elim _ _
      have hcover : cover₁ = cover₂ := Subsingleton.elim _ _
      have hdisjoint : disjoint₁ = disjoint₂ := Subsingleton.elim _ _
      subst hleft_strictMono
      subst hright_strictMono
      subst hcover
      subst hdisjoint
      rfl

/-- The sign of a shuffle: the signature of the permutation of `Fin (p + q)`
that maps the first `p` positions to `μ.left` and the last `q` to `μ.right`.
Equivalently, `(-1)^k` where `k` is the number of inversions. -/
def Shuffle.sign {p q : ℕ} (μ : Shuffle p q) : ℤ := by
  classical
  let e : Fin p ⊕ Fin q ≃ Fin (p + q) :=
    Equiv.ofBijective (Sum.elim μ.left μ.right) <| by
      constructor
      · intro a b h
        cases a with
        | inl i =>
          cases b with
          | inl i' =>
            exact congrArg Sum.inl (μ.left_strictMono.injective h)
          | inr j =>
            exfalso
            have hdisj :
                ∀ x, x ∈ Set.range μ.left → x ∈ Set.range μ.right → False := by
              simpa [Set.disjoint_left] using μ.disjoint
            exact hdisj _ ⟨i, rfl⟩
              ⟨j, h.symm⟩
        | inr j =>
          cases b with
          | inl i =>
            exfalso
            have hdisj :
                ∀ x, x ∈ Set.range μ.left → x ∈ Set.range μ.right → False := by
              simpa [Set.disjoint_left] using μ.disjoint
            exact hdisj _ ⟨i, h.symm⟩
              ⟨j, rfl⟩
          | inr j' =>
            exact congrArg Sum.inr (μ.right_strictMono.injective h)
      · intro i
        rcases μ.cover i with hi | hi
        · rcases hi with ⟨a, rfl⟩
          exact ⟨Sum.inl a, rfl⟩
        · rcases hi with ⟨b, rfl⟩
          exact ⟨Sum.inr b, rfl⟩
  exact
    (Equiv.Perm.sign ((finSumFinEquiv : Fin p ⊕ Fin q ≃ Fin (p + q)).symm.trans e) : ℤ)

/-- `Shuffle.sign` depends only on the two embedding functions `left` and `right`. -/
theorem Shuffle.sign_eq_of_left_right_eq {p q : ℕ} {μ ν : Shuffle p q}
    (hleft : μ.left = ν.left) (hright : μ.right = ν.right) :
    μ.sign = ν.sign := by
  cases μ with
  | mk left₁ right₁ left_strictMono₁ right_strictMono₁ cover₁ disjoint₁ =>
    cases ν with
    | mk left₂ right₂ left_strictMono₂ right_strictMono₂ cover₂ disjoint₂ =>
      subst hleft
      subst hright
      have hleft_strictMono : left_strictMono₁ = left_strictMono₂ := Subsingleton.elim _ _
      have hright_strictMono : right_strictMono₁ = right_strictMono₂ := Subsingleton.elim _ _
      have hcover : cover₁ = cover₂ := Subsingleton.elim _ _
      have hdisjoint : disjoint₁ = disjoint₂ := Subsingleton.elim _ _
      subst hleft_strictMono
      subst hright_strictMono
      subst hcover
      subst hdisjoint
      rfl

/-! ### Simplex-level cross product -/

variable {C}

/-- Given a p-simplex σ in X, a q-simplex τ in Y, and a (p,q)-shuffle μ,
produce a (p+q)-simplex in X × Y by combining σ and τ according to μ.

Geometrically: μ determines a maximal simplex in the standard triangulation
of Δ^p × Δ^q; this maps it into X × Y using σ on the first factor and τ
on the second. -/
def shuffleSimplex {X Y : TopCat.{v}} {p q : ℕ}
    (s : SingularSimplex X p) (t : SingularSimplex Y q) (μ : Shuffle p q) :
    SingularSimplex (X ⨯ Y) (p + q) := by
  let countBelow {n : ℕ} (f : Fin n → Fin (p + q)) (k : Fin (p + q + 1)) : ℕ :=
    (Finset.univ.filter fun i : Fin n => (f i : ℕ) < (k : ℕ)).card
  have countBelow_mono {n : ℕ} (f : Fin n → Fin (p + q)) :
      Monotone (countBelow f) := by
    intro i j hij
    refine Finset.card_le_card ?_
    intro a ha
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ha ⊢
    exact lt_of_lt_of_le ha hij
  let leftIdx : Fin (p + q + 1) → Fin (p + 1) := fun k =>
    ⟨countBelow (n := p) μ.left k, by
      have hle : countBelow (n := p) μ.left k ≤ (Finset.univ : Finset (Fin p)).card :=
        Finset.card_filter_le _ _
      simpa [countBelow] using hle⟩
  let rightIdx : Fin (p + q + 1) → Fin (q + 1) := fun k =>
    ⟨countBelow (n := q) μ.right k, by
      have hle : countBelow (n := q) μ.right k ≤ (Finset.univ : Finset (Fin q)).card :=
        Finset.card_filter_le _ _
      simpa [countBelow] using hle⟩
  have hleftMono : Monotone leftIdx := by
    intro i j hij
    exact Fin.mk_le_mk.mpr ((countBelow_mono (n := p) μ.left) hij)
  have hrightMono : Monotone rightIdx := by
    intro i j hij
    exact Fin.mk_le_mk.mpr ((countBelow_mono (n := q) μ.right) hij)
  let leftOH : Fin (p + q + 1) →o Fin (p + 1) := ⟨leftIdx, hleftMono⟩
  let rightOH : Fin (p + q + 1) →o Fin (q + 1) := ⟨rightIdx, hrightMono⟩
  let n : SimplexCategoryᵒᵖ := Opposite.op (SimplexCategory.mk (p + q))
  let sx : SingularSimplex X (p + q) :=
    (TopCat.toSSet.obj X).map (SimplexCategory.mkHom leftOH).op s
  let tx : SingularSimplex Y (p + q) :=
    (TopCat.toSSet.obj Y).map (SimplexCategory.mkHom rightOH).op t
  let fsx := TopCat.toSSetObjEquiv X n sx
  let ftx := TopCat.toSSetObjEquiv Y n tx
  exact
    (TopCat.toSSetObjEquiv (X ⨯ Y) n).symm
      (((TopCat.prodIsoProd X Y).inv.hom).comp (fsx.prodMk ftx))

/-- Naturality of `TopCat.toSSetObjEquiv` with respect to maps in `TopCat`. -/
theorem toSSetObjEquiv_natural {X X' : TopCat.{v}} (f : X ⟶ X') (n : SimplexCategoryᵒᵖ)
    (x : (TopCat.toSSet.obj X).obj n) :
    TopCat.toSSetObjEquiv X' n ((TopCat.toSSet.map f).app n x) =
      f.hom.comp (TopCat.toSSetObjEquiv X n x) := by
  rfl

/-- Compatibility of `prodIsoProd.inv` with `prodMk` under maps on both factors. -/
theorem prodIsoProd_inv_comp_prodMk_natural
    {X X' Y Y' : TopCat.{v}} {Z : Type v} [TopologicalSpace Z]
    (f : X ⟶ X') (g : Y ⟶ Y') (a : C(Z, X)) (b : C(Z, Y)) :
    ((TopCat.prodIsoProd X' Y').inv.hom).comp ((f.hom.comp a).prodMk (g.hom.comp b)) =
      (prod.map f g).hom.comp (((TopCat.prodIsoProd X Y).inv.hom).comp (a.prodMk b)) := by
  sorry

/-- Naturality of `shuffleSimplex` under maps on both factors. -/
theorem shuffleSimplex_natural {X X' Y Y' : TopCat.{v}} {p q : ℕ}
    (f : X ⟶ X') (g : Y ⟶ Y')
    (s : SingularSimplex X p) (t : SingularSimplex Y q) (μ : Shuffle p q) :
    ((TopCat.toSSet.map (prod.map f g)).app (Opposite.op (SimplexCategory.mk (p + q))))
      (shuffleSimplex s t μ) =
    shuffleSimplex
      (((TopCat.toSSet.map f).app (Opposite.op (SimplexCategory.mk p))) s)
      (((TopCat.toSSet.map g).app (Opposite.op (SimplexCategory.mk q))) t)
      μ := by
  sorry

/-- The unique endomorphism of `⦋0⦌` is the identity. -/
private lemma simplexCategory_hom_mk_const_zero_eq_id :
    (SimplexCategory.Hom.mk (a := SimplexCategory.mk 0) (b := SimplexCategory.mk 0)
      ({ toFun := fun _ : Fin 1 => (0 : Fin 1)
         monotone' := by intro i j _; simp } : Fin 1 →o Fin 1)) =
    𝟙 (SimplexCategory.mk 0) := by
  apply SimplexCategory.Hom.ext
  ext i
  fin_cases i
  rfl

/-- Normalization at degree `(0,0)`: `shuffleSimplex` agrees with pairing points. -/
theorem shuffleSimplex_zero_zero {X Y : TopCat.{v}}
    (s : SingularSimplex X 0) (t : SingularSimplex Y 0) (μ : Shuffle 0 0) :
    shuffleSimplex s t μ =
      (TopCat.toSSetObjEquiv (X ⨯ Y) (Opposite.op (SimplexCategory.mk 0))).symm
        (((TopCat.prodIsoProd X Y).inv.hom).comp
          ((TopCat.toSSetObjEquiv X (Opposite.op (SimplexCategory.mk 0)) s).prodMk
            (TopCat.toSSetObjEquiv Y (Opposite.op (SimplexCategory.mk 0)) t))) := by
  cases μ
  simp [shuffleSimplex, SimplexCategory.mkHom, simplexCategory_hom_mk_const_zero_eq_id]

/-- Face decomposition data needed for the Leibniz rule proof. -/
theorem shuffleSimplex_face_decomposition {X Y : TopCat.{v}} {p q : ℕ}
    (s : SingularSimplex X (p + 1)) (t : SingularSimplex Y (q + 1))
    (μ : Shuffle (p + 1) (q + 1)) (i : Fin ((p + 1) + (q + 1))) :
    (i ∈ Set.range μ.left →
      ∃ μL : Shuffle p (q + 1), True) ∧
    (i ∈ Set.range μ.right →
      ∃ μR : Shuffle (p + 1) q, True) := by
  sorry

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
    crossProduct C R p q := sorry

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
