/-
  Eilenberg–Zilber cross product for simplicial sets.

  The Eilenberg–Zilber map is a natural chain map
    C_*(S) ⊗ C_*(T) ⟶ C_*(S × T)
  for simplicial sets S, T, defined as a signed sum over (p,q)-shuffles.

  This file works at the level of SSet (simplicial sets) rather than TopCat.
  The topological version is recovered by precomposing with TopCat.toSSet.
-/
import Mathlib.AlgebraicTopology.SingularHomology.Basic
import Mathlib.Algebra.Homology.Homotopy
import Mathlib.CategoryTheory.Monoidal.Category
import Mathlib.CategoryTheory.Monoidal.Preadditive
import Mathlib.CategoryTheory.Monoidal.Linear
import HomologyLean.CategoryTheory.SubTensorHom
import Mathlib.CategoryTheory.Monoidal.Closed.Basic
import Mathlib.CategoryTheory.Monoidal.Limits.Preserves
import Mathlib.CategoryTheory.Monoidal.Mon_
import Mathlib.CategoryTheory.Monoidal.Types.Coyoneda
import Mathlib.GroupTheory.Perm.Sign
import HomologyLean.SingularHomology.Shuffle
import HomologyLean.SingularHomology.SumInvolution
import HomologyLean.SingularHomology.Representable
import Mathlib.Algebra.Homology.Monoidal
import Mathlib.AlgebraicTopology.SimplicialSet.Monoidal
import Mathlib.AlgebraicTopology.SimplicialSet.ProdStdSimplex
import Mathlib.AlgebraicTopology.SimplicialSet.SimplicialHomotopy

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicTopology
open scoped MonoidalCategory Simplicial
open Representable

universe u v w

variable {C : Type u} [Category.{v} C] [HasCoproducts C] [Preadditive C] [CategoryWithHomology C]
   [MonoidalCategory C] [SymmetricCategory C] [MonoidalPreadditive C] [MonoidalClosed C]
   [HasForget.{v} C] [MonoidalUnitorRepresentable (C := C)]
   [(forget C).IsRightAdjoint] [(forget C).leftAdjoint.Monoidal]
   [(forget C).LaxMonoidal] [(Adjunction.ofIsRightAdjoint (forget C)).IsMonoidal]
   [NatTrans.IsMonoidal (MonoidalUnitorRepresentable.forgetIso (C := C)).hom]
   [MonoidalLinear ℤ C]

namespace HomologyLean.SingularHomology.SSetEZ

/-! ### Abbreviations -/

/-- The free functor left adjoint to `forget C`. -/
private abbrev Free : Type v ⥤ C := (forget C).leftAdjoint

/-! ### Free-forgetful equivalences -/

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
  (Functor.Monoidal.μIso Free A B).symm.homFromEquiv.symm |>.trans
  ((Adjunction.ofIsRightAdjoint (forget C)).homEquiv (A × B) M) |>.trans
  (Equiv.arrowCongr (Equiv.refl _)
    ((MonoidalUnitorRepresentable.forgetIso (C := C)).app M).toEquiv)

/-- The singular chain complex functor on SSet with coefficients in 𝟙_ C. -/
private abbrev SCF (C : Type u) [Category.{v} C] [HasCoproducts.{w} C] [Preadditive C]
    [MonoidalCategory C] : SSet.{w} ⥤ ChainComplex C ℕ :=
  (SSet.singularChainComplexFunctor.{w} C).obj (𝟙_ C)

/-- The singular chain complex of a simplicial set S with coefficients in 𝟙_ C. -/
private abbrev singChain (C : Type u) [Category.{v} C] [HasCoproducts.{w} C] [Preadditive C]
    [MonoidalCategory C] (S : SSet.{w}) : ChainComplex C ℕ :=
  (SCF C).obj S

-- `⊗` is ambiguous between `C` and `SSet` when both monoidal structures are in scope.
local notation:50 S " ⊗ₛ " T => (MonoidalCategory.tensorObj (C := SSet) S T)

/-! ### SSet.yonedaEquiv simp lemmas -/

@[simp] lemma yonedaEquiv_symm_app {X : SSet.{v}} {n : SimplexCategory}
    (x : X.obj (Opposite.op n)) {m : SimplexCategoryᵒᵖ}
    (f : m.unop ⟶ n) :
    (SSet.yonedaEquiv.symm x).app m (SSet.stdSimplex.objEquiv.symm f) =
      X.map f.op x :=
  rfl

/-- The product of two n-simplices: given `s ∈ S_n` and `t ∈ T_n`,
form the n-simplex in `S ⊗ T`. The monoidal product in `SSet` is levelwise,
so this is just the pair `(s, t)`. -/
def prodSimplex {S T : SSet.{w}} {n : ℕ}
    (s : S _⦋n⦌) (t : T _⦋n⦌) : (S ⊗ₛ T) _⦋n⦌ :=
  (s, t)

/-! ### Shuffle simplices -/

/-- Given a p-simplex `s` in `S`, a q-simplex `t` in `T`, and a (p,q)-shuffle `μ`,
produce an n-simplex in `S ⊗ T` (where `n = p + q`).

The shuffle `μ` determines a monotone map `Fin (p+q+1) →o Fin (p+1) × Fin (q+1)`.
We apply the two projections as `SimplexCategory` morphisms to `s` and `t` respectively,
then pair the results in the levelwise product `(S ⊗ T) _⦋p+q⦌`. -/
def shuffleSimplex {S T : SSet.{w}} {p q n : ℕ}
    (s : S _⦋p⦌) (t : T _⦋q⦌) (μ : Shuffle p q)
    (hn : n = p + q := by omega) :
    (S ⊗ₛ T) _⦋n⦌ := by
  subst hn
  -- Explicit `let` bindings needed: `SimplexCategory.Hom.mk` has implicit
  -- `{a b : SimplexCategory}` that Lean can't infer when inlined into the
  -- tuple, because the elaborator tries to unify both `S.map` and `T.map`
  -- simultaneously and can't resolve which `SimplexCategory` objects go where.
  let fstHom : (⦋p + q⦌ : SimplexCategory) ⟶ ⦋p⦌ :=
    SimplexCategory.Hom.mk (OrderHom.fst.comp μ.1)
  let sndHom : (⦋p + q⦌ : SimplexCategory) ⟶ ⦋q⦌ :=
    SimplexCategory.Hom.mk (OrderHom.snd.comp μ.1)
  exact (S.map fstHom.op s, T.map sndHom.op t)

/-! ### Simplex-level cross product -/

/-- The coprojection (basis inclusion) for a simplex: given an n-simplex `s` in `S`,
produce the corresponding basis element `𝟙_ C ⟶ C_n(S; 𝟙_ C)` via the coproduct. -/
private abbrev simplexCoprojection {S : SSet.{w}} {n : ℕ}
    (s : S _⦋n⦌) : 𝟙_ C ⟶ (singChain C S).X n :=
  Sigma.ι (fun _ : S _⦋n⦌ ↦ 𝟙_ C) s

/-- The universal simplex-level cross product on the standard simplices.

The signed formal sum `∑_μ sign(μ) · ι(shuffleSimplex id_p id_q μ)` over all
(p,q)-shuffles, where `id_p` and `id_q` are the identity simplices of `Δ[p]`
and `Δ[q]`. -/
def universalSimplexCrossProduct (p q : ℕ) {n : ℕ} (hn : n = p + q := by omega) :
    𝟙_ C ⟶ (singChain C (Δ[p] ⊗ₛ Δ[q])).X n :=
  ∑ μ : Shuffle p q, μ.sign • simplexCoprojection
    (shuffleSimplex (SSet.stdSimplex.objEquiv.symm (𝟙 ⦋p⦌))
      (SSet.stdSimplex.objEquiv.symm (𝟙 ⦋q⦌)) μ hn)

local notation:50 f " ⊗ₘₛ " g =>
  (MonoidalCategory.tensorHom (C := SSet) f g)

/-- The simplex-level cross product: the signed formal sum over all shuffles.

Given a p-simplex `s` in `S` and a q-simplex `t` in `T`, produce a morphism
`𝟙_ C ⟶ C_n(S ⊗ T; 𝟙_ C)` (where `n = p + q`) by composing the universal
cross product on `Δ[p] ⊗ Δ[q]` with the functorial map induced by
`yonedaEquiv.symm s ⊗ yonedaEquiv.symm t : Δ[p] ⊗ Δ[q] ⟶ S ⊗ T`. -/
def simplexCrossProduct {S T : SSet.{w}} {p q n : ℕ}
    (s : S _⦋p⦌) (t : T _⦋q⦌)
    (hn : n = p + q := by omega) :
    𝟙_ C ⟶ (singChain C (S ⊗ₛ T)).X n :=
  universalSimplexCrossProduct p q hn ≫
    ((SCF C).map (SSet.yonedaEquiv.symm s ⊗ₘₛ SSet.yonedaEquiv.symm t)).f n

/-- Variant of `simplexCrossProduct` as an explicit set-level map:
takes a pair `(s, t)` of simplices and returns an element of
`𝟙_ C ⟶ C_n(S ⊗ T; 𝟙_ C)` (where `n = p + q`). -/
def simplexCrossProduct' {S T : SSet.{w}} {p q n : ℕ}
    (hn : n = p + q := by omega) :
    S _⦋p⦌ × T _⦋q⦌ → Hom[𝟙_ C |-].obj ((singChain C (S ⊗ₛ T)).X n) :=
  fun ⟨s, t⟩ => simplexCrossProduct s t hn

/-! ### Chain group equivalences -/

/-- The degree-`p` chain group `(singChain C S).X p` is isomorphic to
`Free.obj (S _⦋p⦌)`, the free object on the set of `p`-simplices.

For SSet, the chain group is definitionally `∐_{σ : S _⦋p⦌} 𝟙_ C`, so
this is just `sigmaConstIsoFree` applied pointwise. -/
noncomputable def chainGroupIsoFree {S : SSet.{v}} (p : ℕ) :
    (singChain C S).X p ≅ Free.obj (S _⦋p⦌) :=
  sigmaConstIsoFree.app (S _⦋p⦌)

/-- The hom-set equivalence for the tensor of chain groups: morphisms
`C_p(S) ⊗ C_q(T) ⟶ M` in `C` correspond bijectively to set-level maps
`S _⦋p⦌ × T _⦋q⦌ → Hom(𝟙_ C, M)`.

Obtained by transporting `freeTensorHomEquiv` along `chainGroupIsoFree`,
which identifies `C_p(S) ≅ Free(S _⦋p⦌)`. -/
noncomputable def chainTensorHomEquiv {S T : SSet.{v}} {p q : ℕ} (M : C) :
    ((singChain C S).X p ⊗ (singChain C T).X q ⟶ M) ≃
    (S _⦋p⦌ × T _⦋q⦌ → Hom[𝟙_ C |-].obj M) :=
  (MonoidalCategory.tensorIso (chainGroupIsoFree (C := C) p)
    (chainGroupIsoFree (C := C) q)).symm.homFromEquiv.symm |>.trans
  (freeTensorHomEquiv (S _⦋p⦌) (T _⦋q⦌) M)

/-! ### Chain-level cross product -/

/-- The cross product on chain groups:
`C_p(S; 𝟙_ C) ⊗ C_q(T; 𝟙_ C) ⟶ C_n(S ⊗ T; 𝟙_ C)` (where `n = p + q`).

Defined by lifting the simplex-level cross product `simplexCrossProduct'` via
`chainTensorHomEquiv`. -/
def chainCrossProduct {S T : SSet.{v}} {p q n : ℕ}
    (hn : n = p + q := by omega) :
    (singChain C S).X p ⊗ (singChain C T).X q ⟶
    (singChain C (S ⊗ₛ T)).X n :=
  (chainTensorHomEquiv _).symm (simplexCrossProduct' hn)

/-- Applying `chainTensorHomEquiv` to `chainCrossProduct` recovers
`simplexCrossProduct'`: the chain-level cross product is the unique lift of
the simplex-level cross product. -/
@[simp]
lemma chainCrossProduct.spec {S T : SSet.{v}} {p q n : ℕ}
    (hn : n = p + q := by omega) :
    chainTensorHomEquiv (S := S) (T := T) _
      (chainCrossProduct (C := C) hn) = simplexCrossProduct' hn :=
  (chainTensorHomEquiv _).right_inv (simplexCrossProduct' hn)

/-- Two morphisms out of `C_p(S) ⊗ C_q(T)` are equal iff they agree on all pairs
of simplex coprojections. This is the tensor analogue of `Sigma.hom_ext`. -/
lemma chainCrossProduct.ext {S T : SSet.{v}} {p q : ℕ} {M : C}
    {f g : (singChain C S).X p ⊗ (singChain C T).X q ⟶ M}
    (h : chainTensorHomEquiv M f = chainTensorHomEquiv M g) : f = g :=
  (chainTensorHomEquiv M).injective h

/-! ### Free generator lemmas -/

/-- The "free generator" morphism: for `a : A`, the morphism `𝟙_ C ⟶ Free.obj A`
obtained by applying `forgetIso` to the adjunction unit at `a`.
Represents the inclusion of the generator `a` into the free object. -/
private noncomputable abbrev freeGen {A : Type v} (a : A) : 𝟙_ C ⟶ Free.obj A :=
  (MonoidalUnitorRepresentable.forgetIso (C := C)).hom.app (Free.obj A)
    ((Adjunction.ofIsRightAdjoint (forget C)).unit.app A a)

/-- The free generator at `s`, mapped through `chainGroupIsoFree.inv`,
equals the coproduct injection `simplexCoprojection s`. -/
private lemma freeGen_chainGroupIsoFree {S : SSet.{v}} {p : ℕ}
    (s : S _⦋p⦌) :
    freeGen (C := C) s ≫ (chainGroupIsoFree (C := C) p).inv =
    simplexCoprojection s := by
  simp only [chainGroupIsoFree]
  simp only [sigmaConstIsoFree]
  dsimp only [freeGen]
  set φ := ((Adjunction.ofIsRightAdjoint (forget C)).leftAdjointUniq
    ((sigmaConstAdj (𝟙_ C)).ofNatIsoRight MonoidalUnitorRepresentable.forgetIso.symm)).hom.app
    (S _⦋p⦌)
  have hnat := congr_fun (MonoidalUnitorRepresentable.forgetIso (C := C) |>.hom.naturality φ)
    ((Adjunction.ofIsRightAdjoint (forget C)).unit.app (S _⦋p⦌) s)
  simp only [types_comp_apply] at hnat
  dsimp [coyoneda] at hnat
  erw [← hnat]; clear hnat
  change MonoidalUnitorRepresentable.forgetIso.hom.app _
    (((Adjunction.ofIsRightAdjoint (forget C)).unit.app _ ≫ (forget C).map φ) s) = _
  rw [Adjunction.unit_leftAdjointUniq_hom_app]
  simp only [Adjunction.ofNatIsoRight, Adjunction.mkOfHomEquiv_unit_app]
  simp only [Equiv.trans_apply, Adjunction.equivHomsetRightOfNatIso]
  dsimp only [Equiv.coe_fn_mk]
  rw [Adjunction.homEquiv_unit]
  simp only [types_comp_apply]
  dsimp [coyoneda]
  simp only [Category.comp_id]
  change (MonoidalUnitorRepresentable.forgetIso (C := C)).hom.app _
    ((MonoidalUnitorRepresentable.forgetIso (C := C)).inv.app _
      ((sigmaConstAdj (𝟙_ C)).unit.app _ s)) = _
  simp only [← types_comp_apply (MonoidalUnitorRepresentable.forgetIso.inv.app _)
    (MonoidalUnitorRepresentable.forgetIso.hom.app _)]
  simp only [← NatTrans.comp_app, Iso.inv_hom_id, NatTrans.id_app, types_id_apply]
  rfl

/-- `OplaxMonoidal.δ` sends the free generator at `(a, b)` to the left unitor inverse
composed with the tensor of free generators at `a` and `b`. -/
private lemma freeGen_δ (A B : Type v) (a : A) (b : B) :
    freeGen (C := C) (a, b) ≫ Functor.OplaxMonoidal.δ Free A B =
    (λ_ (𝟙_ C)).inv ≫ (freeGen (C := C) a ⊗ₘ freeGen (C := C) b) := by
  dsimp only [freeGen]
  set δ := Functor.OplaxMonoidal.δ (Free (C := C)) A B
  have hnat := congr_fun (MonoidalUnitorRepresentable.forgetIso (C := C) |>.hom.naturality δ)
    ((Adjunction.ofIsRightAdjoint (forget C)).unit.app (A × B) (a, b))
  simp only [types_comp_apply] at hnat
  dsimp [coyoneda] at hnat
  erw [← hnat]; clear hnat
  change MonoidalUnitorRepresentable.forgetIso.hom.app _
    (((Adjunction.ofIsRightAdjoint (forget C)).unit.app _ ≫ (forget C).map δ) (a, b)) = _
  rw [Adjunction.unit_app_tensor_comp_map_δ]
  simp only [types_comp_apply]
  dsimp
  rw [← types_comp_apply (Functor.LaxMonoidal.μ (forget C) _ _)
    (MonoidalUnitorRepresentable.forgetIso.hom.app _),
    NatTrans.IsMonoidal.tensor (τ := MonoidalUnitorRepresentable.forgetIso.hom)]
  simp only [types_comp_apply]
  dsimp
  rfl

/-- Evaluating `chainTensorHomEquiv` on coprojection pairs: the forward map
sends `f` at `(s, t)` to `(λ_ (𝟙_ C)).inv ≫ (ι s ⊗ₘ ι t) ≫ f`. -/
lemma chainTensorHomEquiv_apply {S T : SSet.{v}} {p q : ℕ} {M : C}
    (f : (singChain C S).X p ⊗ (singChain C T).X q ⟶ M)
    (s : S _⦋p⦌) (t : T _⦋q⦌) :
    chainTensorHomEquiv M f (s, t) =
    (λ_ (𝟙_ C)).inv ≫
      MonoidalCategory.tensorHom (simplexCoprojection s) (simplexCoprojection t) ≫ f := by
  simp only [chainTensorHomEquiv, freeTensorHomEquiv, Iso.homFromEquiv, Equiv.trans_apply]
  change ((MonoidalUnitorRepresentable.forgetIso (C := C)).app M).hom
    (((Adjunction.ofIsRightAdjoint (forget C)).homEquiv _ M)
      ((Functor.Monoidal.μIso Free _ _).symm.hom ≫
        ((chainGroupIsoFree (C := C) p) ⊗ᵢ
          (chainGroupIsoFree (C := C) q)).symm.hom ≫ f)
      (s, t)) =
    (λ_ (𝟙_ C)).inv ≫ (simplexCoprojection s ⊗ₘ simplexCoprojection t) ≫ f
  have hassoc : (Functor.Monoidal.μIso Free _ _).symm.hom ≫
      ((chainGroupIsoFree (C := C) p) ⊗ᵢ
        (chainGroupIsoFree (C := C) q)).symm.hom ≫ f =
    ((Functor.Monoidal.μIso Free _ _).symm.hom ≫
      ((chainGroupIsoFree (C := C) p) ⊗ᵢ
        (chainGroupIsoFree (C := C) q)).symm.hom) ≫ f :=
    (Category.assoc _ _ _).symm
  simp_rw [hassoc, Adjunction.homEquiv_naturality_right]
  simp only [types_comp_apply]
  set y := (forget C).map ((chainGroupIsoFree (C := C) p) ⊗ᵢ
      (chainGroupIsoFree (C := C) q)).symm.hom
    (((Adjunction.ofIsRightAdjoint (forget C)).homEquiv _ _)
      (Functor.Monoidal.μIso Free _ _).symm.hom (s, t))
  have hnat := congr_fun (MonoidalUnitorRepresentable.forgetIso (C := C) |>.hom.naturality f) y
  simp only [types_comp_apply] at hnat
  change (MonoidalUnitorRepresentable.forgetIso (C := C)).hom.app M ((forget C).map f y) =
    (λ_ (𝟙_ C)).inv ≫ (simplexCoprojection s ⊗ₘ simplexCoprojection t) ≫ f
  rw [hnat]; dsimp [coyoneda]; rw [← Category.assoc ((λ_ (𝟙_ C)).inv)]; congr 1
  simp only [y]; clear y hnat hassoc f M
  have hnat2 := congr_fun ((MonoidalUnitorRepresentable.forgetIso (C := C)).hom.naturality
    ((chainGroupIsoFree (C := C) p) ⊗ᵢ
      (chainGroupIsoFree (C := C) q)).symm.hom)
    (((Adjunction.ofIsRightAdjoint (forget C)).homEquiv _ _)
      (Functor.Monoidal.μIso Free _ _).symm.hom (s, t))
  simp only [types_comp_apply] at hnat2
  erw [hnat2]; dsimp [coyoneda]
  rw [Adjunction.homEquiv_unit]
  simp only [types_comp_apply]
  have hnat3 := congr_fun ((MonoidalUnitorRepresentable.forgetIso (C := C)).hom.naturality
    (Functor.OplaxMonoidal.δ Free _ _))
    ((Adjunction.ofIsRightAdjoint (forget C)).unit.app _ (s, t))
  simp only [types_comp_apply] at hnat3
  erw [hnat3]; dsimp [coyoneda]
  rw [Category.assoc]
  simp only [types_tensorObj_def] at *
  rw [← Category.assoc, freeGen_δ, Category.assoc,
    MonoidalCategory.tensorHom_comp_tensorHom,
    freeGen_chainGroupIsoFree, freeGen_chainGroupIsoFree]

/-- On 0-simplices, `simplexCrossProduct s t` is just `simplexCoprojection (prodSimplex s t)`:
there is a unique (0,0)-shuffle with sign 1, so the shuffle sum collapses. -/
lemma simplexCrossProduct_zero_zero {S T : SSet.{v}}
    (s : S _⦋0⦌) (t : T _⦋0⦌) :
    simplexCrossProduct (C := C) s t = simplexCoprojection (prodSimplex s t) := by
  simp only [simplexCrossProduct, universalSimplexCrossProduct, shuffleSimplex]
  rw [Fintype.sum_subsingleton _ default]
  have : (default : Shuffle 0 0).sign = 1 := by simp [Shuffle.sign, Shuffle.invCount]
  rw [this, one_smul]
  dsimp [simplexCoprojection, SCF, SSet.singularChainComplexFunctor]
  erw [CategoryTheory.Limits.Sigma.ι_comp_map']
  simp only [Category.id_comp]
  congr 1
  show (SSet.yonedaEquiv.symm s ⊗ₘₛ SSet.yonedaEquiv.symm t).app _ _ = prodSimplex s t
  simp only [SSet.tensorHom_app_apply, prodSimplex]
  refine Prod.ext ?_ ?_ <;> {
    change (SSet.yonedaEquiv.symm _).app _ (Δ[0].map _ (SSet.stdSimplex.objEquiv.symm (𝟙 ⦋0⦌))) = _
    rw [SSet.stdSimplex.map_apply, yonedaEquiv_symm_app]
    simp [SimplexCategory.hom_zero_zero]
  }

/-- The cross product of two 0-simplex coprojections factors through the
coprojection of the product simplex, up to the left unitor. -/
theorem crossProduct_normalized' {S T : SSet.{v}}
    (s : S _⦋0⦌) (t : T _⦋0⦌) :
    MonoidalCategory.tensorHom (simplexCoprojection (C := C) s)
      (simplexCoprojection t) ≫ chainCrossProduct (C := C) =
    (λ_ (𝟙_ C)).hom ≫ simplexCoprojection (prodSimplex s t) := by
  rw [← Iso.inv_comp_eq (λ_ (𝟙_ C))]
  rw [← chainTensorHomEquiv_apply]
  rw [congrFun (chainCrossProduct.spec (C := C)) (s, t)]
  exact simplexCrossProduct_zero_zero s t

@[simp] lemma simplexCoprojection_comp_SCF_map {S T : SSet.{v}} {n : ℕ}
    (s : S _⦋n⦌) (f : S ⟶ T) :
    simplexCoprojection (C := C) s ≫ ((SCF C).map f).f n =
    simplexCoprojection (f.app _ s) := by
  dsimp [simplexCoprojection, SCF, SSet.singularChainComplexFunctor]
  erw [CategoryTheory.Limits.Sigma.ι_comp_map']
  simp only [Category.id_comp]

/-- Factoring a coprojection through the identity simplex: `ι s` equals
`ι (objEquiv.symm (𝟙 ⦋n⦌))` composed with the chain map induced by `yonedaEquiv.symm s`.
The Leibniz rule needs to factor `ι s ⊗ₘ ι t` into
`(ι id ⊗ₘ ι id) ≫ (s_* ⊗ₘ t_*)`, which requires rewriting the LHS of
`simplexCoprojection_comp_SCF_map` rather than the RHS. -/
lemma simplexCoprojection_factor {S : SSet.{v}} {n : ℕ} (s : S _⦋n⦌) :
    simplexCoprojection (C := C) s =
    simplexCoprojection (SSet.stdSimplex.objEquiv.symm (𝟙 ⦋n⦌)) ≫
      ((SCF C).map (SSet.yonedaEquiv.symm s)).f n := by
  rw [simplexCoprojection_comp_SCF_map, yonedaEquiv_symm_app]
  simp

lemma crossProduct_natural_pure_tensor {S S' T T' : SSet.{v}}
    (f : S ⟶ S') (g : T ⟶ T') {p q n : ℕ}
    (s : S _⦋p⦌) (t : T _⦋q⦌)
    (hn : n = p + q := by omega) :
    simplexCrossProduct s t hn ≫
      ((SCF C).map (f ⊗ₘₛ g)).f n =
    simplexCrossProduct (C := C) (f.app _ s) (g.app _ t) hn := by
  subst hn
  simp only [simplexCrossProduct, Category.assoc]
  -- Combine `.f n` components: `(SCF C).map φ).f n ≫ ((SCF C).map ψ).f n = ((SCF C).map (φ ≫ ψ)).f n`
  rw [← HomologicalComplex.comp_f, ← Functor.map_comp]
  congr 1
  -- `(yonedaEquiv.symm s ⊗ₘₛ yonedaEquiv.symm t) ≫ (f ⊗ₘₛ g)
  --  = yonedaEquiv.symm (f.app _ s) ⊗ₘₛ yonedaEquiv.symm (g.app _ t)`
  rw [MonoidalCategory.tensorHom_comp_tensorHom]
  -- `yonedaEquiv.symm s ≫ f = yonedaEquiv.symm (f.app _ s)` by Yoneda naturality
  have yoneda_nat : ∀ {A B : SSet.{v}} {m : SimplexCategory} (x : A.obj (Opposite.op m)) (h : A ⟶ B),
      SSet.yonedaEquiv.symm x ≫ h = SSet.yonedaEquiv.symm (h.app _ x) := by
    intros; apply SSet.yonedaEquiv.injective; simp [SSet.yonedaEquiv_comp]
  rw [yoneda_nat, yoneda_nat]

/-- Naturality of the chain-level cross product: given simplicial maps `f : S ⟶ S'`
and `g : T ⟶ T'`, the cross product commutes with the induced chain maps:
`chainCrossProduct ≫ (f ⊗ₘₛ g)_* = (f_* ⊗ g_*) ≫ chainCrossProduct`.

This lifts `crossProduct_natural_pure_tensor` from the simplex level to the chain level
using `chainCrossProduct.ext` (injectivity of `chainTensorHomEquiv`). -/
theorem crossProduct_natural {S S' T T' : SSet.{v}}
    (f : S ⟶ S') (g : T ⟶ T') {p q n : ℕ}
    (hn : n = p + q := by omega) :
    chainCrossProduct (C := C) hn ≫ ((SCF C).map (f ⊗ₘₛ g)).f n =
    (((SCF C).map f).f p ⊗ₘ ((SCF C).map g).f q) ≫ chainCrossProduct (C := C) hn := by
  apply chainCrossProduct.ext
  ext ⟨s, t⟩
  simp only [chainTensorHomEquiv_apply]
  -- RHS: rewrite (ι s ⊗ₘ ι t) ≫ (f_* ⊗ₘ g_*) = (ι s ≫ f_*) ⊗ₘ (ι t ≫ g_*)
  rw [MonoidalCategory.tensorHom_comp_tensorHom_assoc]
  rw [simplexCoprojection_comp_SCF_map, simplexCoprojection_comp_SCF_map]
  -- LHS: reassociate so `← chainTensorHomEquiv_apply` can match
  rw [show (λ_ (𝟙_ C)).inv ≫
    (simplexCoprojection s ⊗ₘ simplexCoprojection t) ≫ chainCrossProduct hn ≫
      ((SCF C).map (f ⊗ₘₛ g)).f n =
    ((λ_ (𝟙_ C)).inv ≫
      (simplexCoprojection s ⊗ₘ simplexCoprojection t) ≫ chainCrossProduct hn) ≫
      ((SCF C).map (f ⊗ₘₛ g)).f n from by simp [Category.assoc]]
  rw [← chainTensorHomEquiv_apply]
  rw [congrFun (chainCrossProduct.spec (C := C) hn) (s, t)]
  -- RHS: reduce via `chainCrossProduct.spec`
  rw [← chainTensorHomEquiv_apply]
  rw [congrFun (chainCrossProduct.spec (C := C) hn) (f.app _ s, g.app _ t)]
  exact crossProduct_natural_pure_tensor f g s t hn

end HomologyLean.SingularHomology.SSetEZ
