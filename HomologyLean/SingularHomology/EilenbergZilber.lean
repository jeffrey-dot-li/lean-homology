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

universe u v

namespace HomologyLean.SingularHomology.SSetEZ

-- `⊗` is ambiguous between `C` and `SSet` when both monoidal structures are in scope.
local notation:50 S " ⊗ₛ " T => (MonoidalCategory.tensorObj (C := SSet) S T)

/-! ### SSet.yonedaEquiv simp lemmas -/

@[simp] lemma yonedaEquiv_symm_app {X : SSet.{v}} {n : SimplexCategory}
    (x : X.obj (Opposite.op n)) {m : SimplexCategoryᵒᵖ}
    (f : m.unop ⟶ n) :
    (SSet.yonedaEquiv.symm x).app m (SSet.stdSimplex.objEquiv.symm f) =
      X.map f.op x :=
  rfl

@[simp] lemma yonedaEquiv_symm_objEquiv_symm_app {n n' : SimplexCategory} {m : SimplexCategoryᵒᵖ}
    (f : n ⟶ n') (g : m.unop ⟶ n) :
    (SSet.yonedaEquiv.{v}.symm (SSet.stdSimplex.objEquiv.symm f)).app m
      (SSet.stdSimplex.objEquiv.symm g) =
    SSet.stdSimplex.objEquiv.symm (g ≫ f) :=
  rfl

/-- Precomposing `yonedaEquiv.symm x` with a morphism `h : A ⟶ B` of simplicial sets
is the same as applying `h` to `x` first:
`yonedaEquiv.symm x ≫ h = yonedaEquiv.symm (h.app _ x)`. -/
@[simp] lemma yonedaEquiv_symm_comp {A B : SSet.{v}} {m : SimplexCategory}
    (x : A.obj (Opposite.op m)) (h : A ⟶ B) :
    SSet.yonedaEquiv.symm x ≫ h = SSet.yonedaEquiv.symm (h.app _ x) := by
  apply SSet.yonedaEquiv.injective; simp [SSet.yonedaEquiv_comp]

lemma SimplexCategory.eqToHom_comp_δ {n n' : ℕ} (hn : n = n') (i : Fin (n' + 2)) :
    eqToHom (show (⦋n⦌ : SimplexCategory) = ⦋n'⦌ by rw [hn]) ≫ SimplexCategory.δ i =
      SimplexCategory.δ (i.cast (by omega)) ≫
        eqToHom (show (⦋n + 1⦌ : SimplexCategory) = ⦋n' + 1⦌ by rw [hn]) := by
  subst hn; simp

/-- The product of two n-simplices: given `s ∈ S_n` and `t ∈ T_n`,
form the n-simplex in `S ⊗ T`. The monoidal product in `SSet` is levelwise,
so this is just the pair `(s, t)`. -/
def prodSimplex {S T : SSet.{v}} {n : ℕ}
    (s : S _⦋n⦌) (t : T _⦋n⦌) : (S ⊗ₛ T) _⦋n⦌ :=
  (s, t)

@[simp] lemma SSet.tensorObj_map_fst {S T : SSet.{v}} {d e : SimplexCategoryᵒᵖ}
    (f : d ⟶ e) (x : (S ⊗ₛ T).obj d) :
    ((S ⊗ₛ T).map f x).1 = S.map f x.1 := rfl

@[simp] lemma SSet.tensorObj_map_snd {S T : SSet.{v}} {d e : SimplexCategoryᵒᵖ}
    (f : d ⟶ e) (x : (S ⊗ₛ T).obj d) :
    ((S ⊗ₛ T).map f x).2 = T.map f x.2 := rfl

/-! ### Shuffle simplices -/

/-- The first projection of a `(p,q)`-shuffle as a `SimplexCategory` morphism `⦋p+q⦌ ⟶ ⦋p⦌`. -/
abbrev Shuffle.fstHom (μ : Shuffle p q) : (⦋p + q⦌ : SimplexCategory) ⟶ ⦋p⦌ :=
  SimplexCategory.Hom.mk (OrderHom.fst.comp μ.1)

/-- The second projection of a `(p,q)`-shuffle as a `SimplexCategory` morphism `⦋p+q⦌ ⟶ ⦋q⦌`. -/
abbrev Shuffle.sndHom (μ : Shuffle p q) : (⦋p + q⦌ : SimplexCategory) ⟶ ⦋q⦌ :=
  SimplexCategory.Hom.mk (OrderHom.snd.comp μ.1)

/-- Given a p-simplex `s` in `S`, a q-simplex `t` in `T`, and a (p,q)-shuffle `μ`,
produce an n-simplex in `S ⊗ T` (where `n = p + q`).

The shuffle `μ` determines a monotone map `Fin (p+q+1) →o Fin (p+1) × Fin (q+1)`.
We apply the two projections as `SimplexCategory` morphisms to `s` and `t` respectively,
then pair the results in the levelwise product `(S ⊗ T) _⦋p+q⦌`. -/
def shuffleSimplex {S T : SSet.{v}} {p q n : ℕ}
    (s : S _⦋p⦌) (t : T _⦋q⦌) (μ : Shuffle p q)
    (hn : n = p + q := by omega) :
    (S ⊗ₛ T) _⦋n⦌ :=
  (S ⊗ₛ T).map (eqToHom (congrArg SimplexCategory.mk hn)).op
    (S.map (Shuffle.fstHom μ).op s, T.map (Shuffle.sndHom μ).op t)

/-- Transport on a simplicial set: `(h ▸ x)` equals `X.map (eqToHom ...).op x`.
This converts the opaque `▸` into a functorial `map`, enabling composition with other maps.
No successor-indexed terms appear, so `generalize` + `subst` works. -/
private lemma sset_transport_eq_map {X : SSet.{v}} {m n : ℕ} (h : m = n) (x : X _⦋n⦌) :
    (h ▸ x : X _⦋m⦌) = X.map (eqToHom (congrArg SimplexCategory.mk h)).op x := by
  subst h; simp

/-- Face map on a product applied to a `shuffleSimplex`: the face map `δ_i` acts by
precomposition on each component, absorbing into the shuffle projections. -/
lemma δ_shuffleSimplex {S T : SSet.{v}} {p q n : ℕ}
    (s : S _⦋p⦌) (t : T _⦋q⦌) (μ : Shuffle p q) (i : Fin (n + 2))
    (hn : n + 1 = p + q) :
    (S ⊗ₛ T).δ i (shuffleSimplex s t μ hn) =
    prodSimplex
      (S.map (SimplexCategory.δ i ≫ eqToHom (congrArg SimplexCategory.mk hn) ≫
        Shuffle.fstHom μ).op s)
      (T.map (SimplexCategory.δ i ≫ eqToHom (congrArg SimplexCategory.mk hn) ≫
        Shuffle.sndHom μ).op t) := by
  simp only [shuffleSimplex, SimplicialObject.δ, prodSimplex]
  generalize_proofs h_eqToHom
  rw [← FunctorToTypes.map_comp_apply]
  -- LHS: (S ⊗ T).map (δ i ≫ eqToHom).op pair — expand tensor map componentwise
  refine Prod.ext ?_ ?_ <;> {
    dsimp [SSet.tensorHom_app_apply]
    rw [← FunctorToTypes.map_comp_apply]
    simp only [← op_comp, Category.assoc]
  }

/-- Composing `δ r ≫ eqToHom ≫ fstHom` of `swapDiagonalSteps μ r h` gives the same
result as for `μ`, because `δ r` maps via `succAbove r` which avoids vertex `r`,
and `swapDiagonalSteps` only changes the value at `r`. -/
private lemma fstHom_swapDiagonalSteps_comp_δ {p q : ℕ}
    (μ : Shuffle (p + 1) (q + 1)) (r : Fin (p + (q + 1) + 2))
    (h : Shuffle.isDiagonalVertex μ (r.cast (by omega))) :
    SimplexCategory.δ r ≫
      eqToHom (congrArg SimplexCategory.mk (show p + (q + 1) + 1 = (p + 1) + (q + 1) by omega)) ≫
      Shuffle.fstHom (μ.swapDiagonalSteps (r.cast (by omega)) h) =
    SimplexCategory.δ r ≫
      eqToHom (congrArg SimplexCategory.mk (show p + (q + 1) + 1 = (p + 1) + (q + 1) by omega)) ≫
      Shuffle.fstHom μ := by
  ext ⟨i, hi⟩
  simp only [SimplexCategory.comp_toOrderHom, OrderHom.comp_coe, Function.comp_apply,
    SimplexCategory.Hom.toOrderHom_mk, SimplexCategory.eqToHom_toOrderHom,
    SimplexCategory.len_mk, Shuffle.fstHom]
  -- Name the composed argument from the goal so Lean resolves the Fin types internally
  set arg := (Fin.castOrderIso _).toOrderEmbedding.toOrderHom
    ((SimplexCategory.Hom.toOrderHom (SimplexCategory.δ r)) ⟨i, hi⟩)
  exact congrArg (fun x => (x.1 : ℕ)) (Shuffle.swapDiagonalSteps_apply_ne μ _ h arg (by
    simp only [arg, SimplexCategory.δ, SimplexCategory.mkHom, SimplexCategory.Hom.toOrderHom_mk,
      ne_eq, Fin.ext_iff, Fin.val_cast]
    exact fun heq => absurd (Fin.ext heq)
      (Fin.succAbove_ne r ⟨i, by simp only [SimplexCategory.len_mk] at hi; omega⟩)))

private lemma sndHom_swapDiagonalSteps_comp_δ {p q : ℕ}
    (μ : Shuffle (p + 1) (q + 1)) (r : Fin (p + (q + 1) + 2))
    (h : Shuffle.isDiagonalVertex μ (r.cast (by omega))) :
    SimplexCategory.δ r ≫
      eqToHom (congrArg SimplexCategory.mk (show p + (q + 1) + 1 = (p + 1) + (q + 1) by omega)) ≫
      Shuffle.sndHom (μ.swapDiagonalSteps (r.cast (by omega)) h) =
    SimplexCategory.δ r ≫
      eqToHom (congrArg SimplexCategory.mk (show p + (q + 1) + 1 = (p + 1) + (q + 1) by omega)) ≫
      Shuffle.sndHom μ := by
  ext ⟨i, hi⟩
  simp only [SimplexCategory.comp_toOrderHom, OrderHom.comp_coe, Function.comp_apply,
    SimplexCategory.Hom.toOrderHom_mk, SimplexCategory.eqToHom_toOrderHom,
    SimplexCategory.len_mk, Shuffle.sndHom]
  set arg := (Fin.castOrderIso _).toOrderEmbedding.toOrderHom
    ((SimplexCategory.Hom.toOrderHom (SimplexCategory.δ r)) ⟨i, hi⟩)
  exact congrArg (fun x => (x.2 : ℕ)) (Shuffle.swapDiagonalSteps_apply_ne μ _ h arg (by
    simp only [arg, SimplexCategory.δ, SimplexCategory.mkHom, SimplexCategory.Hom.toOrderHom_mk,
      ne_eq, Fin.ext_iff, Fin.val_cast]
    exact fun heq => absurd (Fin.ext heq)
      (Fin.succAbove_ne r ⟨i, by simp only [SimplexCategory.len_mk] at hi; omega⟩)))

/-- Left insertion face factorization (fst component):
`δ_{insertLeftIndex} ≫ eqToHom ≫ fstHom (insertLeftStep ν j) = δ j ≫ fstHom ν`.

This is the SSet analogue of the first component of `insertLeftStep_comp_δ`. -/
private lemma fstHom_insertLeftStep_comp_δ {p q : ℕ} (ν : Shuffle p q) (j : Fin (p + 2)) :
    SimplexCategory.δ ((ν.insertLeftIndex j).cast (by omega)) ≫
      eqToHom (congrArg SimplexCategory.mk (show p + q + 1 = (p + 1) + q by omega)) ≫
      Shuffle.fstHom (ν.insertLeftStep j) =
    Shuffle.fstHom ν ≫ SimplexCategory.δ j := by
  ext ⟨i, hi⟩
  simp only [SimplexCategory.comp_toOrderHom, OrderHom.comp_coe, Function.comp_apply,
    SimplexCategory.Hom.toOrderHom_mk, SimplexCategory.eqToHom_toOrderHom,
    SimplexCategory.len_mk, Shuffle.fstHom]
  simp only [SimplexCategory.len_mk] at hi
  -- Bridge: (δ (cast t) ≫ eqToHom).toOrderHom ⟨i, hi⟩ has the same Fin.val
  -- as succAbove ⟨t.val, _⟩ (⟨i, _⟩.cast _), so insertLeftStep_face applies.
  have hface := Shuffle.insertLeftStep_face ν j ⟨i, by omega⟩
  suffices harg : ∀ (a b : Fin ((p + 1) + q + 1)), a.val = b.val →
      (ν.insertLeftStep j).1 a = (ν.insertLeftStep j).1 b from
    congrArg (fun x => (x.1 : ℕ)) ((harg _ _ (by
      dsimp [SimplexCategory.δ, Fin.succAboveOrderEmb, SimplexCategory.comp_toOrderHom,
        SimplexCategory.eqToHom_toOrderHom, Fin.castOrderIso]
      -- Both sides are succAbove with same Fin.val index; unfold and close by cases
      simp only [Fin.succAbove, Fin.lt_def, Fin.val_castSucc]
      split_ifs <;> simp_all)).trans hface)
  exact fun _ _ h => congr_arg _ (Fin.ext h)

/-- Left insertion face factorization (snd component):
`δ_{insertLeftIndex} ≫ eqToHom ≫ sndHom (insertLeftStep ν j) = sndHom ν`. -/
private lemma sndHom_insertLeftStep_comp_δ {p q : ℕ} (ν : Shuffle p q) (j : Fin (p + 2)) :
    SimplexCategory.δ ((ν.insertLeftIndex j).cast (by omega)) ≫
      eqToHom (congrArg SimplexCategory.mk (show p + q + 1 = (p + 1) + q by omega)) ≫
      Shuffle.sndHom (ν.insertLeftStep j) =
    Shuffle.sndHom ν := by
  ext ⟨i, hi⟩
  simp only [SimplexCategory.comp_toOrderHom, OrderHom.comp_coe, Function.comp_apply,
    SimplexCategory.Hom.toOrderHom_mk, SimplexCategory.eqToHom_toOrderHom,
    SimplexCategory.len_mk, Shuffle.sndHom]
  simp only [SimplexCategory.len_mk] at hi
  have hface := Shuffle.insertLeftStep_face ν j ⟨i, by omega⟩
  suffices harg : ∀ (a b : Fin ((p + 1) + q + 1)), a.val = b.val →
      (ν.insertLeftStep j).1 a = (ν.insertLeftStep j).1 b from
    congrArg (fun x => (x.2 : ℕ)) ((harg _ _ (by
      dsimp [SimplexCategory.δ, Fin.succAboveOrderEmb, SimplexCategory.comp_toOrderHom,
        SimplexCategory.eqToHom_toOrderHom, Fin.castOrderIso]
      simp only [Fin.succAbove, Fin.lt_def, Fin.val_castSucc]
      split_ifs <;> simp_all)).trans hface)
  exact fun _ _ h => congr_arg _ (Fin.ext h)

/-- Right insertion face factorization (fst component):
`δ_{insertRightIndex} ≫ eqToHom ≫ fstHom (insertRightStep ν k) = fstHom ν`. -/
private lemma fstHom_insertRightStep_comp_δ {p q : ℕ} (ν : Shuffle p q) (k : Fin (q + 2)) :
    SimplexCategory.δ ((ν.insertRightIndex k).cast (by omega)) ≫
      eqToHom (congrArg SimplexCategory.mk (show p + q + 1 = p + (q + 1) by omega)) ≫
      Shuffle.fstHom (ν.insertRightStep k) =
    Shuffle.fstHom ν := by
  ext ⟨i, hi⟩
  simp only [SimplexCategory.comp_toOrderHom, OrderHom.comp_coe, Function.comp_apply,
    SimplexCategory.Hom.toOrderHom_mk, SimplexCategory.eqToHom_toOrderHom,
    SimplexCategory.len_mk, Shuffle.fstHom]
  simp only [SimplexCategory.len_mk] at hi
  have hface := Shuffle.insertRightStep_face ν k ⟨i, by omega⟩
  suffices harg : ∀ (a b : Fin (p + (q + 1) + 1)), a.val = b.val →
      (ν.insertRightStep k).1 a = (ν.insertRightStep k).1 b from
    congrArg (fun x => (x.1 : ℕ)) ((harg _ _ (by
      dsimp [SimplexCategory.δ, Fin.succAboveOrderEmb, SimplexCategory.comp_toOrderHom,
        SimplexCategory.eqToHom_toOrderHom, Fin.castOrderIso])).trans hface)
  exact fun _ _ h => congr_arg _ (Fin.ext h)

/-- Right insertion face factorization (snd component):
`δ_{insertRightIndex} ≫ eqToHom ≫ sndHom (insertRightStep ν k) = sndHom ν ≫ δ k`. -/
private lemma sndHom_insertRightStep_comp_δ {p q : ℕ} (ν : Shuffle p q) (k : Fin (q + 2)) :
    SimplexCategory.δ ((ν.insertRightIndex k).cast (by omega)) ≫
      eqToHom (congrArg SimplexCategory.mk (show p + q + 1 = p + (q + 1) by omega)) ≫
      Shuffle.sndHom (ν.insertRightStep k) =
    Shuffle.sndHom ν ≫ SimplexCategory.δ k := by
  ext ⟨i, hi⟩
  simp only [SimplexCategory.comp_toOrderHom, OrderHom.comp_coe, Function.comp_apply,
    SimplexCategory.Hom.toOrderHom_mk, SimplexCategory.eqToHom_toOrderHom,
    SimplexCategory.len_mk, Shuffle.sndHom]
  simp only [SimplexCategory.len_mk] at hi
  have hface := Shuffle.insertRightStep_face ν k ⟨i, by omega⟩
  suffices harg : ∀ (a b : Fin (p + (q + 1) + 1)), a.val = b.val →
      (ν.insertRightStep k).1 a = (ν.insertRightStep k).1 b from
    congrArg (fun x => (x.2 : ℕ)) ((harg _ _ (by
      dsimp [SimplexCategory.δ, Fin.succAboveOrderEmb, SimplexCategory.comp_toOrderHom,
        SimplexCategory.eqToHom_toOrderHom, Fin.castOrderIso])).trans hface)
  exact fun _ _ h => congr_arg _ (Fin.ext h)

private abbrev idSimplex (n : ℕ) : Δ[n] _⦋n⦌ := SSet.stdSimplex.objEquiv.symm (𝟙 ⦋n⦌)
private abbrev faceSimplex {n : ℕ} (j : Fin (n + 2)) : Δ[n + 1] _⦋n⦌ :=
  SSet.stdSimplex.objEquiv.symm (SimplexCategory.δ j)

section BasicChainComplex
variable {C : Type u} [Category.{v} C] [HasCoproducts C] [Preadditive C] [MonoidalCategory C]

/-- The singular chain complex functor on SSet with coefficients in `𝟙_ C`. -/
private abbrev SCF : SSet.{v} ⥤ ChainComplex C ℕ :=
  (SSet.singularChainComplexFunctor.{v} C).obj (𝟙_ C)

/-- The singular chain complex of a simplicial set `S` with coefficients in `𝟙_ C`. -/
private abbrev singChain (S : SSet.{v}) : ChainComplex C ℕ :=
  (SCF (C := C)).obj S

/-! ### Simplex-level cross product -/

/-- The coprojection (basis inclusion) for a simplex: given an n-simplex `s` in `S`,
produce the corresponding basis element `𝟙_ C ⟶ C_n(S; 𝟙_ C)` via the coproduct. -/
private abbrev simplexCoprojection {S : SSet.{v}} {n : ℕ}
    (s : S _⦋n⦌) : 𝟙_ C ⟶ (singChain (C := C) S).X n :=
  Sigma.ι (fun _ : S _⦋n⦌ ↦ 𝟙_ C) s

/-- The universal simplex-level cross product on the standard simplices.

The signed formal sum `∑_μ sign(μ) · ι(shuffleSimplex id_p id_q μ)` over all
(p,q)-shuffles, where `id_p` and `id_q` are the identity simplices of `Δ[p]`
and `Δ[q]`. -/
def universalSimplexCrossProduct (p q : ℕ) {n : ℕ} (hn : n = p + q := by omega) :
    𝟙_ C ⟶ (singChain (C := C) (Δ[p] ⊗ₛ Δ[q])).X n :=
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
def simplexCrossProduct {S T : SSet.{v}} {p q n : ℕ}
    (s : S _⦋p⦌) (t : T _⦋q⦌)
    (hn : n = p + q := by omega) :
    𝟙_ C ⟶ (singChain (C := C) (S ⊗ₛ T)).X n :=
  universalSimplexCrossProduct p q hn ≫
    ((SCF (C := C)).map (SSet.yonedaEquiv.symm s ⊗ₘₛ SSet.yonedaEquiv.symm t)).f n

-- TODO: make `simplexCrossProduct'` the primary definition and provide
-- curried `simplexCrossProduct` as a wrapper.
/-- Variant of `simplexCrossProduct` as an explicit set-level map:
takes a pair `(s, t)` of simplices and returns an element of
`𝟙_ C ⟶ C_n(S ⊗ T; 𝟙_ C)` (where `n = p + q`). -/
def simplexCrossProduct' {S T : SSet.{v}} {p q n : ℕ}
    (hn : n = p + q := by omega) :
    S _⦋p⦌ × T _⦋q⦌ → Hom[𝟙_ C |-].obj ((singChain (C := C) (S ⊗ₛ T)).X n) :=
  fun ⟨s, t⟩ => simplexCrossProduct s t hn
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
  rw [CategoryTheory.Limits.Sigma.ι_comp_map']
  simp only [Category.id_comp]
  congr 1
  show (SSet.yonedaEquiv.symm s ⊗ₘₛ SSet.yonedaEquiv.symm t).app _ _ = prodSimplex s t
  simp only [SSet.tensorHom_app_apply, prodSimplex, FunctorToTypes.map_id_apply]
  refine Prod.ext ?_ ?_ <;> {
    change (SSet.yonedaEquiv.symm _).app _ (Δ[0].map _ (SSet.stdSimplex.objEquiv.symm (𝟙 ⦋0⦌))) = _
    rw [SSet.stdSimplex.map_apply, yonedaEquiv_symm_app]
    simp [SimplexCategory.hom_zero_zero]
  }
@[simp] lemma simplexCoprojection_comp_SCF_map {S T : SSet.{v}} {n : ℕ}
    (s : S _⦋n⦌) (f : S ⟶ T) :
    simplexCoprojection (C := C) s ≫ ((SCF (C := C)).map f).f n =
    simplexCoprojection (f.app _ s) := by
  dsimp [simplexCoprojection, SCF, SSet.singularChainComplexFunctor]
  simp [CategoryTheory.Limits.Sigma.ι_comp_map']

/-- Factoring a coprojection through the identity simplex: `ι s` equals
`ι (objEquiv.symm (𝟙 ⦋n⦌))` composed with the chain map induced by `yonedaEquiv.symm s`.
The Leibniz rule needs to factor `ι s ⊗ₘ ι t` into
`(ι id ⊗ₘ ι id) ≫ (s_* ⊗ₘ t_*)`, which requires rewriting the LHS of
`simplexCoprojection_comp_SCF_map` rather than the RHS. -/
lemma simplexCoprojection_factor {S : SSet.{v}} {n : ℕ} (s : S _⦋n⦌) :
    simplexCoprojection (C := C) s =
    simplexCoprojection (SSet.stdSimplex.objEquiv.symm (𝟙 ⦋n⦌)) ≫
      ((SCF (C := C)).map (SSet.yonedaEquiv.symm s)).f n := by
  rw [simplexCoprojection_comp_SCF_map, yonedaEquiv_symm_app]
  simp

lemma crossProduct_natural_pure_tensor {S S' T T' : SSet.{v}}
    (f : S ⟶ S') (g : T ⟶ T') {p q n : ℕ}
    (s : S _⦋p⦌) (t : T _⦋q⦌)
    (hn : n = p + q := by omega) :
    simplexCrossProduct s t hn ≫
      ((SCF (C := C)).map (f ⊗ₘₛ g)).f n =
    simplexCrossProduct (C := C) (f.app _ s) (g.app _ t) hn := by
  subst hn
  simp only [simplexCrossProduct, Category.assoc]
  -- Combine `.f n` components:
  -- `((SCF (C := C)).map φ).f n ≫ ((SCF (C := C)).map ψ).f n
  --   = ((SCF (C := C)).map (φ ≫ ψ)).f n`.
  rw [← HomologicalComplex.comp_f, ← Functor.map_comp]
  congr 1
  -- `(yonedaEquiv.symm s ⊗ₘₛ yonedaEquiv.symm t) ≫ (f ⊗ₘₛ g)
  --  = yonedaEquiv.symm (f.app _ s) ⊗ₘₛ yonedaEquiv.symm (g.app _ t)`
  rw [MonoidalCategory.tensorHom_comp_tensorHom]
  rw [yonedaEquiv_symm_comp, yonedaEquiv_symm_comp]

/-! ### Leibniz rule infrastructure -/

/-- The boundary map of `singChain` equals the alternating face map differential.
This avoids unfolding `singChain`/`SCF` through deep functor composition. -/
lemma singChain_d_eq_alternatingFaceMapObjD (S : SSet.{v}) (n : ℕ) {m : ℕ} (hm : m = n + 1) :
    (singChain (C := C) S).d m n =
    eqToHom (congrArg (singChain (C := C) S).X hm) ≫
    AlternatingFaceMapComplex.objD
      (((SimplicialObject.whiskering (Type v) C).obj
        ((sigmaConst (C := C)).obj (𝟙_ C))).obj S) n := by
  subst hm
  simp only [eqToHom_refl, Category.id_comp, singChain]
  dsimp [SCF, SSet.singularChainComplexFunctor]
  rw [alternatingFaceMapComplex_obj_d]
  rfl

/-- Functoriality of `simplexCoprojection`: the face map acts by precomposition
on simplices through the coproduct structure. -/
lemma simplexCoprojection_comp_eqToHom_comp_δ {S : SSet.{v}} {n m : ℕ} (h : n = m + 1)
    (s : S _⦋n⦌) (i : Fin (m + 2)) :
    simplexCoprojection (C := C) s ≫
      eqToHom (congrArg (singChain (C := C) S).X h) ≫
      (((SimplicialObject.whiskering (Type v) C).obj ((sigmaConst (C := C)).obj (𝟙_ C))).obj
        S).δ i =
    simplexCoprojection (C := C) (S.δ i (h ▸ s)) := by
  subst h
  simp only [eqToHom_refl, Category.id_comp]
  dsimp [simplexCoprojection, singChain, SCF, SSet.singularChainComplexFunctor,
    SimplicialObject.δ, SimplicialObject.whiskering]
  simp [CategoryTheory.Limits.Sigma.ι_comp_map']
/-! ### Universal Leibniz rule for the simplex-level cross product

**Proof sketch** (after expanding ∂ into face maps):

The LHS is `∑ μ, μ.sign • ∑ r, (-1)^r • coprojection(μ ∘ δ_r)` (double sum over
all `(p+1,q+1)`-shuffles and face indices).

The RHS is two sums: one over `(j, ν)` with `ν : Shuffle p (q+1)`, one over
`(k, ν)` with `ν : Shuffle (p+1) q`.

**Strategy: inject the RHS into the LHS, then cancel the remainder.**

1. **Functoriality**: rewrite `coprojection(σ) ≫ δ_r` as `coprojection(δ_r(σ))`.

2. **Inject RHS terms into LHS** via `insertLeftStep`/`insertRightStep`.

3. **Cancel diagonal remainder** via `swapDiagonalSteps` sign-reversing involution.
-/

/-- The boundary of the universal simplex cross product decomposes as a signed sum
of face-map cross products (the "universal Leibniz rule"):
```
  universalSimplexCrossProduct (p+1) (q+1) ≫ ∂ =
    ∑ j, (-1)^j · simplexCrossProduct (faceSimplex j) (idSimplex (q+1)) +
    (-1)^{p+1} · ∑ j, (-1)^j · simplexCrossProduct (idSimplex (p+1)) (faceSimplex j)
```
-/
theorem universalSimplexCrossProduct_boundary (p q : ℕ) :
    universalSimplexCrossProduct (C := C) (p + 1) (q + 1) ≫
      (singChain (C := C) (Δ[p + 1] ⊗ₛ Δ[q + 1])).d
        ((p + 1) + (q + 1)) (p + (q + 1)) =
    ∑ j : Fin (p + 2),
      ((-1 : ℤ) ^ (j : ℕ)) •
        simplexCrossProduct (C := C) (faceSimplex j) (idSimplex (q + 1)) +
    ((-1 : ℤ) ^ (p + 1)) •
      ∑ j : Fin (q + 2),
        ((-1 : ℤ) ^ (j : ℕ)) •
          simplexCrossProduct (C := C) (idSimplex (p + 1)) (faceSimplex j) := by
  have hrel : (p + 1 + (q + 1) : ℕ) = (p + (q + 1)) + 1 := by omega
  -- Expand d into alternating face map sum
  rw [universalSimplexCrossProduct, Preadditive.sum_comp]
  -- Navigate into each summand to rewrite d
  conv_lhs =>
    arg 2; ext x
    rw [Preadditive.zsmul_comp]
    arg 2  -- into the `coprojection ≫ d` part
    arg 2  -- into `d`
    rw [singChain_d_eq_alternatingFaceMapObjD _ _ hrel]
  -- Expand objD and distribute
  simp only [AlternatingFaceMapComplex.objD, Preadditive.comp_sum, Preadditive.comp_zsmul]
  -- Functoriality: rewrite coprojection ≫ eqToHom ≫ δ as coprojection(δ(σ))
  simp_rw [simplexCoprojection_comp_eqToHom_comp_δ hrel]
  -- Step 2: Fold `hrel ▸ shuffleSimplex ...` back into `shuffleSimplex ... hrel`
  -- The outer hrel ▸ and shuffleSimplex's internal eqToHom compose into a single eqToHom.
  conv_lhs =>
    arg 2; ext μ
    arg 2; arg 2; ext r
    arg 2; arg 1; arg 3
    tactic =>
      simp only [shuffleSimplex]
      rw [sset_transport_eq_map, ← FunctorToTypes.map_comp_apply, ← op_comp, eqToHom_trans]
      omega
  -- Step 3: Unfold simplexCrossProduct on the RHS, keeping shuffleSimplex folded.
  unfold simplexCrossProduct universalSimplexCrossProduct
  simp_rw [Preadditive.sum_comp, Preadditive.zsmul_comp, simplexCoprojection_comp_SCF_map]
  -- Step 4: Simplify the RHS tensor maps and yoneda terms.
  -- Split tensor maps, unfold shuffleSimplex to expose eqToHom + pair,
  -- expand .1/.2 through the tensor map, simplify yoneda terms.
  simp only [SSet.tensorHom_app_apply]
  unfold shuffleSimplex faceSimplex idSimplex
  simp only [SSet.stdSimplex.map_apply, Quiver.Hom.unop_op, Equiv.apply_symm_apply,
    Category.comp_id]
  -- Step 5: Expand .1/.2 of (S ⊗ T).map f.op pair on the RHS using tensorObj_map_fst/snd
  simp only [SSet.tensorObj_map_fst, SSet.tensorObj_map_snd]
  -- Step 6: Normalize Δ[n].map f.op (objEquiv.symm g) → objEquiv.symm (g ≫ f.unop),
  -- then cancel objEquiv ∘ objEquiv.symm
  simp only [SSet.stdSimplex.map_apply, Quiver.Hom.unop_op, Equiv.apply_symm_apply]
  -- Step 7: Collapse the double sum
  -- `∑ μ, μ.sign • ∑ r, (-1)^r • ...` into
  -- `∑ (μ, r), (μ.sign * (-1)^r) • ...`.
  simp_rw [Finset.smul_sum, smul_smul]
  -- Step 8: Split inner sum into diagonal + non-diagonal vertices.
  let isDiag := fun (μ : Shuffle (p + 1) (q + 1)) (r : Fin (p + (q + 1) + 2)) =>
    Shuffle.isDiagonalVertex μ (r.cast (show p + (q + 1) + 2 = (p + 1) + (q + 1) + 1 from by omega))
  haveI isDiag_dec : ∀ μ, DecidablePred (isDiag μ) :=
    fun μ r => Shuffle.isDiagonalVertex_decidable μ _
  conv_lhs =>
    enter [2, x]
    rw [show ∑ r, _ = _ from
      (Finset.sum_filter_add_sum_filter_not Finset.univ (isDiag x) _).symm]
  -- Step 9: Distribute ∑ x over the diagonal + non-diagonal split
  simp_rw [Finset.sum_add_distrib]
  -- Step 10: Cancel the diagonal sum via sign-reversing involution.
  convert (zero_add _) using 2
  · exact SumInvolution.sum_sum_involution_zero isDiag _
      (fun μ r h => Shuffle.swapDiagonalSteps μ (r.cast (by omega)) h)
      (fun μ r h => Shuffle.swapDiagonalSteps_vertex μ (r.cast (by omega)) h)
      (fun μ r h => Shuffle.swapDiagonalSteps_involutive μ (r.cast (by omega)) h)
      (fun μ r h => by
        dsimp only
        have hsign := Shuffle.swapDiagonalSteps_neg_sign μ (r.cast (by omega)) h
        rw [hsign, neg_mul, neg_smul]
        -- Map part: swapDiagonalSteps only changes the value at r,
        -- but δ r avoids r (via succAbove), so the compositions agree.
        congr 1; congr 1; congr 1
        -- Goal: δ r (map eqToHom (swap_pair)) = δ r (map eqToHom (pair))
        -- Suffices to show the underlying OrderHom compositions agree.
        simp only [SimplicialObject.δ, ← FunctorToTypes.map_comp_apply, ← op_comp]
        refine Prod.ext ?_ ?_
        · simp only [SSet.tensorObj_map_fst, SSet.stdSimplex.map_apply,
            Quiver.Hom.unop_op, Equiv.apply_symm_apply, Category.assoc]
          exact congrArg SSet.stdSimplex.objEquiv.symm
            (fstHom_swapDiagonalSteps_comp_δ μ r h)
        · simp only [SSet.tensorObj_map_snd, SSet.stdSimplex.map_apply,
            Quiver.Hom.unop_op, Equiv.apply_symm_apply, Category.assoc]
          exact congrArg SSet.stdSimplex.objEquiv.symm
            (sndHom_swapDiagonalSteps_comp_δ μ r h))
      (fun μ r h => Shuffle.swapDiagonalSteps_ne μ (r.cast (by omega)) h)
  · -- Step 11: Split non-diagonal sum into left-type + right-type vertices.
    let isLeftType := fun (μ : Shuffle (p + 1) (q + 1)) (r : Fin (p + (q + 1) + 2)) =>
      Shuffle.isLeftStep μ ⟨min r.val ((p + 1) + (q + 1) - 1), by omega⟩
    haveI isLeftType_dec : ∀ μ, DecidablePred (isLeftType μ) :=
      fun μ r => Shuffle.isLeftStep_decidable μ _
    conv_rhs =>
      enter [2, x]
      rw [(Finset.sum_filter_add_sum_filter_not
        (Finset.univ.filter (fun r => ¬isDiag x r)) (isLeftType x) _).symm]
    simp_rw [Finset.sum_add_distrib]
    congr 1
    · -- Step 12: Left bijection via insertLeftStep
      rw [← Fintype.sum_prod_type']
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
          exact Fin.ext (by simpa using congrArg (fun x => x.val) heq)
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
          simpa [Fin.val_cast] using hr_eq
        · exfalso
          have hnotleft := Shuffle.insertRightStep_not_isLeftType ν k
          apply hnotleft
          have hrv : r.val = (Shuffle.insertRightIndex ν k).val := by
            simpa using hr_eq.symm
          subst hμ_eq
          have : isLeftType (Shuffle.insertRightStep ν k) r = Shuffle.isLeftStep
            (Shuffle.insertRightStep ν k) ⟨min r.val ((p + 1) + (q + 1) - 1), by omega⟩ := rfl
          rw [this] at hlt
          convert hlt using 2; congr 1
      · -- Summand equality (left case)
        intro ⟨j, ν⟩ _
        dsimp only
        have hsign := Shuffle.sign_insertLeftStep ν j
        congr 1
        · simp only [Fin.val_cast]; linarith
        · -- Map equality: use fstHom/sndHom_insertLeftStep_comp_δ
          congr 1
          -- RHS: δ (insertLeftIndex.cast) applied to shuffleSimplex of insertLeftStep
          -- LHS: (δ j applied to fstHom ν component, sndHom ν component)
          -- After simplifying, need Prod.ext with the two helper lemmas
          simp only [SimplicialObject.δ, ← FunctorToTypes.map_comp_apply, ← op_comp]
          refine Prod.ext ?_ ?_
          · simp only [SSet.tensorObj_map_fst, SSet.stdSimplex.map_apply,
              Quiver.Hom.unop_op, Equiv.apply_symm_apply, Category.assoc]
            exact congrArg SSet.stdSimplex.objEquiv.symm
              (fstHom_insertLeftStep_comp_δ ν j).symm
          · simp only [SSet.tensorObj_map_snd, SSet.stdSimplex.map_apply,
              Quiver.Hom.unop_op, Equiv.apply_symm_apply, Category.assoc]
            exact congrArg SSet.stdSimplex.objEquiv.symm
              (sndHom_insertLeftStep_comp_δ ν j).symm
    · -- Step 13: Right bijection via insertRightStep
      rw [← Fintype.sum_prod_type']
      rw [Finset.sum_sigma']
      apply Finset.sum_nbij
        (fun x => ⟨Shuffle.insertRightStep x.2 x.1,
          (Shuffle.insertRightIndex x.2 x.1).cast (by omega)⟩)
      · intro ⟨k, ν⟩ _
        simp only [Finset.mem_sigma, Finset.mem_univ, Finset.mem_filter, true_and]
        exact ⟨Shuffle.insertRightStep_not_diagonal ν k,
               fun h => Shuffle.insertRightStep_not_isLeftType ν k h⟩
      · intro ⟨k₁, ν₁⟩ _ ⟨k₂, ν₂⟩ _ h
        rw [Sigma.mk.inj_iff] at h
        obtain ⟨hμ, hr⟩ := h
        have hr' : Shuffle.insertRightIndex ν₁ k₁ = Shuffle.insertRightIndex ν₂ k₂ := by
          have heq := eq_of_heq hr
          exact Fin.ext (by simpa using congrArg (fun x => x.val) heq)
        obtain ⟨hk, hν⟩ := Shuffle.insertRightStep_injective k₁ k₂ ν₁ ν₂ hμ hr'
        exact Prod.ext hk hν
      · intro ⟨μ, r⟩ hmem
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
          simpa using hr_eq.symm
        · exact ⟨(k, ν), Finset.mem_univ _,
            Sigma.ext hμ_eq.symm (heq_of_eq (Fin.ext (by simpa using hr_eq)))⟩
      · -- Summand equality (right case)
        intro ⟨k, ν⟩ _
        dsimp only
        have hsign := Shuffle.sign_insertRightStep ν k
        congr 1
        · simp only [Fin.val_cast]; linarith
        · -- Map equality: use fstHom/sndHom_insertRightStep_comp_δ
          congr 1
          simp only [SimplicialObject.δ, ← FunctorToTypes.map_comp_apply, ← op_comp]
          refine Prod.ext ?_ ?_
          · simp only [SSet.tensorObj_map_fst]
            rw [yonedaEquiv_symm_objEquiv_symm_app]
            simp only [SSet.stdSimplex.map_apply, Quiver.Hom.unop_op, Equiv.apply_symm_apply,
              Category.assoc, Category.comp_id]
            congr 1
            conv_lhs => rw [(fstHom_insertRightStep_comp_δ ν k).symm]
            slice_lhs 1 2 => rw [SimplexCategory.eqToHom_comp_δ (by omega)]
            simp [Category.assoc]
          · simp only [SSet.tensorObj_map_snd]
            rw [yonedaEquiv_symm_objEquiv_symm_app]
            simp only [SSet.stdSimplex.map_apply, Quiver.Hom.unop_op, Equiv.apply_symm_apply,
              Category.assoc]
            congr 1
            rw [(sndHom_insertRightStep_comp_δ ν k).symm]
            slice_lhs 1 2 => rw [SimplexCategory.eqToHom_comp_δ (by omega)]
            simp [Category.assoc]

/-! ### Zero-index cross product lemmas -/

/-- For `q = 0`, the cross product of an `n`-simplex `s` in `S` with a `0`-simplex `c`
in `T` reduces to a single coprojection: there is a unique `(n, 0)`-shuffle with sign `1`,
so the shuffle sum collapses. -/
lemma simplexCrossProduct_zero_right {S T : SSet.{v}} {n : ℕ}
    (s : S _⦋n⦌) (c : T _⦋0⦌) :
    simplexCrossProduct (C := C) s c (show n = n + 0 by omega) =
    simplexCoprojection (shuffleSimplex s c default (show n = n + 0 by omega)) := by
  simp only [simplexCrossProduct, universalSimplexCrossProduct]
  rw [Fintype.sum_unique, Preadditive.zsmul_comp]
  have hd : (default : Shuffle n 0).sign = 1 := by
    simp only [Shuffle.sign, Shuffle.invCount]
    suffices h : (∑ r : Fin (n + 0),
      if ((default : Shuffle n 0).1 (Fin.castSucc r)).1 <
         ((default : Shuffle n 0).1 (Fin.succ r)).1
      then ((default : Shuffle n 0).1 (Fin.castSucc r)).2.val else 0) = 0 by
      rw [h]; ring
    apply Finset.sum_eq_zero; intro i _
    dsimp [Unique_Shuffle_n_0]; split_ifs <;> rfl
  rw [hd, one_smul, simplexCoprojection_comp_SCF_map]
  congr 1
  simp only [SSet.tensorHom_app_apply, shuffleSimplex, SSet.tensorObj_map_fst,
    SSet.tensorObj_map_snd]
  refine Prod.ext ?_ ?_ <;> {
    change (SSet.yonedaEquiv.symm _).app _ (Δ[_].map _ (SSet.stdSimplex.objEquiv.symm _)) = _
    rw [SSet.stdSimplex.map_apply, yonedaEquiv_symm_app]
    simp only [SSet.stdSimplex.objEquiv, SSet.tensorObj_map_fst, SSet.tensorObj_map_snd]
    simp [Equiv.ulift]
  }

/-- For `p = 0`, the cross product of a `0`-simplex `c` in `S` with an `n`-simplex `s`
in `T` reduces to a single coprojection: there is a unique `(0, n)`-shuffle with sign `1`. -/
lemma simplexCrossProduct_zero_left {S T : SSet.{v}} {n : ℕ}
    (c : S _⦋0⦌) (s : T _⦋n⦌) :
    simplexCrossProduct (C := C) c s (show n = 0 + n by omega) =
    simplexCoprojection (shuffleSimplex c s default (show n = 0 + n by omega)) := by
  simp only [simplexCrossProduct, universalSimplexCrossProduct]
  rw [Fintype.sum_unique, Preadditive.zsmul_comp]
  have hd : (default : Shuffle 0 n).sign = 1 := by
    simp only [Shuffle.sign, Shuffle.invCount]
    suffices h : (∑ r : Fin (0 + n),
      if ((default : Shuffle 0 n).1 (Fin.castSucc r)).1 <
         ((default : Shuffle 0 n).1 (Fin.succ r)).1
      then ((default : Shuffle 0 n).1 (Fin.castSucc r)).2.val else 0) = 0 by
      rw [h]; ring
    apply Finset.sum_eq_zero; intro i _
    dsimp [Unique_Shuffle_0_n]; split_ifs with h
    · exact absurd h (lt_irrefl _)
    · rfl
  rw [hd, one_smul, simplexCoprojection_comp_SCF_map]
  congr 1
  simp only [SSet.tensorHom_app_apply, shuffleSimplex, SSet.tensorObj_map_fst,
    SSet.tensorObj_map_snd]
  refine Prod.ext ?_ ?_ <;> {
    change (SSet.yonedaEquiv.symm _).app _ (Δ[_].map _ (SSet.stdSimplex.objEquiv.symm _)) = _
    rw [SSet.stdSimplex.map_apply, yonedaEquiv_symm_app]
    simp only [SSet.stdSimplex.objEquiv, SSet.tensorObj_map_fst, SSet.tensorObj_map_snd]
    simp [Equiv.ulift]
  }

section FreeForgetful
variable [HasForget.{v} C] [MonoidalUnitorRepresentable (C := C)]
  [(forget C).IsRightAdjoint]

/-! ### Abbreviations -/

/-- The free functor left adjoint to `forget C`. -/
private abbrev Free : Type v ⥤ C := (forget C).leftAdjoint

/-! ### Chain group equivalences -/

/-- The degree-`p` chain group `(singChain (C := C) S).X p` is isomorphic to
`Free.obj (S _⦋p⦌)`, the free object on the set of `p`-simplices.

For SSet, the chain group is definitionally `∐_{σ : S _⦋p⦌} 𝟙_ C`, so
this is just `sigmaConstIsoFree` applied pointwise. -/
noncomputable def chainGroupIsoFree {S : SSet.{v}} (p : ℕ) :
    (singChain (C := C) S).X p ≅ Free.obj (S _⦋p⦌) :=
  sigmaConstIsoFree.app (S _⦋p⦌)

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
  change MonoidalUnitorRepresentable.forgetIso.hom.app (Free.obj (S _⦋p⦌))
      ((Adjunction.ofIsRightAdjoint (forget C)).unit.app (S _⦋p⦌) s) ≫ φ =
    simplexCoprojection s
  rw [← hnat]; clear hnat
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

section MonoidalFree
variable [(forget C).leftAdjoint.Monoidal]

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

/-- The hom-set equivalence for the tensor of chain groups: morphisms
`C_p(S) ⊗ C_q(T) ⟶ M` in `C` correspond bijectively to set-level maps
`S _⦋p⦌ × T _⦋q⦌ → Hom(𝟙_ C, M)`.

Obtained by transporting `freeTensorHomEquiv` along `chainGroupIsoFree`,
which identifies `C_p(S) ≅ Free(S _⦋p⦌)`. -/
noncomputable def chainTensorHomEquiv {S T : SSet.{v}} {p q : ℕ} (M : C) :
    ((singChain (C := C) S).X p ⊗ (singChain (C := C) T).X q ⟶ M) ≃
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
    (singChain (C := C) S).X p ⊗ (singChain (C := C) T).X q ⟶
    (singChain (C := C) (S ⊗ₛ T)).X n :=
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
    {f g : (singChain (C := C) S).X p ⊗ (singChain (C := C) T).X q ⟶ M}
    (h : chainTensorHomEquiv M f = chainTensorHomEquiv M g) : f = g :=
  (chainTensorHomEquiv M).injective h

/-- `OplaxMonoidal.δ` sends the free generator at `(a, b)` to the left unitor inverse
composed with the tensor of free generators at `a` and `b`.

This lemma is intentionally stated here with explicit instance binders, rather than being
placed inside a larger local section. Its proof needs exactly the monoidal coherence data
for `Free` and `forget` (`LaxMonoidal`, `IsMonoidal`, and the monoidality of `forgetIso`),
but it does not use the later additive or Eilenberg-Zilber assembly assumptions.
Keeping those requirements local prevents unrelated section variables from leaking into the
declaration. -/
private lemma freeGen_δ {C : Type u} [Category.{v} C] [MonoidalCategory C] [HasForget.{v} C]
    [MonoidalUnitorRepresentable (C := C)] [(forget C).IsRightAdjoint]
    [(forget C).leftAdjoint.Monoidal] [(forget C).LaxMonoidal]
    [(Adjunction.ofIsRightAdjoint (forget C)).IsMonoidal]
    [NatTrans.IsMonoidal (MonoidalUnitorRepresentable.forgetIso (C := C)).hom]
    (A B : Type v) (a : A) (b : B) :
    freeGen (C := C) (a, b) ≫ Functor.OplaxMonoidal.δ (Free (C := C)) A B =
    (λ_ (𝟙_ C)).inv ≫ (freeGen (C := C) a ⊗ₘ freeGen (C := C) b) := by
  dsimp only [freeGen]
  set δ := Functor.OplaxMonoidal.δ (Free (C := C)) A B
  have hnat := congr_fun (MonoidalUnitorRepresentable.forgetIso (C := C) |>.hom.naturality δ)
    ((Adjunction.ofIsRightAdjoint (forget C)).unit.app (A × B) (a, b))
  simp only [types_comp_apply] at hnat
  dsimp [coyoneda] at hnat
  change MonoidalUnitorRepresentable.forgetIso.hom.app (Free.obj (A ⊗ B))
      ((Adjunction.ofIsRightAdjoint (forget C)).unit.app (A × B) (a, b)) ≫ δ =
    (λ_ (𝟙_ C)).inv ≫
      (MonoidalUnitorRepresentable.forgetIso.hom.app (Free.obj A)
          ((Adjunction.ofIsRightAdjoint (forget C)).unit.app A a) ⊗ₘ
        MonoidalUnitorRepresentable.forgetIso.hom.app (Free.obj B)
          ((Adjunction.ofIsRightAdjoint (forget C)).unit.app B b))
  rw [← hnat]; clear hnat
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
lemma chainTensorHomEquiv_apply [(forget C).LaxMonoidal]
    [(Adjunction.ofIsRightAdjoint (forget C)).IsMonoidal]
    [NatTrans.IsMonoidal (MonoidalUnitorRepresentable.forgetIso (C := C)).hom]
    {S T : SSet.{v}} {p q : ℕ} {M : C}
    (f : (singChain (C := C) S).X p ⊗ (singChain (C := C) T).X q ⟶ M)
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
  rw [hnat2]; dsimp [coyoneda]
  rw [Adjunction.homEquiv_unit]
  simp only [types_comp_apply]
  have hnat3 := congr_fun ((MonoidalUnitorRepresentable.forgetIso (C := C)).hom.naturality
    (Functor.OplaxMonoidal.δ Free _ _))
    ((Adjunction.ofIsRightAdjoint (forget C)).unit.app _ (s, t))
  simp only [types_comp_apply] at hnat3
  rw [hnat3]; dsimp [coyoneda]
  rw [Category.assoc]
  simp only [types_tensorObj_def] at *
  rw [← Category.assoc, freeGen_δ, Category.assoc,
    MonoidalCategory.tensorHom_comp_tensorHom,
    freeGen_chainGroupIsoFree, freeGen_chainGroupIsoFree]

/-- The cross product of two 0-simplex coprojections factors through the
coprojection of the product simplex, up to the left unitor. -/
theorem crossProduct_normalized [(forget C).LaxMonoidal]
    [(Adjunction.ofIsRightAdjoint (forget C)).IsMonoidal]
    [NatTrans.IsMonoidal (MonoidalUnitorRepresentable.forgetIso (C := C)).hom]
    {S T : SSet.{v}} (s : S _⦋0⦌) (t : T _⦋0⦌) :
    MonoidalCategory.tensorHom (simplexCoprojection (C := C) s)
      (simplexCoprojection t) ≫ chainCrossProduct (C := C) =
    (λ_ (𝟙_ C)).hom ≫ simplexCoprojection (prodSimplex s t) := by
  rw [← Iso.inv_comp_eq (λ_ (𝟙_ C))]
  rw [← chainTensorHomEquiv_apply]
  rw [congrFun (chainCrossProduct.spec (C := C)) (s, t)]
  exact simplexCrossProduct_zero_zero s t

/-- Naturality of the chain-level cross product: given simplicial maps `f : S ⟶ S'`
and `g : T ⟶ T'`, the cross product commutes with the induced chain maps:
`chainCrossProduct ≫ (f ⊗ₘₛ g)_* = (f_* ⊗ g_*) ≫ chainCrossProduct`.

This lifts `crossProduct_natural_pure_tensor` from the simplex level to the chain level
using `chainCrossProduct.ext` (injectivity of `chainTensorHomEquiv`). -/
theorem crossProduct_natural [(forget C).LaxMonoidal]
    [(Adjunction.ofIsRightAdjoint (forget C)).IsMonoidal]
    [NatTrans.IsMonoidal (MonoidalUnitorRepresentable.forgetIso (C := C)).hom]
    {S S' T T' : SSet.{v}} (f : S ⟶ S') (g : T ⟶ T') {p q n : ℕ}
    (hn : n = p + q := by omega) :
    chainCrossProduct (C := C) hn ≫ ((SCF (C := C)).map (f ⊗ₘₛ g)).f n =
    (((SCF (C := C)).map f).f p ⊗ₘ ((SCF (C := C)).map g).f q) ≫ chainCrossProduct (C := C) hn := by
  apply chainCrossProduct.ext
  ext ⟨s, t⟩
  simp only [chainTensorHomEquiv_apply]
  -- RHS: rewrite (ι s ⊗ₘ ι t) ≫ (f_* ⊗ₘ g_*) = (ι s ≫ f_*) ⊗ₘ (ι t ≫ g_*)
  rw [MonoidalCategory.tensorHom_comp_tensorHom_assoc]
  rw [simplexCoprojection_comp_SCF_map, simplexCoprojection_comp_SCF_map]
  -- LHS: reassociate so `← chainTensorHomEquiv_apply` can match
  rw [show (λ_ (𝟙_ C)).inv ≫
    (simplexCoprojection s ⊗ₘ simplexCoprojection t) ≫ chainCrossProduct hn ≫
      ((SCF (C := C)).map (f ⊗ₘₛ g)).f n =
    ((λ_ (𝟙_ C)).inv ≫
      (simplexCoprojection s ⊗ₘ simplexCoprojection t) ≫ chainCrossProduct hn) ≫
      ((SCF (C := C)).map (f ⊗ₘₛ g)).f n from by simp [Category.assoc]]
  rw [← chainTensorHomEquiv_apply]
  rw [congrFun (chainCrossProduct.spec (C := C) hn) (s, t)]
  -- RHS: reduce via `chainCrossProduct.spec`
  rw [← chainTensorHomEquiv_apply]
  rw [congrFun (chainCrossProduct.spec (C := C) hn) (f.app _ s, g.app _ t)]
  exact crossProduct_natural_pure_tensor f g s t hn

/-! ### Coprojection-level and simplex-level Leibniz rules -/

/-- The chain-level cross product absorbs coprojection tensors: tensoring two
simplex coprojections and composing with `chainCrossProduct` equals the left
unitor composed with the simplex-level cross product.
`(ι s ⊗ₘ ι t) ≫ chainCrossProduct = (λ_).hom ≫ simplexCrossProduct s t`. -/
private lemma coprojection_tensorHom_chainCrossProduct [(forget C).LaxMonoidal]
    [(Adjunction.ofIsRightAdjoint (forget C)).IsMonoidal]
    [NatTrans.IsMonoidal (MonoidalUnitorRepresentable.forgetIso (C := C)).hom]
    {S T : SSet.{v}} {a b n : ℕ} (hn : n = a + b)
    (s : S _⦋a⦌) (t : T _⦋b⦌) :
    (simplexCoprojection (C := C) s ⊗ₘ simplexCoprojection t) ≫
      chainCrossProduct (C := C) hn =
    (λ_ (𝟙_ C)).hom ≫ simplexCrossProduct (C := C) s t hn := by
  rw [← Iso.inv_comp_eq (λ_ (𝟙_ C))]
  rw [← chainTensorHomEquiv_apply]
  exact congrFun (chainCrossProduct.spec (C := C) hn) (s, t)

section MonoidalAdditive
variable [MonoidalPreadditive C]

/-! ### Tensor product of chain complexes: instances -/

section TensorAdditiveInstances
variable [MonoidalPreadditive C]

instance curriedTensor_additive :
    (MonoidalCategory.curriedTensor C).Additive where
  map_add {X Y} f g := by
    apply NatTrans.ext; funext Z
    exact MonoidalPreadditive.add_whiskerRight f g

end TensorAdditiveInstances

instance hasCoproducts_zero_of_v : HasCoproducts.{0} C :=
  hasCoproducts_shrink.{0, v}

noncomputable instance hasFiniteCoproducts_of_v : HasFiniteCoproducts C :=
  @hasFiniteCoproducts_of_hasCoproducts C _ (hasCoproducts_shrink.{0, v})

noncomputable instance hasZeroObject_of_v : HasZeroObject C :=
  hasZeroObject_of_hasInitial_object

/-! ### Eilenberg–Zilber chain map

The cross product assembled into a chain map
`(singChain (C := C) S).tensorObj (singChain (C := C) T) ⟶ singChain (C := C) (S ⊗ T)`.
-/

-- Selective open: `open HomologicalComplex` would bring the `Monoidal` namespace prefix
-- into scope, shadowing `Functor.Monoidal` and breaking `[(forget C).leftAdjoint.Monoidal]`.
open HomologicalComplex (ιTensorObj mapBifunctorDesc ι_mapBifunctorDesc)

/-- Degree-`n` component of the Eilenberg–Zilber chain map:
`⨁_{p+q=n} C_p(S) ⊗ C_q(T) → C_n(S ⊗ T)` via `chainCrossProduct` on each summand. -/
noncomputable def eilenbergZilber_f (S T : SSet.{v}) (n : ℕ) :
    ((singChain (C := C) S).tensorObj (singChain (C := C) T)).X n ⟶
    (singChain (C := C) (S ⊗ₛ T)).X n :=
  mapBifunctorDesc (fun p q (h : p + q = n) =>
    chainCrossProduct (C := C) h.symm)

/-- Inclusion of the `(p, q)` summand followed by `eilenbergZilber_f` equals
`chainCrossProduct`. -/
@[simp] lemma ι_eilenbergZilber_f (S T : SSet.{v}) (p q n : ℕ) (h : p + q = n) :
    ιTensorObj (singChain (C := C) S) (singChain (C := C) T) p q n h ≫
      eilenbergZilber_f (C := C) S T n =
    chainCrossProduct (C := C) h.symm :=
  ι_mapBifunctorDesc _ _ _ h
section MonoidalCoherence
variable [(forget C).LaxMonoidal]
  [(Adjunction.ofIsRightAdjoint (forget C)).IsMonoidal]
  [NatTrans.IsMonoidal (MonoidalUnitorRepresentable.forgetIso (C := C)).hom]

section MonoidalLinear
variable [MonoidalLinear ℤ C]

/-- The universal Leibniz rule lifted to the coprojection/`chainCrossProduct` level. -/
private lemma universalSimplexCrossProduct_coprojection_boundary (p q : ℕ) :
    ((simplexCoprojection (C := C) (idSimplex (p + 1)) ⊗ₘ
        simplexCoprojection (idSimplex (q + 1))) ≫
      chainCrossProduct (C := C) (show (p + 1) + (q + 1) = (p + 1) + (q + 1) from rfl)) ≫
      (singChain (C := C) (Δ[p + 1] ⊗ₛ Δ[q + 1])).d ((p + 1) + (q + 1)) (p + (q + 1)) =
    ((simplexCoprojection (idSimplex (p + 1)) ⊗ₘ simplexCoprojection (idSimplex (q + 1))) ≫
        ((singChain (C := C) Δ[p + 1]).d (p + 1) p ⊗ₘ
          𝟙 ((singChain (C := C) Δ[q + 1]).X (q + 1)))) ≫
      chainCrossProduct (C := C) (show p + (q + 1) = p + (q + 1) from rfl) +
    ((-1 : ℤ) ^ (p + 1)) •
      ((simplexCoprojection (idSimplex (p + 1)) ⊗ₘ simplexCoprojection (idSimplex (q + 1))) ≫
          (𝟙 ((singChain (C := C) Δ[p + 1]).X (p + 1)) ⊗ₘ
            (singChain (C := C) Δ[q + 1]).d (q + 1) q)) ≫
        chainCrossProduct (C := C) (show p + (q + 1) = (p + 1) + q from by omega) := by
  rw [coprojection_tensorHom_chainCrossProduct]
  simp only [simplexCrossProduct, Category.assoc]
  -- yonedaEquiv.symm (idSimplex n) = 𝟙 Δ[n]
  have yoneda_id : ∀ (n : ℕ), SSet.yonedaEquiv.symm (idSimplex n) = 𝟙 Δ[n] := by
    intro n
    dsimp [idSimplex]
    ext d x : 2
    simpa using
      (yonedaEquiv_symm_objEquiv_symm_app (f := 𝟙 ⦋n⦌) (g := x.down))
  rw [yoneda_id, yoneda_id, MonoidalCategory.id_tensorHom_id]
  slice_lhs 3 4 => rw [(SCF (C := C)).map_id, HomologicalComplex.id_f]
  simp only [Category.id_comp]
  rw [universalSimplexCrossProduct_boundary, Preadditive.comp_add, Preadditive.comp_zsmul]
  congr 1
  · -- Goal 1: left face sum
    simp only [Preadditive.comp_sum, Preadditive.comp_zsmul,
      ← coprojection_tensorHom_chainCrossProduct]
    rw [MonoidalCategory.tensorHom_comp_tensorHom_assoc, Category.comp_id]
    conv_rhs =>
      enter [1, 1, 2]
      rw [singChain_d_eq_alternatingFaceMapObjD (C := C) Δ[p + 1] p rfl]
    simp only [eqToHom_refl, Category.id_comp, AlternatingFaceMapComplex.objD,
      Preadditive.comp_sum, Preadditive.comp_zsmul,
      sum_tensor, Preadditive.sum_comp]
    apply Finset.sum_congr rfl; intro j _
    conv_lhs =>
      enter [2, 1, 1, 1]
      rw [show faceSimplex j = (Δ[p + 1] : SSet).δ j (idSimplex (p + 1)) from by
        simp [faceSimplex, idSimplex, SimplicialObject.δ, SSet.stdSimplex.map_apply]]
    rw [← Preadditive.zsmul_comp, ← Preadditive.zsmul_comp]
    congr 1
    conv_rhs => enter [1]; rw [Preadditive.zsmul_comp]
    conv_rhs => rw [MonoidalCategory.tensorHom_def, MonoidalLinear.smul_whiskerRight,
      Preadditive.zsmul_comp, ← MonoidalCategory.tensorHom_def]
    congr 1; congr 1
    rw [← simplexCoprojection_comp_eqToHom_comp_δ (C := C) rfl (idSimplex (p + 1)) j,
        eqToHom_refl, Category.id_comp]
  · -- Goal 2: right face sum
    congr 1
    simp only [Preadditive.comp_sum, Preadditive.comp_zsmul,
      ← coprojection_tensorHom_chainCrossProduct]
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
      rw [show faceSimplex j = (Δ[q + 1] : SSet).δ j (idSimplex (q + 1)) from by
        simp [faceSimplex, idSimplex, SimplicialObject.δ, SSet.stdSimplex.map_apply]]
    rw [← Preadditive.zsmul_comp]
    conv_rhs =>
      enter [1, 2]; rw [← Preadditive.zsmul_comp]
    conv_rhs =>
      enter [1]
      rw [MonoidalCategory.tensorHom_def', Preadditive.zsmul_comp,
        MonoidalLinear.whiskerLeft_smul, Preadditive.zsmul_comp,
        ← MonoidalCategory.tensorHom_def']
    congr 1; congr 1; congr 1
    rw [← simplexCoprojection_comp_eqToHom_comp_δ (C := C) rfl (idSimplex (q + 1)) j,
        eqToHom_refl, Category.id_comp]

/-- Simplex-level Leibniz rule for `chainCrossProduct`: the cross product of
`(s, t)` composed with the boundary equals the signed sum of face-map cross products.

This lifts `universalSimplexCrossProduct_boundary` from the standard simplices to
arbitrary simplices `s : S _⦋p+1⦌`, `t : T _⦋q+1⦌`,
by factoring through `ι(id) ≫ s_*` and using naturality + chain map condition. -/
lemma simplexCrossProduct_boundary {S T : SSet.{v}} (p q : ℕ)
    (s : S _⦋p + 1⦌) (t : T _⦋q + 1⦌) :
    (simplexCoprojection (C := C) s ⊗ₘ simplexCoprojection t) ≫
      chainCrossProduct (C := C) (show (p + 1) + (q + 1) = (p + 1) + (q + 1) from rfl) ≫
      (singChain (C := C) (S ⊗ₛ T)).d ((p + 1) + (q + 1)) (p + (q + 1)) =
    (simplexCoprojection s ⊗ₘ simplexCoprojection t) ≫
      ((singChain (C := C) S).d (p + 1) p ⊗ₘ
          𝟙 ((singChain (C := C) T).X (q + 1))) ≫
        chainCrossProduct (C := C) (show p + (q + 1) = p + (q + 1) from rfl) +
    ((-1 : ℤ) ^ (p + 1)) •
      ((simplexCoprojection s ⊗ₘ simplexCoprojection t) ≫
        (𝟙 ((singChain (C := C) S).X (p + 1)) ⊗ₘ
            (singChain (C := C) T).d (q + 1) q) ≫
          chainCrossProduct (C := C) (show p + (q + 1) = (p + 1) + q from by omega)) := by
  set fs := SSet.yonedaEquiv.symm s
  set ft := SSet.yonedaEquiv.symm t
  rw [simplexCoprojection_factor s, simplexCoprojection_factor t,
      ← MonoidalCategory.tensorHom_comp_tensorHom]
  simp only [Category.assoc]
  slice_lhs 2 3 => rw [(crossProduct_natural (C := C) fs ft).symm]
  simp only [Category.assoc]
  rw [((SCF (C := C)).map (fs ⊗ₘₛ ft)).comm ((p + 1) + (q + 1)) (p + (q + 1))]
  -- RHS Term 1: fuse (fs_* ⊗ ft_*) ≫ (d_S ⊗ 𝟙) into (fs_* ≫ d_S ⊗ ft_*),
  -- apply chain map comm fs_* ≫ d_S = d_Δ ≫ fs_*, then unfuse back
  conv_rhs =>
    enter [1, 2]
    rw [MonoidalCategory.tensorHom_comp_tensorHom_assoc,
        ((SCF (C := C)).map fs).comm (p + 1) p, Category.comp_id,
        ← Category.id_comp (((SCF (C := C)).map ft).f (q + 1)),
        ← MonoidalCategory.tensorHom_comp_tensorHom_assoc]
  -- RHS Term 2: fuse (fs_* ⊗ ft_*) ≫ (𝟙 ⊗ d_T) into (fs_* ⊗ ft_* ≫ d_T),
  -- apply chain map comm ft_* ≫ d_T = d_Δ ≫ ft_*, then unfuse back
  conv_rhs =>
    enter [2, 2, 2]
    rw [MonoidalCategory.tensorHom_comp_tensorHom_assoc,
        ((SCF (C := C)).map ft).comm (q + 1) q, Category.comp_id,
        ← Category.id_comp (((SCF (C := C)).map fs).f (p + 1)),
        ← MonoidalCategory.tensorHom_comp_tensorHom_assoc]
  -- Now each summand has ... ≫ (d ⊗ 𝟙) ≫ (fs_* ⊗ ft_*) ≫ chainCrossProduct.
  -- Use `crossProduct_natural` backwards:
  -- `(fs_* ⊗ ft_*) ≫ chainCrossProduct = chainCrossProduct ≫ (fs ⊗ ft)_*`.
  -- Term 1: navigate to (fs_* ⊗ ft_*) ≫ chainCrossProduct at position [2, 2] of the first summand
  conv_rhs =>
    enter [1, 2, 2]
    rw [(crossProduct_natural (C := C) fs ft).symm]
  -- Term 2: navigate to (fs_* ⊗ ft_*) ≫ chainCrossProduct at position [2, 2, 2] of the zsmul term
  conv_rhs =>
    enter [2, 2, 2, 2]
    rw [(crossProduct_natural (C := C) fs ft
      (show p + (q + 1) = (p + 1) + q from by omega)).symm]
  -- Factor out trailing ≫ (fs ⊗ ft)_* from both summands by left-associating
  simp only [← Category.assoc]
  rw [← Preadditive.zsmul_comp, ← Preadditive.add_comp]
  congr 1
  exact universalSimplexCrossProduct_coprojection_boundary p q

/-- **Leibniz rule** (chain map condition): The chain-level cross product is compatible
with the boundary operators. -/
theorem chainCrossProduct_leibniz {S T : SSet.{v}} (p q : ℕ) :
    chainCrossProduct (C := C) (show (p + 1) + (q + 1) = (p + 1) + (q + 1) from rfl) ≫
      (singChain (C := C) (S ⊗ₛ T)).d ((p + 1) + (q + 1)) (p + (q + 1)) =
    ((singChain (C := C) S).d (p + 1) p ⊗ₘ
        𝟙 ((singChain (C := C) T).X (q + 1))) ≫
      chainCrossProduct (C := C) (show p + (q + 1) = p + (q + 1) from rfl) +
    ((-1 : ℤ) ^ (p + 1)) •
      ((𝟙 ((singChain (C := C) S).X (p + 1)) ⊗ₘ
          (singChain (C := C) T).d (q + 1) q) ≫
        chainCrossProduct (C := C) (show p + (q + 1) = (p + 1) + q from by omega)) := by
  apply chainCrossProduct.ext
  ext ⟨s, t⟩
  simp only [chainTensorHomEquiv_apply]
  rw [Preadditive.comp_add, Preadditive.comp_zsmul]
  congr 1
  exact simplexCrossProduct_boundary (C := C) p q s t

/-! ### Edge cases for the Leibniz rule -/

/-- Edge case `(p+1, 0)`: the Leibniz rule when the right factor has degree 0. -/
theorem chainCrossProduct_leibniz_right_zero {S T : SSet.{v}} (p : ℕ) :
    chainCrossProduct (C := C) (show (p + 1) + 0 = (p + 1) + 0 from rfl) ≫
      (singChain (C := C) (S ⊗ₛ T)).d ((p + 1) + 0) (p + 0) =
    ((singChain (C := C) S).d (p + 1) p ⊗ₘ
        𝟙 ((singChain (C := C) T).X 0)) ≫
      chainCrossProduct (C := C) (show p + 0 = p + 0 from rfl) := by
  apply chainCrossProduct.ext; ext ⟨s, t⟩
  simp only [chainTensorHomEquiv_apply]
  congr 1
  -- LHS: unfold `crossProduct (p + 1, 0)` via
  -- `coprojection_tensorHom_chainCrossProduct` and `simplexCrossProduct_zero_right`.
  rw [← Category.assoc (simplexCoprojection s ⊗ₘ _)]
  rw [coprojection_tensorHom_chainCrossProduct]
  rw [simplexCrossProduct_zero_right (C := C)]
  -- LHS: expand d(S⊗T) into face map sum
  -- The indices are (p+1+0, p+0) which need to match (p+1, p)
  rw [Category.assoc,
    show (singChain (C := C) (S ⊗ₛ T)).d (p + 1 + 0) (p + 0) =
      (singChain (C := C) (S ⊗ₛ T)).d (p + 1) p from rfl,
    singChain_d_eq_alternatingFaceMapObjD (C := C) (S ⊗ₛ T) p rfl]
  simp only [eqToHom_refl, Category.id_comp, AlternatingFaceMapComplex.objD,
    Preadditive.comp_sum, Preadditive.comp_zsmul]
  -- RHS: fuse (ι s ⊗ ι t) ≫ (d_S ⊗ 𝟙) into ((ι s ≫ d_S) ⊗ ι t)
  conv_rhs =>
    rw [← Category.assoc, MonoidalCategory.tensorHom_comp_tensorHom, Category.comp_id]
  -- RHS: expand d_S
  conv_rhs =>
    enter [1, 1]
    rw [singChain_d_eq_alternatingFaceMapObjD (C := C) S p rfl]
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
  -- LHS: fold ι(shuffleSimplex ...) ≫ δⱼ as ι(δⱼ(shuffleSimplex ...))
  have fold_lhs := simplexCoprojection_comp_eqToHom_comp_δ (C := C) rfl
    (shuffleSimplex s t default (show p + 1 = (p + 1) + 0 by omega)) j
  simp only [eqToHom_refl, Category.id_comp] at fold_lhs
  rw [fold_lhs]
  -- RHS: fold ι s ≫ δⱼ as ι(δⱼ(s))
  conv_rhs =>
    enter [1, 1]
    rw [show simplexCoprojection (C := C) s ≫
        (((SimplicialObject.whiskering (Type v) C).obj ((sigmaConst (C := C)).obj (𝟙_ C))).obj
          S).δ j =
      simplexCoprojection (C := C) (S.δ j s) from by
      have := simplexCoprojection_comp_eqToHom_comp_δ (C := C) rfl s j
      simp only [eqToHom_refl, Category.id_comp] at this
      exact this]
  -- RHS: use coprojection_tensorHom_chainCrossProduct and simplexCrossProduct_zero_right
  rw [coprojection_tensorHom_chainCrossProduct]
  rw [simplexCrossProduct_zero_right (C := C)]
  -- Both sides: (λ_).hom ≫ ι(shuffleSimplex ...)
  -- Show δⱼ(shuffleSimplex s t default) = shuffleSimplex (S.δ j s) t default
  congr 2
  -- δⱼ(shuffleSimplex s t default) = shuffleSimplex (δⱼ s) t default
  -- Unfold shuffleSimplex: it's (S ⊗ T).map eqToHom.op (S.map fstHom.op s, T.map sndHom.op t)
  -- δⱼ on a tensor product acts componentwise, and for the default (n,0)-shuffle,
  -- fstHom = id and sndHom = the unique map to [0], so δⱼ passes through to the first factor.
  simp only [shuffleSimplex, SimplicialObject.δ]
  -- LHS: fold map ∘ map into map (comp), then expand componentwise
  rw [← FunctorToTypes.map_comp_apply]
  refine Prod.ext ?_ ?_
  · -- First component: S.map ((eqToHom ≫ δⱼ) ≫ fstHom).op s = S.map (eqToHom ≫ fstHom ≫ δⱼ).op s
    -- Both reduce to `S.map (eqToHom ≫ δⱼ ≫ fstHom).op s`
    -- versus `S.map (eqToHom ≫ fstHom).op (S.map δⱼ.op s)`.
    simp only [SSet.tensorObj_map_fst, ← FunctorToTypes.map_comp_apply]
    congr 1
  · -- Second component: T.map ((eqToHom ≫ δⱼ) ≫ sndHom).op t = T.map (eqToHom ≫ sndHom).op t
    -- δⱼ ≫ sndHom default = sndHom default since sndHom is the unique map to [0]
    simp only [SSet.tensorObj_map_snd, ← FunctorToTypes.map_comp_apply]
    congr 1

/-- Edge case `(0, q+1)`: the Leibniz rule when the left factor has degree 0. -/
theorem chainCrossProduct_leibniz_left_zero {S T : SSet.{v}} (q : ℕ) :
    (chainCrossProduct (C := C) (p := 0) (q := q + 1) :
        _ ⟶ (singChain (C := C) (S ⊗ₛ T)).X (q + 1)) ≫
      (singChain (C := C) (S ⊗ₛ T)).d (q + 1) q =
    (𝟙 ((singChain (C := C) S).X 0) ⊗ₘ
        (singChain (C := C) T).d (q + 1) q) ≫
      (chainCrossProduct (C := C) (p := 0) (q := q) :
        _ ⟶ (singChain (C := C) (S ⊗ₛ T)).X q) := by
  apply chainCrossProduct.ext; ext ⟨s, t⟩
  simp only [chainTensorHomEquiv_apply]
  congr 1
  -- LHS: use `coprojection_tensorHom_chainCrossProduct` to rewrite to
  -- `simplexCrossProduct`, then `simplexCrossProduct_zero_left`.
  rw [← Category.assoc (simplexCoprojection s ⊗ₘ _)]
  rw [coprojection_tensorHom_chainCrossProduct]
  rw [simplexCrossProduct_zero_left (C := C)]
  -- LHS: expand d(S⊗T) into face map sum
  rw [Category.assoc, singChain_d_eq_alternatingFaceMapObjD (C := C) (S ⊗ₛ T) q rfl]
  simp only [eqToHom_refl, Category.id_comp, AlternatingFaceMapComplex.objD,
    Preadditive.comp_sum, Preadditive.comp_zsmul]
  -- RHS: fuse (ι s ⊗ ι t) ≫ (𝟙 ⊗ d_T) into (ι s ⊗ (ι t ≫ d_T))
  conv_rhs =>
    rw [← Category.assoc, MonoidalCategory.tensorHom_comp_tensorHom]
    enter [1, 1]; rw [Category.comp_id]
  -- RHS: expand d_T
  conv_rhs =>
    enter [1, 2]
    rw [singChain_d_eq_alternatingFaceMapObjD (C := C) T q rfl]
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
  -- LHS: fold ι(shuffleSimplex ...) ≫ δⱼ as ι(δⱼ(shuffleSimplex ...))
  have fold_lhs := simplexCoprojection_comp_eqToHom_comp_δ (C := C) rfl
    (shuffleSimplex s t default (show q + 1 = 0 + (q + 1) by omega)) j
  simp only [eqToHom_refl, Category.id_comp] at fold_lhs
  rw [fold_lhs]
  -- RHS: fold ι t ≫ δⱼ as ι(δⱼ(t))
  conv_rhs =>
    enter [1, 2]
    rw [show simplexCoprojection (C := C) t ≫
        (((SimplicialObject.whiskering (Type v) C).obj ((sigmaConst (C := C)).obj (𝟙_ C))).obj
          T).δ j =
      simplexCoprojection (C := C) (T.δ j t) from by
      have := simplexCoprojection_comp_eqToHom_comp_δ (C := C) rfl t j
      simp only [eqToHom_refl, Category.id_comp] at this
      exact this]
  -- RHS: use coprojection_tensorHom_chainCrossProduct and simplexCrossProduct_zero_left
  rw [coprojection_tensorHom_chainCrossProduct]
  rw [simplexCrossProduct_zero_left (C := C)]
  -- Both sides: (λ_).hom ≫ ι(shuffleSimplex ...)
  congr 2
  -- δⱼ(shuffleSimplex s t default) = shuffleSimplex s (δⱼ t) default
  simp only [shuffleSimplex, SimplicialObject.δ]
  rw [← FunctorToTypes.map_comp_apply]
  refine Prod.ext ?_ ?_
  · -- First component: fstHom default = unique map from [0], so δⱼ ≫ fstHom = fstHom
    simp only [SSet.tensorObj_map_fst, ← FunctorToTypes.map_comp_apply]
    congr 1
  · -- Second component: both op-morphism compositions are equal in SimplexCategoryᵒᵖ
    simp only [SSet.tensorObj_map_snd, ← FunctorToTypes.map_comp_apply]
    -- Show the op-morphisms are equal by reducing to SimplexCategory via ext
    -- Both eqToHom ≫ sndHom default compose to a cast, so both sides are δ j (mod cast).
    refine congrFun (congrArg T.map ?_) t
    simp only [← op_comp]; congr 1
    -- In SimplexCategory: δ j ≫ eqToHom ≫ sndHom default = eqToHom ≫ sndHom default ≫ δ j
    ext ⟨i, hi⟩
    simp only [SimplexCategory.comp_toOrderHom, OrderHom.comp_coe, Function.comp_apply,
      SimplexCategory.Hom.toOrderHom_mk, SimplexCategory.eqToHom_toOrderHom,
      SimplexCategory.len_mk, Shuffle.sndHom, OrderHom.snd_coe]
    -- After unfolding, both sides are (succAbove j ⟨i, _⟩).val applied through default shuffles
    -- For default (0,n)-shuffle, (default x).2 = x (modulo cast)
    -- For the default (0,n)-shuffle, (default x).2 = x.cast, so both sides reduce to
    -- (δ j ⟨i, _⟩).val after cast normalization.
    change ((default : Shuffle 0 (q + 1)).1 _).2.val = _
    dsimp [Unique_Shuffle_0_n]
    -- LHS: (Fin.cast _ (δ j ⟨i, hi⟩)).val, RHS: (δ j (Fin.cast _ ⟨i, _⟩)).val
    -- Both are (δ j i).val since cast doesn't change the underlying Nat.
    -- For the default (0,n)-shuffle, (default x).2 = x.cast.
    -- Use `Unique.default` unfolding: default = Unique_Shuffle_0_n.default
    -- which maps x ↦ (0, x.cast).
    -- So (default x).2.val = x.val for any x.
    have snd_default : ∀ (n : ℕ) (x : Fin (0 + n + 1)),
        ((default : Shuffle 0 n).1 x).2.val = x.val := by
      intro n x; rfl
    simp only [snd_default]
    -- RHS: (Hom.mk succAbove.toOrderHom) (↑default ⟨i, ⋯⟩).2
    -- We need (↑default ⟨i, ⋯⟩).2.val = i, then both sides are succAbove j ⟨i, _⟩
    -- The goal is: ↑(succAbove j ⟨i, hi⟩) = ↑(succAbove j (↑default ⟨i, ⋯⟩).2)
    -- Show the Fin arguments are equal by showing their vals are equal
    -- Both sides apply succAbove j to a Fin whose val = i.
    -- LHS: (Fin.cast _ (δ j ⟨i, hi⟩)).val = (δ j ⟨i, hi⟩).val (cast preserves val)
    -- RHS: (δ j (default ⟨i, _⟩).2).val = (δ j ⟨i, _⟩).val (since (default x).2.val = x.val)
    -- Both equal (succAbove j ⟨i, _⟩).val.
    simp only [Fin.val_cast]
    -- Now: (δ j ⟨i, hi⟩).val = (δ j (↑default ⟨i, ⋯⟩).2).val
    -- Show the argument to δ j has the same val
    have : ((default : Shuffle 0 q).1 (⟨i, by
        simpa [SimplexCategory.len_mk] using hi⟩ : Fin (0 + q + 1))).2.val = i :=
      snd_default q _
    congr 1

/-- Chain map condition on the `(p+1, q+1)` summand.
Dispatches to `chainCrossProduct_leibniz`. -/
lemma eilenbergZilber_comm_case_pq {S T : SSet.{v}} (p q n m : ℕ)
    (hpq : (p + 1) + (q + 1) = n) (hnm : n = m + 1) :
    ιTensorObj (singChain (C := C) S) (singChain (C := C) T) (p + 1) (q + 1) n hpq ≫
      eilenbergZilber_f (C := C) S T n ≫ (singChain (C := C) (S ⊗ₛ T)).d n m =
    ιTensorObj (singChain (C := C) S) (singChain (C := C) T) (p + 1) (q + 1) n hpq ≫
      ((singChain (C := C) S).tensorObj (singChain (C := C) T)).d n m ≫
      eilenbergZilber_f (C := C) S T m := by
  have hm : m = p + (q + 1) := by omega
  subst hpq; subst hm
  rw [reassoc_of% (ι_eilenbergZilber_f (C := C) S T (p + 1) (q + 1)
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
    from rfl, one_smul]
  convert chainCrossProduct_leibniz (C := C) (S := S) (T := T) p q using 1
  congr 1
  · simp [MonoidalCategory.curriedTensor]
  · rw [Units.smul_def, Preadditive.zsmul_comp, Category.assoc, ι_eilenbergZilber_f]
    congr 1
    simp

/-- Chain map condition on the `(p+1, 0)` summand.
Dispatches to `chainCrossProduct_leibniz_right_zero`. -/
lemma eilenbergZilber_comm_case_p0 {S T : SSet.{v}} (p n m : ℕ)
    (hpq : (p + 1) + 0 = n) (hnm : n = m + 1) :
    ιTensorObj (singChain (C := C) S) (singChain (C := C) T) (p + 1) 0 n hpq ≫
      eilenbergZilber_f (C := C) S T n ≫ (singChain (C := C) (S ⊗ₛ T)).d n m =
    ιTensorObj (singChain (C := C) S) (singChain (C := C) T) (p + 1) 0 n hpq ≫
      ((singChain (C := C) S).tensorObj (singChain (C := C) T)).d n m ≫
      eilenbergZilber_f (C := C) S T m := by
  have hm : m = p := by omega
  subst hpq; subst hm
  rw [reassoc_of% (ι_eilenbergZilber_f (C := C) S T (m + 1) 0 (m + 1))]
  rw [HomologicalComplex.mapBifunctor.d_eq, Preadditive.add_comp,
    Preadditive.comp_add,
    HomologicalComplex.mapBifunctor.ι_D₁_assoc, HomologicalComplex.mapBifunctor.ι_D₂_assoc]
  have hd₂ : HomologicalComplex.mapBifunctor.d₂ (singChain (C := C) S) (singChain (C := C) T)
      (MonoidalCategory.curriedTensor C) (ComplexShape.down ℕ) (m + 1) 0 m = 0 :=
    HomologicalComplex.mapBifunctor.d₂_eq_zero _ _ _ _ _ _ _
      (fun h => by simp [ComplexShape.down_Rel] at h)
  simp only [hd₂, zero_comp, add_zero]
  rw [HomologicalComplex.mapBifunctor.d₁_eq _ _ _ _ (show (ComplexShape.down ℕ).Rel (m + 1) m
    from by simp [ComplexShape.down_Rel]) 0 m (by simp)]
  change chainCrossProduct _ ≫ _ = (_ • _) ≫ _
  rw [show (ComplexShape.down ℕ).ε₁ (ComplexShape.down ℕ) (ComplexShape.down ℕ) (m + 1, 0) = 1
    from rfl, one_smul, Category.assoc, ι_eilenbergZilber_f]
  convert chainCrossProduct_leibniz_right_zero (C := C) (S := S) (T := T) m using 1
  simp [MonoidalCategory.curriedTensor]

/-- Chain map condition on the `(0, q+1)` summand.
Dispatches to `chainCrossProduct_leibniz_left_zero`. -/
lemma eilenbergZilber_comm_case_0q {S T : SSet.{v}} (q n m : ℕ)
    (hpq : 0 + (q + 1) = n) (hnm : n = m + 1) :
    ιTensorObj (singChain (C := C) S) (singChain (C := C) T) 0 (q + 1) n hpq ≫
      eilenbergZilber_f (C := C) S T n ≫ (singChain (C := C) (S ⊗ₛ T)).d n m =
    ιTensorObj (singChain (C := C) S) (singChain (C := C) T) 0 (q + 1) n hpq ≫
      ((singChain (C := C) S).tensorObj (singChain (C := C) T)).d n m ≫
      eilenbergZilber_f (C := C) S T m := by
  have hm : m = q := by omega
  have hn : n = q + 1 := by omega
  subst hm; subst hn
  rw [reassoc_of% (ι_eilenbergZilber_f (C := C) S T 0 (m + 1) (m + 1))]
  rw [HomologicalComplex.mapBifunctor.d_eq, Preadditive.add_comp,
    Preadditive.comp_add,
    HomologicalComplex.mapBifunctor.ι_D₁_assoc, HomologicalComplex.mapBifunctor.ι_D₂_assoc]
  have hd₁ : HomologicalComplex.mapBifunctor.d₁ (singChain (C := C) S) (singChain (C := C) T)
      (MonoidalCategory.curriedTensor C) (ComplexShape.down ℕ) 0 (m + 1) m = 0 :=
    HomologicalComplex.mapBifunctor.d₁_eq_zero _ _ _ _ _ _ _
      (fun h => by simp [ComplexShape.down_Rel] at h)
  simp only [hd₁, zero_comp, zero_add]
  rw [HomologicalComplex.mapBifunctor.d₂_eq _ _ _ _ _ (show (ComplexShape.down ℕ).Rel (m + 1) m
    from by simp [ComplexShape.down_Rel]) m (by simp)]
  change chainCrossProduct _ ≫ _ = (_ • _) ≫ _
  rw [show (ComplexShape.down ℕ).ε₂ (ComplexShape.down ℕ) (ComplexShape.down ℕ) (0, m + 1) = 1
    from by simp [ComplexShape.ε₂, ComplexShape.ε], one_smul, Category.assoc, ι_eilenbergZilber_f]
  convert chainCrossProduct_leibniz_left_zero (C := C) (S := S) (T := T) m using 1
  simp [MonoidalCategory.curriedTensor]
/-- The Eilenberg–Zilber chain map condition: `eilenbergZilber_f` commutes with
the differentials. Case-splits on the `(p, q)` summand. -/
lemma eilenbergZilber_comm (S T : SSet.{v}) (n m : ℕ) (hnm : n = m + 1) :
    eilenbergZilber_f (C := C) S T n ≫ (singChain (C := C) (S ⊗ₛ T)).d n m =
    ((singChain (C := C) S).tensorObj (singChain (C := C) T)).d n m ≫
      eilenbergZilber_f (C := C) S T m := by
  apply HomologicalComplex.mapBifunctor.hom_ext
  intro p q hpq
  change p + q = n at hpq
  rcases p with _ | p <;> rcases q with _ | q
  · omega
  · exact eilenbergZilber_comm_case_0q q n m hpq hnm
  · exact eilenbergZilber_comm_case_p0 p n m hpq hnm
  · exact eilenbergZilber_comm_case_pq p q n m hpq hnm
/-- **Eilenberg–Zilber cross product chain map** for simplicial sets.

The cross product of singular chains, packaged as a chain map from the tensor
product of singular chain complexes to the singular chain complex of the monoidal product:
```
  eilenbergZilber :
    (singChain (C := C) S).tensorObj (singChain (C := C) T) ⟶
      singChain (C := C) (S ⊗ T)
``` -/
noncomputable def eilenbergZilber (S T : SSet.{v}) :
    (singChain (C := C) S).tensorObj (singChain (C := C) T) ⟶ singChain (C := C) (S ⊗ₛ T) where
  f n := eilenbergZilber_f (C := C) S T n
  comm' n m hnm := by
    have h : n = m + 1 := by rw [ComplexShape.down_Rel] at hnm; omega
    exact eilenbergZilber_comm (C := C) S T n m h

/-! ### Eilenberg–Zilber as a natural transformation

The Eilenberg–Zilber map is natural in `(S, T)`: for simplicial maps `f : S₁ ⟶ S₂`
and `g : T₁ ⟶ T₂`, the square
```
  C_*(S₁) ⊗ C_*(T₁) --EZ--> C_*(S₁ ⊗ T₁)
        |                          |
  f_* ⊗ g_*                  (f ⊗ g)_*
        |                          |
  C_*(S₂) ⊗ C_*(T₂) --EZ--> C_*(S₂ ⊗ T₂)
```
commutes. We package this as a `NatTrans` between two functors
`SSet.{v} × SSet.{v} ⥤ ChainComplex C ℕ`.
-/


/-- **Naturality of the Eilenberg–Zilber map at a pair of morphisms `(f, g)`.**

For simplicial maps `f : S₁ ⟶ S₂` and `g : T₁ ⟶ T₂`:
```
  eilenbergZilber S₁ T₁ ≫ (SCF (C := C)).map (f ⊗ g) =
    tensorHom ((SCF (C := C)).map f) ((SCF (C := C)).map g) ≫ eilenbergZilber S₂ T₂
``` -/
lemma eilenbergZilber_natural {S₁ S₂ T₁ T₂ : SSet.{v}} (f : S₁ ⟶ S₂) (g : T₁ ⟶ T₂) :
    eilenbergZilber (C := C) S₁ T₁ ≫ (SCF (C := C)).map (f ⊗ₘₛ g) =
    HomologicalComplex.tensorHom ((SCF (C := C)).map f) ((SCF (C := C)).map g) ≫
      eilenbergZilber (C := C) S₂ T₂ := by
  apply HomologicalComplex.Hom.ext; funext n
  apply HomologicalComplex.mapBifunctor.hom_ext; intro p q h
  simp only [HomologicalComplex.comp_f, eilenbergZilber]
  change
      HomologicalComplex.ιTensorObj
        (singChain (C := C) S₁) (singChain (C := C) T₁) p q n (by omega) ≫
      eilenbergZilber_f S₁ T₁ n ≫ ((SCF (C := C)).map (f ⊗ₘₛ g)).f n =
    HomologicalComplex.ιTensorObj
      (singChain (C := C) S₁) (singChain (C := C) T₁) p q n (by omega) ≫
      (HomologicalComplex.tensorHom ((SCF (C := C)).map f) ((SCF (C := C)).map g)).f n ≫
        eilenbergZilber_f S₂ T₂ n
  rw [reassoc_of% (ι_eilenbergZilber_f (C := C) S₁ T₁ p q n h)]
  rw [HomologicalComplex.ι_mapBifunctorMap_assoc, ι_eilenbergZilber_f]
  rw [crossProduct_natural (C := C) f g (hn := h.symm)]
  simp [Category.assoc, MonoidalCategory.tensorHom_def]

section EilenbergZilberAssembly
variable [CategoryWithHomology C] [SymmetricCategory C] [MonoidalClosed C]

variable [∀ (X : C), PreservesFiniteCoproducts (MonoidalCategory.tensorRight X)]

-- Caching the `MonoidalCategory` instance avoids a heartbeat-expensive synthesis chain
-- through `GradedObject.HasTensor`, `HasGoodTensor₁₂Tensor`, etc.
noncomputable instance chainComplexMonoidal : MonoidalCategory (ChainComplex C ℕ) :=
  HomologicalComplex.monoidalCategory C (ComplexShape.down ℕ)


/-- **The Eilenberg–Zilber cross product as a natural transformation** for simplicial sets.

A natural transformation from the tensor product of singular chain complexes to the
singular chain complex of the monoidal product:
```
  (SSet.singularChainComplexFunctor C).obj (𝟙_ C) × ... ⋙ ⊗_{ChainComplex} ⟶ ⊗_{SSet} ⋙ ...
```
i.e., `C_*(S) ⊗ C_*(T) → C_*(S ⊗ T)` naturally in `S, T : SSet`. -/
noncomputable def eilenbergZilberNatTrans :
    Functor.prod ((SSet.singularChainComplexFunctor.{v} C).obj (𝟙_ C))
        ((SSet.singularChainComplexFunctor.{v} C).obj (𝟙_ C)) ⋙
      MonoidalCategory.tensor (C := ChainComplex C ℕ) ⟶
    MonoidalCategory.tensor (C := SSet) ⋙
      (SSet.singularChainComplexFunctor.{v} C).obj (𝟙_ C) :=
  { app := fun p => eilenbergZilber (C := C) p.1 p.2
    naturality := fun _ _ f => (eilenbergZilber_natural f.1 f.2).symm }

end EilenbergZilberAssembly
end MonoidalLinear
end MonoidalCoherence
end MonoidalAdditive
end MonoidalFree
end FreeForgetful
end BasicChainComplex

end HomologyLean.SingularHomology.SSetEZ

section TopCatEilenbergZilber
variable {C : Type u} [Category.{v} C] [HasCoproducts C] [Preadditive C]
  [CategoryWithHomology C] [MonoidalCategory C] [SymmetricCategory C]
  [MonoidalPreadditive C] [MonoidalClosed C] [HasForget.{v} C]
  [MonoidalUnitorRepresentable (C := C)] [(forget C).IsRightAdjoint]
  [(forget C).leftAdjoint.Monoidal] [(forget C).LaxMonoidal]
  [(Adjunction.ofIsRightAdjoint (forget C)).IsMonoidal]
  [NatTrans.IsMonoidal (MonoidalUnitorRepresentable.forgetIso (C := C)).hom]
  [MonoidalLinear ℤ C]
  [∀ (X : C), PreservesFiniteCoproducts (MonoidalCategory.tensorRight X)]

/-! ### `TopCat.toSSet` preserves binary products

`TopCat.toSSet` is a right adjoint (to `SSet.toTop` via `sSetTopAdj`), so it preserves
all limits. We register the `IsRightAdjoint` instance so that Mathlib's automatic
`PreservesLimitsOfSize` kicks in, giving `PreservesLimit (pair X Y) TopCat.toSSet`. -/

noncomputable instance : CartesianMonoidalCategory TopCat := .ofHasFiniteProducts

noncomputable instance : TopCat.toSSet.IsRightAdjoint :=
  ⟨SSet.toTop, ⟨sSetTopAdj⟩⟩

/-- `TopCat.toSSet` commutes with monoidal products, naturally in both variables.

The natural isomorphism `⊗_TopCat ⋙ toSSet ≅ (toSSet × toSSet) ⋙ ⊗_SSet`
between functors `TopCat × TopCat ⥤ SSet`. -/
noncomputable def TopCat.toSSet_prodNatIso :
    MonoidalCategory.tensor (C := TopCat) ⋙ TopCat.toSSet ≅
    TopCat.toSSet.prod TopCat.toSSet ⋙
      MonoidalCategory.tensor (C := SSet) :=
  letI : TopCat.toSSet.Monoidal := Functor.Monoidal.ofChosenFiniteProducts _
  (Functor.Monoidal.μNatIso TopCat.toSSet).symm

open HomologyLean.SingularHomology.SSetEZ in
/-- Internal form of the TopCat Eilenberg–Zilber nat trans, using the private `SCF` abbreviation.
See `TopCat.eilenbergZilberNatTrans` for the public API. -/
noncomputable def TopCat.eilenbergZilberNatTrans' :
    Functor.prod (TopCat.toSSet ⋙ SCF (C := C)) (TopCat.toSSet ⋙ SCF (C := C)) ⋙
      MonoidalCategory.tensor (C := ChainComplex C ℕ) ⟶
    MonoidalCategory.tensor (C := TopCat) ⋙ TopCat.toSSet ⋙ SCF (C := C) :=
  (TopCat.toSSet.prod TopCat.toSSet).whiskerLeft
      (HomologyLean.SingularHomology.SSetEZ.eilenbergZilberNatTrans (C := C)) ≫
    Functor.whiskerRight toSSet_prodNatIso.inv (SCF (C := C))

open HomologyLean.SingularHomology.SSetEZ AlgebraicTopology in
/-- **The Eilenberg–Zilber cross product for topological spaces.**

A natural transformation `C_*(X) ⊗ C_*(Y) → C_*(X × Y)` for `X, Y : TopCat`,
obtained by pasting `toSSet_prodNatIso` with the SSet-level `eilenbergZilberNatTrans`. -/
noncomputable def TopCat.eilenbergZilberNatTrans :
    Functor.prod ((singularChainComplexFunctor.{v} C).obj (𝟙_ C))
        ((singularChainComplexFunctor.{v} C).obj (𝟙_ C)) ⋙
      MonoidalCategory.tensor (C := ChainComplex C ℕ) ⟶
    MonoidalCategory.tensor (C := TopCat) ⋙
      (singularChainComplexFunctor.{v} C).obj (𝟙_ C) :=
  TopCat.eilenbergZilberNatTrans'

end TopCatEilenbergZilber
