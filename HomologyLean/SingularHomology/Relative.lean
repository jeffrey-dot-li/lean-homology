/-
  Relative singular chains and homology for a topological pair (X, A).

  Given a subspace inclusion i : A ⟶ X, we define:
  - The chain map C_*(A) → C_*(X) induced by inclusion
  - The relative chain complex C_*(X, A) := cokernel of the inclusion
  - Relative singular homology H_n(X, A; R)
  - The short exact sequence 0 → C_*(A) → C_*(X) → C_*(X,A) → 0
-/
import Mathlib.AlgebraicTopology.SingularHomology.Basic
import Mathlib.Algebra.Homology.HomologicalComplexAbelian
import Mathlib.Algebra.Homology.ShortComplex.ShortExact
import Mathlib.CategoryTheory.Limits.MonoCoprod

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicTopology HomologicalComplex

universe u v

variable (C : Type u) [Category.{v} C] [Abelian C] [HasCoproducts C]

namespace HomologyLean.SingularHomology

/-! ## Singular chain map induced by a continuous map -/

/-- The singular chain complex of a space X with coefficients in R.
This is `((singularChainComplexFunctor C).obj R).obj X`. -/
abbrev singularChains (R : C) (X : TopCat) : ChainComplex C ℕ :=
  ((singularChainComplexFunctor C).obj R).obj X

/-- The chain map `C_*(A; R) → C_*(X; R)` induced by a continuous map `i : A ⟶ X`. -/
abbrev singularChainMap (R : C) {A X : TopCat} (i : A ⟶ X) :
    singularChains C R A ⟶ singularChains C R X :=
  ((singularChainComplexFunctor C).obj R).map i

/-! ## Relative singular chain complex -/

/-- The relative singular chain complex `C_*(X, A; R)`, defined as the cokernel
of the chain map `C_*(A; R) → C_*(X; R)` induced by the inclusion `i : A ⟶ X`.

Since `HomologicalComplex C c` is abelian when `C` is abelian, the cokernel
exists and is itself a chain complex. -/
def relativeSingularChainComplex (R : C) {A X : TopCat} (i : A ⟶ X) :
    ChainComplex C ℕ :=
  Limits.cokernel (singularChainMap C R i)

/-- The projection `C_*(X; R) → C_*(X, A; R)`. -/
def relativeSingularChainComplex.π (R : C) {A X : TopCat} (i : A ⟶ X) :
    singularChains C R X ⟶ relativeSingularChainComplex C R i :=
  Limits.cokernel.π (singularChainMap C R i)

/-! ## Relative singular homology -/

/-- The relative singular homology `H_n(X, A; R)`, defined as the n-th homology
of the relative chain complex `C_*(X, A; R)`. -/
def relativeSingularHomology (n : ℕ) (R : C) {A X : TopCat} (i : A ⟶ X) : C :=
  (relativeSingularChainComplex C R i).homology n

/-! ## The short exact sequence of chain complexes -/

/-- The short complex `C_*(A) → C_*(X) → C_*(X, A)` of chain complexes. -/
def relativeSingularChainSC (R : C) {A X : TopCat} (i : A ⟶ X) :
    ShortComplex (ChainComplex C ℕ) :=
  ShortComplex.mk
    (singularChainMap C R i)
    (relativeSingularChainComplex.π C R i)
    (Limits.cokernel.condition _)

/-- The short complex `C_*(A) → C_*(X) → C_*(X, A)` is exact at `C_*(X)`,
since `π` is the cokernel of the inclusion map. -/
theorem relativeSingularChainSC_exact (R : C) {A X : TopCat} (i : A ⟶ X) :
    (relativeSingularChainSC C R i).Exact :=
  ShortComplex.exact_of_g_is_cokernel _ (Limits.cokernelIsCokernel _)

/-- The projection in the relative SES is epi. -/
instance relativeSingularChainSC_epi_g (R : C) {A X : TopCat} (i : A ⟶ X) :
    Epi (relativeSingularChainSC C R i).g := by
  change Epi (Limits.cokernel.π (singularChainMap C R i))
  infer_instance

/-! ## Monomorphism of the inclusion map

The chain map `C_*(A) → C_*(X)` is mono when `i : A ⟶ X` is mono.
This requires that the singular chain complex functor preserves monomorphisms.
This is the main technical content needed to make the SES short exact. -/

/-- The chain map induced by a mono `i : A ↪ X` is mono.

**Proof sketch** (sorry'd): The functor `singularChainComplexFunctor` is a
composition of functors that preserve monomorphisms:
1. `TopCat.toSSet` sends monos to degreewise monos (since the singular set
   of a subspace is a sub-simplicial-set)
2. The free abelian group functor `∐ (fun _ => R)` preserves monos
   (coproducts of monos are mono in abelian categories)
3. The alternating face map complex preserves degreewise monos. -/
theorem singularChainMap_mono (R : C) {A X : TopCat} (i : A ⟶ X) [Mono i] :
    Mono (singularChainMap C R i) := by
  apply HomologicalComplex.mono_of_mono_f
  intro n
  dsimp [singularChainMap, singularChainComplexFunctor, SSet.singularChainComplexFunctor]
  apply CategoryTheory.Limits.MonoCoprod.mono_map'_of_injective
  intro σ₁ σ₂ h
  simp only [TopCat.toSSet, Presheaf.restrictedULiftYoneda_map_app] at h
  dsimp [uliftYoneda] at h
  exact ULift.ext _ _ ((cancel_mono i).mp (congrArg ULift.down h))

/-- When `i : A ⟶ X` is mono, the relative singular chain sequence is short exact. -/
theorem relativeSingularChainSES_shortExact (R : C) {A X : TopCat} (i : A ⟶ X) [Mono i] :
    (relativeSingularChainSC C R i).ShortExact where
  exact := relativeSingularChainSC_exact C R i
  mono_f := singularChainMap_mono C R i
  epi_g := relativeSingularChainSC_epi_g C R i

/-! ## Functoriality of relative homology -/

/-- A map of pairs `(f, f|_A) : (X, A) → (Y, B)` induces a map on relative chain complexes.

Given `f : X ⟶ Y` and `fA : A ⟶ B` such that `fA ≫ j = i ≫ f` (the restriction diagram
commutes), we get a map `C_*(X, A) → C_*(Y, B)`. -/
def relativeSingularChainMap (R : C) {A X B Y : TopCat}
    (i : A ⟶ X) (j : B ⟶ Y) (f : X ⟶ Y) (fA : A ⟶ B)
    (comm : fA ≫ j = i ≫ f) :
    relativeSingularChainComplex C R i ⟶ relativeSingularChainComplex C R j :=
  Limits.cokernel.map _ _ (singularChainMap C R fA) (singularChainMap C R f)
    (by simp only [singularChainMap, ← Functor.map_comp, comm])

end HomologyLean.SingularHomology
