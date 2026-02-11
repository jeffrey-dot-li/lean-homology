/-
  The long exact sequence of singular homology for a topological pair.

  Given a pair (X, A) with inclusion i : A ⟶ X (mono), we construct the
  6-term exact sequence:
    H_{n+1}(A) → H_{n+1}(X) → H_{n+1}(X,A) →[δ] H_n(A) → H_n(X) → H_n(X,A)

  This follows by applying the abstract homology LES machinery
  (`composableArrows₅_exact`) to the short exact sequence of chain complexes
  from `Relative.lean`.
-/
import Mathlib.Algebra.Homology.HomologySequenceLemmas
import HomologyLean.SingularHomology.Relative

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicTopology
open HomologicalComplex HomologicalComplex.HomologySequence

universe u v

variable (C : Type u) [Category.{v} C] [Abelian C] [HasCoproducts C]

namespace HomologyLean.SingularHomology

/-! ## The connecting homomorphism -/

/-- The connecting homomorphism `δ : H_n(X, A; R) → H_{n-1}(A; R)` in the
long exact sequence of a pair. It is defined as the connecting homomorphism
of the short exact sequence `0 → C_*(A) → C_*(X) → C_*(X,A) → 0`. -/
def connectingMorphism (R : C) {A X : TopCat} (i : A ⟶ X) [Mono i]
    (n₁ n₀ : ℕ) (h : (ComplexShape.down ℕ).Rel n₁ n₀) :
    (relativeSingularChainComplex C R i).homology n₁ ⟶
      (singularChains C R A).homology n₀ :=
  (relativeSingularChainSES_shortExact C R i).δ n₁ n₀ h

/-! ## The long exact sequence -/

/-- The 6-term composable arrows in the homology LES of a pair (X, A).
For each pair of consecutive indices `n₁ > n₀`, this is the sequence:
  H_{n₁}(A) → H_{n₁}(X) → H_{n₁}(X,A) → H_{n₀}(A) → H_{n₀}(X) → H_{n₀}(X,A) -/
def singularHomologyLES (R : C) {A X : TopCat} (i : A ⟶ X) [Mono i]
    (n₁ n₀ : ℕ) (h : (ComplexShape.down ℕ).Rel n₁ n₀) :
    ComposableArrows C 5 :=
  composableArrows₅ (relativeSingularChainSES_shortExact C R i) n₁ n₀ h

/-- The 6-term homology LES of a pair is exact. -/
theorem singularHomologyLES_exact (R : C) {A X : TopCat} (i : A ⟶ X) [Mono i]
    (n₁ n₀ : ℕ) (h : (ComplexShape.down ℕ).Rel n₁ n₀) :
    (singularHomologyLES C R i n₁ n₀ h).Exact :=
  composableArrows₅_exact (relativeSingularChainSES_shortExact C R i) n₁ n₀ h

/-! ## Naturality -/

/-- The connecting homomorphism is natural with respect to maps of pairs.

Given a commutative diagram of pairs `(f, fA) : (X, A) → (Y, B)`,
the connecting homomorphisms fit into a commutative square:
```
  H_n(X, A) --δ-→ H_{n-1}(A)
      |                |
   f_*|            fA_*|
      ↓                ↓
  H_n(Y, B) --δ-→ H_{n-1}(B)
```
-/
theorem connectingMorphism_natural (R : C) {A X B Y : TopCat}
    (i : A ⟶ X) (j : B ⟶ Y) (f : X ⟶ Y) (fA : A ⟶ B)
    (comm : fA ≫ j = i ≫ f) [Mono i] [Mono j]
    (n₁ n₀ : ℕ) (h : (ComplexShape.down ℕ).Rel n₁ n₀) :
    connectingMorphism C R i n₁ n₀ h ≫
      homologyMap (singularChainMap C R fA) n₀ =
    homologyMap (relativeSingularChainMap C R i j f fA comm) n₁ ≫
      connectingMorphism C R j n₁ n₀ h := by
  simp only [connectingMorphism]
  -- Apply Mathlib's abstract δ-naturality to the morphism of short exact sequences
  -- φ : (C_*(A) → C_*(X) → C_*(X,A)) ⟶ (C_*(B) → C_*(Y) → C_*(Y,B))
  have := δ_naturality
    (ShortComplex.homMk
      (singularChainMap C R fA)
      (singularChainMap C R f)
      (relativeSingularChainMap C R i j f fA comm)
      (by simp only [relativeSingularChainSC, singularChainMap, ← Functor.map_comp, comm])
      (by simp only [relativeSingularChainSC, relativeSingularChainComplex.π,
            relativeSingularChainMap, Limits.cokernel.π_desc]))
    (relativeSingularChainSES_shortExact C R i)
    (relativeSingularChainSES_shortExact C R j) n₁ n₀ h
  simp only [ShortComplex.homMk_τ₁, ShortComplex.homMk_τ₃] at this
  exact this

end HomologyLean.SingularHomology
