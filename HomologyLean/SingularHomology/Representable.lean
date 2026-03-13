/-
  Representable functor notation and related classes.

  Scoped notation for the covariant and contravariant representable functors,
  and the `MonoidalUnitorRepresentable` typeclass asserting that `Hom(𝟙_ C, -)`
  has a left adjoint.
-/
import Mathlib.CategoryTheory.Yoneda
import Mathlib.CategoryTheory.Monoidal.Category
import Mathlib.CategoryTheory.Adjunction.Basic
import Mathlib.CategoryTheory.Adjunction.Unique
import Mathlib.CategoryTheory.ConcreteCategory.Basic
import Mathlib.CategoryTheory.Monoidal.Closed.Types
import Mathlib.CategoryTheory.Limits.Shapes.Products
import Mathlib.Algebra.Category.ModuleCat.Monoidal.Closed

open CategoryTheory
open scoped MonoidalCategory

universe u v

/-- The covariant representable functor `Hom(X, -)`. -/
scoped[Representable] notation "Hom[" X " |-]" => coyoneda.obj (Opposite.op X)

/-- The contravariant representable functor `Hom(-, X)`. -/
scoped[Representable] notation "Hom[-| " X "]" => yoneda.obj X

open Representable
-- Note this doesn't require the forgetful functor to be right adjoint, only that it is faithful
variable (C : Type u) [Category.{v} C] [MonoidalCategory C] [HasForget.{v} C]

/-- The forgetful functor `forget C` is naturally isomorphic to `Hom(𝟙_ C, -)`. -/
class MonoidalUnitorRepresentable where
  forgetIso : forget C ≅ Hom[𝟙_ C |-]

-- `forget (Type u) = 𝟭 _` and `Hom[PUnit |-]` sends `X` to `(PUnit → X) ≃ X`.
instance : MonoidalUnitorRepresentable (C := Type u) where
  forgetIso := Coyoneda.punitIso.symm

section ModuleCat

-- `𝟙_ (ModuleCat R) = R` as a module over itself; `Hom(R, M)` is naturally isomorphic
-- to the underlying type of `M` via `f ↦ f 1` / `x ↦ (r ↦ r • x)`.
instance {R : Type u} [CommRing R] : MonoidalUnitorRepresentable (C := ModuleCat.{u} R) where
  forgetIso := sorry

end ModuleCat

section SigmaConstIsoFree

variable {C : Type u} [Category.{v} C] [Limits.HasCoproducts C] [MonoidalCategory C]
  [HasForget.{v} C] [MonoidalUnitorRepresentable (C := C)]
  [(forget C).IsRightAdjoint]

/-- `Limits.sigmaConst.obj (𝟙_ C)` is naturally isomorphic to
the abstract free functor `(forget C).leftAdjoint`. Both send a set `A` to
the "free object on `A`": `sigmaConst` uses `∐ (fun _ : A => 𝟙_ C)`, while
`leftAdjoint` is the abstract left adjoint to the forgetful functor. -/
noncomputable def sigmaConstIsoFree :
    Limits.sigmaConst.obj (𝟙_ C) ≅ (forget C).leftAdjoint := by
  have adj1 : Limits.sigmaConst.obj (𝟙_ C) ⊣ (Hom[𝟙_ C |-] : C ⥤ Type v) :=
    Limits.sigmaConstAdj (𝟙_ C)
  have adj2 : Limits.sigmaConst.obj (𝟙_ C) ⊣ forget C :=
    adj1.ofNatIsoRight (MonoidalUnitorRepresentable.forgetIso (C := C)).symm
  exact Adjunction.leftAdjointUniq adj2 (Adjunction.ofIsRightAdjoint (forget C))

end SigmaConstIsoFree
