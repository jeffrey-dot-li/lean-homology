/-
Copyright (c) 2021 Shing Tak Lam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shing Tak Lam
-/
import Mathlib.CategoryTheory.Category.Init
import Mathlib.Data.Finset.Attr
import Mathlib.Tactic.Common
import Mathlib.Tactic.Finiteness.Attr
import Mathlib.Tactic.SetLike
import Mathlib.Util.CompileInductive
import Mathlib.CategoryTheory.Groupoid
import Mathlib.Topology.Category.TopCat.Basic
import Mathlib.Topology.Homotopy.Path
import Mathlib.Data.Set.Subsingleton
import Mathlib.AlgebraicTopology.FundamentalGroupoid.Basic

/-!
# Fundamental groupoid of a space

Given a topological space `X`, we can define the fundamental groupoid of `X` to be the category with
objects being points of `X`, and morphisms `x ⟶ y` being paths from `x` to `y`, quotiented by
homotopy equivalence. With this, the fundamental group of `X` based at `x` is just the automorphism
group of `x`.
-/

open CategoryTheory

universe u

variable {X : Type u} [TopologicalSpace X]
variable {x₀ x₁ : X}

noncomputable section

open unitInterval


namespace FundamentalGroupoid

-- TODO: It seems that `Equiv.nontrivial_congr` doesn't exist.
-- Once it is added, please add the corresponding lemma and instance.

instance {X : Type u} [Inhabited X] : Inhabited (FundamentalGroupoid X) :=
  ⟨⟨default⟩⟩

attribute [local instance] Path.Homotopic.setoid

/-- Variation of `fromPath` that uses `Path` instead of `Path.Homotopic.Quotient`. -/
abbrev fromPath' {X : Type*} [TopologicalSpace X] {x₀ x₁ : X} (f : Path x₀ x₁) : mk x₀ ⟶ mk x₁ :=
  Quotient.mk _ f

@[simp] lemma fromPath'_refl {X : Type*} [TopologicalSpace X] {x : X} :
    fromPath' (Path.refl x) = 𝟙 _ := rfl

@[simp] lemma fromPath'_symm {X : Type*} [TopologicalSpace X] {x₀ x₁ : X} (f : Path x₀ x₁) :
    fromPath' f.symm = inv (fromPath' f) := by
  rw [← Groupoid.inv_eq_inv]
  rfl

@[simp] lemma fromPath'_trans {X : Type*} [TopologicalSpace X] {x₀ x₁ x₂ : X} (f : Path x₀ x₁)
    (g : Path x₁ x₂) : fromPath' (f.trans g) = (fromPath' f) ≫ (fromPath' g) := rfl

/-- Two paths are equal in the fundamental groupoid if and only if they are homotopic. -/
theorem fromPath'_eq_iff_homotopic {X : Type*} [TopologicalSpace X] {x₀ x₁ : X}
    (f : Path x₀ x₁) (g : Path x₀ x₁) : fromPath' f = fromPath' g ↔ f.Homotopic g :=
  ⟨fun ih ↦ Quotient.exact ih, fun h ↦ Quotient.sound h⟩



declare_aesop_rule_sets [path_simps]

end FundamentalGroupoid
