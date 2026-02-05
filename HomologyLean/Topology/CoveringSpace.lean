import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import Mathlib.AlgebraicTopology.FundamentalGroupoid.FundamentalGroup
import Mathlib.AlgebraicTopology.FundamentalGroupoid.SimplyConnected
import Mathlib.Topology.Homotopy.Lifting
import Mathlib.Topology.Connected.PathConnected
import Mathlib.Analysis.Convex.Contractible
import Mathlib.Algebra.Group.TypeTags.Basic
-- import Mathlib.Topology.Homeomorph.Defs
import HomologyLean.FundamentalGroupoid.Basic

/-!
# Covering Spaces

This file contains results about covering spaces, including pullback properties.

## Main results

* `IsCoveringMap.pullback`: The pullback of a covering map along a continuous map is a covering map.
-/

open Topology

variable {X X' Y : Type*} [TopologicalSpace X] [TopologicalSpace X'] [TopologicalSpace Y]

/-- The pullback (fiber product) of p : X' → X along f : Y → X
in the category of topological spaces.
This is a subtype of Y × X' with the subspace topology. -/
def Pullback (p : X' → X) (f : Y → X) : Type _ :=
  {yx : Y × X' // f yx.1 = p yx.2}

/-- The pullback has the subspace topology from Y × X'. -/
instance Pullback.instTopologicalSpace (p : X' → X) (f : Y → X) :
    TopologicalSpace (Pullback p f) :=
  instTopologicalSpaceSubtype

/-- The projection from the pullback to Y. -/
def Pullback.proj₁ (p : X' → X) (f : Y → X) : Pullback p f → Y :=
  fun yx => yx.val.1

/-- The projection from the pullback to X'. -/
def Pullback.proj₂ (p : X' → X) (f : Y → X) : Pullback p f → X' :=
  fun yx => yx.val.2

/-- The first projection is continuous. -/
theorem Pullback.continuous_proj₁ (p : X' → X) (f : Y → X) :
    Continuous (Pullback.proj₁ p f) :=
  Continuous.fst continuous_subtype_val

/-- The second projection is continuous. -/
theorem Pullback.continuous_proj₂ (p : X' → X) (f : Y → X) :
    Continuous (Pullback.proj₂ p f) :=
  Continuous.snd continuous_subtype_val

/-- The pullback square commutes. -/
theorem Pullback.comm (p : X' → X) (f : Y → X)  :
    f ∘ (Pullback.proj₁ p f) = p ∘ (Pullback.proj₂ p f) := by
    ext yx
    exact yx.property


/-- The preimage under proj₁ of f⁻¹(U) equals the preimage under proj₂ of p⁻¹(U).
This follows from the commutativity of the pullback square. -/
theorem Pullback.preimage_proj₁_eq_preimage_proj₂ (p : X' → X) (f : Y → X) (U : Set X) :
    Pullback.proj₁ p f ⁻¹' (f ⁻¹' U) = Pullback.proj₂ p f ⁻¹' (p ⁻¹' U) := by
  ext yx
  simp only [Set.mem_preimage, proj₁, proj₂]
  rw [yx.property]

/-- Given a homeomorphism h : ↑A ≃ₜ B and a continuous map g : Y → X with A ⊆ X,
    the restriction of g to g⁻¹'(A) composed with h gives a continuous map to B. -/
def Homeomorph.preimageMap {X Y B : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    [TopologicalSpace B] {A : Set X} (h : ↑A ≃ₜ B) (g : Y → X) :
    ↑(g ⁻¹' A) → B :=
  fun ⟨y, hy⟩ => h ⟨g y, hy⟩

theorem Homeomorph.preimageMap_continuous {X Y B : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    [TopologicalSpace B] {A : Set X} (h : ↑A ≃ₜ B) (g : Y → X) (hg : Continuous g) :
    Continuous (h.preimageMap g) := by
  apply Continuous.comp h.continuous
  exact Continuous.subtype_mk (hg.comp continuous_subtype_val) _

/-- Given a homeomorphism h : ↑A ≃ₜ B and a continuous map g : Y → X,
    the preimage g⁻¹'(A) is homeomorphic to the preimage under (h.preimageMap g) of B,
    which is the whole space. More usefully, for any S ⊆ B:
    (h.preimageMap g)⁻¹'(S) ≃ g⁻¹'(h.symm '' S ∩ A) in a natural way. -/
def Homeomorph.preimageMap_preimage {X Y B : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    [TopologicalSpace B] {A : Set X} (h : ↑A ≃ₜ B) (g : Y → X) :
    ↑(g ⁻¹' A) ≃ₜ ↑(g ⁻¹' (Subtype.val '' (h ⁻¹' (_root_.Set.univ : Set B)))) := by
  have : Subtype.val '' (h ⁻¹' (_root_.Set.univ : Set B)) = A := by
    simp only [Set.preimage_univ, Set.image_univ, Subtype.range_coe_subtype, Set.setOf_mem_eq]
  rw [this]
  exact Homeomorph.refl _

/-- Given a homeomorphism h : ↑A ≃ₜ B and g : Y → X (continuous), there is a homeomorphism
    between ↑(g⁻¹' A) and the pullback of h along (g restricted to g⁻¹' A).
    More precisely: ↑(g⁻¹' A) ≃ₜ ↑(g⁻¹' A) but the map to B factors through h. -/
def Homeomorph.pullbackPreimage {X Y B : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    [TopologicalSpace B] {A : Set X} (h : ↑A ≃ₜ B) (g : Y → X) (hg : Continuous g) :
    ↑(g ⁻¹' A) ≃ₜ ↑(g ⁻¹' A) := Homeomorph.refl _

/-- If p : X' → X is a covering map and f : Y → X is continuous,
then the projection from the pullback Y ×_X X' to Y is a covering map. -/
theorem IsCoveringMap.pullback {p : X' → X} {f : Y → X}
    (hp : IsCoveringMap p) (cont_f : Continuous f) :
    IsCoveringMap (Pullback.proj₁ p f) := by

  unfold IsCoveringMap
  intro y
  unfold IsCoveringMap at hp
  have hp := hp (f y)
  unfold IsEvenlyCovered
  unfold IsEvenlyCovered at hp
  constructor
  · -- Prove the fiber has discrete topology
    -- Direct homeomorphism: p⁻¹{f y} ≃ₜ Pullback.proj₁⁻¹{y}
    haveI : DiscreteTopology ↑(p ⁻¹' {f y}) := hp.1
    let fiberHomeo : ↑(p ⁻¹' {f y}) ≃ₜ ↑(Pullback.proj₁ p f ⁻¹' {y}) := {
      toFun := fun ⟨x', hx'⟩ => ⟨⟨⟨y, x'⟩, hx'.symm⟩, rfl⟩
      invFun := fun ⟨⟨⟨y', x'⟩, h⟩, hy'⟩ => ⟨x', by
        simp only [Set.mem_preimage, Set.mem_singleton_iff, Pullback.proj₁] at hy'
        simp only [Set.mem_preimage, Set.mem_singleton_iff]
        rw [← h, hy']⟩
      left_inv := fun _ => rfl
      right_inv := fun ⟨⟨⟨y', x'⟩, h⟩, hy'⟩ => by
        simp only [Set.mem_preimage, Set.mem_singleton_iff, Pullback.proj₁] at hy'
        simp only [Subtype.mk.injEq]
        subst hy'
        rfl
      continuous_toFun := by
        apply Continuous.subtype_mk
        apply Continuous.subtype_mk
        exact Continuous.prodMk continuous_const continuous_subtype_val
      continuous_invFun := by
        apply Continuous.subtype_mk
        exact (Pullback.continuous_proj₂ p f).comp continuous_subtype_val
    }
    exact fiberHomeo.discreteTopology
  · obtain ⟨U_fy, h_Ufy⟩ := hp.right
    obtain ⟨fy_Ufy, open_Ufy, open_pinv_Ufy, pinv_Ufy_inv⟩ := h_Ufy
    let W_y := f⁻¹' U_fy
    use  f⁻¹' U_fy
    refine And.intro ?ha ?hrest
    -- y in W_y
    · apply fy_Ufy
    refine And.intro ?hb ?hrestb
    -- Wy is open
    · apply cont_f.isOpen_preimage
      apply open_Ufy
    refine And.intro ?hc ?hrestc
    -- pullback of Wy is open
    · apply (Pullback.continuous_proj₁ _ _).isOpen_preimage
      apply cont_f.isOpen_preimage
      apply open_Ufy
    · -- Pullback of Wy isomorphic to Wy × fiber
      obtain ⟨pneg, hpneg⟩ := pinv_Ufy_inv
      -- Homeomorphism between fibers (use a fresh name to avoid conflicts)
      let pbFiberHomeo : ↑(p ⁻¹' {f y}) ≃ₜ ↑(Pullback.proj₁ p f ⁻¹' {y}) := {
        toFun := fun ⟨x', hx'⟩ => ⟨⟨⟨y, x'⟩, hx'.symm⟩, rfl⟩
        invFun := fun ⟨⟨⟨y', x'⟩, h⟩, hy'⟩ => ⟨x', by
          simp only [Set.mem_preimage, Set.mem_singleton_iff, Pullback.proj₁] at hy'
          simp only [Set.mem_preimage, Set.mem_singleton_iff]
          rw [← h, hy']⟩
        left_inv := fun _ => rfl
        right_inv := fun ⟨⟨⟨y', x'⟩, h⟩, hy'⟩ => by
          simp only [Set.mem_preimage, Set.mem_singleton_iff, Pullback.proj₁] at hy'
          simp only [Subtype.mk.injEq]
          subst hy'
          rfl
        continuous_toFun := by
          apply Continuous.subtype_mk
          apply Continuous.subtype_mk
          exact Continuous.prodMk continuous_const continuous_subtype_val
        continuous_invFun := by
          apply Continuous.subtype_mk
          exact (Pullback.continuous_proj₂ p f).comp continuous_subtype_val
      }
      -- Direct construction of the trivialization homeomorphism
      -- For now, use sorry to establish the structure
      refine ⟨?_, ?_⟩
      · -- Homeomorphism goal
        sorry
      · -- Projection property
        sorry









    --     refine And.intro ?ha ?hrest
    -- refine And.intro ?hb ?hrest_
