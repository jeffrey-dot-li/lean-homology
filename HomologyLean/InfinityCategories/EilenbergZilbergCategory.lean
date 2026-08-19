import Mathlib.CategoryTheory.MorphismProperty.Basic
import Mathlib.CategoryTheory.MorphismProperty.Factorization
import Mathlib.CategoryTheory.EpiMono
import Mathlib.AlgebraicTopology.SimplexCategory.Basic
import Mathlib.CategoryTheory.Comma.Presheaf.Basic

/-!
# Eilenberg–Zilber categories

This file introduces the data underlying an Eilenberg–Zilber category.

An Eilenberg–Zilber category consists of a category `A`, two wide subcategories
`A⁺` and `A⁻`, and a degree function from the objects of `A` to the natural
numbers. The defining axioms will be added alongside their formalization.

Wide subcategories are represented by morphism properties that contain every
identity morphism and are closed under composition.
-/

open CategoryTheory

universe v u

namespace HomologyLean.InfinityCategories

/--
A wide subcategory of `A`, represented by the morphisms that belong to it.

Because it is wide, it has every object of `A`; closure under identities and
composition is therefore enough to specify its category structure.
-/
structure WideSubcategory (A : Type u) [Category.{v} A] where
  /-- The morphisms belonging to the wide subcategory. -/
  hom : MorphismProperty A
  /-- Every identity morphism belongs to the wide subcategory. -/
  id_mem : ∀ X : A, hom (𝟙 X)
  /-- The composite of two morphisms in the wide subcategory also belongs to it. -/
  comp_mem :
    ∀ {X Y Z : A} {f : X ⟶ Y} {g : Y ⟶ Z},
      hom f → hom g → hom (f ≫ g)

/-- The inverse image of a wide subcategory under a functor. -/
def WideSubcategory.inverseImage {A : Type u} {B : Type*}
    [Category.{v} A] [Category B] (W : WideSubcategory A) (F : B ⥤ A) :
    WideSubcategory B where
  hom := W.hom.inverseImage F
  id_mem := fun X ↦ by
    simpa using W.id_mem (F.obj X)
  comp_mem := fun hf hg ↦ by
    simpa using W.comp_mem hf hg

abbrev splitEpimorphisms (A : Type u) [Category.{v} A] :
    MorphismProperty A :=
  fun _ _ f => IsSplitEpi f

/--
The initial data of an Eilenberg–Zilber category.

The fields `plus` and `minus` represent the wide subcategories `A⁺` and `A⁻`,
respectively. Further fields will express the degree, factorization, and
pushout axioms from the definition.
-/
class EilenbergZilberCategory (A : Type u) [Category.{v} A] where
  /-- The degree-raising wide subcategory `A⁺`. -/
  plus : WideSubcategory A
  /-- The degree-lowering wide subcategory `A⁻`. -/
  minus : WideSubcategory A
  /-- The degree of an object. -/
  degree : A → ℕ
  -- Any Isomorphism is in both A+ and A-
  isomorphisms_le_plus :
    MorphismProperty.isomorphisms A ≤ plus.hom
  isomorphisms_le_minus :
    MorphismProperty.isomorphisms A ≤ minus.hom
  -- Non isos change degree
  degree_lt_of_plus {X Y : A} (f : X ⟶ Y)
      (hf : plus.hom f) (hf_noniso : ¬ IsIso f) :
    degree X < degree Y
  degree_lt_of_minus {X Y : A} (f : X ⟶ Y)
      (hf : minus.hom f) (hf_noniso : ¬ IsIso f) :
    degree Y < degree X
  -- Factorization
  factorization :
    MorphismProperty.HasFactorization minus.hom plus.hom
  -- Factorization Unique
  factorization_unique {X Y : A} (f : X ⟶ Y)
      (F G : MorphismProperty.MapFactorizationData
        minus.hom plus.hom f) :
    ∃! e : F.Z ≅ G.Z,
      F.i ≫ e.hom = G.i ∧
        e.hom ≫ G.p = F.p
  -- Section
  section_of_minus :
    minus.hom ≤ splitEpimorphisms A
  -- Section Unique
  eq_of_sections_eq {X Y : A} (f g : X ⟶ Y)
      (hf : minus.hom f) (hg : minus.hom g)
      (hsections : ∀ s : Y ⟶ X,
        s ≫ f = 𝟙 Y ↔ s ≫ g = 𝟙 Y) :
    f = g



namespace EilenbergZilberCategory

variable {A : Type u} [Category.{v} A] [EilenbergZilberCategory A]

/-- A morphism belongs to the positive wide subcategory `A⁺`. -/
abbrev IsPlus {X Y : A} (f : X ⟶ Y) : Prop :=
  EilenbergZilberCategory.plus.hom f

/-- A morphism belongs to the negative wide subcategory `A⁻`. -/
abbrev IsMinus {X Y : A} (f : X ⟶ Y) : Prop :=
  EilenbergZilberCategory.minus.hom f

/--
Two epimorphisms in the simplex category with the same sections are equal.
-/
lemma SimplexCategory.eq_of_epi_of_sections_eq {X Y : SimplexCategory} (f g : X ⟶ Y)
    (hf : Epi f) (_hg : Epi g)
    (hsections : ∀ s : Y ⟶ X, s ≫ f = 𝟙 Y ↔ s ≫ g = 𝟙 Y) :
    f = g := by
  have hsurj : Function.Surjective f.toOrderHom :=
    (SimplexCategory.epi_iff_surjective (f := f)).mp hf
  apply SimplexCategory.Hom.ext
  apply OrderHom.ext
  funext x
  let φ : Fin (Y.len + 1) → Fin (X.len + 1) := fun y ↦
    if h : y = f.toOrderHom x then x else (hsurj y).choose
  have hφ : ∀ y, f.toOrderHom (φ y) = y := by
    intro y
    dsimp [φ]
    split_ifs with h
    · subst y
      rfl
    · exact (hsurj y).choose_spec
  have hφmono : Monotone φ := by
    intro a b
    contrapose
    intro h
    simp only [not_le] at h ⊢
    suffices b ≤ a by
      apply lt_of_le_of_ne this
      rintro rfl
      simp at h
    have H := f.toOrderHom.monotone (le_of_lt h)
    simpa only [hφ] using H
  let s : Y ⟶ X := SimplexCategory.Hom.mk ⟨φ, hφmono⟩
  have hsf : s ≫ f = 𝟙 Y := by
    apply SimplexCategory.Hom.ext
    apply OrderHom.ext
    funext y
    simpa [s] using hφ y
  have hsg := (hsections s).mp hsf
  have hx := SimplexCategory.congr_toOrderHom_apply hsg (f.toOrderHom x)
  simpa [s, φ] using hx.symm

/-- The simplex category `Δ` is an Eilenberg–Zilber category. -/
instance SimplexCategory.eilenbergZilberCategory :
    EilenbergZilberCategory SimplexCategory where
  plus := {
    hom := MorphismProperty.monomorphisms SimplexCategory
    id_mem := fun _ ↦ inferInstance
    comp_mem := fun hf hg ↦ mono_comp' hf hg
  }
  minus := {
    hom := MorphismProperty.epimorphisms SimplexCategory
    id_mem := fun _ ↦ inferInstance
    comp_mem := fun hf hg ↦ epi_comp' hf hg
  }
  degree := fun n ↦ n.len
  isomorphisms_le_minus := fun _ _ f hf ↦
    @IsIso.epi_of_iso _ _ _ _ f hf
  isomorphisms_le_plus := fun _ _ f hf ↦
    @IsIso.mono_of_iso _ _ _ _ f hf
  degree_lt_of_plus := fun {X Y} f hf hf' ↦
    @SimplexCategory.len_lt_of_mono X Y f hf fun h ↦
      hf' ((@SimplexCategory.isIso_iff_of_mono X Y f hf).2
        (congrArg SimplexCategory.len h.symm))

  degree_lt_of_minus := fun {X Y} f hf hf' ↦
    lt_of_le_of_ne
      (@SimplexCategory.len_le_of_epi X Y f hf)
      (fun h ↦ hf' ((@SimplexCategory.isIso_iff_of_epi X Y f hf).2 h.symm))
  factorization := {
    nonempty_mapFactorizationData := fun f ↦ ⟨{
      Z := Limits.image f
      i := Limits.factorThruImage f
      p := Limits.image.ι f
      fac := Limits.image.fac f
      hi := inferInstance
      hp := inferInstance
    }⟩
  }
  factorization_unique := by
    intro X Y f F G
    letI : Epi F.i := F.hi
    letI : Mono F.p := F.hp
    letI : Epi G.i := G.hi
    letI : Mono G.p := G.hp
    letI : StrongEpi F.i := strongEpi_of_epi F.i
    letI : StrongEpi G.i := strongEpi_of_epi G.i
    let eF := Limits.image.isoStrongEpiMono F.i F.p F.fac
    let eG := Limits.image.isoStrongEpiMono G.i G.p G.fac
    let e := eF ≪≫ eG.symm
    have he_right : e.hom ≫ G.p = F.p := by
      dsimp [e, eF, eG]
      simp
    have he_left : F.i ≫ e.hom = G.i := by
      apply (cancel_mono G.p).1
      simp only [Category.assoc, he_right, F.fac, G.fac]
    refine ⟨e, ⟨he_left, he_right⟩, ?_⟩
    intro e' he'
    apply Iso.ext
    apply (cancel_mono G.p).1
    exact he'.2.trans he_right.symm
  section_of_minus := by
    intro X Y f hf
    letI : Epi f := hf
    exact SplitEpiCategory.isSplitEpi_of_epi f
  eq_of_sections_eq := by
    intro X Y f g hf hg hsections
    exact SimplexCategory.eq_of_epi_of_sections_eq f g hf hg hsections

/--
A factorization of the underlying map of a morphism of costructured arrows
lifts to a factorization of that morphism.
-/
def MorphismProperty.MapFactorizationData.liftCostructuredArrow
    {C D : Type*} [Category C] [Category D] {S : C ⥤ D} {T : D}
    (W₁ W₂ : MorphismProperty C) {U V : CostructuredArrow S T} (f : U ⟶ V)
    (F : MorphismProperty.MapFactorizationData W₁ W₂ f.left) :
    MorphismProperty.MapFactorizationData
      (W₁.inverseImage (CostructuredArrow.proj S T))
      (W₂.inverseImage (CostructuredArrow.proj S T)) f where
  Z := CostructuredArrow.mk (S.map F.p ≫ V.hom)
  i := CostructuredArrow.homMk F.i (by
    change S.map F.i ≫ (S.map F.p ≫ V.hom) = U.hom
    rw [← Category.assoc, ← Functor.map_comp, F.fac]
    exact CostructuredArrow.w f)
  p := CostructuredArrow.homMk F.p
  fac := CostructuredArrow.hom_ext _ _ (by simp)
  hi := F.hi
  hp := F.hp

/-- Project a factorization of costructured arrows to the underlying category. -/
def MorphismProperty.MapFactorizationData.projectCostructuredArrow
    {C D : Type*} [Category C] [Category D] {S : C ⥤ D} {T : D}
    (W₁ W₂ : MorphismProperty C) {U V : CostructuredArrow S T} (f : U ⟶ V)
    (F : MorphismProperty.MapFactorizationData
      (W₁.inverseImage (CostructuredArrow.proj S T))
      (W₂.inverseImage (CostructuredArrow.proj S T)) f) :
    MorphismProperty.MapFactorizationData W₁ W₂ f.left where
  Z := F.Z.left
  i := F.i.left
  p := F.p.left
  fac := congrArg CostructuredArrow.Hom.left F.fac
  hi := F.hi
  hp := F.hp

/-- Lift a section of an underlying map to a morphism of costructured arrows. -/
def CostructuredArrow.sectionMk
    {C D : Type*} [Category C] [Category D] {S : C ⥤ D} {T : D}
    {U V : CostructuredArrow S T} (f : U ⟶ V) (s : V.left ⟶ U.left)
    (hs : s ≫ f.left = 𝟙 V.left) : V ⟶ U :=
  CostructuredArrow.homMk s (by
    rw [← CostructuredArrow.w f, ← Category.assoc, ← Functor.map_comp, hs]
    simp only [S.map_id, Category.id_comp])

/-- The lifted underlying section is a section in the costructured-arrow category. -/
@[simp]
lemma CostructuredArrow.sectionMk_comp
    {C D : Type*} [Category C] [Category D] {S : C ⥤ D} {T : D}
    {U V : CostructuredArrow S T} (f : U ⟶ V) (s : V.left ⟶ U.left)
    (hs : s ≫ f.left = 𝟙 V.left) :
    CostructuredArrow.sectionMk f s hs ≫ f = 𝟙 V :=
  CostructuredArrow.hom_ext _ _ hs

/-- A costructured-arrow morphism is split epi when its underlying morphism is. -/
lemma CostructuredArrow.isSplitEpi_of_left
    {C D : Type*} [Category C] [Category D] {S : C ⥤ D} {T : D}
    {U V : CostructuredArrow S T} (f : U ⟶ V) (hf : IsSplitEpi f.left) :
    IsSplitEpi f := by
  obtain ⟨sf⟩ := hf.exists_splitEpi
  apply IsSplitEpi.mk'
  refine {
    section_ := CostructuredArrow.homMk sf.section_ ?_
    id := CostructuredArrow.hom_ext _ _ sf.id
  }
  change S.map sf.section_ ≫ U.hom = V.hom
  rw [← CostructuredArrow.w f, ← Category.assoc, ← Functor.map_comp, sf.id]
  simp only [S.map_id, Category.id_comp]

/--
The category of elements `A/X` of a presheaf `X` on an Eilenberg–Zilber
category `A` is an Eilenberg–Zilber category.
-/
noncomputable instance costructuredArrowEilenbergZilberCategory
    {A : Type u} [Category.{v} A] [EilenbergZilberCategory A]
    (X : Aᵒᵖ ⥤ Type v) :
    EilenbergZilberCategory (CostructuredArrow yoneda X) := by
  let π : CostructuredArrow yoneda X ⥤ A := CostructuredArrow.proj yoneda X
  refine {
    plus := EilenbergZilberCategory.plus.inverseImage π
    minus := EilenbergZilberCategory.minus.inverseImage π
    degree := fun Y ↦ EilenbergZilberCategory.degree (π.obj Y)
    isomorphisms_le_plus := by
      intro Y Z f hf
      letI : IsIso f := hf
      exact EilenbergZilberCategory.isomorphisms_le_plus (π.map f) inferInstance
    isomorphisms_le_minus := by
      intro Y Z f hf
      letI : IsIso f := hf
      exact EilenbergZilberCategory.isomorphisms_le_minus (π.map f) inferInstance
    degree_lt_of_plus := by
      intro Y Z f hf hf_noniso
      apply EilenbergZilberCategory.degree_lt_of_plus (π.map f) hf
      intro hπ
      letI : IsIso (π.map f) := hπ
      exact hf_noniso (isIso_of_reflects_iso f π)
    degree_lt_of_minus := by
      intro Y Z f hf hf_noniso
      apply EilenbergZilberCategory.degree_lt_of_minus (π.map f) hf
      intro hπ
      letI : IsIso (π.map f) := hπ
      exact hf_noniso (isIso_of_reflects_iso f π)
    factorization := {
      nonempty_mapFactorizationData := fun f ↦ by
        obtain ⟨F⟩ :=
          EilenbergZilberCategory.factorization.nonempty_mapFactorizationData (π.map f)
        exact ⟨MorphismProperty.MapFactorizationData.liftCostructuredArrow
          EilenbergZilberCategory.minus.hom EilenbergZilberCategory.plus.hom f F⟩
    }
    factorization_unique := by
      intro U V f F G
      let F₀ := MorphismProperty.MapFactorizationData.projectCostructuredArrow
        EilenbergZilberCategory.minus.hom EilenbergZilberCategory.plus.hom f F
      let G₀ := MorphismProperty.MapFactorizationData.projectCostructuredArrow
        EilenbergZilberCategory.minus.hom EilenbergZilberCategory.plus.hom f G
      obtain ⟨e₀, he₀, he₀_unique⟩ :=
        EilenbergZilberCategory.factorization_unique f.left F₀ G₀
      change F.Z.left ≅ G.Z.left at e₀
      change F.i.left ≫ e₀.hom = G.i.left ∧ e₀.hom ≫ G.p.left = F.p.left at he₀
      change ∀ y : F.Z.left ≅ G.Z.left,
        F.i.left ≫ y.hom = G.i.left ∧ y.hom ≫ G.p.left = F.p.left → y = e₀ at he₀_unique
      let e : F.Z ≅ G.Z := CostructuredArrow.isoMk e₀ (by
        change yoneda.map e₀.hom ≫ G.Z.hom = F.Z.hom
        rw [← CostructuredArrow.w G.p, ← Category.assoc,
          ← Functor.map_comp, he₀.2]
        exact CostructuredArrow.w F.p)
      have he_left : F.i ≫ e.hom = G.i :=
        CostructuredArrow.hom_ext _ _ he₀.1
      have he_right : e.hom ≫ G.p = F.p :=
        CostructuredArrow.hom_ext _ _ he₀.2
      refine ⟨e, ⟨he_left, he_right⟩, ?_⟩
      intro e' he'
      let e'₀ : F.Z.left ≅ G.Z.left := {
        hom := e'.hom.left
        inv := e'.inv.left
        hom_inv_id := congrArg CostructuredArrow.Hom.left e'.hom_inv_id
        inv_hom_id := congrArg CostructuredArrow.Hom.left e'.inv_hom_id
      }
      have hbase : e'₀ = e₀ := he₀_unique e'₀ ⟨
        congrArg CostructuredArrow.Hom.left he'.1,
        congrArg CostructuredArrow.Hom.left he'.2⟩
      apply Iso.ext
      apply CostructuredArrow.hom_ext
      simpa [e, e'₀] using congrArg Iso.hom hbase
    section_of_minus := by
      intro U V f hf
      apply CostructuredArrow.isSplitEpi_of_left f
      exact EilenbergZilberCategory.section_of_minus f.left hf
    eq_of_sections_eq := by
      intro U V f g hf hg hsections
      apply CostructuredArrow.hom_ext
      apply EilenbergZilberCategory.eq_of_sections_eq f.left g.left hf hg
      intro s
      constructor
      · intro hs
        let s' := CostructuredArrow.sectionMk f s hs
        have hs'g := (hsections s').mp (CostructuredArrow.sectionMk_comp f s hs)
        exact congrArg CostructuredArrow.Hom.left hs'g
      · intro hs
        let s' := CostructuredArrow.sectionMk g s hs
        have hs'f := (hsections s').mpr (CostructuredArrow.sectionMk_comp g s hs)
        exact congrArg CostructuredArrow.Hom.left hs'f
  }

end EilenbergZilberCategory

end HomologyLean.InfinityCategories
