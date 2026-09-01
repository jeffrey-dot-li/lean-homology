import Mathlib.CategoryTheory.MorphismProperty.Basic
import Mathlib.CategoryTheory.MorphismProperty.Factorization
import Mathlib.CategoryTheory.EpiMono
import Mathlib.AlgebraicTopology.SimplexCategory.Basic
import Mathlib.CategoryTheory.Comma.Presheaf.Basic
import Mathlib.AlgebraicTopology.SimplicialSet.Degenerate

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

universe w v u

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
  /--
  Every isomorphism is induced by an equality of objects; in particular,
  there are no nontrivial automorphisms.
  -/
  isIso_eqToHom {X Y : A} (f : X ⟶ Y) (hf : IsIso f) :
    ∃ h : X = Y, f = eqToHom h
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

namespace Presheaf

/--
A decomposition of a section `x` of a presheaf consists of a section over an
object of strictly smaller degree whose restriction is `x`.
-/
structure Decomposition (X : Aᵒᵖ ⥤ Type w) {a : A}
    (x : X.obj (Opposite.op a)) where
  /-- The object over which the decomposing section is defined. -/
  b : A
  /-- The map along which the decomposing section restricts to `x`. -/
  σ : a ⟶ b
  /-- The decomposing section lies over an object of strictly smaller degree. -/
  degree_lt : EilenbergZilberCategory.degree b < EilenbergZilberCategory.degree a
  /-- The section over `b` that restricts to `x`. -/
  y : X.obj (Opposite.op b)
  /-- Restricting `y` along `σ` gives `x`. -/
  map_y : X.map σ.op y = x

/-- A section of a presheaf is degenerate when it admits a decomposition. -/
def IsDegenerate (X : Aᵒᵖ ⥤ Type w) {a : A}
    (x : X.obj (Opposite.op a)) : Prop :=
  Nonempty (Decomposition X x)

/-- A section of a presheaf is nondegenerate when it is not degenerate. -/
def IsNondegenerate (X : Aᵒᵖ ⥤ Type w) {a : A}
    (x : X.obj (Opposite.op a)) : Prop :=
  ¬IsDegenerate X x

/--
An inverse decomposition of a section `x` consists of an `A⁻`-morphism
`σ : a ⟶ b` and a section over `b` whose restriction along `σ` is `x`.

Unlike `Decomposition`, this permits `σ` to be an identity.
-/
structure MinusDecomposition (X : Aᵒᵖ ⥤ Type w) {a : A}
    (x : X.obj (Opposite.op a)) where
  /-- The object over which the decomposing section is defined. -/
  b : A
  /-- The inverse morphism along which the section restricts to `x`. -/
  σ : a ⟶ b
  /-- The decomposing morphism belongs to `A⁻`. -/
  σ_mem : IsMinus σ
  /-- The section over `b`. -/
  y : X.obj (Opposite.op b)
  /-- Restricting `y` along `σ` gives `x`. -/
  map_y : X.map σ.op y = x

/-- Compose two inverse decompositions. -/
def MinusDecomposition.comp {X : Aᵒᵖ ⥤ Type w} {a : A}
    {x : X.obj (Opposite.op a)} (d : MinusDecomposition X x)
    (e : MinusDecomposition X d.y) :
    MinusDecomposition X x where
  b := e.b
  σ := d.σ ≫ e.σ
  σ_mem := EilenbergZilberCategory.minus.comp_mem d.σ_mem e.σ_mem
  y := e.y
  map_y := by
    calc
      X.map (d.σ ≫ e.σ).op e.y =
          X.map d.σ.op (X.map e.σ.op e.y) :=
        ConcreteCategory.congr_hom (X.map_comp e.σ.op d.σ.op) e.y
      _ = X.map d.σ.op d.y := by rw [e.map_y]
      _ = x := d.map_y

/--
A section is degenerate exactly when it admits an inverse decomposition whose
target object has strictly smaller degree.
-/
lemma isDegenerate_iff_exists_minusDecomposition_degree_lt
    (X : Aᵒᵖ ⥤ Type w) {a : A} (x : X.obj (Opposite.op a)) :
    IsDegenerate X x ↔
      ∃ d : MinusDecomposition X x,
        EilenbergZilberCategory.degree d.b < EilenbergZilberCategory.degree a := by
  constructor
  · rintro ⟨d⟩
    obtain ⟨F⟩ :=
      EilenbergZilberCategory.factorization.nonempty_mapFactorizationData d.σ
    let y' := X.map F.p.op d.y
    have hmap : X.map F.i.op y' = x := by
      calc
        X.map F.i.op (X.map F.p.op d.y) =
            X.map (F.p.op ≫ F.i.op) d.y :=
          (ConcreteCategory.congr_hom (X.map_comp F.p.op F.i.op) d.y).symm
        _ = X.map (F.i ≫ F.p).op d.y := rfl
        _ = X.map d.σ.op d.y := by rw [F.fac]
        _ = x := d.map_y
    refine ⟨{
      b := F.Z
      σ := F.i
      σ_mem := F.hi
      y := y'
      map_y := hmap
    }, ?_⟩
    have hle : EilenbergZilberCategory.degree F.Z ≤
        EilenbergZilberCategory.degree d.b := by
      by_cases hp : IsIso F.p
      · obtain ⟨h, _⟩ := EilenbergZilberCategory.isIso_eqToHom F.p hp
        exact (congrArg EilenbergZilberCategory.degree h).le
      · exact (EilenbergZilberCategory.degree_lt_of_plus F.p F.hp hp).le
    exact hle.trans_lt d.degree_lt
  · rintro ⟨d, hd⟩
    exact ⟨{
      b := d.b
      σ := d.σ
      degree_lt := hd
      y := d.y
      map_y := d.map_y
    }⟩

/--
If a section over `c` restricts to a nondegenerate section over `b`, then the
degree of `b` is at most that of `c`.
-/
lemma degree_le_of_map_eq_nondegenerate
    (X : Aᵒᵖ ⥤ Type w) {b c : A}
    (u : b ⟶ c) (y : X.obj (Opposite.op b)) (z : X.obj (Opposite.op c))
    (hu : X.map u.op z = y) (hy : IsNondegenerate X y) :
    EilenbergZilberCategory.degree b ≤ EilenbergZilberCategory.degree c := by
  obtain ⟨F⟩ :=
    EilenbergZilberCategory.factorization.nonempty_mapFactorizationData u
  let y' := X.map F.p.op z
  have hmap : X.map F.i.op y' = y := by
    calc
      X.map F.i.op (X.map F.p.op z) =
          X.map (F.p.op ≫ F.i.op) z :=
        (ConcreteCategory.congr_hom (X.map_comp F.p.op F.i.op) z).symm
      _ = X.map (F.i ≫ F.p).op z := rfl
      _ = X.map u.op z := by rw [F.fac]
      _ = y := hu
  have hFi : IsIso F.i := by
    by_contra h
    apply hy
    rw [isDegenerate_iff_exists_minusDecomposition_degree_lt]
    exact ⟨{
      b := F.Z
      σ := F.i
      σ_mem := F.hi
      y := y'
      map_y := hmap
    }, EilenbergZilberCategory.degree_lt_of_minus F.i F.hi h⟩
  obtain ⟨hbZ, _⟩ := EilenbergZilberCategory.isIso_eqToHom F.i hFi
  have hZc : EilenbergZilberCategory.degree F.Z ≤
      EilenbergZilberCategory.degree c := by
    by_cases hFp : IsIso F.p
    · obtain ⟨hZc, _⟩ := EilenbergZilberCategory.isIso_eqToHom F.p hFp
      exact (congrArg EilenbergZilberCategory.degree hZc).le
    · exact (EilenbergZilberCategory.degree_lt_of_plus F.p F.hp hFp).le
  simpa only [hbZ] using hZc

/--
A map between equal-degree objects that carries a section to a nondegenerate
section is an isomorphism.
-/
lemma isIso_of_map_eq_nondegenerate_of_degree_eq
    (X : Aᵒᵖ ⥤ Type w) {b c : A}
    (u : b ⟶ c) (y : X.obj (Opposite.op b)) (z : X.obj (Opposite.op c))
    (hu : X.map u.op z = y) (hy : IsNondegenerate X y)
    (hdeg : EilenbergZilberCategory.degree b = EilenbergZilberCategory.degree c) :
    IsIso u := by
  obtain ⟨F⟩ :=
    EilenbergZilberCategory.factorization.nonempty_mapFactorizationData u
  let y' := X.map F.p.op z
  have hmap : X.map F.i.op y' = y := by
    calc
      X.map F.i.op (X.map F.p.op z) =
          X.map (F.p.op ≫ F.i.op) z :=
        (ConcreteCategory.congr_hom (X.map_comp F.p.op F.i.op) z).symm
      _ = X.map (F.i ≫ F.p).op z := rfl
      _ = X.map u.op z := by rw [F.fac]
      _ = y := hu
  have hFi : IsIso F.i := by
    by_contra h
    apply hy
    rw [isDegenerate_iff_exists_minusDecomposition_degree_lt]
    exact ⟨{
      b := F.Z
      σ := F.i
      σ_mem := F.hi
      y := y'
      map_y := hmap
    }, EilenbergZilberCategory.degree_lt_of_minus F.i F.hi h⟩
  obtain ⟨hbZ, _⟩ := EilenbergZilberCategory.isIso_eqToHom F.i hFi
  have hFp : IsIso F.p := by
    by_contra h
    have hp := EilenbergZilberCategory.degree_lt_of_plus F.p F.hp h
    have hdegZ : EilenbergZilberCategory.degree F.Z =
        EilenbergZilberCategory.degree b :=
      congrArg EilenbergZilberCategory.degree hbZ.symm
    rw [hdegZ, hdeg] at hp
    exact (lt_irrefl _ hp)
  rw [← F.fac]
  letI : IsIso F.i := hFi
  letI : IsIso F.p := hFp
  infer_instance

/--
Two `A⁻`-morphisms inducing the same section from the same nondegenerate
section are equal.
-/
lemma eq_of_minus_maps_eq_nondegenerate
    (X : Aᵒᵖ ⥤ Type w) {a b : A}
    (x : X.obj (Opposite.op a)) (y : X.obj (Opposite.op b))
    (σ τ : a ⟶ b) (hσ : IsMinus σ) (hτ : IsMinus τ)
    (hσy : X.map σ.op y = x) (hτy : X.map τ.op y = x)
    (hy : IsNondegenerate X y) :
    σ = τ := by
  have section_imp (f g : a ⟶ b)
      (hf : X.map f.op y = x) (hg : X.map g.op y = x) :
      ∀ s : b ⟶ a, s ≫ f = 𝟙 b → s ≫ g = 𝟙 b := by
    intro s hs
    have hmap : X.map (s ≫ g).op y = y := by
      calc
        X.map (s ≫ g).op y = X.map s.op (X.map g.op y) :=
          ConcreteCategory.congr_hom (X.map_comp g.op s.op) y
        _ = X.map s.op x := by rw [hg]
        _ = X.map s.op (X.map f.op y) := by rw [hf]
        _ = X.map (f.op ≫ s.op) y :=
          (ConcreteCategory.congr_hom (X.map_comp f.op s.op) y).symm
        _ = X.map (s ≫ f).op y := rfl
        _ = X.map (𝟙 b).op y := by rw [hs]
        _ = y := by simp
    have hiso : IsIso (s ≫ g) :=
      isIso_of_map_eq_nondegenerate_of_degree_eq
        X (s ≫ g) y y hmap hy rfl
    obtain ⟨h, heq⟩ :=
      EilenbergZilberCategory.isIso_eqToHom (s ≫ g) hiso
    simpa using heq
  apply EilenbergZilberCategory.eq_of_sections_eq σ τ hσ hτ
  intro s
  exact ⟨section_imp σ τ hσy hτy s, section_imp τ σ hτy hσy s⟩

/-- Extensionality for inverse decompositions, including dependent transport. -/
lemma MinusDecomposition.ext {X : Aᵒᵖ ⥤ Type w} {a : A}
    {x : X.obj (Opposite.op a)} {d e : MinusDecomposition X x}
    (h : d.b = e.b)
    (hy : X.map (eqToHom h).op e.y = d.y)
    (hσ : d.σ ≫ eqToHom h = e.σ) :
    d = e := by
  cases d with
  | mk db dσ dσ_mem dy dmap =>
    cases e with
    | mk eb eσ eσ_mem ey emap =>
      change db = eb at h
      change X.map (eqToHom h).op ey = dy at hy
      change dσ ≫ eqToHom h = eσ at hσ
      subst eb
      simp at hy hσ
      subst ey
      subst eσ
      rfl

/--
Every section admits a unique inverse decomposition whose target section is
nondegenerate.
-/
theorem existsUnique_minusDecomposition (X : Aᵒᵖ ⥤ Type w) {a : A}
    (x : X.obj (Opposite.op a)) :
    ∃! d : MinusDecomposition X x, IsNondegenerate X d.y := by
  classical
  let d₀ : MinusDecomposition X x := {
    b := a
    σ := 𝟙 a
    σ_mem := EilenbergZilberCategory.minus.id_mem a
    y := x
    map_y := by simp
  }
  let P : ℕ → Prop := fun m ↦
    ∃ d : MinusDecomposition X x, EilenbergZilberCategory.degree d.b = m
  have hP : ∃ m, P m :=
    ⟨EilenbergZilberCategory.degree a, d₀, rfl⟩
  obtain ⟨d, hd⟩ := Nat.find_spec hP
  have hd_nondegenerate : IsNondegenerate X d.y := by
    intro hdeg
    obtain ⟨e, he⟩ :=
      (isDegenerate_iff_exists_minusDecomposition_degree_lt X d.y).mp hdeg
    have hmin : Nat.find hP ≤ EilenbergZilberCategory.degree e.b :=
      Nat.find_min' hP ⟨d.comp e, rfl⟩
    apply (not_lt_of_ge hmin)
    simpa only [hd] using he
  refine ⟨d, hd_nondegenerate, ?_⟩
  intro e he_nondegenerate
  have comparison_map (p q : MinusDecomposition X x)
      (s : p.b ⟶ a) (hs : s ≫ p.σ = 𝟙 p.b) :
      X.map (s ≫ q.σ).op q.y = p.y := by
    calc
      X.map (s ≫ q.σ).op q.y =
          X.map s.op (X.map q.σ.op q.y) :=
        ConcreteCategory.congr_hom (X.map_comp q.σ.op s.op) q.y
      _ = X.map s.op x := by rw [q.map_y]
      _ = X.map s.op (X.map p.σ.op p.y) := by rw [p.map_y]
      _ = X.map (p.σ.op ≫ s.op) p.y :=
        (ConcreteCategory.congr_hom (X.map_comp p.σ.op s.op) p.y).symm
      _ = X.map (s ≫ p.σ).op p.y := rfl
      _ = X.map (𝟙 p.b).op p.y := by rw [hs]
      _ = p.y := by simp
  obtain ⟨sd⟩ :=
    (EilenbergZilberCategory.section_of_minus d.σ d.σ_mem).exists_splitEpi
  obtain ⟨se⟩ :=
    (EilenbergZilberCategory.section_of_minus e.σ e.σ_mem).exists_splitEpi
  let u : d.b ⟶ e.b := sd.section_ ≫ e.σ
  let v : e.b ⟶ d.b := se.section_ ≫ d.σ
  have hu : X.map u.op e.y = d.y :=
    comparison_map d e sd.section_ sd.id
  have hv : X.map v.op d.y = e.y :=
    comparison_map e d se.section_ se.id
  have hde : EilenbergZilberCategory.degree d.b ≤
      EilenbergZilberCategory.degree e.b :=
    degree_le_of_map_eq_nondegenerate X u d.y e.y hu hd_nondegenerate
  have hed : EilenbergZilberCategory.degree e.b ≤
      EilenbergZilberCategory.degree d.b :=
    degree_le_of_map_eq_nondegenerate X v e.y d.y hv he_nondegenerate
  have hdegree : EilenbergZilberCategory.degree d.b =
      EilenbergZilberCategory.degree e.b :=
    le_antisymm hde hed
  have hu_iso : IsIso u :=
    isIso_of_map_eq_nondegenerate_of_degree_eq
      X u d.y e.y hu hd_nondegenerate hdegree
  obtain ⟨h, hu_eq⟩ :=
    EilenbergZilberCategory.isIso_eqToHom u hu_iso
  have hy : X.map (eqToHom h).op e.y = d.y := by
    rw [← hu_eq]
    exact hu
  have hdσ_mem : IsMinus (d.σ ≫ eqToHom h) :=
    EilenbergZilberCategory.minus.comp_mem d.σ_mem
      (EilenbergZilberCategory.isomorphisms_le_minus
        (eqToHom h) (by infer_instance))
  have hdσ_map : X.map (d.σ ≫ eqToHom h).op e.y = x := by
    calc
      X.map (d.σ ≫ eqToHom h).op e.y =
          X.map d.σ.op (X.map (eqToHom h).op e.y) :=
        ConcreteCategory.congr_hom
          (X.map_comp (eqToHom h).op d.σ.op) e.y
      _ = X.map d.σ.op d.y := by rw [hy]
      _ = x := d.map_y
  have hσ : d.σ ≫ eqToHom h = e.σ :=
    eq_of_minus_maps_eq_nondegenerate X x e.y
      (d.σ ≫ eqToHom h) e.σ hdσ_mem e.σ_mem
      hdσ_map e.map_y he_nondegenerate
  exact (MinusDecomposition.ext h hy hσ).symm

/-- Any two inverse decompositions with nondegenerate target sections are equal. -/
lemma MinusDecomposition.eq_of_nondegenerate
    (X : Aᵒᵖ ⥤ Type w) {a : A} {x : X.obj (Opposite.op a)}
    (d e : MinusDecomposition X x)
    (hd : IsNondegenerate X d.y) (he : IsNondegenerate X e.y) :
    d = e := by
  obtain ⟨z, hz, hunique⟩ := existsUnique_minusDecomposition X x
  exact (hunique d hd).trans (hunique e he).symm

/--
A section belongs to the `n`-skeleton when it is induced from a section over
an object of degree at most `n`.
-/
def IsInSkeleton (n : ℕ) (X : Aᵒᵖ ⥤ Type w) {a : A}
    (x : X.obj (Opposite.op a)) : Prop :=
  ∃ (b : A) (_ : EilenbergZilberCategory.degree b ≤ n)
    (σ : a ⟶ b) (y : X.obj (Opposite.op b)), X.map σ.op y = x

/-- The `n`-skeleton of a presheaf. -/
def skeleton (n : ℕ) (X : Aᵒᵖ ⥤ Type w) : Aᵒᵖ ⥤ Type w where
  obj a := {x : X.obj a // IsInSkeleton n X (a := a.unop) x}
  map f := ↾fun x ↦ ⟨X.map f x.1, by
    rcases x.2 with ⟨b, hb, σ, y, hy⟩
    refine ⟨b, hb, f.unop ≫ σ, y, ?_⟩
    change X.map (σ.op ≫ f) y = X.map f x.1
    rw [X.map_comp]
    change X.map f (X.map σ.op y) = X.map f x.1
    rw [hy]⟩
  map_id := by
    intro a
    ext x
    simp
  map_comp := by
    intro a b c f g
    ext x
    simp

/-- The canonical inclusion of the `n`-skeleton into the original presheaf. -/
def skeletonι (n : ℕ) (X : Aᵒᵖ ⥤ Type w) : skeleton n X ⟶ X where
  app _ := ↾fun x ↦ x.1
  naturality := by
    intro a b f
    ext x
    rfl

/-- A morphism of presheaves restricts to a morphism of their `n`-skeleta. -/
def skeletonMap (n : ℕ) {X Y : Aᵒᵖ ⥤ Type w} (f : X ⟶ Y) :
    skeleton n X ⟶ skeleton n Y where
  app a := ↾fun x ↦ ⟨f.app a x.1, by
    rcases x.2 with ⟨b, hb, σ, y, hy⟩
    refine ⟨b, hb, σ, f.app (Opposite.op b) y, ?_⟩
    rw [← hy]
    exact (ConcreteCategory.congr_hom (f.naturality σ.op) y).symm⟩
  naturality := by
    intro a b g
    ext x
    apply Subtype.ext
    change f.app b (X.map g x.1) = Y.map g (f.app a x.1)
    exact ConcreteCategory.congr_hom (f.naturality g) x.1

/-- Taking the `n`-skeleton is functorial in the presheaf. -/
def skeletonFunctor (n : ℕ) :
    (Aᵒᵖ ⥤ Type w) ⥤ Aᵒᵖ ⥤ Type w where
  obj X := skeleton n X
  map f := skeletonMap n f
  map_id := by
    intro X
    ext a x
    apply Subtype.ext
    rfl
  map_comp := by
    intro X Y Z f g
    ext a x
    apply Subtype.ext
    rfl

/-- Every section over an object of degree at most `n` belongs to the `n`-skeleton. -/
lemma isInSkeleton_of_degree_le (n : ℕ) (X : Aᵒᵖ ⥤ Type w) {a : A}
    (ha : EilenbergZilberCategory.degree a ≤ n) (x : X.obj (Opposite.op a)) :
    IsInSkeleton n X x := by
  refine ⟨a, ha, 𝟙 a, x, ?_⟩
  simp

/--
Above degree `n`, every section in the `n`-skeleton is degenerate in the
original presheaf.
-/
lemma isDegenerate_of_isInSkeleton (n : ℕ) (X : Aᵒᵖ ⥤ Type w) {a : A}
    (ha : n < EilenbergZilberCategory.degree a) (x : X.obj (Opposite.op a))
    (hx : IsInSkeleton n X x) :
    IsDegenerate X x := by
  rcases hx with ⟨b, hb, σ, y, hy⟩
  exact ⟨{
    b := b
    σ := σ
    degree_lt := hb.trans_lt ha
    y := y
    map_y := hy
  }⟩

/-- The square expressing naturality of the skeleton inclusion commutes. -/
@[reassoc]
lemma skeletonMap_comp_ι (n : ℕ) {X Y : Aᵒᵖ ⥤ Type w} (f : X ⟶ Y) :
    skeletonMap n f ≫ skeletonι n Y = skeletonι n X ≫ f := by
  ext a x
  rfl

/--
`skeletonMap n f` is the unique morphism between skeleta compatible with `f`
and the canonical inclusions.
-/
lemma skeletonMap_unique (n : ℕ) {X Y : Aᵒᵖ ⥤ Type w} (f : X ⟶ Y)
    (g : skeleton n X ⟶ skeleton n Y)
    (hg : g ≫ skeletonι n Y = skeletonι n X ≫ f) :
    g = skeletonMap n f := by
  ext a x
  apply Subtype.ext
  have h := congrArg (fun k ↦ k.app a) hg
  simpa [skeletonι, skeletonMap] using ConcreteCategory.congr_hom h x

end Presheaf

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
  isIso_eqToHom := by
    intro X Y f hf
    letI : IsIso f := hf
    have hXY : X = Y := SimplexCategory.ext (SimplexCategory.len_eq_of_isIso f)
    subst Y
    exact ⟨rfl, SimplexCategory.eq_id_of_isIso f⟩
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

/-! ## Recovering Mathlib's simplicial-set decomposition theorems

This section specializes the general Eilenberg–Zilber decomposition theorem to
`SimplexCategory`. After identifying the general degeneracy predicates with
Mathlib's predicates, it restates and reproves Mathlib's decomposition theorems
as corollaries of the general result.
-/

namespace SimplexCategoryCorollaries

open Opposite Simplicial

section MathlibRestatements

variable {X : SSet.{w}} {n : ℕ}

/--
For simplicial sets, the general Eilenberg–Zilber notion of degeneracy agrees
with Mathlib's existing predicate.
-/
lemma isDegenerate_iff_mem_degenerate (x : X _⦋n⦌) :
    Presheaf.IsDegenerate X x ↔ x ∈ X.degenerate n := by
  constructor
  · rintro ⟨⟨b, σ, hb, y, hy⟩⟩
    induction b using SimplexCategory.rec with
    | _ m =>
      exact ⟨m, hb, σ, y, hy⟩
  · rintro ⟨m, hm, f, y, hy⟩
    exact ⟨{
      b := ⦋m⦌
      σ := f
      degree_lt := hm
      y := y
      map_y := hy
    }⟩

/--
For simplicial sets, the general Eilenberg–Zilber notion of nondegeneracy
agrees with Mathlib's existing predicate.
-/
lemma isNondegenerate_iff_mem_nonDegenerate (x : X _⦋n⦌) :
    Presheaf.IsNondegenerate X x ↔ x ∈ X.nonDegenerate n := by
  simp only [Presheaf.IsNondegenerate,
    SSet.mem_nonDegenerate_iff_notMem_degenerate,
    isDegenerate_iff_mem_degenerate]

/--
Restatement of Mathlib's `SSet.exists_nonDegenerate`, deduced from the general
Eilenberg–Zilber decomposition theorem.
-/
lemma exists_nonDegenerate_of_eilenbergZilber (x : X _⦋n⦌) :
    ∃ (m : ℕ) (f : ⦋n⦌ ⟶ ⦋m⦌) (_ : Epi f)
      (y : X.nonDegenerate m), x = X.map f.op y := by
  obtain ⟨d, hd, _⟩ := Presheaf.existsUnique_minusDecomposition X x
  rcases d with ⟨b, f, hf, y, hy⟩
  induction b using SimplexCategory.rec with
  | _ m =>
    exact ⟨m, f, hf, ⟨y, (isNondegenerate_iff_mem_nonDegenerate y).mp hd⟩, hy.symm⟩

/--
Restatement of Mathlib's `SSet.unique_nonDegenerate_dim`, deduced from the
general Eilenberg–Zilber uniqueness theorem.
-/
lemma unique_nonDegenerate_dim_of_eilenbergZilber (x : X _⦋n⦌) {m₁ m₂ : ℕ}
    (f₁ : ⦋n⦌ ⟶ ⦋m₁⦌) [Epi f₁]
    (y₁ : X.nonDegenerate m₁) (hy₁ : x = X.map f₁.op y₁)
    (f₂ : ⦋n⦌ ⟶ ⦋m₂⦌) [Epi f₂]
    (y₂ : X.nonDegenerate m₂) (hy₂ : x = X.map f₂.op y₂) :
    m₁ = m₂ := by
  let d₁ : Presheaf.MinusDecomposition X x := {
    b := ⦋m₁⦌
    σ := f₁
    σ_mem := (inferInstance : Epi f₁)
    y := y₁
    map_y := hy₁.symm
  }
  let d₂ : Presheaf.MinusDecomposition X x := {
    b := ⦋m₂⦌
    σ := f₂
    σ_mem := (inferInstance : Epi f₂)
    y := y₂
    map_y := hy₂.symm
  }
  have hd₁ : Presheaf.IsNondegenerate X d₁.y := by
    change Presheaf.IsNondegenerate X (y₁ : X _⦋m₁⦌)
    exact (isNondegenerate_iff_mem_nonDegenerate
      (X := X) (n := m₁) y₁.1).mpr y₁.2
  have hd₂ : Presheaf.IsNondegenerate X d₂.y := by
    change Presheaf.IsNondegenerate X (y₂ : X _⦋m₂⦌)
    exact (isNondegenerate_iff_mem_nonDegenerate
      (X := X) (n := m₂) y₂.1).mpr y₂.2
  have hd : d₁ = d₂ :=
    Presheaf.MinusDecomposition.eq_of_nondegenerate X d₁ d₂
      hd₁ hd₂
  simpa [d₁, d₂] using congrArg
    (fun d : Presheaf.MinusDecomposition X x ↦ d.b.len) hd

/--
If one equal-dimensional nondegenerate decomposition is along an epimorphism,
then the map in any other such decomposition is also an epimorphism.
-/
lemma epi_of_nonDegenerate_decompositions (x : X _⦋n⦌) {m : ℕ}
    (f₁ : ⦋n⦌ ⟶ ⦋m⦌) [Epi f₁]
    (y₁ : X.nonDegenerate m) (hy₁ : x = X.map f₁.op y₁)
    (f₂ : ⦋n⦌ ⟶ ⦋m⦌)
    (y₂ : X.nonDegenerate m) (hy₂ : x = X.map f₂.op y₂) :
    Epi f₂ := by
  obtain ⟨sf⟩ :=
    (EilenbergZilberCategory.section_of_minus f₁
      (inferInstance : Epi f₁)).exists_splitEpi
  let g := sf.section_ ≫ f₂
  have hg : X.map g.op y₂ = y₁ := by
    calc
      X.map (sf.section_ ≫ f₂).op y₂ =
          X.map sf.section_.op (X.map f₂.op y₂) :=
        ConcreteCategory.congr_hom (X.map_comp f₂.op sf.section_.op) y₂
      _ = X.map sf.section_.op x := by rw [← hy₂]
      _ = X.map sf.section_.op (X.map f₁.op y₁) := by rw [hy₁]
      _ = X.map (f₁.op ≫ sf.section_.op) y₁ :=
        (ConcreteCategory.congr_hom
          (X.map_comp f₁.op sf.section_.op) y₁).symm
      _ = X.map (sf.section_ ≫ f₁).op y₁ := rfl
      _ = X.map (𝟙 ⦋m⦌).op y₁ := by rw [sf.id]
      _ = y₁ := by simp
  have hg_iso : IsIso g :=
    Presheaf.isIso_of_map_eq_nondegenerate_of_degree_eq
      X g y₁ y₂ hg
      ((isNondegenerate_iff_mem_nonDegenerate
        (X := X) (n := m) y₁.1).mpr y₁.2) rfl
  letI : IsIso g := hg_iso
  haveI : Epi g := inferInstance
  exact epi_of_epi sf.section_ f₂

/--
Both the simplex and map in an equal-dimensional nondegenerate decomposition
are unique.
-/
lemma unique_nonDegenerate_decomposition_of_eilenbergZilber
    (x : X _⦋n⦌) {m : ℕ}
    (f₁ : ⦋n⦌ ⟶ ⦋m⦌) [Epi f₁]
    (y₁ : X.nonDegenerate m) (hy₁ : x = X.map f₁.op y₁)
    (f₂ : ⦋n⦌ ⟶ ⦋m⦌)
    (y₂ : X.nonDegenerate m) (hy₂ : x = X.map f₂.op y₂) :
    y₁ = y₂ ∧ f₁ = f₂ := by
  letI : Epi f₂ :=
    epi_of_nonDegenerate_decompositions x f₁ y₁ hy₁ f₂ y₂ hy₂
  let d₁ : Presheaf.MinusDecomposition X x := {
    b := ⦋m⦌
    σ := f₁
    σ_mem := (inferInstance : Epi f₁)
    y := y₁
    map_y := hy₁.symm
  }
  let d₂ : Presheaf.MinusDecomposition X x := {
    b := ⦋m⦌
    σ := f₂
    σ_mem := (inferInstance : Epi f₂)
    y := y₂
    map_y := hy₂.symm
  }
  have hd₁ : Presheaf.IsNondegenerate X d₁.y := by
    change Presheaf.IsNondegenerate X (y₁ : X _⦋m⦌)
    exact (isNondegenerate_iff_mem_nonDegenerate
      (X := X) (n := m) y₁.1).mpr y₁.2
  have hd₂ : Presheaf.IsNondegenerate X d₂.y := by
    change Presheaf.IsNondegenerate X (y₂ : X _⦋m⦌)
    exact (isNondegenerate_iff_mem_nonDegenerate
      (X := X) (n := m) y₂.1).mpr y₂.2
  have hd : d₁ = d₂ :=
    Presheaf.MinusDecomposition.eq_of_nondegenerate X d₁ d₂ hd₁ hd₂
  have hySigma := congrArg
    (fun d : Presheaf.MinusDecomposition X x ↦
      (⟨d.b, d.y⟩ : Σ b, X.obj (op b))) hd
  change (⟨⦋m⦌, y₁.1⟩ : Σ b, X.obj (op b)) =
    (⟨⦋m⦌, y₂.1⟩ : Σ b, X.obj (op b)) at hySigma
  have hfSigma := congrArg
    (fun d : Presheaf.MinusDecomposition X x ↦
      (⟨d.b, d.σ⟩ : Σ b, ⦋n⦌ ⟶ b)) hd
  change (⟨⦋m⦌, f₁⟩ : Σ b, ⦋n⦌ ⟶ b) =
    (⟨⦋m⦌, f₂⟩ : Σ b, ⦋n⦌ ⟶ b) at hfSigma
  constructor
  · apply Subtype.ext
    injection hySigma
  · injection hfSigma

/--
Restatement of Mathlib's `SSet.unique_nonDegenerate_simplex`, deduced from the
general Eilenberg–Zilber uniqueness theorem.
-/
lemma unique_nonDegenerate_simplex_of_eilenbergZilber (x : X _⦋n⦌) {m : ℕ}
    (f₁ : ⦋n⦌ ⟶ ⦋m⦌) [Epi f₁]
    (y₁ : X.nonDegenerate m) (hy₁ : x = X.map f₁.op y₁)
    (f₂ : ⦋n⦌ ⟶ ⦋m⦌)
    (y₂ : X.nonDegenerate m) (hy₂ : x = X.map f₂.op y₂) :
    y₁ = y₂ := by
  exact (unique_nonDegenerate_decomposition_of_eilenbergZilber
    x f₁ y₁ hy₁ f₂ y₂ hy₂).1

/--
Restatement of Mathlib's `SSet.unique_nonDegenerate_map`, deduced from the
general Eilenberg–Zilber uniqueness theorem.
-/
lemma unique_nonDegenerate_map_of_eilenbergZilber (x : X _⦋n⦌) {m : ℕ}
    (f₁ : ⦋n⦌ ⟶ ⦋m⦌) [Epi f₁]
    (y₁ : X.nonDegenerate m) (hy₁ : x = X.map f₁.op y₁)
    (f₂ : ⦋n⦌ ⟶ ⦋m⦌)
    (y₂ : X.nonDegenerate m) (hy₂ : x = X.map f₂.op y₂) :
    f₁ = f₂ := by
  exact (unique_nonDegenerate_decomposition_of_eilenbergZilber
    x f₁ y₁ hy₁ f₂ y₂ hy₂).2

end MathlibRestatements

end SimplexCategoryCorollaries

/-! ## Eilenberg–Zilber structure on costructured-arrow categories

This section collects the constructions used to lift an Eilenberg–Zilber
structure from `A` to the category of elements `CostructuredArrow yoneda X`.
-/

section CostructuredArrows

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
Two costructured arrows are equal when their left objects are equal and their
structure maps agree after transport along that equality.
-/
lemma CostructuredArrow.eq_of_left_eq
    {C D : Type*} [Category C] [Category D] {S : C ⥤ D} {T : D}
    {U V : CostructuredArrow S T} (h : U.left = V.left)
    (hw : S.map (eqToHom h) ≫ V.hom = U.hom) :
    U = V := by
  cases U with
  | mk Ul Ur Uh =>
    cases V with
    | mk Vl Vr Vh =>
      change Ul = Vl at h
      change S.map (eqToHom h) ≫ Vh = Uh at hw
      subst Vl
      have hright : Ur = Vr := Subsingleton.elim _ _
      subst Vr
      simp at hw
      subst Vh
      rfl

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
    isIso_eqToHom := by
      intro U V f hf
      letI : IsIso f := hf
      haveI : IsIso (π.map f) := inferInstance
      obtain ⟨h, hf_left⟩ :=
        EilenbergZilberCategory.isIso_eqToHom (π.map f) (inferInstance : IsIso (π.map f))
      change U.left = V.left at h
      change f.left = eqToHom h at hf_left
      have hw : yoneda.map (eqToHom h) ≫ V.hom = U.hom := by
        rw [← hf_left]
        exact CostructuredArrow.w f
      have hUV : U = V := CostructuredArrow.eq_of_left_eq h hw
      subst V
      exact ⟨rfl, CostructuredArrow.hom_ext _ _ (by simpa using hf_left)⟩
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

end CostructuredArrows

end EilenbergZilberCategory

end HomologyLean.InfinityCategories
