import Mathlib.AlgebraicTopology.AlternatingFaceMapComplex
import Mathlib.Algebra.Homology.Homotopy
import Mathlib.Algebra.Homology.TotalComplex
import Mathlib.CategoryTheory.Preadditive.FunctorCategory
import HomologyLean.SingularHomology.Shuffle
import HomologyLean.Tactic.NameParts

open HomologyLean.Tactic.NameParts

open AlgebraicTopology CategoryTheory.Limits
open scoped Simplicial
open HomologyLean.SingularHomology

namespace CategoryTheory

variable {C : Type*} [Category* C]

variable (C) in
abbrev BisimplicialObject := SimplicialObject (SimplicialObject C)

namespace BisimplicialObject

@[simps!]
def diag : BisimplicialObject C ⥤ SimplicialObject C :=
  Functor.uncurry ⋙ (Functor.whiskeringLeft _ _ _).obj (Functor.diag _)

variable [Preadditive C] [HasFiniteCoproducts C]

-- SimplicialObject is a `def` (not `abbrev`), so typeclass search doesn't
-- unfold it to `Functor SimplexCategoryᵒᵖ C` to find functorCategoryPreadditive.
instance : Preadditive (SimplicialObject C) := CategoryTheory.functorCategoryPreadditive

instance : (alternatingFaceMapComplex C).Additive := { }

open ComplexShape in
instance (K : ChainComplex (ChainComplex C ℕ) ℕ) :
    HomologicalComplex₂.HasTotal K (.down ℕ) := by
  intro n
  let f (pq : ((down ℕ).π (down ℕ) (down ℕ) ⁻¹' {n})) : Fin (n + 1) × Fin (n + 1) :=
    ⟨⟨pq.1.1, by
      have := pq.2
      simp only [Set.mem_preimage, π_def, Set.mem_singleton_iff] at this
      lia⟩, ⟨pq.1.2, by
      have := pq.2
      simp only [Set.mem_preimage, π_def, Set.mem_singleton_iff] at this
      lia⟩⟩
  have := Finite.of_injective f (fun _ _ ↦ by grind)
  infer_instance

noncomputable abbrev F₁ : BisimplicialObject C ⥤ ChainComplex C ℕ :=
  alternatingFaceMapComplex _  ⋙
    (alternatingFaceMapComplex C).mapHomologicalComplex _ ⋙
      HomologicalComplex₂.totalFunctor _ _ _ _

abbrev F₂ : BisimplicialObject C ⥤ ChainComplex C ℕ :=
  diag ⋙ alternatingFaceMapComplex C

/-- The double complex obtained by applying `alternatingFaceMapComplex` in both simplicial
directions. Its `(p, q)` entry is `X_{p,q}`. -/
abbrev doubleComplex (X : BisimplicialObject C) :
    HomologicalComplex (ChainComplex C ℕ) (ComplexShape.down ℕ) :=
  ((alternatingFaceMapComplex C).mapHomologicalComplex _).obj
    ((alternatingFaceMapComplex (SimplicialObject C)).obj X)

/-! ### Basic simplicial maps

The Alexander-Whitney and shuffle maps are built from the standard front and back inclusions
`ι_front` and `ι_back`. -/

/-- Front face inclusion `[p] ⟶ [p+q]`: the unique monotone map sending `i ↦ i`. -/
def ι_front (p q : ℕ) : (⦋p⦌ : SimplexCategory) ⟶ ⦋p + q⦌ :=
  SimplexCategory.mkHom ⟨fun i => ⟨i.1, by omega⟩, fun _ _ h => h⟩

/-- Back face inclusion `[q] ⟶ [p+q]`: the unique monotone map sending `j ↦ p + j`. -/
def ι_back (p q : ℕ) : (⦋q⦌ : SimplexCategory) ⟶ ⦋p + q⦌ :=
  SimplexCategory.mkHom ⟨fun j => ⟨p + j.1, by omega⟩, fun _ _ h => Nat.add_le_add_left h _⟩

/-- `ι_front(p, q) ≫ δ k = δ k ≫ ι_front(p+1, q)` when `k ≤ p`, i.e., the face map
acts within the front range. Here `δ k` on the left is `[p+q] → [p+q+1]` and
`δ k` on the right is `[p] → [p+1]`. -/
lemma ι_front_comp_δ_of_le (p q : ℕ) (k : Fin (p + q + 2))
    (hk : (k : ℕ) ≤ p) :
    ι_front p q ≫ SimplexCategory.δ k =
      SimplexCategory.δ ⟨k, by omega⟩ ≫ ι_front (p + 1) q ≫
        eqToHom (by ring_nf) := by
  ext ⟨i, hi⟩
  simp only [SimplexCategory.comp_toOrderHom, OrderHom.comp_coe, Function.comp_apply,
    SimplexCategory.eqToHom_toOrderHom, SimplexCategory.len_mk]
  simp only [SimplexCategory.len_mk] at hi
  dsimp [ι_front, SimplexCategory.δ, Fin.succAboveOrderEmb, Fin.castOrderIso]
  simp only [Fin.succAbove, Fin.lt_def, Fin.val_castSucc]
  split_ifs <;> simp_all

/-- `ι_front(p, q) ≫ δ k = ι_front(p, q+1)` when `k > p`, i.e., the face map
acts beyond the front range — all front vertices stay below the skipped index. -/
lemma ι_front_comp_δ_of_gt (p q : ℕ) (k : Fin (p + q + 2))
    (hk : p < (k : ℕ)) :
    ι_front p q ≫ SimplexCategory.δ k =
      ι_front p (q + 1) ≫ eqToHom (by ring_nf) := by
  ext ⟨i, hi⟩
  simp only [SimplexCategory.comp_toOrderHom, OrderHom.comp_coe, Function.comp_apply,
    SimplexCategory.eqToHom_toOrderHom, SimplexCategory.len_mk]
  simp only [SimplexCategory.len_mk] at hi
  dsimp [ι_front, SimplexCategory.δ, Fin.succAboveOrderEmb, Fin.castOrderIso]
  simp only [Fin.succAbove, Fin.lt_def, Fin.val_castSucc]
  split_ifs <;> simp_all
  omega

/-- `ι_back(p, q) ≫ δ k = ι_back(p+1, q)` when `k ≤ p`, i.e., the face map
acts before the back range — all back vertices shift by one. -/
lemma ι_back_comp_δ_of_le (p q : ℕ) (k : Fin (p + q + 2))
    (hk : (k : ℕ) ≤ p) :
    ι_back p q ≫ SimplexCategory.δ k =
      ι_back (p + 1) q ≫ eqToHom (by ring_nf) := by
  ext ⟨i, hi⟩
  simp only [SimplexCategory.comp_toOrderHom, OrderHom.comp_coe, Function.comp_apply,
    SimplexCategory.eqToHom_toOrderHom, SimplexCategory.len_mk]
  simp only [SimplexCategory.len_mk] at hi
  dsimp [ι_back, SimplexCategory.δ, Fin.succAboveOrderEmb, Fin.castOrderIso]
  simp only [Fin.succAbove, Fin.lt_def, Fin.val_castSucc]
  split_ifs <;> simp_all <;> omega

/-- `ι_back(p, q) ≫ δ k = δ (k - p) ≫ ι_back(p, q+1)` when `k > p`, i.e., the face
map acts within the back range. Here `δ (k-p)` is the face map on `[q]`. -/
lemma ι_back_comp_δ_of_gt (p q : ℕ) (k : Fin (p + q + 2))
    (hk : p < (k : ℕ)) :
    ι_back p q ≫ SimplexCategory.δ k =
      SimplexCategory.δ ⟨k - p, by omega⟩ ≫ ι_back p (q + 1) ≫
        eqToHom (by ring_nf) := by
  ext ⟨i, hi⟩
  simp only [SimplexCategory.comp_toOrderHom, OrderHom.comp_coe, Function.comp_apply,
    SimplexCategory.eqToHom_toOrderHom, SimplexCategory.len_mk]
  simp only [SimplexCategory.len_mk] at hi
  dsimp [ι_back, SimplexCategory.δ, Fin.succAboveOrderEmb, Fin.castOrderIso]
  simp only [Fin.succAbove, Fin.lt_def, Fin.val_castSucc]
  split_ifs <;> simp_all <;> omega

/-- The top face of `[p+1]` followed by the front inclusion is the front inclusion
`[p] ⟶ [p+(q+1)]`, up to the arithmetic reassociation of the target. -/
private lemma δ_last_comp_ι_front (p q : ℕ) :
    SimplexCategory.δ (Fin.last (p + 1)) ≫ ι_front (p + 1) q =
      ι_front p (q + 1) ≫ eqToHom (by congr 1; omega) := by
  ext ⟨i, hi⟩
  simp only [SimplexCategory.comp_toOrderHom, OrderHom.comp_coe, Function.comp_apply,
    SimplexCategory.eqToHom_toOrderHom, SimplexCategory.len_mk]
  simp only [SimplexCategory.len_mk] at hi
  dsimp [ι_front, SimplexCategory.δ, Fin.succAboveOrderEmb, Fin.castOrderIso]
  simp only [Fin.succAbove, Fin.lt_def, Fin.val_last, Fin.val_castSucc]
  split_ifs
  simp_all

/-- The bottom face of `[q+1]` followed by the back inclusion shifts the back block
from offset `p` to offset `p+1`, up to the arithmetic reassociation of the target. -/
private lemma δ_zero_comp_ι_back (p q : ℕ) :
    SimplexCategory.δ 0 ≫ ι_back p (q + 1) =
      ι_back (p + 1) q ≫ eqToHom (by congr 1; omega) := by
  ext ⟨i, hi⟩
  simp only [SimplexCategory.comp_toOrderHom, OrderHom.comp_coe, Function.comp_apply,
    SimplexCategory.eqToHom_toOrderHom, SimplexCategory.len_mk]
  simp only [SimplexCategory.len_mk] at hi
  dsimp [ι_back, SimplexCategory.δ, Fin.succAboveOrderEmb, Fin.castOrderIso]
  omega

/-! ### Alexander-Whitney map

The Alexander-Whitney map `F₂(X) ⟶ F₁(X)` sends the diagonal chain complex to the total complex by
copairing the component maps `awComponent X p q` over all decompositions `p + q = n`. -/

/-- The `(p, q)` component of the Alexander-Whitney map. -/
noncomputable def awComponent (X : BisimplicialObject C) (p q : ℕ) :
    (X.obj (Opposite.op ⦋p + q⦌)).obj (Opposite.op ⦋p + q⦌) ⟶
    (X.obj (Opposite.op ⦋p⦌)).obj (Opposite.op ⦋q⦌) :=
  (X.map (ι_front p q).op).app (Opposite.op ⦋p + q⦌) ≫
    (X.obj (Opposite.op ⦋p⦌)).map (ι_back p q).op

omit [Preadditive C] [HasFiniteCoproducts C] in
/-- Rewrite a diagonal face composed with an Alexander-Whitney component.

The result splits according to whether the face lands in the front block or the back block. -/
private lemma diag_δ_comp_eqToHom_awComponent (X : BisimplicialObject C)
    (n p q : ℕ) (hpq : p + q = n) (k : Fin (n + 2)) :
    (X.map (SimplexCategory.δ k).op).app (Opposite.op ⦋n + 1⦌) ≫
      (X.obj (Opposite.op ⦋n⦌)).map (SimplexCategory.δ k).op ≫
        eqToHom (by subst hpq; rfl) ≫ awComponent X p q =
    if hk : (k : ℕ) ≤ p then
      eqToHom (by subst hpq; simp only [show p + 1 + q = p + q + 1 by omega]) ≫
        awComponent X (p + 1) q ≫
          (X.map (SimplexCategory.δ ⟨k, by omega⟩).op).app (Opposite.op ⦋q⦌)
    else
      eqToHom (by subst hpq; simp only [show p + (q + 1) = p + q + 1 by omega]) ≫
        awComponent X p (q + 1) ≫
          (X.obj (Opposite.op ⦋p⦌)).map
            (SimplexCategory.δ ⟨k - p, by omega⟩).op := by
  subst hpq
  unfold awComponent
  split_ifs with hk
  · simp only [Category.assoc]
    simp only [eqToHom_refl, Category.id_comp]
    slice_lhs 2 3 =>
      rw [(X.map (ι_front p q).op).naturality (SimplexCategory.δ k).op]
    simp only [Category.assoc]
    slice_lhs 1 2 => rw [← NatTrans.comp_app, ← Functor.map_comp]
    rw [← op_comp, ι_front_comp_δ_of_le p q k hk]
    simp only [op_comp, Functor.map_comp, NatTrans.comp_app, Category.assoc]
    slice_lhs 4 5 => rw [← Functor.map_comp, ← op_comp, ι_back_comp_δ_of_le p q k hk]
    simp only [op_comp, Functor.map_comp, eqToHom_op, eqToHom_map, eqToHom_app]
    generalize_proofs at *
    -- Apply θ = X.map (δ k).op naturality on the RHS w.r.t. the back-face ι_back, turning
    -- `X_⦋p+1⦌.map ι_back ≫ θ.app ⦋q⦌` into `θ.app ⦋p+1+q⦌ ≫ X_⦋p⦌.map ι_back`.
    slice_rhs 3 4 =>
      rw [(X.map (SimplexCategory.δ ⟨↑k, by omega⟩).op).naturality (ι_back (p + 1) q).op]
    -- Fuse the two vertical maps `η.app d ≫ θ.app d` into a single
    -- `(X.map (ι_front.op ≫ δ.op)).app d` on both sides, leaving one natural transformation.
    slice_lhs 2 3 => rw [← NatTrans.comp_app, ← Functor.map_comp]
    slice_rhs 2 3 => rw [← NatTrans.comp_app, ← Functor.map_comp]
    simp only [Category.assoc]
    -- Slide the leftover eqToHom (horizontal degree p+q+1 → p+1+q) across the fused map via
    -- its naturality for the cast morphism, lining both sides up at degree p+1+q. The goal has
    -- a bare `eqToHom`; first re-express it as `X_⦋p⦌.map (eqToHom _)` so naturality matches.
    slice_lhs 2 3 =>
      rw [← eqToHom_map (X _⦋p⦌) (show (Opposite.op ⦋p + q + 1⦌ : SimplexCategoryᵒᵖ) =
            Opposite.op ⦋p + 1 + q⦌ from by rw [show p + q + 1 = p + 1 + q from by omega])]
      rw [← (X.map ((ι_front (p + 1) q).op ≫ (SimplexCategory.δ ⟨↑k, by omega⟩).op)).naturality
        (eqToHom (show (Opposite.op ⦋p + q + 1⦌ : SimplexCategoryᵒᵖ) = Opposite.op ⦋p + 1 + q⦌ from
          by rw [show p + q + 1 = p + 1 + q from by omega]))]
    simp only [eqToHom_map, eqToHom_trans_assoc, Category.assoc]
  · simp only [Category.assoc]
    simp only [eqToHom_refl, Category.id_comp]
    slice_lhs 2 3 =>
      rw [(X.map (ι_front p q).op).naturality (SimplexCategory.δ k).op]
    simp only [Category.assoc]
    slice_lhs 1 2 => rw [← NatTrans.comp_app, ← Functor.map_comp]
    rw [← op_comp, ι_front_comp_δ_of_gt p q k (by omega)]
    simp only [op_comp, Functor.map_comp, NatTrans.comp_app, Category.assoc]
    slice_lhs 3 4 => rw [← Functor.map_comp, ← op_comp, ι_back_comp_δ_of_gt p q k (by omega)]
    simp only [op_comp, Functor.map_comp, eqToHom_op, eqToHom_map, eqToHom_app, Category.assoc]
    -- The two eqToHom casts collapse (`p+q+1` and `p+(q+1)` are defeq), leaving identical
    -- composites whose only difference is the defeq index `⦋p+q+1⦌` vs `⦋p+(q+1)⦌`.
    simp only [eqToHom_refl, Category.id_comp]
    rfl

omit [Preadditive C] [HasFiniteCoproducts C] in
/-- The top face of `awComponent (p+1, q)` agrees with the bottom face of
`awComponent (p, q+1)`, up to the canonical arithmetic cast. -/
private lemma awComponent_top_face_eq_bottom_face (X : BisimplicialObject C) (p q : ℕ) :
    awComponent X (p + 1) q ≫
        (X.map (SimplexCategory.δ (Fin.last (p + 1))).op).app (Opposite.op ⦋q⦌) =
      eqToHom (by simp only [show p + 1 + q = p + (q + 1) by omega]) ≫
        awComponent X p (q + 1) ≫
        (X _⦋p⦌).map (SimplexCategory.δ 0).op := by
  unfold awComponent
  simp only [Category.assoc]
  rw [(X.map (SimplexCategory.δ (Fin.last (p + 1))).op).naturality
    (ι_back (p + 1) q).op]
  simp only [← Functor.map_comp]
  slice_lhs 1 2 => rw [← NatTrans.comp_app, ← Functor.map_comp]
  rw [← op_comp, δ_last_comp_ι_front]
  rw [← op_comp, δ_zero_comp_ι_back]
  simp only [op_comp, Functor.map_comp, NatTrans.comp_app, Category.assoc]
  slice_lhs 1 1 => rw [eqToHom_op, eqToHom_map, eqToHom_app]
  slice_rhs 2 3 =>
    rw [← (X.map (ι_front p (q + 1)).op).naturality
      (eqToHom (by congr 1; omega)).op]
  simp only [Category.assoc, eqToHom_op, eqToHom_map, eqToHom_trans_assoc]

private lemma sum_bij_front {α : Type*} [AddCommMonoid α] {j : ℕ} (x : Fin (j + 1))
    {f : Fin (↑x + 1) → α}
    {g :
      {y : Fin (j + 2) // y ∈ Finset.univ.filter (fun y : Fin (j + 2) => (↑y : ℕ) ≤ ↑x)} → α}
    (hfg : ∀ i : Fin (↑x + 1),
      f i =
        g ⟨(⟨↑i, by omega⟩ : Fin (j + 2)), by
          simp only [Finset.mem_filter, Finset.mem_univ, true_and]
          omega⟩) :
    ∑ i : Fin (↑x + 1), f i = ∑ y, g y := by
  refine Finset.sum_bij'
    (fun (i : Fin (↑x + 1)) _ => ⟨(⟨↑i, by omega⟩ : Fin (j + 2)), by
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      omega⟩)
    (fun y _ => (⟨↑(↑y : Fin (j + 2)), by
      have := (Finset.mem_filter.mp y.2).2
      omega⟩ : Fin (↑x + 1)))
    ?_ ?_ ?_ ?_ ?_
  · intros; exact Finset.mem_univ _
  · intros; exact Finset.mem_univ _
  · intros; rfl
  · intros; rfl
  · intros; simpa using hfg _

private lemma sum_bij_back {α : Type*} [AddCommMonoid α] {j : ℕ} (x : Fin (j + 1))
    {f : Fin (j - ↑x + 1) → α}
    {g :
      {y : Fin (j + 2) // y ∈ Finset.univ.filter (fun y : Fin (j + 2) => ¬ (↑y : ℕ) ≤ ↑x)} → α}
    (hfg : ∀ i : Fin (j - ↑x + 1),
      f i =
        g ⟨(⟨↑x + 1 + ↑i, by omega⟩ : Fin (j + 2)), by
          simp only [Finset.mem_filter, Finset.mem_univ, true_and]
          omega⟩) :
    ∑ i : Fin (j - ↑x + 1), f i = ∑ y, g y := by
  refine Finset.sum_bij'
    (fun (i : Fin (j - ↑x + 1)) _ => ⟨(⟨↑x + 1 + ↑i, by omega⟩ : Fin (j + 2)), by
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      omega⟩)
    (fun y _ => (⟨↑(↑y : Fin (j + 2)) - (↑x + 1), by
      have h1 := (Finset.mem_filter.mp y.2).2
      have h2 := (↑y : Fin (j + 2)).isLt
      omega⟩ : Fin (j - ↑x + 1)))
    ?_ ?_ ?_ ?_ ?_
  · intros; exact Finset.mem_univ _
  · intros; exact Finset.mem_univ _
  · intros; apply Fin.ext; simp
  · intro y hy
    apply Subtype.ext; apply Fin.ext
    have hgt := (Finset.mem_filter.mp y.2).2
    simp at hgt ⊢
    omega
  · intros; simpa using hfg _

/-- The Alexander-Whitney chain map `F₂(X) ⟶ F₁(X)`. -/
noncomputable def alexanderWhitney (X : BisimplicialObject C) :
    F₂.obj X ⟶ F₁.obj X where
  f n := by
    change (X.obj (Opposite.op ⦋n⦌)).obj (Opposite.op ⦋n⦌) ⟶ _
    exact ∑ p : Fin (n + 1),
      eqToHom (by simp [Nat.add_sub_cancel' (Nat.lt_succ_iff.mp p.isLt)]) ≫
        awComponent X p (n - p) ≫
          HomologicalComplex₂.ιTotal (doubleComplex X) (ComplexShape.down ℕ) p (n - p) n (by
            simp only [ComplexShape.π_def, Nat.add_sub_cancel' (Nat.lt_succ_iff.mp p.isLt)])
  comm' := by
    intro i j h
    simp only [id]
    rw [ComplexShape.down_Rel] at h; subst h
    -- Expand the total differential on the left into its `D₁ + D₂` pieces.
    simp only [Preadditive.sum_comp, Category.assoc]
    change ∑ x : Fin (j + 2), _ ≫ _ ≫ _ ≫
      (HomologicalComplex₂.total (doubleComplex X) (ComplexShape.down ℕ)).d (j + 1) j = _
    rw [HomologicalComplex₂.total_d]
    simp only [Preadditive.comp_add, Finset.sum_add_distrib,
      HomologicalComplex₂.ι_D₁, HomologicalComplex₂.ι_D₂]
    -- Expand the diagonal differential on the right as the alternating face sum.
    simp only [Preadditive.comp_sum]
    simp only [F₂, Functor.comp_obj, diag_obj_obj, alternatingFaceMapComplex_obj_d,
      AlternatingFaceMapComplex.objD, SimplicialObject.δ, diag_obj_map]
    simp only [Preadditive.sum_comp, Preadditive.zsmul_comp, Category.assoc]
    -- Rewrite each diagonal face through `awComponent`.
    -- `conv` is used here because the target term sits under nested sums and casts.
    conv_rhs =>
      enter [2, x, 2, x_1, 2]
      rw [reassoc_of% diag_δ_comp_eqToHom_awComponent X j (↑x) (j - ↑x)
        (Nat.add_sub_cancel' (Nat.lt_succ_iff.mp x.isLt)) x_1]
    simp only [smul_dite, dite_comp]
    simp_rw [Finset.sum_dite]
    rw [Finset.sum_add_distrib]
    -- Separate off the two boundary faces so the remaining sums have matching index ranges.
    conv_lhs => rw [Fin.sum_univ_succ]
    rw [HomologicalComplex₂.d₁_eq_zero _ _ _ _ _ (by simp), comp_zero, comp_zero, zero_add]
    conv_lhs => enter [2]; rw [Fin.sum_univ_castSucc]
    rw [HomologicalComplex₂.d₂_eq_zero _ _ _ _ _ (by simp), comp_zero, comp_zero, add_zero]
    -- Expand `d₁` and `d₂` into alternating face sums.
    conv_lhs =>
      enter [1, 2, i]
      rw [HomologicalComplex₂.d₁_eq _ _
            (show (ComplexShape.down ℕ).Rel (↑i.succ) ↑i by simp) _ _ (by simp; omega)]
    conv_lhs =>
      enter [2, 2, i]
      rw [HomologicalComplex₂.d₂_eq _ _ _
            (show (ComplexShape.down ℕ).Rel (j + 1 - ↑i.castSucc) (j - ↑i.castSucc) by
              simp; omega) _ (by simp; omega)]
    -- Replace the total-complex signs by their explicit formulas.
    simp_rw [show ∀ p q : ℕ,
              ((ComplexShape.down ℕ).ε₁ (.down ℕ) (.down ℕ) (p, q) : ℤˣ) = 1
              from fun _ _ => rfl,
             one_smul,
             show ∀ p q : ℕ,
              ((ComplexShape.down ℕ).ε₂ (.down ℕ) (.down ℕ) (p, q) : ℤˣ) = (-1 : ℤˣ)^p
              from fun _ _ => rfl]
    simp only [Fin.val_castSucc]
    -- Rewrite the `d₂` index into successor form before unfolding the differential.
    conv_lhs =>
      enter [2, 2, x]
      rw [(HomologicalComplex.eqToHom_comp_d _
            (show (ComplexShape.down ℕ).Rel (j + 1 - ↑x) (j - ↑x) by
              simp [ComplexShape.down_Rel]; omega)
            (show (ComplexShape.down ℕ).Rel ((j - ↑x) + 1) (j - ↑x) by
              simp [ComplexShape.down_Rel])).symm]
    conv_lhs =>
      enter [2, 2, x]
      simp only [Functor.mapHomologicalComplex_obj_X, alternatingFaceMapComplex_obj_X,
        alternatingFaceMapComplex_obj_d, AlternatingFaceMapComplex.objD, SimplicialObject.δ]
    -- Expose the `.f` component so `NatTrans.app` distributes over the sum.
    conv_lhs =>
      enter [1, 2, x]
      simp only [Fin.val_succ, doubleComplex, Functor.mapHomologicalComplex_obj_d,
        alternatingFaceMapComplex_map_f, alternatingFaceMapComplex_obj_d,
        AlternatingFaceMapComplex.objD, SimplicialObject.δ]
    conv_lhs =>
      enter [1, 2, x]
      rw [NatTrans.app_sum, Finset.sum_congr rfl (fun x _ => NatTrans.app_zsmul _ _ _)]
    -- Distribute composition and scalar multiplication to put both sides into the same shape.
    simp only [Units.smul_def, Preadditive.comp_sum, Preadditive.sum_comp,
      Preadditive.zsmul_comp, Preadditive.comp_zsmul, Category.assoc,
      Finset.smul_sum, smul_smul]
    -- Peel the remaining boundary faces so the interior ranges line up.
    conv_lhs =>
      enter [1, 2, x]
      rw [Fin.sum_univ_castSucc]
    conv_lhs =>
      enter [2, 2, x]
      rw [Fin.sum_univ_succ]
    simp only [Finset.sum_add_distrib]
    -- Name the summands and regroup them so the boundary terms can be cancelled together.
    name_parts ?A0 + ?B0 + (?C0 + ?D0) = ?E0 + ?F0
    rw [show A0 + B0 + (C0 + D0) = (A0 + D0) + (B0 + C0) from by abel]
    -- Reindex the interior sums and then cancel the boundary pair.
    have hAE : A0 = E0 := by
      refine Finset.sum_congr rfl (fun x _ => ?_)
      refine sum_bij_front (x := x) ?_
      intro a
      have k : j + 1 - (↑x + 1) = j - ↑x := by omega
      generalize_proofs at *
      generalize j + 1 - (↑x + 1) = q at *
      subst k
      rfl
    have hDF : D0 = F0 := by
      refine Finset.sum_congr rfl (fun x _ => ?_)
      refine sum_bij_back
        (α := ((alternatingFaceMapComplex C).obj (diag.obj X)).X (j + 1) ⟶
          (HomologicalComplex₂.total X.doubleComplex (ComplexShape.down ℕ)).X j)
        (x := x) ?_
      intro a
      have k : j + 1 - ↑x = j - ↑x + 1 := by omega
      generalize_proofs at *
      generalize j + 1 - ↑x = q at *
      subst k
      simp only [eqToHom_refl, Category.id_comp]
      congr 1
      · push_cast
        rw [Fin.val_succ, pow_add]
        ring
      · congr
        apply Fin.ext
        simp
        omega
    have hBC : B0 + C0 = 0 := by
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_eq_zero
      intro x _
      have k : j + 1 - (↑x + 1) = j - ↑x := by omega
      generalize_proofs at *
      generalize j + 1 - (↑x + 1) = q at *
      subst k
      simp only [Fin.val_zero, pow_zero, mul_one]
      name_parts ?s1 • ?MA + ?s2 • ?MB = 0
      suffices hAB : MA = MB by
        have hscalar : s1 = -s2 := by
          change ((-1 : ℤ) ^ ((Fin.last ((x.val : ℕ) + 1)).val : ℕ)) = -↑((-1 : ℤˣ) ^ x.val)
          rw [Fin.val_last, pow_succ, Units.val_pow_eq_pow_val]
          push_cast
          ring
        rw [hAB, hscalar, neg_smul, neg_add_cancel]
      simp only [MA, MB]
      simp only [← Category.assoc]
      congr 1
      simp only [Category.assoc]
      rw [awComponent_top_face_eq_bottom_face]
      generalize hq : j + 1 - ↑x = q at *
      have hq' : j - ↑x + 1 = q := by omega
      subst hq'
      simp only [eqToHom_trans_assoc]
      congr 1
      simp only [eqToHom_refl, Category.id_comp]
    rw [hAE, hDF, hBC, add_zero]
/-! ### Shuffle map

The shuffle map `F₁(X) ⟶ F₂(X)` is defined on each bidegree `(p, q)` by the signed sum over
`(p, q)`-shuffles, and then assembled with `totalDesc`. -/

/-- First projection of a shuffle as a `SimplexCategory` morphism `⦋p+q⦌ ⟶ ⦋p⦌`. -/
def shuffleFstHom {p q : ℕ} (μ : Shuffle p q) : (⦋p + q⦌ : SimplexCategory) ⟶ ⦋p⦌ :=
  SimplexCategory.Hom.mk (OrderHom.fst.comp μ.1)

/-- Second projection of a shuffle as a `SimplexCategory` morphism `⦋p+q⦌ ⟶ ⦋q⦌`. -/
def shuffleSndHom {p q : ℕ} (μ : Shuffle p q) : (⦋p + q⦌ : SimplexCategory) ⟶ ⦋q⦌ :=
  SimplexCategory.Hom.mk (OrderHom.snd.comp μ.1)

/-- The `(p, q)` component of the shuffle map. -/
noncomputable def ezComponent (X : BisimplicialObject C) (p q : ℕ) :
    (X.obj (Opposite.op ⦋p⦌)).obj (Opposite.op ⦋q⦌) ⟶
    (X.obj (Opposite.op ⦋p + q⦌)).obj (Opposite.op ⦋p + q⦌) :=
  ∑ μ : Shuffle p q, μ.sign •
    ((X.obj (Opposite.op ⦋p⦌)).map (shuffleSndHom μ).op ≫
      (X.map (shuffleFstHom μ).op).app (Opposite.op ⦋p + q⦌))

/-! ### Boundary formula for the shuffle components

The chain map condition for `shuffleMap` is reduced to a componentwise identity for
`ezComponent`: composing with the diagonal differential splits into the expected vertical and
horizontal boundary terms. -/

/-- Left insertion face factorization (fst component):
`δ_{insertLeftIndex} ≫ eqToHom ≫ fstHom(insertLeftStep ν j) = fstHom(ν) ≫ δ(j)`. -/
private lemma fstHom_insertLeftStep_comp_δ {p q n : ℕ}
    (ν : Shuffle p q) (j : Fin (p + 2)) (hn : n + 1 = (p + 1) + q) :
    SimplexCategory.δ ((ν.insertLeftIndex j).cast (by omega)) ≫
      eqToHom (congrArg SimplexCategory.mk hn) ≫
      shuffleFstHom (ν.insertLeftStep j) =
    eqToHom (congrArg SimplexCategory.mk (by omega : n = p + q)) ≫
      shuffleFstHom ν ≫ SimplexCategory.δ j := by
  ext ⟨i, hi⟩
  simp only [SimplexCategory.comp_toOrderHom, OrderHom.comp_coe, Function.comp_apply,
    SimplexCategory.Hom.toOrderHom_mk, SimplexCategory.eqToHom_toOrderHom,
    SimplexCategory.len_mk, shuffleFstHom]
  simp only [SimplexCategory.len_mk] at hi
  have hface := Shuffle.insertLeftStep_face ν j ⟨i, by omega⟩
  suffices harg : ∀ (a b : Fin ((p + 1) + q + 1)), a.val = b.val →
      (ν.insertLeftStep j).1 a = (ν.insertLeftStep j).1 b from
    congrArg (fun x => (x.1 : ℕ)) ((harg _ _ (by
      dsimp [SimplexCategory.δ, Fin.succAboveOrderEmb, SimplexCategory.comp_toOrderHom,
        SimplexCategory.eqToHom_toOrderHom, Fin.castOrderIso]
      simp only [Fin.succAbove, Fin.lt_def, Fin.val_castSucc]
      split_ifs <;> simp_all)).trans hface)
  exact fun _ _ h => congr_arg _ (Fin.ext h)

/-- Left insertion face factorization (snd component):
`δ_{insertLeftIndex} ≫ eqToHom ≫ sndHom(insertLeftStep ν j) = sndHom(ν)`. -/
private lemma sndHom_insertLeftStep_comp_δ {p q n : ℕ}
    (ν : Shuffle p q) (j : Fin (p + 2)) (hn : n + 1 = (p + 1) + q) :
    SimplexCategory.δ ((ν.insertLeftIndex j).cast (by omega)) ≫
      eqToHom (congrArg SimplexCategory.mk hn) ≫
      shuffleSndHom (ν.insertLeftStep j) =
    eqToHom (congrArg SimplexCategory.mk (by omega : n = p + q)) ≫
      shuffleSndHom ν := by
  ext ⟨i, hi⟩
  simp only [SimplexCategory.comp_toOrderHom, OrderHom.comp_coe, Function.comp_apply,
    SimplexCategory.Hom.toOrderHom_mk, SimplexCategory.eqToHom_toOrderHom,
    SimplexCategory.len_mk, shuffleSndHom]
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
`δ_{insertRightIndex} ≫ eqToHom ≫ fstHom(insertRightStep ν k) = fstHom(ν)`. -/
private lemma fstHom_insertRightStep_comp_δ {p q n : ℕ}
    (ν : Shuffle p q) (k : Fin (q + 2)) (hn : n + 1 = p + (q + 1)) :
    SimplexCategory.δ ((ν.insertRightIndex k).cast (by omega)) ≫
      eqToHom (congrArg SimplexCategory.mk hn) ≫
      shuffleFstHom (ν.insertRightStep k) =
    eqToHom (congrArg SimplexCategory.mk (by omega : n = p + q)) ≫
      shuffleFstHom ν := by
  ext ⟨i, hi⟩
  simp only [SimplexCategory.comp_toOrderHom, OrderHom.comp_coe, Function.comp_apply,
    SimplexCategory.Hom.toOrderHom_mk, SimplexCategory.eqToHom_toOrderHom,
    SimplexCategory.len_mk, shuffleFstHom]
  simp only [SimplexCategory.len_mk] at hi
  have hface := Shuffle.insertRightStep_face ν k ⟨i, by omega⟩
  suffices harg : ∀ (a b : Fin (p + (q + 1) + 1)), a.val = b.val →
      (ν.insertRightStep k).1 a = (ν.insertRightStep k).1 b from
    congrArg (fun x => (x.1 : ℕ)) ((harg _ _ (by
      dsimp [SimplexCategory.δ, Fin.succAboveOrderEmb, SimplexCategory.comp_toOrderHom,
        SimplexCategory.eqToHom_toOrderHom, Fin.castOrderIso]
      simp only [Fin.succAbove, Fin.lt_def, Fin.val_castSucc]
      split_ifs <;> simp_all)).trans hface)
  exact fun _ _ h => congr_arg _ (Fin.ext h)

/-- Right insertion face factorization (snd component):
`δ_{insertRightIndex} ≫ eqToHom ≫ sndHom(insertRightStep ν k) = sndHom(ν) ≫ δ(k)`. -/
private lemma sndHom_insertRightStep_comp_δ {p q n : ℕ}
    (ν : Shuffle p q) (k : Fin (q + 2)) (hn : n + 1 = p + (q + 1)) :
    SimplexCategory.δ ((ν.insertRightIndex k).cast (by omega)) ≫
      eqToHom (congrArg SimplexCategory.mk hn) ≫
      shuffleSndHom (ν.insertRightStep k) =
    eqToHom (congrArg SimplexCategory.mk (by omega : n = p + q)) ≫
      shuffleSndHom ν ≫ SimplexCategory.δ k := by
  ext ⟨i, hi⟩
  simp only [SimplexCategory.comp_toOrderHom, OrderHom.comp_coe, Function.comp_apply,
    SimplexCategory.Hom.toOrderHom_mk, SimplexCategory.eqToHom_toOrderHom,
    SimplexCategory.len_mk, shuffleSndHom]
  simp only [SimplexCategory.len_mk] at hi
  have hface := Shuffle.insertRightStep_face ν k ⟨i, by omega⟩
  suffices harg : ∀ (a b : Fin (p + (q + 1) + 1)), a.val = b.val →
      (ν.insertRightStep k).1 a = (ν.insertRightStep k).1 b from
    congrArg (fun x => (x.2 : ℕ)) ((harg _ _ (by
      dsimp [SimplexCategory.δ, Fin.succAboveOrderEmb, SimplexCategory.comp_toOrderHom,
        SimplexCategory.eqToHom_toOrderHom, Fin.castOrderIso]
      simp only [Fin.succAbove, Fin.lt_def, Fin.val_castSucc]
      split_ifs <;> simp_all)).trans hface)
  exact fun _ _ h => congr_arg _ (Fin.ext h)

/-- Composing `δ r ≫ eqToHom ≫ shuffleFstHom` of `swapDiagonalSteps μ` gives the same
result as for `μ`, because `δ r` maps via `succAbove r` which avoids vertex `r`,
and `swapDiagonalSteps` only changes the value at `r`. -/
lemma fstHom_swapDiagonalSteps_comp_δ {p q n : ℕ}
    (μ : Shuffle p q) (r : Fin (n + 2)) (hn : n + 1 = p + q)
    (h : Shuffle.isDiagonalVertex μ (r.cast (by omega))) :
    SimplexCategory.δ r ≫
      eqToHom (congrArg SimplexCategory.mk hn) ≫
      shuffleFstHom (μ.swapDiagonalSteps (r.cast (by omega)) h) =
    SimplexCategory.δ r ≫
      eqToHom (congrArg SimplexCategory.mk hn) ≫
      shuffleFstHom μ := by
  ext ⟨i, hi⟩
  simp only [SimplexCategory.comp_toOrderHom, OrderHom.comp_coe, Function.comp_apply,
    SimplexCategory.Hom.toOrderHom_mk, SimplexCategory.eqToHom_toOrderHom,
    SimplexCategory.len_mk, shuffleFstHom]
  set arg := (Fin.castOrderIso _).toOrderEmbedding.toOrderHom
    ((SimplexCategory.Hom.toOrderHom (SimplexCategory.δ r)) ⟨i, hi⟩)
  exact congrArg (fun x => (x.1 : ℕ)) (Shuffle.swapDiagonalSteps_apply_ne μ _ h arg (by
    simp only [arg, SimplexCategory.δ, SimplexCategory.mkHom, SimplexCategory.Hom.toOrderHom_mk,
      ne_eq, Fin.ext_iff, Fin.val_cast]
    exact fun heq => absurd (Fin.ext heq)
      (Fin.succAbove_ne r ⟨i, by simp only [SimplexCategory.len_mk] at hi; omega⟩)))

lemma sndHom_swapDiagonalSteps_comp_δ {p q n : ℕ}
    (μ : Shuffle p q) (r : Fin (n + 2)) (hn : n + 1 = p + q)
    (h : Shuffle.isDiagonalVertex μ (r.cast (by omega))) :
    SimplexCategory.δ r ≫
      eqToHom (congrArg SimplexCategory.mk hn) ≫
      shuffleSndHom (μ.swapDiagonalSteps (r.cast (by omega)) h) =
    SimplexCategory.δ r ≫
      eqToHom (congrArg SimplexCategory.mk hn) ≫
      shuffleSndHom μ := by
  ext ⟨i, hi⟩
  simp only [SimplexCategory.comp_toOrderHom, OrderHom.comp_coe, Function.comp_apply,
    SimplexCategory.Hom.toOrderHom_mk, SimplexCategory.eqToHom_toOrderHom,
    SimplexCategory.len_mk, shuffleSndHom]
  set arg := (Fin.castOrderIso _).toOrderEmbedding.toOrderHom
    ((SimplexCategory.Hom.toOrderHom (SimplexCategory.δ r)) ⟨i, hi⟩)
  exact congrArg (fun x => (x.2 : ℕ)) (Shuffle.swapDiagonalSteps_apply_ne μ _ h arg (by
    simp only [arg, SimplexCategory.δ, SimplexCategory.mkHom, SimplexCategory.Hom.toOrderHom_mk,
      ne_eq, Fin.ext_iff, Fin.val_cast]
    exact fun heq => absurd (Fin.ext heq)
      (Fin.succAbove_ne r ⟨i, by simp only [SimplexCategory.len_mk] at hi; omega⟩)))

omit [HasFiniteCoproducts C] in
/-- Boundary formula for `ezComponent`.

Composing `ezComponent X p q` with the diagonal differential splits into the vertical boundary
term coming from the first simplicial direction and the horizontal boundary term coming from the
second. The differential is written as `.d` rather than `objD` to avoid index-cast noise. -/
lemma ezComponent_boundary (X : BisimplicialObject C) (p q j : ℕ)
    (h : (ComplexShape.down ℕ).Rel (p + q) j) :
    ezComponent X p q ≫
      ((alternatingFaceMapComplex C).obj (diag.obj X)).d (p + q) j =
    -- Vertical part: face maps in the first simplicial direction
    (match p with
    | 0 => 0
    | p' + 1 =>
      ∑ k : Fin (p' + 2), (-1 : ℤ) ^ (k : ℕ) •
        ((X.map (SimplexCategory.δ k).op).app (Opposite.op ⦋q⦌) ≫
          ezComponent X p' q ≫
          eqToHom (by
            have : j + 1 = p' + 1 + q := by rwa [ComplexShape.down_Rel] at h
            simp [show p' + q = j from by omega]))) +
    -- Horizontal part: face maps in the second simplicial direction
    (match q with
    | 0 => 0
    | q' + 1 =>
      (-1 : ℤ) ^ p •
        ∑ k : Fin (q' + 2), (-1 : ℤ) ^ (k : ℕ) •
          ((X.obj (Opposite.op ⦋p⦌)).map (SimplexCategory.δ k).op ≫
            ezComponent X p q' ≫
            eqToHom (by
              have : j + 1 = p + (q' + 1) := by rwa [ComplexShape.down_Rel] at h
              simp [show p + q' = j from by omega]))) := by
  -- Expand `ezComponent` and distribute composition over the shuffle sum.
  simp only [ezComponent, Preadditive.sum_comp, Preadditive.zsmul_comp]
  -- Rewrite `.d (p+q) j` into successor form so `alternatingFaceMapComplex_obj_d` applies,
  -- then expand the differential as an alternating face sum.
  have hrel : (ComplexShape.down ℕ).Rel (j + 1) j := by simp [ComplexShape.down_Rel]
  simp_rw [(HomologicalComplex.eqToHom_comp_d _ h hrel).symm,
    alternatingFaceMapComplex_obj_d, AlternatingFaceMapComplex.objD,
    Category.assoc, Preadditive.comp_sum, Preadditive.comp_zsmul]
  -- Expand each diagonal face into its vertical and horizontal parts.
  simp only [SimplicialObject.δ, diag_obj_map]
  -- Commute the shuffle maps past the diagonal faces by naturality.
  simp_rw [← (X.map (SimplexCategory.δ _).op).naturality]
  simp_rw [← Category.assoc
    ((X.map (shuffleFstHom _).op).app (Opposite.op ⦋p + q⦌))]
  -- Split the resulting cast into its vertical and horizontal pieces.
  generalize_proofs _ _ heq
  have hpq : Opposite.op ⦋p + q⦌ = Opposite.op (⦋j + 1⦌ : SimplexCategory) := by
    exact congrArg Opposite.op (congrArg SimplexCategory.mk
      (show p + q = j + 1 by rw [ComplexShape.down_Rel] at h; omega))
  have heq_vert : (X.obj (Opposite.op ⦋p + q⦌)).obj (Opposite.op ⦋p + q⦌) =
      (X.obj (Opposite.op ⦋j + 1⦌)).obj (Opposite.op ⦋p + q⦌) :=
    congrFun (congrArg Prefunctor.obj (congrArg Functor.toPrefunctor (congrArg X.obj hpq)))
      (Opposite.op ⦋p + q⦌)
  have heq_horiz : (X.obj (Opposite.op ⦋j + 1⦌)).obj (Opposite.op ⦋p + q⦌) =
      (X.obj (Opposite.op ⦋j + 1⦌)).obj (Opposite.op ⦋j + 1⦌) :=
    congrArg (X.obj (Opposite.op ⦋j + 1⦌)).obj hpq
  simp_rw [show eqToHom heq = eqToHom heq_vert ≫ eqToHom heq_horiz from by
    rw [show heq = heq_vert.trans heq_horiz from proof_irrel _ _, eqToHom_trans],
    Category.assoc]
  -- Rewrite the horizontal cast as a functorial map.
  simp_rw [show eqToHom heq_horiz = (X.obj (Opposite.op ⦋j + 1⦌)).map (eqToHom hpq) from
    (eqToHom_map (X.obj (Opposite.op ⦋j + 1⦌)) hpq).symm]
  simp_rw [← Category.assoc ((X.obj (Opposite.op ⦋j + 1⦌)).map (eqToHom hpq)),
    ← Functor.map_comp]
  -- Rewrite the vertical cast as a naturality square.
  simp_rw [show eqToHom heq_vert = (X.map (eqToHom hpq)).app (Opposite.op ⦋p + q⦌) from by
    rw [eqToHom_map, eqToHom_app]]
  simp_rw [← Category.assoc ((X.map (shuffleFstHom _).op).app (Opposite.op ⦋p + q⦌))]
  simp_rw [← NatTrans.comp_app, ← Functor.map_comp]
  simp_rw [← Category.assoc ((X.map ((shuffleFstHom _).op ≫ eqToHom hpq)).app _),
    ← (X.map ((shuffleFstHom _).op ≫ eqToHom hpq)).naturality, Category.assoc]
  -- Merge adjacent horizontal and vertical maps.
  simp_rw [← Category.assoc ((X.obj (Opposite.op ⦋p⦌)).map (shuffleSndHom _).op),
    ← Functor.map_comp,
    ← NatTrans.comp_app, ← Functor.map_comp]
  -- Put the coefficients into a single scalar on each summand.
  simp_rw [Finset.smul_sum, smul_smul]
  -- Split the face sum into diagonal and non-diagonal vertices.
  have hj : p + q = j + 1 := by rw [ComplexShape.down_Rel] at h; omega
  let castIdx : Fin (j + 2) → Index (p + q) := fun r => r.cast (by omega)
  let isDiag := fun (μ : Shuffle p q) (r : Fin (j + 2)) =>
    Shuffle.isDiagonalVertex μ (castIdx r)
  haveI isDiag_dec : ∀ μ, DecidablePred (isDiag μ) :=
    fun μ r => Shuffle.isDiagonalVertex_decidable μ _
  conv_lhs =>
    enter [2, x]
    rw [show ∑ r, _ = _ from
      (Finset.sum_filter_add_sum_filter_not Finset.univ (isDiag x) _).symm]
  -- Distribute the outer sum over this decomposition.
  simp_rw [Finset.sum_add_distrib]
  -- Cancel the diagonal part by the standard sign-reversing involution.
  -- Helper to recover `isDiagonalVertex` from membership in the sigma-type filter.
  have diag_of_mem {x : Σ _ : Shuffle p q, Fin (j + 2)}
      (hx : x ∈ (Finset.univ : Finset (Shuffle p q)).sigma
        fun μ => Finset.filter (isDiag μ) Finset.univ) :
      Shuffle.isDiagonalVertex x.1 (castIdx x.2) := by
    simp only [Finset.mem_sigma, Finset.mem_univ, Finset.mem_filter, true_and,
      isDiag] at hx
    exact hx
  convert (zero_add _) using 2
  · rw [Finset.sum_sigma' (σ := fun _ : Shuffle p q => Fin (j + 2))
        Finset.univ (fun μ => Finset.filter (isDiag μ) Finset.univ)]
    refine Finset.sum_involution
      (fun x hx => ⟨Shuffle.swapDiagonalSteps x.1 (castIdx x.2) (diag_of_mem hx), x.2⟩)
      (fun x hx => by
        have hr := diag_of_mem hx
        rw [Shuffle.swapDiagonalSteps_neg_sign x.1 (castIdx x.2) hr, neg_mul, neg_smul,
          add_eq_zero_iff_eq_neg, neg_neg]
        dsimp only
        have hsnd := sndHom_swapDiagonalSteps_comp_δ x.1 x.2 hj.symm hr
        have hfst := fstHom_swapDiagonalSteps_comp_δ x.1 x.2 hj.symm hr
        -- Pass to opposites so the shuffle identities match the maps appearing in the summand.
        have hsnd_op := congrArg Quiver.Hom.op hsnd
        have hfst_op := congrArg Quiver.Hom.op hfst
        simp only [op_comp] at hsnd_op hfst_op
        simp only [eqToHom_op, Category.assoc] at hsnd_op hfst_op
        -- The cast proofs differ syntactically, so `generalize_proofs` is used to align them.
        generalize_proofs _ _ _ _ _ _ _ _ _ _ hsndP _ _ hfstP _ at hsnd_op hfst_op ⊢
        simp only [Category.assoc] at hsnd_op hfst_op ⊢
        rw [hsnd_op.symm, hfst_op.symm])
      (fun x hx _ => by
        have hr := diag_of_mem hx
        exact ne_of_apply_ne Sigma.fst
          (Shuffle.swapDiagonalSteps_ne x.1 (castIdx x.2) hr))
      (fun x hx => by
        have hr := diag_of_mem hx
        simp only [Finset.mem_sigma, Finset.mem_univ, Finset.mem_filter, true_and, isDiag]
        simpa using Shuffle.swapDiagonalSteps_vertex x.1 (castIdx x.2) hr)
      (fun x hx => by
        have hr := diag_of_mem hx
        exact Sigma.ext
          (Shuffle.swapDiagonalSteps_involutive x.1 (castIdx x.2) hr) (by simp))
  · -- Split the non-diagonal part into left-type and right-type vertices.
    let isLeftType := fun (μ : Shuffle p q) (r : Fin (j + 2)) =>
      Shuffle.isLeftStep μ ⟨min r.val (p + q - 1), by omega⟩
    haveI isLeftType_dec : ∀ μ, DecidablePred (isLeftType μ) :=
      fun μ r => Shuffle.isLeftStep_decidable μ _
    conv_rhs =>
      enter [2, x]
      rw [(Finset.sum_filter_add_sum_filter_not
        (Finset.univ.filter (fun r => ¬isDiag x r)) (isLeftType x) _).symm]
    simp_rw [Finset.sum_add_distrib]
    congr 1
    · -- Left-type vertices produce the vertical differential.
      rcases p with _ | p'
      · -- If `p = 0`, there are no left steps.
        symm
        apply Finset.sum_eq_zero
        intro μ _
        apply Finset.sum_eq_zero
        intro r hr
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hr
        -- `Shuffle 0 q` has no left steps because the first coordinate is forced to be `0`.
        exfalso
        have hlt := hr.2
        simp only [isLeftType, Shuffle.isLeftStep] at hlt
        exact absurd hlt (by omega)
      · -- For `p + 1`, reindex by `insertLeftStep`.
        simp only []
        rw [← Fintype.sum_prod_type']
        rw [Finset.sum_sigma']
        apply Finset.sum_nbij
          (fun x => ⟨Shuffle.insertLeftStep x.2 x.1,
            (Shuffle.insertLeftIndex x.2 x.1).cast (by omega)⟩)
        · -- The image lies in the non-diagonal left-type part.
          intro ⟨j, ν⟩ _
          simp only [Finset.mem_sigma, Finset.mem_univ, Finset.mem_filter, true_and]
          exact ⟨Shuffle.insertLeftStep_not_diagonal ν j,
                 Shuffle.insertLeftStep_isLeftType ν j⟩
        · -- Injectivity.
          intro ⟨j₁, ν₁⟩ _ ⟨j₂, ν₂⟩ _ h
          rw [Sigma.mk.inj_iff] at h
          obtain ⟨hμ, hr⟩ := h
          have hr' : Shuffle.insertLeftIndex ν₁ j₁ = Shuffle.insertLeftIndex ν₂ j₂ := by
            have heq := eq_of_heq hr
            exact Fin.ext (by simpa using congrArg (fun x => x.val) heq)
          obtain ⟨hj, hν⟩ := Shuffle.insertLeftStep_injective j₁ j₂ ν₁ ν₂ hμ hr'
          exact Prod.ext hj hν
        · -- Surjectivity.
          intro ⟨μ, r⟩ hmem
          simp only [Finset.mem_coe, Finset.mem_sigma, Finset.mem_univ, Finset.mem_filter,
            true_and] at hmem
          obtain ⟨hnd, hlt⟩ := hmem
          rcases q with _ | q'
          · -- If `q = 0`, there is only the default shuffle.
            have hj' : p' + 1 = j + 1 := by omega
            refine ⟨(⟨r.val, by omega⟩, default), Finset.mem_univ _, ?_⟩
            apply Sigma.ext
            · exact Subsingleton.elim _ _
            · apply heq_of_eq; apply Fin.ext
              simp only [Shuffle.insertLeftIndex, Fin.val_cast]
              have hfst : ∀ (r₁ : Fin (p' + 0 + 1)),
                  ((default : Shuffle p' 0).1 r₁).1.val = r₁.val := by
                intro r₁
                have hcs := Shuffle.coordSum_eq (default : Shuffle p' 0) r₁
                have hsnd := Fin.eq_zero ((default : Shuffle p' 0).1 r₁).2
                simp [hsnd] at hcs; omega
              simp_rw [hfst]
              exact Fin.card_filter_val_lt.trans (by omega)
          · rcases Shuffle.nondiag_mem_insertLeft_or_insertRight μ (r.cast (by omega)) hnd with
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
                (Shuffle.insertRightStep ν k) ⟨min r.val ((p' + 1) + (q' + 1) - 1), by omega⟩ := rfl
              rw [this] at hlt
              convert hlt using 2; congr 1
        · -- Compare the summands after rewriting the inserted shuffle maps.
          intro ⟨jj, ν⟩ _
          dsimp only
          have hsign := Shuffle.sign_insertLeftStep ν jj
          congr 1
          · simp only [Fin.val_cast]; linarith
          ·
            have hfst_op := congrArg Quiver.Hom.op
              (fstHom_insertLeftStep_comp_δ ν jj hj.symm)
            have hsnd_op := congrArg Quiver.Hom.op
              (sndHom_insertLeftStep_comp_δ ν jj hj.symm)
            simp only [op_comp, eqToHom_op, Category.assoc] at hfst_op hsnd_op
            generalize_proofs _ _ _ _ _ _ hsndP _ hfstP _ at hsnd_op hfst_op ⊢
            simp only [Category.assoc] at hfst_op ⊢
            rw [hsnd_op, hfst_op]
            simp only [Functor.map_comp, NatTrans.comp_app, Category.assoc]
            simp only [eqToHom_map, eqToHom_app]
            rw [←reassoc_of% (X.map (SimplexCategory.δ jj).op).naturality (shuffleSndHom ν).op]
            congr 1
            generalize_proofs h1 h2
            have hpq' := congrArg Opposite.op
              (congrArg SimplexCategory.mk (show p' + q = j from by omega))
            rw [NatTrans.congr _ hpq', NatTrans.congr _ hpq']
            simp only [eqToHom_map, eqToHom_trans, eqToHom_trans_assoc, Category.assoc,
              eqToHom_refl, Category.id_comp]
    · -- Right-type vertices produce the horizontal differential.
      rcases q with _ | q'
      · -- If `q = 0`, there are no right-type vertices.
        symm
        apply Finset.sum_eq_zero
        intro μ _
        apply Finset.sum_eq_zero
        intro r hr
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hr
        -- In `Shuffle p 0`, every step is left, so the right-type part is empty.
        exfalso
        have hnotleft := hr.2
        simp only [isLeftType, Shuffle.isLeftStep] at hnotleft
        apply hnotleft
        set idx₀ : Fin (p + 0) := ⟨min r.val (p + 0 - 1), by omega⟩
        have hcs1 := Shuffle.coordSum_eq μ idx₀.castSucc
        have hcs2 := Shuffle.coordSum_eq μ idx₀.succ
        have hs1 := Fin.eq_zero (μ.1 idx₀.castSucc).2
        have hs2 := Fin.eq_zero (μ.1 idx₀.succ).2
        simp only [Fin.ext_iff, Fin.val_zero] at hs1 hs2
        simp only [Fin.val_succ, Fin.val_castSucc] at hcs1 hcs2
        omega
      · -- For `q + 1`, reindex by `insertRightStep`.
        simp only []
        rw [← Fintype.sum_prod_type']
        rw [Finset.sum_sigma']
        apply Finset.sum_nbij
          (fun x => ⟨Shuffle.insertRightStep x.2 x.1,
            (Shuffle.insertRightIndex x.2 x.1).cast (by omega)⟩)
        · -- The image lands in the non-diagonal right-type part.
          intro ⟨k, ν⟩ _
          simp only [Finset.mem_sigma, Finset.mem_univ, Finset.mem_filter, true_and]
          constructor
          · -- For `p = 0`, diagonality is impossible because the first coordinate is constant.
            rcases p with _ | p'
            · intro hdiag
              simp only [isDiag, Shuffle.isDiagonalVertex] at hdiag
              split_ifs at hdiag with h1 h2
              all_goals simp only [Shuffle.isLeftStep] at hdiag; all_goals omega
            · exact Shuffle.insertRightStep_not_diagonal ν k
          · -- This is exactly the right-type condition.
            exact Shuffle.insertRightStep_not_isLeftType ν k
        · -- Injectivity.
          intro ⟨k₁, ν₁⟩ _ ⟨k₂, ν₂⟩ _ h
          rw [Sigma.mk.inj_iff] at h
          obtain ⟨hμ, hr⟩ := h
          have hr' : Shuffle.insertRightIndex ν₁ k₁ = Shuffle.insertRightIndex ν₂ k₂ := by
            have heq := eq_of_heq hr
            exact Fin.ext (by simpa using congrArg (fun x => x.val) heq)
          obtain ⟨hk, hν⟩ := Shuffle.insertRightStep_injective k₁ k₂ ν₁ ν₂ hμ hr'
          exact Prod.ext hk hν
        · -- Surjectivity.
          intro ⟨μ, r⟩ hmem
          simp only [Finset.mem_coe, Finset.mem_sigma, Finset.mem_univ, Finset.mem_filter,
            true_and] at hmem
          obtain ⟨hnd, hnotleft⟩ := hmem
          rcases p with _ | p'
          · -- If `p = 0`, there is only the default shuffle.
            have hj' : q' + 1 = j + 1 := by omega
            refine ⟨(⟨r.val, by omega⟩, default), Finset.mem_univ _, ?_⟩
            apply Sigma.ext
            · exact Subsingleton.elim _ _
            · apply heq_of_eq; apply Fin.ext
              simp only [Shuffle.insertRightIndex, Fin.val_cast]
              have hsnd : ∀ (r₁ : Fin (0 + q' + 1)),
                  ((default : Shuffle 0 q').1 r₁).2.val = r₁.val := by
                intro r₁
                have hcs := Shuffle.coordSum_eq (default : Shuffle 0 q') r₁
                have hfst := Fin.eq_zero ((default : Shuffle 0 q').1 r₁).1
                simp only [Fin.ext_iff, Fin.val_zero] at hfst
                omega
              simp_rw [hsnd]
              exact Fin.card_filter_val_lt.trans (by omega)
          · rcases Shuffle.nondiag_mem_insertLeft_or_insertRight μ (r.cast (by omega)) hnd with
              ⟨j, ν, hμ_eq, hr_eq⟩ | ⟨k, ν, hμ_eq, hr_eq⟩
            · exfalso
              apply hnotleft
              have hleft := Shuffle.insertLeftStep_isLeftType ν j
              subst hμ_eq
              change isLeftType (Shuffle.insertLeftStep ν j) r
              simp only [isLeftType]
              convert hleft using 2
              congr 1; simp only [Fin.val_cast] at hr_eq; omega
            · refine ⟨(k, ν), Finset.mem_univ _, ?_⟩
              apply Sigma.ext hμ_eq.symm
              apply heq_of_eq; apply Fin.ext
              simpa [Fin.val_cast] using hr_eq
        · -- Compare the summands after rewriting the inserted shuffle maps.
          intro ⟨kk, ν⟩ _
          dsimp only
          have hsign := Shuffle.sign_insertRightStep ν kk
          congr 1
          · simp only [Fin.val_cast]; linarith
          ·
            have hfst_op := congrArg Quiver.Hom.op
              (fstHom_insertRightStep_comp_δ ν kk hj.symm)
            have hsnd_op := congrArg Quiver.Hom.op
              (sndHom_insertRightStep_comp_δ ν kk hj.symm)
            simp only [op_comp, eqToHom_op, Category.assoc] at hfst_op hsnd_op
            generalize_proofs _ _ _ _ _ _ hsndP _ hfstP _ at hsnd_op hfst_op ⊢
            simp only [Category.assoc] at hfst_op hsnd_op ⊢
            rw [hsnd_op, hfst_op]
            simp only [Functor.map_comp, NatTrans.comp_app, Category.assoc]
            simp only [eqToHom_map, eqToHom_app]
            -- The only difference is the placement of the final arithmetic cast.
            congr 1; congr 1
            generalize_proofs h1 h2
            have hpq' := congrArg Opposite.op
              (congrArg SimplexCategory.mk (show p + q' = j from by omega))
            rw [NatTrans.congr _ hpq']
            simp only [eqToHom_map, eqToHom_trans, Category.assoc]


/-- The shuffle chain map `F₁(X) ⟶ F₂(X)`. -/
noncomputable def shuffleMap (X : BisimplicialObject C) :
    F₁.obj X ⟶ F₂.obj X where
  f n := HomologicalComplex₂.totalDesc (doubleComplex X) (fun p q h => by
    simp only [ComplexShape.π_def] at h
    exact ezComponent X p q ≫ eqToHom (by subst h; rfl))
  comm' := by
    intro i j h
    -- Reduce to equality after precomposing with each coproduct inclusion.
    apply HomologicalComplex₂.total.hom_ext
    intro p q hp
    -- Replace `i` by `p + q`.
    simp only [ComplexShape.π_def] at hp; subst hp
    -- Identify the left side with `ezComponent`, and the right side with the two total-complex
    -- differential pieces `d₁` and `d₂`.
    simp only [Functor.mapHomologicalComplex_obj_X, alternatingFaceMapComplex_obj_X,
      Functor.comp_obj, diag_obj_obj, HomologicalComplex₂.totalFunctor_obj, ComplexShape.π_def,
      HomologicalComplex₂.ι_totalDesc_assoc, Category.assoc,
      eqToHom_refl, Category.id_comp]
    rw [HomologicalComplex₂.total_d]
    simp only [Preadditive.comp_add, Preadditive.add_comp,
      HomologicalComplex₂.ι_D₁_assoc, HomologicalComplex₂.ι_D₂_assoc,
      Functor.mapHomologicalComplex_obj_X, alternatingFaceMapComplex_obj_X]
    rw [ezComponent_boundary X p q j h]
    -- The boundary formula now matches the `d₁` and `d₂` contributions separately.
    apply congrArg₂ HAdd.hAdd
    ---- Vertical part ----
    · rcases p with _ | p
      · -- If `p = 0`, the vertical differential vanishes.
        simp only
        rw [HomologicalComplex₂.d₁_eq_zero]
        · simp
        · intro hrel; simp [ComplexShape.down_Rel] at hrel
      · -- Otherwise expand `d₁` and simplify the sign `ε₁ = 1`.
        simp only [alternatingFaceMapComplex_obj_X, diag_obj_obj, Int.reduceNeg]
        rw [HomologicalComplex₂.d₁_eq (doubleComplex X) (ComplexShape.down ℕ)
          (show (ComplexShape.down ℕ).Rel (p + 1) p from by simp [ComplexShape.down_Rel])
          q j (by simp [ComplexShape.π_def]; rw [ComplexShape.down_Rel] at h; omega)]
        simp only [show ComplexShape.ε₁ (ComplexShape.down ℕ) (ComplexShape.down ℕ)
          (ComplexShape.down ℕ) (p + 1, q) = 1 from rfl, one_smul, Category.assoc,
          Functor.mapHomologicalComplex_obj_X, alternatingFaceMapComplex_obj_X]
        simp only [HomologicalComplex₂.ι_totalDesc]
        simp only [← Preadditive.sum_comp, ← Preadditive.zsmul_comp]
        congr 1
        simp only [doubleComplex, Functor.mapHomologicalComplex_obj_d,
          alternatingFaceMapComplex_obj_d]
        simp only [AlternatingFaceMapComplex.objD, SimplicialObject.δ,
          alternatingFaceMapComplex_map_f]
        conv_rhs => rw [NatTrans.app_sum,
          Finset.sum_congr rfl (fun x _ => NatTrans.app_zsmul _ _ _)]
    ---- Horizontal part ----
    · rcases q with _ | q
      · -- If `q = 0`, the horizontal differential vanishes.
        simp only
        rw [HomologicalComplex₂.d₂_eq_zero]
        · simp
        · intro hrel; simp [ComplexShape.down_Rel] at hrel
      · -- Otherwise expand `d₂` and simplify the sign `ε₂ = (-1)^p`.
        simp only [alternatingFaceMapComplex_obj_X, diag_obj_obj, Int.reduceNeg]
        rw [HomologicalComplex₂.d₂_eq (doubleComplex X) (ComplexShape.down ℕ)
          p (show (ComplexShape.down ℕ).Rel (q + 1) q from by simp [ComplexShape.down_Rel])
          j (by simp [ComplexShape.π_def]; rw [ComplexShape.down_Rel] at h; omega)]
        simp only [show ComplexShape.ε₂ (ComplexShape.down ℕ) (ComplexShape.down ℕ)
          (ComplexShape.down ℕ) (p, q + 1) = (-1 : ℤˣ) ^ p from rfl,
          Functor.mapHomologicalComplex_obj_X, alternatingFaceMapComplex_obj_X]
        simp only [Units.smul_def, Preadditive.zsmul_comp, Category.assoc]
        simp only [← Preadditive.sum_comp, ← Preadditive.zsmul_comp]
        congr 1
        · congr 1
          simp only [
            alternatingFaceMapComplex_obj_d, AlternatingFaceMapComplex.objD, SimplicialObject.δ]
        · simp only [HomologicalComplex₂.ι_totalDesc]

/-- In degree `0`, the composite `alexanderWhitney ≫ shuffleMap` is the identity. -/
lemma awShuffle_f_zero (X : BisimplicialObject C) :
    (alexanderWhitney X ≫ shuffleMap X).f 0 =
      (𝟙 (F₂.obj X) : (F₂.obj X) ⟶ (F₂.obj X)).f 0 := by
  rw [HomologicalComplex.comp_f]
  simp [alexanderWhitney, shuffleMap]
  simp only [awComponent, ezComponent, ι_front, ι_back, shuffleFstHom, shuffleSndHom]
  have hid : ∀ (f : (⦋0⦌ : SimplexCategory) ⟶ ⦋0⦌), f = 𝟙 _ :=
    fun f => Subsingleton.elim _ _
  simp [hid, Shuffle.sign, Shuffle.invCount]

end BisimplicialObject

end CategoryTheory
