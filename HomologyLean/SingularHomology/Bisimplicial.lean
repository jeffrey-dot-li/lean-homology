import Mathlib.AlgebraicTopology.AlternatingFaceMapComplex
import Mathlib.Algebra.Homology.Homotopy
import Mathlib.Algebra.Homology.TotalComplex
import Mathlib.CategoryTheory.Preadditive.FunctorCategory
import HomologyLean.SingularHomology.Shuffle

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

/-- The double chain complex obtained from a bisimplicial object by applying
`alternatingFaceMapComplex` in both simplicial directions.
Entry `(K X).X p).X q = X_{p,q}`. -/
abbrev doubleComplex (X : BisimplicialObject C) :
    HomologicalComplex (ChainComplex C ℕ) (ComplexShape.down ℕ) :=
  ((alternatingFaceMapComplex C).mapHomologicalComplex _).obj
    ((alternatingFaceMapComplex (SimplicialObject C)).obj X)

/-! ### SimplexCategory morphisms for AW and EZ

The AW and EZ maps are built from two standard families of `SimplexCategory` morphisms:

- **Front face** `ι_front p q : [p] ⟶ [p+q]` — the order-preserving injection `i ↦ i`
- **Back face** `ι_back p q : [q] ⟶ [p+q]` — the order-preserving injection `j ↦ p + j`

For AW, we *pull back* along these (using contravariance of simplicial objects):
`X.map (ι_front p q).op` acts vertically `X_{p+q, -} → X_{p, -}`, and
`(X.obj _).map (ι_back p q).op` acts horizontally `X_{-, p+q} → X_{-, q}`.
-/

/-- Front face inclusion `[p] ⟶ [p+q]`: the unique monotone map sending `i ↦ i`. -/
def ι_front (p q : ℕ) : (⦋p⦌ : SimplexCategory) ⟶ ⦋p + q⦌ :=
  SimplexCategory.mkHom ⟨fun i => ⟨i.1, by omega⟩, fun _ _ h => h⟩

/-- Back face inclusion `[q] ⟶ [p+q]`: the unique monotone map sending `j ↦ p + j`. -/
def ι_back (p q : ℕ) : (⦋q⦌ : SimplexCategory) ⟶ ⦋p + q⦌ :=
  SimplexCategory.mkHom ⟨fun j => ⟨p + j.1, by omega⟩, fun _ _ h => Nat.add_le_add_left h _⟩

/-! ### Alexander-Whitney map

The AW map `F₂(X) ⟶ F₁(X)` sends the diagonal chain complex to the total complex.

At degree `n`, the component into the `(p,q)`-summand (where `p + q = n`) is:
```
  AW_{p,q} : X_{n,n} → X_{p,q}
  AW_{p,q} = (X.map (ι_front p q).op).app _ ≫ (X.obj _).map (ι_back p q).op
```
i.e., apply the front face vertically (`X_{n,n} → X_{p,n}`) then the back face
horizontally (`X_{p,n} → X_{p,q}`).

The full map at degree `n` is the copairing into the coproduct:
`AW_n = ∑_{p+q=n} ι_{p,q} ∘ AW_{p,q} : X_{n,n} → ⨁_{p+q=n} X_{p,q}`
-/

/-- Component `X_{n,n} ⟶ X_{p,q}` of the Alexander-Whitney map,
using front-face vertically and back-face horizontally. -/
noncomputable def awComponent (X : BisimplicialObject C) (p q : ℕ) :
    (X.obj (Opposite.op ⦋p + q⦌)).obj (Opposite.op ⦋p + q⦌) ⟶
    (X.obj (Opposite.op ⦋p⦌)).obj (Opposite.op ⦋q⦌) :=
  (X.map (ι_front p q).op).app (Opposite.op ⦋p + q⦌) ≫
    (X.obj (Opposite.op ⦋p⦌)).map (ι_back p q).op

/-- The Alexander-Whitney chain map `F₂(X) ⟶ F₁(X)`.

At degree `n`, maps `X_{n,n}` into `⨁_{p+q=n} X_{p,q}` by copairing the
`awComponent` maps with the coproduct inclusions `ιTotal`. -/
noncomputable def alexanderWhitney (X : BisimplicialObject C) :
    F₂.obj X ⟶ F₁.obj X where
  f := sorry
  comm' := sorry

/-! ### Eilenberg-Zilber / shuffle map

The EZ map `F₁(X) ⟶ F₂(X)` sends the total complex to the diagonal chain complex.

On the `(p,q)`-summand of the total complex at degree `n = p + q`, it maps
`X_{p,q} → X_{n,n}` via a signed sum over `(p,q)`-shuffles:
```
  EZ_{p,q} = ∑_{μ : Shuffle p q} sign(μ) ·
    ((X.obj (op ⦋p⦌)).map (μ.sndHom).op ≫ (X.map (μ.fstHom).op).app (op ⦋p+q⦌))
```
i.e., apply `sndHom` horizontally (`X_{p,q} → X_{p,p+q}`) then `fstHom` vertically
(`X_{p,p+q} → X_{p+q,p+q}`).

The full map at degree `n` is defined by giving a map out of each summand of the
coproduct `⨁_{p+q=n} X_{p,q}`, using `totalDesc`.
-/

/-- First projection of a shuffle as a `SimplexCategory` morphism `⦋p+q⦌ ⟶ ⦋p⦌`. -/
def shuffleFstHom {p q : ℕ} (μ : Shuffle p q) : (⦋p + q⦌ : SimplexCategory) ⟶ ⦋p⦌ :=
  SimplexCategory.Hom.mk (OrderHom.fst.comp μ.1)

/-- Second projection of a shuffle as a `SimplexCategory` morphism `⦋p+q⦌ ⟶ ⦋q⦌`. -/
def shuffleSndHom {p q : ℕ} (μ : Shuffle p q) : (⦋p + q⦌ : SimplexCategory) ⟶ ⦋q⦌ :=
  SimplexCategory.Hom.mk (OrderHom.snd.comp μ.1)

/-- Component `X_{p,q} ⟶ X_{p+q,p+q}` of the Eilenberg-Zilber map: the signed sum
over all `(p,q)`-shuffles, applying degeneracy maps in both simplicial directions. -/
noncomputable def ezComponent (X : BisimplicialObject C) (p q : ℕ) :
    (X.obj (Opposite.op ⦋p⦌)).obj (Opposite.op ⦋q⦌) ⟶
    (X.obj (Opposite.op ⦋p + q⦌)).obj (Opposite.op ⦋p + q⦌) :=
  ∑ μ : Shuffle p q, μ.sign •
    ((X.obj (Opposite.op ⦋p⦌)).map (shuffleSndHom μ).op ≫
      (X.map (shuffleFstHom μ).op).app (Opposite.op ⦋p + q⦌))

/-! ### Leibniz rule for the shuffle map

The chain map condition for the shuffle map reduces to showing that
`ezComponent p q ≫ d_diag(p+q)` splits into a "vertical" sum (matching `d₁`)
and a "horizontal" sum (matching `d₂`).

The diagonal face map `(diag.obj X).δ k` applies `δ k` in both simplicial
directions simultaneously:
  `(diag.obj X).δ k = (X.map (δ k).op).app _ ≫ (X.obj _).map (δ k).op`

The Leibniz rule says that composing the shuffle sum with the alternating
face map differential on the diagonal decomposes as:
  `ezComponent(p,q) ≫ objD(diag X, p+q) = verticalPart + horizontalPart`
where the vertical part involves face maps in the first simplicial direction
composed with `ezComponent(p-1, q)`, and the horizontal part involves face
maps in the second direction composed with `ezComponent(p, q-1)`.

#### Proof strategy

Unlike the SSet Eilenberg-Zilber proof (`crossProduct_boundary_naturality` in
`EilenbergZilber.lean`), there is no naturality reduction available here.
The SSet proof factors through universal simplices `Δ[p] ⊗ Δ[q]` and uses
naturality of the cross product to reduce to `universalSimplexCrossProduct_boundary`.
In the bisimplicial setting, `ezComponent` is already defined abstractly for any
bisimplicial object in a preadditive category, so the proof must be directly
combinatorial.

The proof follows the pattern of `universalSimplexCrossProduct_boundary`:

1. **Expand `ezComponent`**: Unfold as `∑ μ, μ.sign • (sndHom ≫ fstHom)` and
   distribute through `d` via `Preadditive.sum_comp`, `Preadditive.zsmul_comp`.

2. **Expand the diagonal differential**: The differential is an alternating sum
   of `(diag.obj X).δ k`, each of which decomposes as `δ_vert k ≫ δ_horiz k`.
   Distribute via `Preadditive.comp_sum`, `Preadditive.comp_zsmul`.

3. **Apply simplicial identities**: Rewrite compositions `shuffleFstHom(μ) ≫ δ k`
   and `shuffleSndHom(μ) ≫ δ k` using the simplicial identity `δ ≫ σ` relations.
   This is the core combinatorial step.

4. **Swap sums and reindex**: Interchange `∑ μ ∑ k` to `∑ k ∑ μ` and recognize
   that the inner sum over shuffles reconstitutes `ezComponent` at lower degree,
   yielding the vertical + horizontal decomposition.
-/

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
private lemma fstHom_swapDiagonalSteps_comp_δ {p q n : ℕ}
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

private lemma sndHom_swapDiagonalSteps_comp_δ {p q n : ℕ}
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
/-- **Leibniz rule for the shuffle map.**

The shuffle map component `ezComponent(p, q)`, composed with the alternating
face map differential on the diagonal, decomposes into:
- a "vertical" sum: face maps in the first simplicial direction composed with
  `ezComponent(p-1, q)` (zero when `p = 0`)
- a "horizontal" sum: face maps in the second simplicial direction composed with
  `ezComponent(p, q-1)` (zero when `q = 0`), carrying the sign `(-1)^p`

This is the core combinatorial identity underlying the chain map condition
for the Eilenberg-Zilber map.

The differential `((alternatingFaceMapComplex C).obj (diag.obj X)).d (p+q) j` is
used instead of `objD` to avoid definitional index mismatches. -/
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
  -- Step 1: Expand ezComponent as ∑ μ, sign • (sndHom ≫ fstHom) and distribute through d.
  simp only [ezComponent, Preadditive.sum_comp, Preadditive.zsmul_comp]
  -- Step 2: Shift .d (p+q) j ↦ eqToHom _ ≫ .d (j+1) j so alternatingFaceMapComplex_obj_d
  -- fires, then expand the differential as ∑ (-1)^k • δ k and distribute.
  have hrel : (ComplexShape.down ℕ).Rel (j + 1) j := by simp [ComplexShape.down_Rel]
  simp_rw [(HomologicalComplex.eqToHom_comp_d _ h hrel).symm,
    alternatingFaceMapComplex_obj_d, AlternatingFaceMapComplex.objD,
    Category.assoc, Preadditive.comp_sum, Preadditive.comp_zsmul]
  -- Step 3: Expand (diag.obj X).δ k into vertical ≫ horizontal face maps.
  simp only [SimplicialObject.δ, diag_obj_map]
  -- Step 4: Use naturality of X.map (shuffleFstHom x).op to commute fstHom past δ_vert.
  simp_rw [← (X.map (SimplexCategory.δ _).op).naturality]
  -- Absorb eqToHom and commute fstHom past horizontal δ via naturality of X.map(fstHom).
  simp_rw [← Category.assoc
    ((X.map (shuffleFstHom _).op).app (Opposite.op ⦋p + q⦌))]
  -- Name the diagonal eqToHom proof, then factor it into vertical ≫ horizontal.
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
  -- Fold horizontal: eqToHom heq_horiz = X_⦋j+1⦌.map(eqToHom hpq).
  simp_rw [show eqToHom heq_horiz = (X.obj (Opposite.op ⦋j + 1⦌)).map (eqToHom hpq) from
    (eqToHom_map (X.obj (Opposite.op ⦋j + 1⦌)) hpq).symm]
  -- Fold X_⦋j+1⦌.map(eqToHom hpq) ≫ X_⦋j+1⦌.map(δ k).op into X_⦋j+1⦌.map(eqToHom hpq ≫ (δ k).op).
  simp_rw [← Category.assoc ((X.obj (Opposite.op ⦋j + 1⦌)).map (eqToHom hpq)),
    ← Functor.map_comp]
  -- Fold vertical: eqToHom heq_vert = (X.map (eqToHom hpq)).app _.
  simp_rw [show eqToHom heq_vert = (X.map (eqToHom hpq)).app (Opposite.op ⦋p + q⦌) from by
    rw [eqToHom_map, eqToHom_app]]
  -- Fold fstHom.app ≫ (X.map (eqToHom hpq)).app into (fstHom ≫ X.map(eqToHom hpq)).app.
  simp_rw [← Category.assoc ((X.map (shuffleFstHom _).op).app (Opposite.op ⦋p + q⦌))]
  simp_rw [← NatTrans.comp_app, ← Functor.map_comp]
  simp_rw [← Category.assoc ((X.map ((shuffleFstHom _).op ≫ eqToHom hpq)).app _),
    ← (X.map ((shuffleFstHom _).op ≫ eqToHom hpq)).naturality, Category.assoc]
  -- Fold adjacent horizontal maps and adjacent vertical maps.
  simp_rw [← Category.assoc ((X.obj (Opposite.op ⦋p⦌)).map (shuffleSndHom _).op),
    ← Functor.map_comp,
    ← NatTrans.comp_app, ← Functor.map_comp]
  -- Step 5: Collapse double sum ∑ μ, sign(μ) • ∑ k, (-1)^k • f into ∑ μ, ∑ k, (sign * (-1)^k) • f.
  simp_rw [Finset.smul_sum, smul_smul]
  -- Step 6: Split inner sum into diagonal + non-diagonal vertices.
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
  -- Step 7: Distribute ∑ μ over the diagonal + non-diagonal split.
  simp_rw [Finset.sum_add_distrib]
  -- Step 8: Cancel the diagonal sum via sign-reversing involution.
  -- Helper to extract isDiagonalVertex from sigma finset membership.
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
        -- Lift equalities to op: (δ ≫ eqToHom ≫ f(swap)).op = (δ ≫ eqToHom ≫ f(μ)).op
        -- then expand with op_comp to get
        -- f(swap).op ≫ eqToHom.op ≫ δ.op = f(μ).op ≫ eqToHom.op ≫ δ.op
        have hsnd_op := congrArg Quiver.Hom.op hsnd
        have hfst_op := congrArg Quiver.Hom.op hfst
        simp only [op_comp] at hsnd_op hfst_op
        simp only [eqToHom_op, Category.assoc] at hsnd_op hfst_op
        -- The eqToHom proof terms differ syntactically but are equal by proof_irrel.
        -- Use generalize_proofs to unify them, then rewrite.
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
  · -- Step 9: Split non-diagonal vertices into left-type + right-type.
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
    · -- Step 10: Left faces — match with vertical differential
      rcases p with _ | p'
      · -- p = 0: LHS is 0, RHS sum is empty (no left steps in Shuffle 0 q).
        symm
        apply Finset.sum_eq_zero
        intro μ _
        apply Finset.sum_eq_zero
        intro r hr
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hr
        -- isLeftType requires isLeftStep, but Shuffle 0 q has no left steps:
        -- the first component of μ is always in Fin 1, so it can't strictly increase.
        exfalso
        have hlt := hr.2
        simp only [isLeftType, Shuffle.isLeftStep] at hlt
        exact absurd hlt (by omega)
      · -- p = p' + 1: bijection via insertLeftStep
        simp only []
        rw [← Fintype.sum_prod_type']
        rw [Finset.sum_sigma']
        -- set_option maxHeartbeats 400000 in
        apply Finset.sum_nbij
          (fun x => ⟨Shuffle.insertLeftStep x.2 x.1,
            (Shuffle.insertLeftIndex x.2 x.1).cast (by omega)⟩)
        · -- hi : image lands in the non-diagonal left-type filter
          intro ⟨j, ν⟩ _
          simp only [Finset.mem_sigma, Finset.mem_univ, Finset.mem_filter, true_and]
          exact ⟨Shuffle.insertLeftStep_not_diagonal ν j,
                 Shuffle.insertLeftStep_isLeftType ν j⟩
        · -- hinj : the map is injective
          intro ⟨j₁, ν₁⟩ _ ⟨j₂, ν₂⟩ _ h
          rw [Sigma.mk.inj_iff] at h
          obtain ⟨hμ, hr⟩ := h
          have hr' : Shuffle.insertLeftIndex ν₁ j₁ = Shuffle.insertLeftIndex ν₂ j₂ := by
            have heq := eq_of_heq hr
            exact Fin.ext (by simpa using congrArg (fun x => x.val) heq)
          obtain ⟨hj, hν⟩ := Shuffle.insertLeftStep_injective j₁ j₂ ν₁ ν₂ hμ hr'
          exact Prod.ext hj hν
        · -- hsurj : the map is surjective
          intro ⟨μ, r⟩ hmem
          simp only [Finset.mem_coe, Finset.mem_sigma, Finset.mem_univ, Finset.mem_filter,
            true_and] at hmem
          obtain ⟨hnd, hlt⟩ := hmem
          rcases q with _ | q'
          · -- q = 0: construct the preimage directly. The unique Shuffle p' 0
            -- maps to the unique Shuffle (p'+1) 0 under insertLeftStep at any face.
            have hj' : p' + 1 = j + 1 := by omega
            refine ⟨(⟨r.val, by omega⟩, default), Finset.mem_univ _, ?_⟩
            apply Sigma.ext
            · exact Subsingleton.elim _ _
            · apply heq_of_eq; apply Fin.ext
              simp only [Shuffle.insertLeftIndex, Fin.val_cast]
              -- For Shuffle p' 0, snd ∈ Fin 1 so snd = 0, and coordSum gives fst = index.
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
        · -- Summand equality
          intro ⟨jj, ν⟩ _
          dsimp only
          have hsign := Shuffle.sign_insertLeftStep ν jj
          congr 1
          · simp only [Fin.val_cast]; linarith
          · -- Rewrite RHS composed morphisms using the insertLeftStep face factorizations.
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
    · -- Step 11: Right faces — match with horizontal differential
      rcases q with _ | q'
      · -- q = 0: LHS is 0, RHS sum is empty (no right-type vertices in Shuffle p 0).
        symm
        apply Finset.sum_eq_zero
        intro μ _
        apply Finset.sum_eq_zero
        intro r hr
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hr
        -- For Shuffle p 0, every step is a left step (snd ∈ Fin 1 so snd = 0,
        -- coordSum gives fst = index, hence fst strictly increases).
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
      · -- q = q' + 1: bijection via insertRightStep
        simp only []
        rw [← Fintype.sum_prod_type']
        rw [Finset.sum_sigma']
        apply Finset.sum_nbij
          (fun x => ⟨Shuffle.insertRightStep x.2 x.1,
            (Shuffle.insertRightIndex x.2 x.1).cast (by omega)⟩)
        · -- hi : image lands in the non-diagonal non-left-type filter
          intro ⟨k, ν⟩ _
          simp only [Finset.mem_sigma, Finset.mem_univ, Finset.mem_filter, true_and]
          constructor
          · -- non-diagonal: for p = 0, fst is constant 0 so isLeftStep is always false
            -- and isDiagonalVertex requires isLeftStep to change, hence also false.
            rcases p with _ | p'
            · intro hdiag
              simp only [isDiag, Shuffle.isDiagonalVertex] at hdiag
              split_ifs at hdiag with h1 h2
              all_goals simp only [Shuffle.isLeftStep] at hdiag; all_goals omega
            · exact Shuffle.insertRightStep_not_diagonal ν k
          · -- non-left-type (i.e. right-type)
            exact Shuffle.insertRightStep_not_isLeftType ν k
        · -- hinj : the map is injective
          intro ⟨k₁, ν₁⟩ _ ⟨k₂, ν₂⟩ _ h
          rw [Sigma.mk.inj_iff] at h
          obtain ⟨hμ, hr⟩ := h
          have hr' : Shuffle.insertRightIndex ν₁ k₁ = Shuffle.insertRightIndex ν₂ k₂ := by
            have heq := eq_of_heq hr
            exact Fin.ext (by simpa using congrArg (fun x => x.val) heq)
          obtain ⟨hk, hν⟩ := Shuffle.insertRightStep_injective k₁ k₂ ν₁ ν₂ hμ hr'
          exact Prod.ext hk hν
        · -- hsurj : the map is surjective
          intro ⟨μ, r⟩ hmem
          simp only [Finset.mem_coe, Finset.mem_sigma, Finset.mem_univ, Finset.mem_filter,
            true_and] at hmem
          obtain ⟨hnd, hnotleft⟩ := hmem
          rcases p with _ | p'
          · -- p = 0: the unique Shuffle 0 q' maps to the unique Shuffle 0 (q'+1).
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
        · -- Summand equality
          intro ⟨kk, ν⟩ _
          dsimp only
          have hsign := Shuffle.sign_insertRightStep ν kk
          congr 1
          · simp only [Fin.val_cast]; linarith
          · -- Rewrite RHS composed morphisms using the insertRightStep face factorizations.
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
            -- Both sides share the prefix X_⦋p⦌.map(δ kk).op ≫ X_⦋p⦌.map(sndHom ν).op;
            -- the tails differ only by eqToHom placement around (X.map(fstHom ν).op).app.
            congr 1; congr 1
            generalize_proofs h1 h2
            have hpq' := congrArg Opposite.op
              (congrArg SimplexCategory.mk (show p + q' = j from by omega))
            rw [NatTrans.congr _ hpq']
            simp only [eqToHom_map, eqToHom_trans, Category.assoc]


/-- The Eilenberg-Zilber (shuffle) chain map `F₁(X) ⟶ F₂(X)`.

At degree `n`, maps `⨁_{p+q=n} X_{p,q}` into `X_{n,n}` by giving the `ezComponent`
on each summand, assembled via `totalDesc`. -/
noncomputable def shuffleMap (X : BisimplicialObject C) :
    F₁.obj X ⟶ F₂.obj X where
  f n := HomologicalComplex₂.totalDesc (doubleComplex X) (fun p q h => by
    simp only [ComplexShape.π_def] at h
    exact ezComponent X p q ≫ eqToHom (by subst h; rfl))
  comm' := by
    intro i j h
    -- Reduce to per-summand equality: two maps out of ⨁_{p+q=i} X_{p,q} agree
    -- iff they agree after precomposing with each coproduct inclusion ιTotal.
    apply HomologicalComplex₂.total.hom_ext
    intro p q hp
    -- Eliminate i in favor of p + q.
    simp only [ComplexShape.π_def] at hp; subst hp
    -- Simplify ιTotal ≫ totalDesc to ezComponent on the LHS;
    -- decompose total.d into D₁ + D₂ and simplify ιTotal ≫ D₁/D₂ to d₁/d₂ on the RHS.
    simp only [Functor.mapHomologicalComplex_obj_X, alternatingFaceMapComplex_obj_X,
      Functor.comp_obj, diag_obj_obj, HomologicalComplex₂.totalFunctor_obj, ComplexShape.π_def,
      HomologicalComplex₂.ι_totalDesc_assoc, Category.assoc,
      eqToHom_refl, Category.id_comp]
    rw [HomologicalComplex₂.total_d]
    simp only [Preadditive.comp_add, Preadditive.add_comp,
      HomologicalComplex₂.ι_D₁_assoc, HomologicalComplex₂.ι_D₂_assoc,
      Functor.mapHomologicalComplex_obj_X, alternatingFaceMapComplex_obj_X]
    rw [ezComponent_boundary X p q j h]
    -- Split into vertical = d₁ and horizontal = d₂.
    apply congrArg₂ HAdd.hAdd
    ---- Vertical part: match p with ... = d₁ ≫ totalDesc ----
    · rcases p with _ | p
      · -- p = 0: vertical part is 0, d₁ vanishes (no predecessor of 0).
        simp only
        rw [HomologicalComplex₂.d₁_eq_zero]
        · simp
        · intro hrel; simp [ComplexShape.down_Rel] at hrel
      · -- p = p + 1: expand d₁ via d₁_eq, simplify ε₁ = 1.
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
    ---- Horizontal part: match q with ... = d₂ ≫ totalDesc ----
    · rcases q with _ | q
      · -- q = 0: horizontal part is 0, d₂ vanishes (no predecessor of 0).
        simp only
        rw [HomologicalComplex₂.d₂_eq_zero]
        · simp
        · intro hrel; simp [ComplexShape.down_Rel] at hrel
      · -- q = q + 1: expand d₂ via d₂_eq, simplify ε₂ = (-1)^p.
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

/-! ### Homotopy equivalence -/

/-- `AW ∘ EZ` is chain homotopic to `𝟙` on `F₁(X)`. -/
noncomputable def homotopyShuffleAWId (X : BisimplicialObject C) :
    Homotopy (shuffleMap X ≫ alexanderWhitney X) (𝟙 (F₁.obj X)) := sorry

/-- `EZ ∘ AW` is chain homotopic to `𝟙` on `F₂(X)`. -/
noncomputable def homotopyAWShuffleId (X : BisimplicialObject C) :
    Homotopy (alexanderWhitney X ≫ shuffleMap X) (𝟙 (F₂.obj X)) := sorry

/-- **Eilenberg-Zilber theorem for bisimplicial objects.**

The total complex of the double complex (applying `alternatingFaceMapComplex` in
both simplicial directions) is homotopy equivalent to the chain complex of
the diagonal. -/
noncomputable def eilenbergZilber (X : BisimplicialObject C) :
    HomotopyEquiv (F₁.obj X) (F₂.obj X) where
  hom := shuffleMap X
  inv := alexanderWhitney X
  homotopyHomInvId := homotopyShuffleAWId X
  homotopyInvHomId := homotopyAWShuffleId X

end BisimplicialObject

end CategoryTheory
