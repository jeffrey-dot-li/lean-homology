import HomologyLean.SingularHomology.BisimplicialNormalizedDefs

/-!
# Normalized Eilenberg–Zilber for bisimplicial objects

The literature (Eilenberg–Mac Lane II, Thm 2.1a) proves the Eilenberg–Zilber contraction on the
**normalized** complexes, where one direction is a strict identity and the other is a chain
homotopy via the explicit Eilenberg–Mac Lane homotopy. We assemble that here on the bi-normalized
total complex `N₁` and the normalized Moore complex of the diagonal `N₂` (both defined in
`BisimplicialNormalizedDefs.lean`).

The intended use is to transport this normalized equivalence to the unnormalized `F₁`/`F₂`
(in `Bisimplicial.lean`) along the Dold–Kan homotopy equivalence
`AlgebraicTopology.DoldKan.homotopyEquivNormalizedMooreComplexAlternatingFaceMapComplex`,
to obtain `eilenbergZilber : HomotopyEquiv (F₁.obj X) (F₂.obj X)`.

Everything here requires `[Abelian C]` (for the normalized Moore complex); the unnormalized
constructions in `Bisimplicial.lean` only need `[Preadditive C] [HasFiniteCoproducts C]`.
-/

open AlgebraicTopology AlgebraicTopology.DoldKan CategoryTheory.Limits
open scoped Simplicial
open HomologyLean.SingularHomology

namespace CategoryTheory

namespace BisimplicialObject

variable {C : Type*} [Category* C] [Abelian C]

private lemma mooreInclusion_comp_mooreRetraction :
    mooreInclusion ≫ mooreRetraction = 𝟙 (normalizedMooreComplex C) := by
  ext Y : 2
  exact (splitMonoInclusionOfMooreComplexMap Y).id

/-- **Glue (split mono, lifted to the total complex).** The bi-normalized inclusion is a section
of the retraction. This lifts the Mathlib split-mono identity `(splitMonoInclusionOfMooreComplexMap
_).id` through `totalFunctor` in both simplicial directions. (Reused by `bridge₁`.) -/
@[reassoc]
lemma inclusionN₁_comp_retractionN₁ (X : BisimplicialObject C) :
    inclusionN₁ X ≫ retractionN₁ X = 𝟙 (N₁.obj X) := by
  dsimp only [inclusionN₁, retractionN₁]
  rw [← Functor.map_comp]
  refine Eq.trans (congrArg ((HomologicalComplex₂.totalFunctor _ _ _ _).map) ?_) <|
    (HomologicalComplex₂.totalFunctor _ _ _ _).map_id _
  let Y := ((alternatingFaceMapComplex (SimplicialObject C)).obj X)
  let M := (normalizedMooreComplex C).mapHomologicalComplex (ComplexShape.down ℕ)
  have hBC :
      (NatTrans.mapHomologicalComplex mooreInclusion _).app Y ≫
          (NatTrans.mapHomologicalComplex mooreRetraction _).app Y =
        𝟙 (M.obj Y) := by
    rw [← NatTrans.comp_app, ← NatTrans.mapHomologicalComplex_comp,
      mooreInclusion_comp_mooreRetraction, NatTrans.mapHomologicalComplex_id, NatTrans.id_app]
  calc
    (M.map (inclusionOfMooreComplexMap X) ≫
          (NatTrans.mapHomologicalComplex mooreInclusion _).app Y) ≫
        ((NatTrans.mapHomologicalComplex mooreRetraction _).app Y ≫
          M.map (PInftyToNormalizedMooreComplex X)) =
      M.map (inclusionOfMooreComplexMap X) ≫
          ((NatTrans.mapHomologicalComplex mooreInclusion _).app Y ≫
            (NatTrans.mapHomologicalComplex mooreRetraction _).app Y) ≫
        M.map (PInftyToNormalizedMooreComplex X) := by simp only [Category.assoc]
    _ = M.map (inclusionOfMooreComplexMap X) ≫ M.map (PInftyToNormalizedMooreComplex X) := by
      rw [hBC, Category.id_comp]
    _ = 𝟙 (M.obj ((normalizedMooreComplex (SimplicialObject C)).obj X)) := by
      rw [← M.map_comp]
      change M.map (inclusionOfMooreComplexMap X ≫
          (splitMonoInclusionOfMooreComplexMap X).retraction) = _
      rw [(splitMonoInclusionOfMooreComplexMap X).id, M.map_id]

/-- **Non-diagonal ⟹ one projection collapses at `j+1`.** If vertex `j+1` is not a diagonal
(corner) vertex of the shuffle `x`, then the two adjacent steps point the same way, so deleting
`j+1` (via `δ_{j+1}`) makes one of the two shuffle projections non-surjective: the vertical
projection `sndHom x ∘ δ_{j+1}` (both steps vertical, RR) or the horizontal projection
`fstHom x ∘ δ_{j+1}` (both steps horizontal, LL). This is the combinatorial core feeding the
termwise Moore vanishing in `higherFacesVanish_inclusionN₁_shuffleMap`. -/
private lemma comp_δ_not_surjective {a b : ℕ} (f : (⦋a⦌ : SimplexCategory) ⟶ ⦋b⦌)
    (k : Fin (b + 2)) :
    ¬ Function.Surjective ⇑(SimplexCategory.Hom.toOrderHom (f ≫ SimplexCategory.δ k)) := by
  intro hsurj
  obtain ⟨x, hx⟩ := hsurj k
  simp only [SimplexCategory.comp_toOrderHom, OrderHom.comp_coe, Function.comp_apply,
    SimplexCategory.δ, SimplexCategory.Hom.toOrderHom_mk, Fin.succAboveOrderEmb_apply] at hx
  exact Fin.succAbove_ne k _ hx

private lemma shuffleSndHom_zero_left {q : ℕ} (x : Shuffle 0 q) :
    shuffleSndHom x = eqToHom (congrArg SimplexCategory.mk (by omega : 0 + q = q)) := by
  ext r
  simp only [shuffleSndHom, SimplexCategory.comp_toOrderHom, OrderHom.comp_coe,
    Function.comp_apply, SimplexCategory.Hom.toOrderHom_mk, SimplexCategory.eqToHom_toOrderHom]
  set s : Fin (0 + q + 1) := (Fin.castOrderIso (by simp)).toOrderEmbedding.toOrderHom r
  have hfst := Fin.eq_zero ((x.1 s).1)
  simp only [Fin.ext_iff, Fin.val_zero] at hfst
  have hsum := Shuffle.coordSum_eq x s
  have hs : s.val = r.val := by simp [s]
  simp only [SimplexCategory.len_mk] at hsum
  have hsnd : ((x.1 s).2 : ℕ) = s.val := by omega
  simpa [hs] using hsnd

private lemma shuffleFstHom_zero_right {p : ℕ} (x : Shuffle p 0) :
    shuffleFstHom x = eqToHom (congrArg SimplexCategory.mk (by omega : p + 0 = p)) := by
  ext r
  simp only [shuffleFstHom, SimplexCategory.comp_toOrderHom, OrderHom.comp_coe,
    Function.comp_apply, SimplexCategory.Hom.toOrderHom_mk, SimplexCategory.eqToHom_toOrderHom]
  set s : Fin (p + 0 + 1) := (Fin.castOrderIso (by simp)).toOrderEmbedding.toOrderHom r
  have hsnd := Fin.eq_zero ((x.1 s).2)
  simp only [Fin.ext_iff, Fin.val_zero] at hsnd
  have hsum := Shuffle.coordSum_eq x s
  have hs : s.val = r.val := by simp [s]
  simp only [SimplexCategory.len_mk] at hsum
  have hfst : ((x.1 s).1 : ℕ) = s.val := by omega
  simpa [hs] using hfst

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

private lemma nondiag_sndHom_or_fstHom_comp_δ_not_surjective
    {p q n : ℕ} (x : Shuffle p q) (hpq : p + q = n + 1) (j : Fin (n + 1))
    (hx : ¬ x.isDiagonalVertex ⟨(j : ℕ) + 1, by omega⟩) :
    ¬ Function.Surjective ⇑(SimplexCategory.Hom.toOrderHom
        (SimplexCategory.δ j.succ ≫ eqToHom (congrArg SimplexCategory.mk hpq.symm) ≫
          shuffleSndHom x)) ∨
    ¬ Function.Surjective ⇑(SimplexCategory.Hom.toOrderHom
        (SimplexCategory.δ j.succ ≫ eqToHom (congrArg SimplexCategory.mk hpq.symm) ≫
          shuffleFstHom x)) := by
  rcases p with _ | p
  · left
    have hx0 : x = default := Subsingleton.elim _ _
    subst hx0
    simpa [hpq, shuffleSndHom_zero_left] using
      (comp_δ_not_surjective (𝟙 (⦋n⦌ : SimplexCategory)) j.succ)
  rcases q with _ | q
  · right
    have hx0 : x = default := Subsingleton.elim _ _
    subst hx0
    simpa [hpq, shuffleFstHom_zero_right] using
      (comp_δ_not_surjective (𝟙 (⦋n⦌ : SimplexCategory)) j.succ)
  obtain ⟨k, ν, hkx, hkr⟩ | ⟨k, ν, hkx, hkr⟩ :=
    Shuffle.nondiag_mem_insertLeft_or_insertRight x ⟨(j : ℕ) + 1, by omega⟩ hx
  · right
    have hr : j.succ = (Shuffle.insertLeftIndex ν k).cast (by omega) := by
      apply Fin.ext
      simpa using hkr.symm
    rw [hkx, hr, fstHom_insertLeftStep_comp_δ ν k hpq.symm]
    exact comp_δ_not_surjective
      (eqToHom (congrArg SimplexCategory.mk (by omega : n = p + (q + 1))) ≫ shuffleFstHom ν) k
  · left
    have hr : j.succ = (Shuffle.insertRightIndex ν k).cast (by omega) := by
      apply Fin.ext
      simpa using hkr.symm
    rw [hkx, hr, sndHom_insertRightStep_comp_δ ν k hpq.symm]
    exact comp_δ_not_surjective
      (eqToHom (congrArg SimplexCategory.mk (by omega : n = (p + 1) + q)) ≫ shuffleSndHom ν) k

/-- A Moore inclusion `N(Y) ↪ K(Y)` at degree `q`, postcomposed with `Y.map g.op` for a
non-surjective `g : ⦋n⦌ ⟶ ⦋q⦌` whose image contains `0`, vanishes: `g` factors through a coface
`δ_i` with `i ≠ 0`, which the Moore inclusion annihilates. -/
private lemma inclusionOfMooreComplexMap_comp_map_op_eq_zero (Y : SimplicialObject C) {n q : ℕ}
    (g : (⦋n⦌ : SimplexCategory) ⟶ ⦋q⦌)
    (hns : ¬ Function.Surjective ⇑(SimplexCategory.Hom.toOrderHom g))
    (h0 : ∃ k, (SimplexCategory.Hom.toOrderHom g) k = 0) :
    (inclusionOfMooreComplexMap Y).f q ≫ Y.map g.op = 0 := by
  match q with
  | 0 =>
    haveI : Subsingleton (Fin ((⦋0⦌ : SimplexCategory).len + 1)) := by
      rw [SimplexCategory.len_mk]; exact (inferInstance : Subsingleton (Fin 1))
    exact absurd (fun y => ⟨0, Subsingleton.elim _ _⟩) hns
  | q + 1 =>
    obtain ⟨i, g', hgi⟩ := SimplexCategory.eq_comp_δ_of_not_surjective g hns
    have hi : i ≠ 0 := by
      obtain ⟨k0, hk0⟩ := h0
      rintro rfl
      rw [hgi] at hk0
      simp only [SimplexCategory.comp_toOrderHom, OrderHom.comp_coe, Function.comp_apply,
        SimplexCategory.δ, SimplexCategory.Hom.toOrderHom_mk, Fin.succAboveOrderEmb_apply,
        Fin.succAbove_zero] at hk0
      exact Fin.succ_ne_zero _ hk0
    have hcond : (q : ℕ) + 2 ≤ (i : ℕ) + (q + 1) := by
      have := Fin.pos_of_ne_zero hi; omega
    rw [hgi, op_comp, Y.map_comp, ← Category.assoc,
      show Y.map (SimplexCategory.δ i).op = Y.δ i from rfl,
      (HigherFacesVanish.inclusionOfMooreComplexMap q).comp_δ_eq_zero i hi hcond, zero_comp]

/-- **Outer-direction Moore kill.** The bi-normalized inclusion at bidegree `(p, q)`, postcomposed
with the outer-direction map `X.map h.op` (`h : ⦋m⦌ ⟶ ⦋p⦌` non-surjective with `0` in its image),
vanishes: `h` factors through an outer coface `δ_v` with `v ≠ 0`, which the outer Moore inclusion
`inclusionOfMooreComplexMap X` annihilates (mirrors the inner-direction lemma, but the kill happens
on the outer factor `Aₚq` after commuting the inner Moore inclusion `Bₚq` past `X.map h.op` and using
naturality of `mooreInclusion` + functoriality of `normalizedMooreComplex`). -/
private lemma biInclusion_comp_outer_map_op_eq_zero (X : BisimplicialObject C) {m p : ℕ} (q : ℕ)
    (h : (⦋m⦌ : SimplexCategory) ⟶ ⦋p⦌)
    (hns : ¬ Function.Surjective ⇑(SimplexCategory.Hom.toOrderHom h))
    (h0 : ∃ k, (SimplexCategory.Hom.toOrderHom h) k = 0) :
    (((((normalizedMooreComplex C).mapHomologicalComplex (ComplexShape.down ℕ)).map
              (inclusionOfMooreComplexMap X) ≫
            (NatTrans.mapHomologicalComplex mooreInclusion (ComplexShape.down ℕ)).app
              ((alternatingFaceMapComplex (SimplicialObject C)).obj X)).f p).f q) ≫
        (X.map h.op).app (Opposite.op ⦋q⦌) = 0 := by
  dsimp [mooreInclusion]
  simp only [Category.assoc, inclusionOfMooreComplexMap_f]
  match p with
  | 0 =>
    haveI : Subsingleton (Fin ((⦋0⦌ : SimplexCategory).len + 1)) := by
      rw [SimplexCategory.len_mk]
      exact (inferInstance : Subsingleton (Fin 1))
    exact absurd (fun y => ⟨0, Subsingleton.elim _ _⟩) hns
  | p + 1 =>
    obtain ⟨i, h', hhi⟩ := SimplexCategory.eq_comp_δ_of_not_surjective h hns
    have hi : i ≠ 0 := by
      obtain ⟨k0, hk0⟩ := h0
      rintro rfl
      rw [hhi] at hk0
      simp only [SimplexCategory.comp_toOrderHom, OrderHom.comp_coe, Function.comp_apply,
        SimplexCategory.δ, SimplexCategory.Hom.toOrderHom_mk, Fin.succAboveOrderEmb_apply,
        Fin.succAbove_zero] at hk0
      exact Fin.succ_ne_zero _ hk0
    have hcond : (p : ℕ) + 2 ≤ (i : ℕ) + (p + 1) := by
      have := Fin.pos_of_ne_zero hi
      omega
    rw [Subobject.factorThru_arrow_assoc, Category.assoc]
    have hvanish :
        (NormalizedMooreComplex.objX X (p + 1)).arrow.app (Opposite.op ⦋q⦌) ≫
            (X.map (SimplexCategory.δ i).op).app (Opposite.op ⦋q⦌) = 0 := by
      simpa [SimplicialObject.δ, inclusionOfMooreComplexMap_f] using
        congrArg (fun f => f.app (Opposite.op ⦋q⦌))
          ((HigherFacesVanish.inclusionOfMooreComplexMap (X := X) p).comp_δ_eq_zero i hi hcond)
    rw [hhi, op_comp, X.map_comp, NatTrans.comp_app]
    slice_lhs 2 3 => rw [hvanish]
    simp only [zero_comp, comp_zero]

/-- **(B-core)** Higher faces vanish on the shuffle of a bi-normalized chain: every diagonal
face `δⱼ₊₁` (`j : Fin (n+1)`, i.e. all faces except `δ₀`) annihilates
`(inclusionN₁ X ≫ shuffleMap X).f (n+1)`. This is the combinatorial heart of (B): a shuffle of
chains normalized in both bisimplicial directions has no degenerate component in the diagonal. -/
private lemma higherFacesVanish_inclusionN₁_shuffleMap (X : BisimplicialObject C) (n : ℕ) :
    HigherFacesVanish (X := diag.obj X) (n + 1)
      ((inclusionN₁ X ≫ shuffleMap X).f (n + 1)) := by
  intro j hj
  rw [HomologicalComplex.comp_f]
  apply HomologicalComplex₂.total.hom_ext
  intro p q hpq
  simp only [ComplexShape.π_def] at hpq
  rw [Limits.comp_zero, inclusionN₁, HomologicalComplex₂.totalFunctor_map]
  simp only [Category.assoc]
  rw [HomologicalComplex₂.ιTotal_map_assoc]
  dsimp only [shuffleMap]
  rw [HomologicalComplex₂.ι_totalDesc_assoc]
  simp only [SimplicialObject.δ, diag_obj_map]
  simp only [ezComponent, Preadditive.sum_comp, Preadditive.zsmul_comp, Category.assoc]
  simp_rw [← (X.map (SimplexCategory.δ _).op).naturality]
  simp_rw [← Category.assoc ((X.map (shuffleFstHom _).op).app (Opposite.op ⦋p + q⦌))]
  generalize_proofs _ _ _ _ _ heq
  have hpqop : Opposite.op ⦋p + q⦌ = Opposite.op (⦋n + 1⦌ : SimplexCategory) :=
    congrArg Opposite.op (congrArg SimplexCategory.mk hpq)
  have heq_vert : (X.obj (Opposite.op ⦋p + q⦌)).obj (Opposite.op ⦋p + q⦌) =
      (X.obj (Opposite.op ⦋n + 1⦌)).obj (Opposite.op ⦋p + q⦌) :=
    congrFun (congrArg Prefunctor.obj (congrArg Functor.toPrefunctor (congrArg X.obj hpqop)))
      (Opposite.op ⦋p + q⦌)
  have heq_horiz : (X.obj (Opposite.op ⦋n + 1⦌)).obj (Opposite.op ⦋p + q⦌) =
      (X.obj (Opposite.op ⦋n + 1⦌)).obj (Opposite.op ⦋n + 1⦌) :=
    congrArg (X.obj (Opposite.op ⦋n + 1⦌)).obj hpqop
  simp_rw [show eqToHom heq = eqToHom heq_vert ≫ eqToHom heq_horiz from by
    rw [show heq = heq_vert.trans heq_horiz from proof_irrel _ _, eqToHom_trans],
    Category.assoc]
  -- Fold horizontal `eqToHom heq_horiz` into `X_⦋n+1⦌.map`, then into the horizontal face.
  simp_rw [show eqToHom heq_horiz = (X.obj (Opposite.op ⦋n + 1⦌)).map (eqToHom hpqop) from
    (eqToHom_map (X.obj (Opposite.op ⦋n + 1⦌)) hpqop).symm]
  simp_rw [← Category.assoc ((X.obj (Opposite.op ⦋n + 1⦌)).map (eqToHom hpqop)),
    ← Functor.map_comp]
  -- Fold vertical `eqToHom heq_vert` into `(X.map _).app`, then into the shuffleFstHom map.
  simp_rw [show eqToHom heq_vert = (X.map (eqToHom hpqop)).app (Opposite.op ⦋p + q⦌) from by
    rw [eqToHom_map, eqToHom_app]]
  simp_rw [← Category.assoc ((X.map (shuffleFstHom _).op).app (Opposite.op ⦋p + q⦌)),
    ← NatTrans.comp_app, ← Functor.map_comp]
  -- Commute the vertical map past the horizontal face via naturality.
  simp_rw [← Category.assoc ((X.map ((shuffleFstHom _).op ≫ eqToHom hpqop)).app _),
    ← (X.map ((shuffleFstHom _).op ≫ eqToHom hpqop)).naturality, Category.assoc]
  -- Fold adjacent horizontal maps and adjacent vertical maps into single maps.
  simp_rw [← Category.assoc ((X.obj (Opposite.op ⦋p⦌)).map (shuffleSndHom _).op),
    ← Functor.map_comp, ← NatTrans.comp_app, ← Functor.map_comp]
  -- Distribute the inclusion over the shuffle sum, then split `∑_μ` at vertex `j+1` into the
  -- diagonal (corner) shuffles and the non-diagonal ones.
  rw [Preadditive.comp_sum, ← Finset.sum_filter_add_sum_filter_not Finset.univ
    (fun μ : Shuffle p q => Shuffle.isDiagonalVertex μ ⟨(j : ℕ) + 1, by omega⟩)]
  refine (congrArg₂ (· + ·) ?diag ?nondiag).trans (add_zero 0)
  case diag =>
    -- Corner shuffles cancel pairwise via the `swapDiagonalSteps` sign-reversing involution
    -- (mirror `Bisimplicial.lean:837–871`). Vertex `j+1` is a diagonal vertex on this filter.
    refine Finset.sum_involution
      (fun x hx => Shuffle.swapDiagonalSteps x ⟨(j : ℕ) + 1, by omega⟩
        (Finset.mem_filter.mp hx).2) ?cancel ?ne ?mem ?invol
    case ne =>
      exact fun x hx _ =>
        Shuffle.swapDiagonalSteps_ne x ⟨(j : ℕ) + 1, by omega⟩ (Finset.mem_filter.mp hx).2
    case mem =>
      exact fun x hx => Finset.mem_filter.mpr ⟨Finset.mem_univ _,
        Shuffle.swapDiagonalSteps_vertex x ⟨(j : ℕ) + 1, by omega⟩ (Finset.mem_filter.mp hx).2⟩
    case invol =>
      exact fun x hx =>
        Shuffle.swapDiagonalSteps_involutive x ⟨(j : ℕ) + 1, by omega⟩ (Finset.mem_filter.mp hx).2
    case cancel =>
      intro a ha
      have hr := (Finset.mem_filter.mp ha).2
      dsimp only
      simp only [Shuffle.swapDiagonalSteps_neg_sign _ _ hr, neg_smul, Preadditive.comp_neg]
      rw [add_neg_eq_zero]
      -- Same sign on both sides; reduce to the (op-lifted) `swapDiagonalSteps` face identities.
      have hsnd_op : (shuffleSndHom (a.swapDiagonalSteps ⟨(j : ℕ) + 1, by omega⟩ hr)).op ≫
            eqToHom hpqop ≫ (SimplexCategory.δ j.succ).op
          = (shuffleSndHom a).op ≫ eqToHom hpqop ≫ (SimplexCategory.δ j.succ).op := by
        have h := congrArg Quiver.Hom.op (sndHom_swapDiagonalSteps_comp_δ a j.succ hpq.symm hr)
        simp only [op_comp, eqToHom_op, Category.assoc] at h
        exact h
      have hfst_op : ((shuffleFstHom (a.swapDiagonalSteps ⟨(j : ℕ) + 1, by omega⟩ hr)).op ≫
            eqToHom hpqop) ≫ (SimplexCategory.δ j.succ).op
          = ((shuffleFstHom a).op ≫ eqToHom hpqop) ≫ (SimplexCategory.δ j.succ).op := by
        have h := congrArg Quiver.Hom.op (fstHom_swapDiagonalSteps_comp_δ a j.succ hpq.symm hr)
        simp only [op_comp, eqToHom_op] at h
        exact h
      rw [hsnd_op, hfst_op]
  case nondiag =>
    -- Non-diagonal shuffles: `fstHom μ ∘ δ_{j+1}` (LL) or `sndHom μ ∘ δ_{j+1}` (RR) factors through
    -- a higher coface `δ_v` (`v ≥ 1`); the bi-Moore inclusion (`inclusionOfMooreComplexMap` outer /
    -- `mooreInclusion` inner) annihilates that higher face termwise.
    apply Finset.sum_eq_zero
    intro x hx
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx
    rw [Preadditive.comp_zsmul]
    apply smul_eq_zero_of_right
    simp only [HomologicalComplex.comp_f]
    obtain hns | hns := nondiag_sndHom_or_fstHom_comp_δ_not_surjective x hpq j hx
    · -- RR / inner: `sndHom x ∘ δ_{j+1}` is non-surjective.
      have hBinner :
          (((NatTrans.mapHomologicalComplex mooreInclusion (ComplexShape.down ℕ)).app
                  ((alternatingFaceMapComplex (SimplicialObject C)).obj X)).f p).f q ≫
              X _⦋p⦌.map ((shuffleSndHom x).op ≫ eqToHom hpqop ≫ (SimplexCategory.δ j.succ).op) = 0 := by
        have key := inclusionOfMooreComplexMap_comp_map_op_eq_zero (X _⦋p⦌)
          (SimplexCategory.δ j.succ ≫ eqToHom (congrArg SimplexCategory.mk hpq.symm) ≫
            shuffleSndHom x) hns ⟨0, by
              have hcs := Shuffle.coordSum_eq x 0
              simp only [Fin.val_zero] at hcs
              simp only [SimplexCategory.comp_toOrderHom, OrderHom.comp_coe, Function.comp_apply,
                shuffleSndHom, SimplexCategory.δ, SimplexCategory.mkHom,
                SimplexCategory.Hom.toOrderHom_mk, OrderHom.snd_coe,
                SimplexCategory.eqToHom_toOrderHom]
              dsimp only [Fin.succAboveOrderEmb, Fin.castOrderIso]
              simp only [SimplexCategory.len_mk, OrderEmbedding.toOrderHom_coe,
                OrderEmbedding.coe_ofStrictMono, ne_eq, Fin.succ_ne_zero, not_false_eq_true,
                Fin.succAbove_ne_zero_zero, OrderIso.coe_toOrderEmbedding, RelIso.coe_fn_mk,
                Equiv.coe_fn_mk, Fin.cast_zero]
              apply Fin.ext
              simp only [Fin.val_zero]
              omega⟩
        convert key using 2
        simp only [op_comp, eqToHom_op, Category.assoc]
      rw [Category.assoc, reassoc_of% hBinner, zero_comp, comp_zero]
    · -- LL / outer: `fstHom x ∘ δ_{j+1}` is non-surjective.
      -- Commute the outer face `(X.map fst).app` past the inner vertical map via naturality, so it
      -- lands at vertical degree `q` adjacent to the bi-inclusion, where the outer Moore kill fires.
      rw [(X.map (((shuffleFstHom x).op ≫ eqToHom hpqop) ≫
        (SimplexCategory.δ j.succ).op)).naturality]
      have hOuter :
          ((((((normalizedMooreComplex C).mapHomologicalComplex (ComplexShape.down ℕ)).map
                    (inclusionOfMooreComplexMap X)).f p).f q) ≫
              (((NatTrans.mapHomologicalComplex mooreInclusion (ComplexShape.down ℕ)).app
                    ((alternatingFaceMapComplex (SimplicialObject C)).obj X)).f p).f q) ≫
            (X.map (((shuffleFstHom x).op ≫ eqToHom hpqop) ≫
                (SimplexCategory.δ j.succ).op)).app (Opposite.op ⦋q⦌) = 0 := by
        have key := biInclusion_comp_outer_map_op_eq_zero X q
          (SimplexCategory.δ j.succ ≫ eqToHom (congrArg SimplexCategory.mk hpq.symm) ≫
            shuffleFstHom x) hns ⟨0, by
              have hcs := Shuffle.coordSum_eq x 0
              simp only [Fin.val_zero] at hcs
              simp only [SimplexCategory.comp_toOrderHom, OrderHom.comp_coe, Function.comp_apply,
                shuffleFstHom, SimplexCategory.δ, SimplexCategory.mkHom,
                SimplexCategory.Hom.toOrderHom_mk, OrderHom.fst_coe,
                SimplexCategory.eqToHom_toOrderHom]
              dsimp only [Fin.succAboveOrderEmb, Fin.castOrderIso]
              simp [Fin.succ_succAbove_zero]
              apply Fin.ext
              simp only [Fin.val_zero]
              omega⟩
        convert key using 2
        simp only [op_comp, eqToHom_op, Category.assoc]
      rw [← Category.assoc, hOuter, zero_comp]

/-- **(B) `∇` preserves normalization** (EM Lemma I.5.3). Precomposed with the bi-normalized
inclusion, the shuffle map already lands in the normalized diagonal, so the diagonal
renormalization round-trip `retractionN₂ ≫ inclusionN₂` (which equals `PInfty`) is a no-op.
`@[reassoc]` so it rewrites underneath the trailing `alexanderWhitney ≫ retractionN₁`. -/
@[reassoc]
lemma inclusionN₁_shuffleMap_diag_normalize (X : BisimplicialObject C) :
    inclusionN₁ X ≫ shuffleMap X ≫ retractionN₂ X ≫ inclusionN₂ X
      = inclusionN₁ X ≫ shuffleMap X := by
  rw [retractionN₂, inclusionN₂, PInftyToNormalizedMooreComplex_comp_inclusionOfMooreComplexMap,
    ← Category.assoc]
  ext (_ | n)
  · simp
  · rw [HomologicalComplex.comp_f, PInfty_f]
    exact (higherFacesVanish_inclusionN₁_shuffleMap X n).comp_P_eq_self

omit [Abelian C] in
/-- **Summand merge.** For a single shuffle `x`, the four-map Eilenberg–Zilber ∘ Alexander–Whitney
summand (vertical `sndHom x`, horizontal `fstHom x`, horizontal `ι_front`, vertical `ι_back`)
collapses — by functoriality of `X.map` and bifunctor naturality — to a single bisimplicial
double-operator with inner part `β_x = ι_back ≫ shuffleSndHom x : ⦋m⦌ ⟶ ⦋m⦌` and outer part
`α_x = ι_front ≫ shuffleFstHom x : ⦋r⦌ ⟶ ⦋r⦌`. -/
private lemma ezawSummand_merge (X : BisimplicialObject C) (r m : ℕ) (x : Shuffle r m) :
    (X.obj (Opposite.op ⦋r⦌)).map (shuffleSndHom x).op ≫
        (X.map (shuffleFstHom x).op).app (Opposite.op ⦋r + m⦌) ≫
          (X.map (ι_front r m).op).app (Opposite.op ⦋r + m⦌) ≫
            (X.obj (Opposite.op ⦋r⦌)).map (ι_back r m).op =
      (X.obj (Opposite.op ⦋r⦌)).map (ι_back r m ≫ shuffleSndHom x).op ≫
        (X.map (ι_front r m ≫ shuffleFstHom x).op).app (Opposite.op ⦋m⦌) := by
  -- Fuse the two adjacent horizontal (outer) operators into a single `X.map (ι_front ≫ fstHom x).op`.
  slice_lhs 2 3 => rw [← NatTrans.comp_app, ← Functor.map_comp, ← op_comp]
  -- Push the inner `ι_back` leftward past the outer operator via bifunctor naturality.
  slice_lhs 2 3 => rw [← (X.map (ι_front r m ≫ shuffleFstHom x).op).naturality (ι_back r m).op]
  -- Fuse the two adjacent vertical (inner) operators into `X.map (ι_back ≫ sndHom x).op`.
  slice_lhs 1 2 => rw [← Functor.map_comp, ← op_comp]

/-- **Dual glue (inner direction).** A vertical operator `Y.map g.op` for a non-mono (degenerate)
`g : ⦋n⦌ ⟶ Δ'` (any codomain) is annihilated by the inner Moore retraction `PInfty` at level `n`.
Dual to `inclusionOfMooreComplexMap_comp_map_op_eq_zero`; proved via `degeneracy_comp_PInfty`,
which itself allows arbitrary codomain. -/
private lemma map_op_comp_PInftyToNormalizedMooreComplex_eq_zero {A : Type*} [Category A]
    [Abelian A] (Y : SimplicialObject A) {n : ℕ} {Δ' : SimplexCategory}
    (g : (⦋n⦌ : SimplexCategory) ⟶ Δ') (hg : ¬ Mono g) :
    Y.map g.op ≫ (PInftyToNormalizedMooreComplex Y).f n = 0 := by
  have h := AlgebraicTopology.DoldKan.degeneracy_comp_PInfty Y n g hg
  rw [← PInftyToNormalizedMooreComplex_comp_inclusionOfMooreComplexMap Y,
    HomologicalComplex.comp_f, ← Category.assoc] at h
  haveI : Mono ((inclusionOfMooreComplexMap Y).f n) := by
    rw [inclusionOfMooreComplexMap_f]; infer_instance
  exact zero_of_comp_mono _ h

/-- **Inner-direction kill on the merged operator.** When the inner part `B : ⦋c⦌ ⟶ ⦋s⦌` is
non-mono (degenerate), the merged double-operator (outer `A : ⦋b⦌ ⟶ ⦋r⦌`, possibly mono) composed
with the bi-retraction `R'_{b,c}` vanishes: commute `B` past the outer `A` (bifunctor naturality),
then apply the inner dual glue at level `c`. The endo case `b = r`, `c = s` recovers the diagonal. -/
private lemma inner_map_op_comp_retraction_eq_zero (X : BisimplicialObject C) {r s b c : ℕ}
    (A : (⦋b⦌ : SimplexCategory) ⟶ ⦋r⦌)
    (B : (⦋c⦌ : SimplexCategory) ⟶ ⦋s⦌) (hB : ¬ Mono B) :
    (X.obj (Opposite.op ⦋r⦌)).map B.op ≫ (X.map A.op).app (Opposite.op ⦋c⦌) ≫
        (((NatTrans.mapHomologicalComplex mooreRetraction (ComplexShape.down ℕ)).app
              ((alternatingFaceMapComplex (SimplicialObject C)).obj X) ≫
            ((normalizedMooreComplex C).mapHomologicalComplex (ComplexShape.down ℕ)).map
              (PInftyToNormalizedMooreComplex X)).f b).f c = 0 := by
  slice_lhs 1 2 => rw [(X.map A.op).naturality B.op]
  rw [Category.assoc]
  simp only [HomologicalComplex.comp_f, NatTrans.mapHomologicalComplex_app_f, mooreRetraction,
    alternatingFaceMapComplex_obj_X]
  rw [← Category.assoc (X _⦋b⦌.map B.op),
    map_op_comp_PInftyToNormalizedMooreComplex_eq_zero (X _⦋b⦌) B hB, zero_comp, comp_zero]

/-- **Outer-direction kill on the merged operator.** When the outer part `A : ⦋b⦌ ⟶ ⦋r⦌` is
non-mono (degenerate), the outer operator composed with the bi-retraction `R'_{b,c}` vanishes:
commute the inner `PInfty` leg past `A` (naturality of `PInftyToNormalizedMooreComplex`), then the
outer Moore retraction `factorThru` annihilates the degeneracy. The endo case `b = r` recovers the
diagonal. Dual to `biInclusion_comp_outer_map_op_eq_zero`. -/
private lemma outer_map_op_comp_retraction_eq_zero (X : BisimplicialObject C) {r b c : ℕ}
    (A : (⦋b⦌ : SimplexCategory) ⟶ ⦋r⦌) (hA : ¬ Mono A) :
    (X.map A.op).app (Opposite.op ⦋c⦌) ≫
        (((NatTrans.mapHomologicalComplex mooreRetraction (ComplexShape.down ℕ)).app
              ((alternatingFaceMapComplex (SimplicialObject C)).obj X) ≫
            ((normalizedMooreComplex C).mapHomologicalComplex (ComplexShape.down ℕ)).map
              (PInftyToNormalizedMooreComplex X)).f b).f c = 0 := by
  simp only [HomologicalComplex.comp_f, NatTrans.mapHomologicalComplex_app_f, mooreRetraction,
    Functor.mapHomologicalComplex_map_f, alternatingFaceMapComplex_obj_X]
  -- Commute the outer operator past the inner `PInfty` leg via `PInfty` naturality.
  have hnat := HomologicalComplex.congr_hom
    (PInftyToNormalizedMooreComplex_naturality (X.map A.op)) c
  simp only [HomologicalComplex.comp_f, AlternatingFaceMapComplex.map_f] at hnat
  slice_lhs 1 2 => rw [hnat]
  -- Fold the two outer Moore maps; the outer degeneracy `A` is killed by the outer retraction.
  slice_lhs 2 3 => rw [← HomologicalComplex.comp_f, ← normalizedMooreComplex_map,
    ← Functor.map_comp, map_op_comp_PInftyToNormalizedMooreComplex_eq_zero X A hA,
    Functor.map_zero, HomologicalComplex.zero_f]
  rw [comp_zero]

/-- **Combinatorial core.** Any shuffle other than the staircase `trivialShuffle` has a degenerate
front or back face: either its outer face `α_x = ι_front ≫ shuffleFstHom x` or its inner face
`β_x = ι_back ≫ shuffleSndHom x` is non-mono (non-injective). Proved from `coordSum_eq`: both faces
mono forces the staircase coordinates `x.1 k = (min(k,r), k - r)`. -/
private lemma shuffle_ne_trivialShuffle_not_mono (r m : ℕ) (x : Shuffle r m)
    (hx : x ≠ Shuffle.trivialShuffle r m) :
    ¬ Mono (ι_front r m ≫ shuffleFstHom x) ∨ ¬ Mono (ι_back r m ≫ shuffleSndHom x) := by
  refine Or.inl (fun hmono => hx ?_)
  rw [SimplexCategory.mono_iff_injective] at hmono
  set f := (ι_front r m ≫ shuffleFstHom x).toOrderHom with hf
  have hfi : ∀ i : Fin (r + 1), (f i).val = (x.1 ⟨i.val, by omega⟩).1.val := by
    intro i
    simp [hf, shuffleFstHom, ι_front, SimplexCategory.comp_toOrderHom]
  have hsm : StrictMono f := f.monotone.strictMono_of_injective hmono
  have ha : ∀ i : Fin (r + 1), (x.1 ⟨i.val, by omega⟩).1.val = i.val := by
    intro i
    have h1 : (i : ℕ) ≤ (f i : ℕ) := hsm.le_apply
    have h2 : (f i : ℕ) ≤ (i : ℕ) := hsm.dual.le_apply
    rw [hfi] at h1 h2
    omega
  have hmin : ∀ k : Index (r + m), (x.1 k).1.val = min k.val r := by
    intro k
    by_cases hk : (k : ℕ) ≤ r
    · rw [min_eq_left hk]
      have h := ha ⟨k.val, by omega⟩
      rw [show (⟨(⟨k.val, by omega⟩ : Fin (r + 1)).val, by omega⟩ : Index (r + m)) = k from
        Fin.ext rfl] at h
      exact h
    · rw [min_eq_right (by omega : r ≤ (k : ℕ))]
      have hr : ((x.1 (⟨r, by omega⟩ : Index (r + m))).1 : ℕ) = r := by
        have h := ha ⟨r, by omega⟩
        rw [show (⟨(⟨r, by omega⟩ : Fin (r + 1)).val, by omega⟩ : Index (r + m))
          = ⟨r, by omega⟩ from Fin.ext rfl] at h
        exact h
      have hle : ((x.1 (⟨r, by omega⟩ : Index (r + m))).1 : ℕ) ≤ ((x.1 k).1 : ℕ) :=
        (x.1.monotone (show (⟨r, by omega⟩ : Index (r + m)) ≤ k by
          rw [Fin.le_def]; change r ≤ (k : ℕ); omega)).1
      have hb : ((x.1 k).1 : ℕ) < r + 1 := (x.1 k).1.isLt
      omega
  apply Subtype.ext
  ext k
  · rw [Shuffle.trivialShuffle_apply]
    exact hmin k
  · rw [Shuffle.trivialShuffle_apply]
    have h1 := hmin k
    have h2 := Shuffle.coordSum_eq x k
    show (x.1 k).2.val = (k : ℕ) - r
    omega

/-- **A (identity summand).** The staircase shuffle's EZ∘AW summand is the identity: its front-`r`
face and back-`m` face are the identities (`α = 𝟙`, `β = 𝟙`), so the merged operator is `𝟙`. -/
private lemma ezawSummand_trivial (X : BisimplicialObject C) (r m : ℕ) :
    (X.obj (Opposite.op ⦋r⦌)).map (shuffleSndHom (Shuffle.trivialShuffle r m)).op ≫
        (X.map (shuffleFstHom (Shuffle.trivialShuffle r m)).op).app (Opposite.op ⦋r + m⦌) ≫
          (X.map (ι_front r m).op).app (Opposite.op ⦋r + m⦌) ≫
            (X.obj (Opposite.op ⦋r⦌)).map (ι_back r m).op =
      𝟙 ((X.obj (Opposite.op ⦋r⦌)).obj (Opposite.op ⦋m⦌)) := by
  rw [ezawSummand_merge X r m (Shuffle.trivialShuffle r m)]
  have hsnd : ι_back r m ≫ shuffleSndHom (Shuffle.trivialShuffle r m) = 𝟙 _ := by
    ext x : 3
    simp [ι_back, shuffleSndHom, Shuffle.trivialShuffle]
  have hfst : ι_front r m ≫ shuffleFstHom (Shuffle.trivialShuffle r m) = 𝟙 _ := by
    ext x : 3
    simp only [SimplexCategory.len_mk, ι_front, SimplexCategory.mkHom, shuffleFstHom,
      Shuffle.trivialShuffle, OrderHom.fst_comp_prod, SimplexCategory.comp_toOrderHom,
      SimplexCategory.Hom.toOrderHom_mk, OrderHom.mk_comp_mk, OrderHom.coe_mk, Function.comp_apply,
      SimplexCategory.id_toOrderHom, OrderHom.id_coe, id_eq]
    apply Fin.ext
    show min (x : ℕ) r = (x : ℕ)
    have : (x : ℕ) < r + 1 := x.isLt
    omega
  rw [hsnd, hfst]
  simp

/-- **B (degenerate summands).** Every non-staircase shuffle's summand is killed by the
bi-retraction `R'`. Combines the merge with the combinatorial non-mono dichotomy and the two
dual glue lemmas. -/
private lemma ezawSummand_comp_retraction_eq_zero (X : BisimplicialObject C) (r m : ℕ)
    (x : Shuffle r m) (hx : x ≠ Shuffle.trivialShuffle r m) :
    (X.obj (Opposite.op ⦋r⦌)).map (shuffleSndHom x).op ≫
        (X.map (shuffleFstHom x).op).app (Opposite.op ⦋r + m⦌) ≫
          (X.map (ι_front r m).op).app (Opposite.op ⦋r + m⦌) ≫
            (X.obj (Opposite.op ⦋r⦌)).map (ι_back r m).op ≫
              (((NatTrans.mapHomologicalComplex mooreRetraction (ComplexShape.down ℕ)).app
                    ((alternatingFaceMapComplex (SimplicialObject C)).obj X) ≫
                  ((normalizedMooreComplex C).mapHomologicalComplex (ComplexShape.down ℕ)).map
                    (PInftyToNormalizedMooreComplex X)).f r).f m = 0 := by
  rw [reassoc_of% ezawSummand_merge X r m x]
  rcases shuffle_ne_trivialShuffle_not_mono r m x hx with hα | hβ
  · rw [outer_map_op_comp_retraction_eq_zero X _ hα, comp_zero]
  · exact inner_map_op_comp_retraction_eq_zero X _ _ hβ

/-- **A-diag: the diagonal Eilenberg–MacLane identity.** On the diagonal `(p,q) = (r,m)` the
shuffle/Alexander–Whitney pairing `ezComponent ≫ awComponent` is the identity *plus* degenerate
cross-terms; the bi-normalized retraction component `R'` (the Dold–Kan `PInfty` projection in
both simplicial directions, taken at bidegree `(r,m)`) annihilates the degenerate part, so
`ez ≫ aw ≫ R' = R'`. This is the combinatorial heart of `(A)`. -/
lemma ezComponent_awComponent_comp_retraction (X : BisimplicialObject C) (r m : ℕ) :
    X.ezComponent r m ≫ X.awComponent r m ≫
        (((NatTrans.mapHomologicalComplex mooreRetraction (ComplexShape.down ℕ)).app
              ((alternatingFaceMapComplex (SimplicialObject C)).obj X) ≫
            ((normalizedMooreComplex C).mapHomologicalComplex (ComplexShape.down ℕ)).map
              (PInftyToNormalizedMooreComplex X)).f r).f m =
      (((NatTrans.mapHomologicalComplex mooreRetraction (ComplexShape.down ℕ)).app
            ((alternatingFaceMapComplex (SimplicialObject C)).obj X) ≫
          ((normalizedMooreComplex C).mapHomologicalComplex (ComplexShape.down ℕ)).map
            (PInftyToNormalizedMooreComplex X)).f r).f m := by
  -- Step 1: expand `ez` into its shuffle sum and distribute `≫ aw ≫ R'` through it.
  simp only [ezComponent, awComponent, Preadditive.sum_comp, Preadditive.zsmul_comp,
    Category.assoc]
  -- Step 2: only the staircase (trivial) shuffle survives; every other shuffle is degenerate and
  -- killed by `R'`. The surviving summand has `sign = 1` and a merged operator equal to `𝟙`.
  rw [Finset.sum_eq_single (Shuffle.trivialShuffle r m)
      (fun x _ hx => by rw [ezawSummand_comp_retraction_eq_zero X r m x hx, smul_zero])
      (fun h => absurd (Finset.mem_univ _) h),
    Shuffle.sign_trivialShuffle, one_zsmul, reassoc_of% ezawSummand_trivial X r m]

omit [Abelian C] in
/-- **Off-diagonal summand merge.** Same functoriality collapse as `ezawSummand_merge`, but for a
*mismatched* Alexander–Whitney split `(b, c)` with `b + c = r + s` differing from the shuffle's
bidegree `(r, s)`. The four-map summand (vertical `sndHom μ`, horizontal `fstHom μ`, the cast to
`⦋b+c⦌`, horizontal `ι_front b c`, vertical `ι_back b c`) collapses to a single bisimplicial
double-operator whose inner part is `ι_back b c ≫ cast ≫ sndHom μ : ⦋c⦌ ⟶ ⦋s⦌` and outer part is
`ι_front b c ≫ cast ≫ fstHom μ : ⦋b⦌ ⟶ ⦋r⦌`. -/
private lemma ezawSummand_offDiag_merge (X : BisimplicialObject C) (r s b c : ℕ)
    (hbc : b + c = r + s) (μ : Shuffle r s) :
    (X.obj (Opposite.op ⦋r⦌)).map (shuffleSndHom μ).op ≫
        (X.map (shuffleFstHom μ).op).app (Opposite.op ⦋r + s⦌) ≫
          eqToHom (by rw [show r + s = b + c from hbc.symm]) ≫
            (X.map (ι_front b c).op).app (Opposite.op ⦋b + c⦌) ≫
              (X.obj (Opposite.op ⦋b⦌)).map (ι_back b c).op =
      (X.obj (Opposite.op ⦋r⦌)).map
            (ι_back b c ≫ eqToHom (by rw [hbc]) ≫ shuffleSndHom μ).op ≫
        (X.map (ι_front b c ≫ eqToHom (by rw [hbc]) ≫ shuffleFstHom μ).op).app (Opposite.op ⦋c⦌) := by
  sorry

/-- **(B-off) Off-diagonal summands vanish.** When the Alexander–Whitney split `(b, c)` differs
from the shuffle's bidegree `(r, s)` (`b ≠ r`, with `b + c = r + s`), the merged outer face
`ι_front b c ≫ fstHom μ : ⦋b⦌ ⟶ ⦋r⦌` (when `b > r`) or inner face `ι_back b c ≫ sndHom μ :
⦋c⦌ ⟶ ⦋s⦌` (when `b < r`, so `c > s`) drops dimension, hence is non-mono (`SimplexCategory.le_of_mono`)
and is annihilated by the corresponding `PInfty` leg of the bi-retraction `R'_{b,c}`. The
off-diagonal analogue of `ezawSummand_comp_retraction_eq_zero`; proved via `ezawSummand_offDiag_merge`
plus the (non-endo–generalized) outer/inner kill lemmas. -/
private lemma ezawSummand_offDiag_comp_retraction_eq_zero (X : BisimplicialObject C)
    (r s b c : ℕ) (hbc : b + c = r + s) (hb : b ≠ r) (μ : Shuffle r s) :
    (X.obj (Opposite.op ⦋r⦌)).map (shuffleSndHom μ).op ≫
        (X.map (shuffleFstHom μ).op).app (Opposite.op ⦋r + s⦌) ≫
          eqToHom (by rw [show r + s = b + c from hbc.symm]) ≫
            (X.map (ι_front b c).op).app (Opposite.op ⦋b + c⦌) ≫
              (X.obj (Opposite.op ⦋b⦌)).map (ι_back b c).op ≫
                (((NatTrans.mapHomologicalComplex mooreRetraction (ComplexShape.down ℕ)).app
                      ((alternatingFaceMapComplex (SimplicialObject C)).obj X) ≫
                    ((normalizedMooreComplex C).mapHomologicalComplex (ComplexShape.down ℕ)).map
                      (PInftyToNormalizedMooreComplex X)).f b).f c = 0 := by
  sorry

/-- **(A) EM `f∇ = i` modulo norms.** Unnormalized, `shuffleMap ≫ alexanderWhitney = 𝟙 + D` with
`D` landing in the degenerate subcomplex; the bi-normalized retraction `retractionN₁` annihilates
`D`, leaving `retractionN₁`. The combinatorial core is the shuffle pairing
`ezComponent ≫ awComponent` (diagonal `(r,s) = (p,q)` ↦ identity; off-diagonal ↦ degenerate). -/
lemma shuffleMap_alexanderWhitney_comp_retractionN₁ (X : BisimplicialObject C) :
    shuffleMap X ≫ alexanderWhitney X ≫ retractionN₁ X = retractionN₁ X := by
  ext n
  simp only [HomologicalComplex.comp_f]
  apply HomologicalComplex₂.total.hom_ext
  intro r s hrs
  simp only [ComplexShape.π_def] at hrs
  dsimp only [shuffleMap]
  rw [HomologicalComplex₂.ι_totalDesc_assoc]
  dsimp only [alexanderWhitney]
  simp only [id_eq, Preadditive.comp_sum, Preadditive.sum_comp, Category.assoc]
  simp only [retractionN₁]
  dsimp only [HomologicalComplex₂.totalFunctor]
  simp only [HomologicalComplex₂.ιTotal_map, HomologicalComplex₂.ιTotal_map_assoc]
  -- Step 5: the `ιTotal` coproduct inclusions are independent, so match the sum summand-by-summand.
  -- Only the diagonal term `x = r` survives; off-diagonal `x ≠ r` terms vanish after `≫ r_{x,n-x}`.
  rw [Finset.sum_eq_single (⟨r, by omega⟩ : Fin (n + 1))
    ?offdiag (fun h => absurd (Finset.mem_univ _) h)]
  · -- Diagonal `x = r`: `ez_{r,s} ≫ aw_{r,s} ≫ r_{r,s} = r_{r,s}` (identity modulo degenerate).
    obtain rfl : n = r + s := hrs.symm
    simp only [Fin.val_mk]
    -- `r + s - r = s` lives in dependent positions (awComponent indices, ιTotal proof
    -- witnesses), so `rw` fails with "motive is not type correct". Generalize the term to a
    -- fresh variable everywhere (including proofs), then `subst` it.
    have k : r + s - r = s := by omega
    generalize_proofs at *
    generalize r + s - r = m at *
    subst k
    simp only [eqToHom_trans, eqToHom_refl]
    -- The two `eqToHom` casts are mutually inverse, so they collapse to `𝟙`; drop it. The
    -- trailing `ιTotal` is identical on both sides, so the goal is `ez ≫ aw ≫ R' = R'`
    -- precomposed into `ιTotal`. Close it with the A-diag identity (reassociated past `ιTotal`).
    rw [Category.id_comp]
    simp only [Functor.mapHomologicalComplex_obj_X, alternatingFaceMapComplex_obj_X,
      Functor.comp_obj, normalizedMooreComplex_obj, HomologicalComplex₂.totalFunctor_obj,
      diag_obj_obj, NormalizedMooreComplex.obj_X, HomologicalComplex.comp_f,
      NatTrans.mapHomologicalComplex_app_f, Functor.mapHomologicalComplex_map_f,
      PInftyToNormalizedMooreComplex_f, normalizedMooreComplex_map, NormalizedMooreComplex.map_f,
      Category.assoc, Category.id_comp]
    -- `ezComponent_awComponent_comp_retraction` is stated in clean chain-map form, but the goal
    -- was put in simp-nf (retraction `R'` unfolded into `factorThru`/`arrow`). Normalize the
    -- instantiated lemma with the same simp set so its LHS matches, then close past `ιTotal`.
    have key := ezComponent_awComponent_comp_retraction X r m
    simp only [Functor.mapHomologicalComplex_obj_X, alternatingFaceMapComplex_obj_X,
      normalizedMooreComplex_obj, NormalizedMooreComplex.obj_X, HomologicalComplex.comp_f,
      NatTrans.mapHomologicalComplex_app_f, Functor.mapHomologicalComplex_map_f,
      PInftyToNormalizedMooreComplex_f, normalizedMooreComplex_map, NormalizedMooreComplex.map_f]
      at key
    rw [reassoc_of% key]
  case offdiag =>
    -- Off-diagonal `b ≠ r`: `ez_{r,s} ≫ aw_{b,n-b}` factors through a degeneracy, killed by `R'_{b,n-b}`.
    --
    -- PLAN (mirrors the diagonal `(A)` machinery, but with a *mismatched* split):
    -- Expand `ezComponent r s = ∑_{μ : Shuffle r s} sign μ • (…)` and merge each summand's two
    -- outer (first-variable) legs and two inner (second-variable) legs by functoriality, exactly
    -- as `ezawSummand_merge` does on the diagonal. The merged legs are
    --   outer  `A := ι_front b (n-b) ≫ shuffleFstHom μ : ⦋b⦌ ⟶ ⦋r⦌`
    --   inner  `B := ι_back b (n-b) ≫ shuffleSndHom μ : ⦋n-b⦌ ⟶ ⦋s⦌`.
    -- A dimension count finishes it. Since `b ≠ r` and `r + s = n`:
    --   • `b > r`  ⟹  `A : ⦋b⦌ ⟶ ⦋r⦌` cannot be mono (`SimplexCategory.le_of_mono` would force
    --     `b ≤ r`), so the outer `PInfty` at level `b` kills it.
    --   • `b < r`  ⟹  `n - b = r + s - b > s`, so `B : ⦋n-b⦌ ⟶ ⦋s⦌` cannot be mono, so the inner
    --     `PInfty` at level `n-b` kills it.
    -- So every off-diagonal summand has exactly one dimension-dropping (non-injective) leg,
    -- annihilated by the corresponding `PInfty` in `R'`.
    --
    -- The hard glue already generalizes: the diagonal helpers are stated for endomorphisms
    -- `g : ⦋n⦌ ⟶ ⦋n⦌`, but they reduce to `AlgebraicTopology.DoldKan.degeneracy_comp_PInfty`, which
    -- is stated for arbitrary codomain `θ : ⦋n⦌ ⟶ Δ'` with `¬Mono θ` (and `…_assoc` for the
    -- precomposed form). So `A`, `B` (non-endo) are already supported.
    --
    -- IMPLEMENTATION STEPS:
    --   1. Generalize the 3 private glue helpers (`map_op_comp_PInftyToNormalizedMooreComplex_eq_zero`,
    --      `inner_/outer_map_op_comp_retraction_eq_zero`) to non-endo `g : ⦋m⦌ ⟶ ⦋n⦌`. Cheap, since
    --      the underlying Mathlib lemma needs no endo restriction. Diagonal + off-diagonal then share them.
    --   2. A merge lemma for mismatched splits: same proof shape as `ezawSummand_merge` but with
    --      independent `(r,s)` (shuffle) and `(b, n-b)` (front/back) indices, producing `A`, `B`.
    --      Wrinkle vs. diagonal: discharge the two `eqToHom` casts (`⦋b+(n-b)⦌ = ⦋n⦌ = ⦋r+s⦌`) first,
    --      probably via `generalize`/`subst` on `n - b` (cf. lines 665–668) or `eqToHom`-through-`X.map`.
    --   3. Off-diagonal summand-zero lemma mirroring `ezawSummand_comp_retraction_eq_zero`:
    --      `rcases Nat.lt_or_gt_of_ne hb`; `b > r` ⟹ `¬Mono A` (via `SimplexCategory.le_of_mono`) + outer
    --      kill; `b < r` ⟹ `¬Mono B` + inner kill.
    --   4. Assemble here: expand the sum (`simp only [ezComponent, Preadditive.sum_comp, …]`), then
    --      `Finset.sum_eq_zero` per-summand.
    -- Riskiest part: the `eqToHom` cast bookkeeping in step 2; the vanishing (3–4) is straightforward.
    intro b _ hb
    sorry

/-- **EM Thm 2.1a, first half (`f∇ = i`).** On normalized complexes the composite `∇ ≫ AW`
is the identity *strictly* — the degenerate cross-terms that obstruct this on the unnormalized
complex vanish modulo norms. -/
lemma normalizedShuffle_alexanderWhitney (X : BisimplicialObject C) :
    normalizedShuffleMap X ≫ normalizedAlexanderWhitney X = 𝟙 (N₁.obj X) := by
  simp only [normalizedShuffleMap, normalizedAlexanderWhitney, Category.assoc]
  rw [inclusionN₁_shuffleMap_diag_normalize_assoc,
    shuffleMap_alexanderWhitney_comp_retractionN₁, inclusionN₁_comp_retractionN₁]

/-- **EM Thm 2.1a, second half (`∂Φ + Φ∂ = ∇f − i`).** On normalized complexes the composite
`AW ≫ ∇` is chain homotopic to the identity via the Eilenberg–Mac Lane homotopy `Φ`. -/
noncomputable def homotopyNormalizedAlexanderWhitneyShuffle (X : BisimplicialObject C) :
    Homotopy (normalizedAlexanderWhitney X ≫ normalizedShuffleMap X) (𝟙 (N₂.obj X)) := sorry

/-- **Eilenberg–Zilber theorem on normalized complexes** (Eilenberg–Mac Lane II, Thm 2.1a).
The bi-normalized total complex is homotopy equivalent to the normalized Moore complex of the
diagonal. One direction is a strict identity; the other uses the EM homotopy. -/
noncomputable def eilenbergZilberNormalized (X : BisimplicialObject C) :
    HomotopyEquiv (N₁.obj X) (N₂.obj X) where
  hom := normalizedShuffleMap X
  inv := normalizedAlexanderWhitney X
  homotopyHomInvId := Homotopy.ofEq (normalizedShuffle_alexanderWhitney X)
  homotopyInvHomId := homotopyNormalizedAlexanderWhitneyShuffle X

end BisimplicialObject

end CategoryTheory
