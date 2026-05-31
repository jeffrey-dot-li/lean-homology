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

/-- **(A) EM `f∇ = i` modulo norms.** Unnormalized, `shuffleMap ≫ alexanderWhitney = 𝟙 + D` with
`D` landing in the degenerate subcomplex; the bi-normalized retraction `retractionN₁` annihilates
`D`, leaving `retractionN₁`. The combinatorial core is the shuffle pairing
`ezComponent ≫ awComponent` (diagonal `(r,s) = (p,q)` ↦ identity; off-diagonal ↦ degenerate). -/
lemma shuffleMap_alexanderWhitney_comp_retractionN₁ (X : BisimplicialObject C) :
    shuffleMap X ≫ alexanderWhitney X ≫ retractionN₁ X = retractionN₁ X := sorry

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
