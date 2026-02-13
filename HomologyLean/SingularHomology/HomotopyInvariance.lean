/-
  Homotopy Invariance of singular homology.

  Homotopic maps f, g : X → Y induce equal maps on singular homology:
    H_n(f) = H_n(g) : H_n(X; R) → H_n(Y; R)

  The proof factors through the "prism chain homotopy":
  1. Define inclusions ι₀, ι₁ : X → I × X at time 0 and 1.
  2. View the topological homotopy H as a TopCat morphism I × X → Y.
  3. Construct a chain homotopy P between C_*(ι₀) and C_*(ι₁) using the
     standard triangulation of Δⁿ × I into (n+1) simplices.
  4. Compose P with C_*(H) to get a chain homotopy between C_*(f) and C_*(g),
     using H ∘ ι₀ = f and H ∘ ι₁ = g.

  The prism operator P is built from "prism simplices": for each n-simplex
  σ : Δⁿ → X and i ∈ {0,...,n}, the i-th prism (n+1)-simplex in I × X is
    τᵢ(σ) : Δⁿ⁺¹ → I × X,  p ↦ (tᵢ(p), σ(sᵢ(p)))
  where sᵢ = σᵢ (degeneracy) and tᵢ(p) = p_{i+1} + ... + p_{n+1}.
-/
import Mathlib.AlgebraicTopology.SingularHomology.Basic
import Mathlib.Topology.Homotopy.Basic
import Mathlib.Algebra.Homology.Homotopy
import Mathlib.Topology.UnitInterval

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicTopology unitInterval

universe u v

variable (C : Type u) [Category.{v} C] [HasCoproducts C] [Preadditive C]
  [CategoryWithHomology C]

namespace HomologyLean.SingularHomology

/-! ## Layer 0: Topological plumbing

Inclusions of X into I × X at time 0 and 1, and the homotopy as a
TopCat morphism. -/

/-- Inclusion of X into I × X at time 0: x ↦ (0, x). -/
def topInclusion₀ (X : TopCat.{v}) : X ⟶ TopCat.of (I × X) :=
  ⟨⟨fun x => (⟨0, unitInterval.zero_mem⟩, x), by fun_prop⟩⟩

/-- Inclusion of X into I × X at time 1: x ↦ (1, x). -/
def topInclusion₁ (X : TopCat.{v}) : X ⟶ TopCat.of (I × X) :=
  ⟨⟨fun x => (⟨1, unitInterval.one_mem⟩, x), by fun_prop⟩⟩

/-- A `ContinuousMap.Homotopy` viewed as a TopCat morphism `I × X ⟶ Y`. -/
def homotopyToMorphism {X Y : TopCat.{v}} {f g : X ⟶ Y}
    (H : ContinuousMap.Homotopy f.hom' g.hom') :
    TopCat.of (I × X) ⟶ Y :=
  ⟨H.toContinuousMap⟩

/-- `H ∘ ι₀ = f`: composing the homotopy with inclusion at 0 gives `f`. -/
lemma homotopyToMorphism_comp_topInclusion₀ {X Y : TopCat.{v}} {f g : X ⟶ Y}
    (H : ContinuousMap.Homotopy f.hom' g.hom') :
    topInclusion₀ X ≫ homotopyToMorphism H = f := by
  ext x; exact H.map_zero_left x

/-- `H ∘ ι₁ = g`: composing the homotopy with inclusion at 1 gives `g`. -/
lemma homotopyToMorphism_comp_topInclusion₁ {X Y : TopCat.{v}} {f g : X ⟶ Y}
    (H : ContinuousMap.Homotopy f.hom' g.hom') :
    topInclusion₁ X ≫ homotopyToMorphism H = g := by
  ext x; exact H.map_one_left x

/-! ## Layer 1: Prism chain homotopy

The chain homotopy between C_*(ι₀) and C_*(ι₁), where ι₀, ι₁ : X → I × X
are the inclusions at time 0 and 1. This is the core geometric construction.

**Construction**: For each n-simplex σ : Δⁿ → X and i ∈ {0,...,n}, define
the i-th prism (n+1)-simplex τᵢ(σ) : Δⁿ⁺¹ → I × X by
  τᵢ(σ)(p) = (p_{i+1} + ... + p_{n+1}, σ(sᵢ(p)))
where sᵢ is the topological realization of the i-th degeneracy map.
The prism operator sends σ to ∑ᵢ (-1)ⁱ τᵢ(σ).

**Boundary formula**: ∂P + P∂ = ι₁* - ι₀* follows from face-prism
identities and telescoping. -/

/-- The i-th prism simplex: given a singular n-simplex `s` of `X`, produces
a singular (n+1)-simplex of `I × X`.

Geometrically, `prismSimplex X n i s` maps `p ∈ Δⁿ⁺¹` to
`(p_{i+1} + ⋯ + p_{n+1}, s(sᵢ(p)))` where `sᵢ` is the i-th degeneracy. -/
def prismSimplex (X : TopCat.{v}) (n : ℕ) (_i : Fin (n + 1))
    (s : (TopCat.toSSet.obj X).obj (Opposite.op (SimplexCategory.mk n))) :
    (TopCat.toSSet.obj (TopCat.of (I × X))).obj
      (Opposite.op (SimplexCategory.mk (n + 1))) :=
  by
    let i := _i
    let simplexMap := TopCat.toSSetObjEquiv X (Opposite.op (SimplexCategory.mk n)) s
    let degen :
        C(stdSimplex ℝ (Fin (n + 2)), stdSimplex ℝ (Fin (n + 1))) :=
      ⟨stdSimplex.map (SimplexCategory.σ i).toOrderHom, stdSimplex.continuous_map _⟩
    let xMap : C(stdSimplex ℝ (Fin (n + 2)), X) := simplexMap.comp degen
    let tMap : C(stdSimplex ℝ (Fin (n + 2)), I) := by
      refine ⟨fun p => ?_, ?_⟩
      · refine ⟨∑ j : Fin (n + 2), if i.succ ≤ j then p j else 0, ?_, ?_⟩
        · refine Finset.sum_nonneg ?_
          intro j _
          by_cases h : i.succ ≤ j
          · simp [h]
          · simp [h]
        · have hle :
            (∑ j : Fin (n + 2), if i.succ ≤ j then p j else 0) ≤ ∑ j : Fin (n + 2), p j := by
            refine Finset.sum_le_sum ?_
            intro j _
            by_cases h : i.succ ≤ j
            · simp [h]
            · simp [h]
          simpa using hle.trans_eq p.2.2
      · refine Continuous.subtype_mk ?_ ?_
        · refine continuous_finset_sum _ (fun j _ => ?_)
          by_cases h : i.succ ≤ j
          · simpa [h] using
              ((continuous_apply j).comp continuous_subtype_val : Continuous
                (fun p : stdSimplex ℝ (Fin (n + 2)) => p.1 j))
          · simpa [h] using
              (continuous_const : Continuous
                (fun _ : stdSimplex ℝ (Fin (n + 2)) => (0 : ℝ)))
    refine (TopCat.toSSetObjEquiv (TopCat.of (I × X))
      (Opposite.op (SimplexCategory.mk (n + 1)))).symm ?_
    exact ⟨fun p => (tMap p, xMap p), by fun_prop⟩

/-- The prism operator at degree n: sends `C_n(X; R) → C_{n+1}(I × X; R)`.

For each singular n-simplex `s`, sends it to the signed sum
`∑ᵢ (-1)^{i+1} · ι(prismSimplex X n i s)` in the target coproduct.

Note: the sign is `(-1)^{i+1}` (not `(-1)^i`) because the Mathlib `Homotopy f g`
convention is `f - g = dP + Pd`, while the standard prism operator `∑ (-1)^i`
satisfies `dP + Pd = ι₁ - ι₀`. Negating gives `d(-P) + (-P)d = ι₀ - ι₁`. -/
def prismOperator (R : C) (X : TopCat.{v}) (n : ℕ) :
    (((singularChainComplexFunctor C).obj R).obj X).X n ⟶
      (((singularChainComplexFunctor C).obj R).obj (TopCat.of (I × X))).X (n + 1) :=
  Sigma.desc (fun s =>
    ∑ i : Fin (n + 1),
      ((-1 : ℤ) ^ ((i : ℕ) + 1)) • Sigma.ι (fun _ => R) (prismSimplex X n i s))

/-- The hom data for the prism chain homotopy.
Equals `prismOperator` when `j = i + 1` and `0` otherwise. -/
def prismHom (R : C) (X : TopCat.{v}) (i j : ℕ) :
    (((singularChainComplexFunctor C).obj R).obj X).X i ⟶
      (((singularChainComplexFunctor C).obj R).obj (TopCat.of (I × X))).X j :=
  if h : j = i + 1 then h ▸ prismOperator C R X i else 0

omit [CategoryWithHomology C] in
/-- The prism hom data vanishes except when `j = i + 1`. -/
lemma prismHom_zero (R : C) (X : TopCat.{v}) (i j : ℕ)
    (h : ¬(ComplexShape.down ℕ).Rel j i) :
    prismHom C R X i j = 0 := by
  unfold prismHom; split_ifs with heq <;> simp_all [ComplexShape.down_Rel]

/-
Roadmap lemmas for the prism boundary proof.

These isolate the two sources of complexity:
1. simplicial index algebra (`δ`/`σ` interaction formulas),
2. sign bookkeeping (pairwise cancellation and telescoping).

The intended flow for the final `prismHom_boundary_decompose` proof is:
* expand boundaries of each prism term into face terms;
* rewrite face-index composites via the `simplex_δσ_*` lemmas;
* pair internal faces with opposite signs using `prism_sign_pair_cancel`;
* telescope remaining endpoint faces to `topInclusion₀` and `topInclusion₁`.
-/

/-! ### Chain complex API helpers -/

-- Helper: Sigma.ι composed with a singular chain map
omit [CategoryWithHomology C] in
lemma singularChainMap_ι (R : C) {X Y : TopCat.{v}} (f : X ⟶ Y) (n : ℕ)
    (s : (TopCat.toSSet.obj X).obj (Opposite.op (SimplexCategory.mk n))) :
    Sigma.ι (fun _ => R) s ≫ (((singularChainComplexFunctor C).obj R).map f).f n =
      Sigma.ι (fun _ => R)
        ((TopCat.toSSet.map f).app (Opposite.op (SimplexCategory.mk n)) s) := by
  simp [singularChainComplexFunctor, SSet.singularChainComplexFunctor,
    alternatingFaceMapComplex, AlternatingFaceMapComplex.map,
    Functor.postcompose₂, sigmaConst]

-- Helper: Sigma.ι composed with the boundary map
omit [CategoryWithHomology C] in
lemma singularChainComplex_d_ι (R : C) (X : TopCat.{v}) (n : ℕ)
    (s : (TopCat.toSSet.obj X).obj (Opposite.op (SimplexCategory.mk (n + 1)))) :
    Sigma.ι (fun _ => R) s ≫ (((singularChainComplexFunctor C).obj R).obj X).d (n + 1) n =
      ∑ j : Fin (n + 2), ((-1 : ℤ) ^ (j : ℕ)) •
        Sigma.ι (fun _ => R)
          ((TopCat.toSSet.obj X).map (SimplexCategory.δ j).op s) := by
  simp [singularChainComplexFunctor, SSet.singularChainComplexFunctor,
    alternatingFaceMapComplex, AlternatingFaceMapComplex.obj,
    AlternatingFaceMapComplex.objD, ChainComplex.of_d,
    Functor.postcompose₂, sigmaConst, SimplicialObject.δ,
    SimplicialObject.whiskering,
    Preadditive.comp_sum, Preadditive.comp_zsmul]

/-! ### Face-prism endpoint identities -/

variable {C} in
/-- Face 0 of the 0-th prism simplex gives the inclusion at time 1. -/
lemma face_prismSimplex_top (X : TopCat.{v}) (n : ℕ)
    (s : (TopCat.toSSet.obj X).obj (Opposite.op (SimplexCategory.mk n))) :
    (TopCat.toSSet.obj (TopCat.of (I × X))).map (SimplexCategory.δ 0).op
      (prismSimplex X n ⟨0, Nat.zero_lt_succ n⟩ s) =
    (TopCat.toSSet.map (topInclusion₁ X)).app (Opposite.op (SimplexCategory.mk n)) s := by
  -- Reduce to ContinuousMap equality via toSSetObjEquiv
  apply (TopCat.toSSetObjEquiv _ _).injective
  -- Both sides reduce to ContinuousMap compositions by rfl (see toSSetObjEquiv_map/naturality)
  -- LHS: toSSetObjEquiv ((toSSet Y).map (δ 0).op (prismSimplex s 0))
  --     = (toSSetObjEquiv (prismSimplex s 0)).comp (stdSimplex.map δ_0)
  -- RHS: toSSetObjEquiv ((toSSet.map ι₁).app (op [n]) s)
  --     = ι₁.comp (toSSetObjEquiv s)
  -- After applying toSSetObjEquiv to prismSimplex (which recovers the ContinuousMap),
  -- we need: ContinuousMap p ↦ (tMap(δ_0(p)), s(σ_0(δ_0(p)))) = ContinuousMap p ↦ (1, s(p))
  -- The goal reduces by rfl through the layers to ContinuousMap equality
  -- Use native_decide? No, let me try simp/congr
  -- Actually, since toSSetObjEquiv maps composition holds by rfl,
  -- both sides reduce to the same ContinuousMap
  -- LHS: fun p => (∑ j, if 1 ≤ j then (stdSimplex.map δ_0 p) j else 0, s(σ_0(stdSimplex.map δ_0 p)))
  -- RHS: fun p => (1, s(p))
  -- Need: ∑ j, if 1 ≤ j then (stdSimplex.map δ_0 p) j else 0 = 1
  -- and: s(σ_0(stdSimplex.map δ_0 p)) = s(p)
  -- Both sides are elements that toSSetObjEquiv maps to ContinuousMaps by rfl
  -- Just use ContinuousMap.ext after applying toSSetObjEquiv.injective
  ext ⟨p, hp⟩
  constructor
  · -- I-component: need to show the t-coordinates agree
    -- After δ_0, t = ∑_{j ≥ 1} (δ_0(p))_j = ∑ p_j = 1
    show (TopCat.toSSetObjEquiv _ _ ((TopCat.toSSet.obj _).map _ (prismSimplex X n _ s)) ⟨p, hp⟩).1 =
         (TopCat.toSSetObjEquiv _ _ ((TopCat.toSSet.map _).app _ s) ⟨p, hp⟩).1
    -- Both sides reduce definitionally via the rfl compatibility
    -- LHS = (prismSimplex' ∘ δ_0)(p).1 = ∑_{j≥1} (δ_0(p))_j
    -- RHS = (ι₁ ∘ s)(p).1 = 1
    sorry
  · -- X-component: uses σ_0 ∘ δ_0 = id
    sorry

variable {C} in
/-- Face (n+1) of the n-th prism simplex gives the inclusion at time 0. -/
lemma face_prismSimplex_bot (X : TopCat.{v}) (n : ℕ)
    (s : (TopCat.toSSet.obj X).obj (Opposite.op (SimplexCategory.mk n))) :
    (TopCat.toSSet.obj (TopCat.of (I × X))).map
      (SimplexCategory.δ (Fin.last (n + 1))).op
      (prismSimplex X n ⟨n, lt_add_one n⟩ s) =
    (TopCat.toSSet.map (topInclusion₀ X)).app (Opposite.op (SimplexCategory.mk n)) s := by
  apply (TopCat.toSSetObjEquiv (TopCat.of (I × X))
    (Opposite.op (SimplexCategory.mk n))).injective
  ext p
  sorry

lemma prismHom_comm (R : C) (X : TopCat.{v}) (i : ℕ) :
    (((singularChainComplexFunctor C).obj R).map (topInclusion₀ X)).f i =
      dNext i (prismHom C R X) + prevD i (prismHom C R X) +
        (((singularChainComplexFunctor C).obj R).map (topInclusion₁ X)).f i :=
  by
    sorry

/-- The prism chain homotopy between the chain maps induced by ι₀ and ι₁.

Assembled from `prismHom`, `prismHom_zero`, and `prismHom_comm`. -/
def prismChainHomotopy (R : C) (X : TopCat.{v}) :
    Homotopy
      (((singularChainComplexFunctor C).obj R).map (topInclusion₀ X))
      (((singularChainComplexFunctor C).obj R).map (topInclusion₁ X)) where
  hom := prismHom C R X
  zero _ _ h := prismHom_zero C R X _ _ h
  comm := prismHom_comm C R X

/-! ## Layer 2: Assembly

Compose the prism chain homotopy with C_*(H) and use the endpoint
conditions to get the final chain homotopy between C_*(f) and C_*(g). -/

omit [CategoryWithHomology C] in
/-- Functoriality: the chain map of a composition equals the composition
of the chain maps. -/
lemma singularChainMap_comp {X Y Z : TopCat.{v}} (R : C) (f : X ⟶ Y) (g : Y ⟶ Z) :
    ((singularChainComplexFunctor C).obj R).map (f ≫ g) =
      ((singularChainComplexFunctor C).obj R).map f ≫
        ((singularChainComplexFunctor C).obj R).map g := by
  exact Functor.map_comp _ f g

/-- A topological homotopy `H : f ≃ g` between continuous maps `f g : X → Y`
induces a chain homotopy between the chain maps `C_*(f)` and `C_*(g)`.

**Proof**: Compose the prism chain homotopy (between `C_*(ι₀)` and `C_*(ι₁)`)
with `C_*(H)`, then use `H ∘ ι₀ = f` and `H ∘ ι₁ = g` to rewrite. -/
def singularChain_chainHomotopy_of_homotopy {X Y : TopCat.{v}} {f g : X ⟶ Y}
    (R : C) (H : ContinuousMap.Homotopy f.hom' g.hom') :
    Homotopy
      (((singularChainComplexFunctor C).obj R).map f)
      (((singularChainComplexFunctor C).obj R).map g) := by
  have P := (prismChainHomotopy C R X).compRight
    (((singularChainComplexFunctor C).obj R).map (homotopyToMorphism H))
  rwa [← Functor.map_comp, ← Functor.map_comp,
    homotopyToMorphism_comp_topInclusion₀, homotopyToMorphism_comp_topInclusion₁] at P

/-! ## Homotopy invariance of singular homology -/

/-- Homotopic maps induce equal maps on singular homology.

This follows from `singularChain_chainHomotopy_of_homotopy` via
`Homotopy.homologyMap_eq`. -/
theorem singularHomology_map_eq_of_homotopy {X Y : TopCat.{v}} {f g : X ⟶ Y}
    (R : C) (H : ContinuousMap.Homotopy f.hom' g.hom') (n : ℕ) :
    ((singularHomologyFunctor C n).obj R).map f =
      ((singularHomologyFunctor C n).obj R).map g := by
  exact (singularChain_chainHomotopy_of_homotopy C R H).homologyMap_eq n

/-! ## Homotopy equivalences induce isomorphisms -/

/-- Homotopy equivalent spaces have isomorphic singular homology.

**Proof sketch**: `H_n(f) ∘ H_n(g) = H_n(g ≫ f) = H_n(𝟙 Y) = 𝟙` by
homotopy invariance and functoriality, and similarly for the other composite. -/
def singularHomology_iso_of_homotopyEquiv {X Y : TopCat.{v}} (R : C)
    (f : X ⟶ Y) (g : Y ⟶ X)
    (hfg : ContinuousMap.Homotopy (f ≫ g : X ⟶ X).hom' (𝟙 X : X ⟶ X).hom')
    (hgf : ContinuousMap.Homotopy (g ≫ f : Y ⟶ Y).hom' (𝟙 Y : Y ⟶ Y).hom')
    (n : ℕ) :
    ((singularHomologyFunctor C n).obj R).obj X ≅
      ((singularHomologyFunctor C n).obj R).obj Y where
  hom := ((singularHomologyFunctor C n).obj R).map f
  inv := ((singularHomologyFunctor C n).obj R).map g
  hom_inv_id := by
    rw [← Functor.map_comp, singularHomology_map_eq_of_homotopy C R hfg n]; simp
  inv_hom_id := by
    rw [← Functor.map_comp, singularHomology_map_eq_of_homotopy C R hgf n]; simp

end HomologyLean.SingularHomology
