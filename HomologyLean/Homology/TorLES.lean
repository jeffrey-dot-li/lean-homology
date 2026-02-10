/-
  Long exact sequence of Tor groups from a short exact sequence.

  Proof strategy (horseshoe lemma approach):
  1. Given a SES  0 → X₁ →[f] X₂ →[g] X₃ → 0, take projective resolutions P₁ → X₁, P₃ → X₃.
  2. Construct P₂ inductively with P₂(n) := P₁(n) ⊕ P₃(n):
     - The differential is block-triangular:
       d₂(n) = biprod.map d₁(n) d₃(n) + biprod.inr ≫ α(n) ≫ biprod.inl
     - The correction terms α(n) : P₃(n+1) → P₁(n) are constructed inductively
       so that d₂² = 0 and the augmentation is a chain map.
     - At degree 0: the augmentation P₂(0) → X₂ is given by
       (P₁(0) → X₁ →[f] X₂) + (P₃(0) →[lift] X₂) where the lift uses projectivity of P₃(0).
  3. The maps P₁ →[inl] P₂ →[snd] P₃ form a degreewise split SES of chain complexes.
  4. Tensor with M. Since the SES is degreewise split, tensoring preserves exactness.
  5. Apply composableArrows₅_exact to get the homology LES.
  6. Identify homology of M ⊗ Pᵢ with Tor_n(M, Xᵢ).
-/
import Mathlib.CategoryTheory.Monoidal.Tor
import Mathlib.Algebra.Homology.ShortComplex.ShortExact
import Mathlib.Algebra.Homology.HomologySequenceLemmas
import Mathlib.CategoryTheory.Abelian.Projective.Resolution
import Mathlib.Algebra.Homology.HomologicalComplexAbelian
import HomologyLean.Homology.Biprod


noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open HomologicalComplex HomologicalComplex.HomologySequence

universe v u

variable {C : Type u} [Category.{v} C] [MonoidalCategory C]
  [Abelian C] [MonoidalPreadditive C] [HasProjectiveResolutions C]

namespace HomologyLean.TorLES

/-! ## Step 1: The horseshoe construction

Given a SES `0 → X₁ → X₂ → X₃ → 0` and projective resolutions `P₁ → X₁`, `P₃ → X₃`,
we construct a projective resolution `P₂ → X₂` with `P₂(n) = P₁(n) ⊕ P₃(n)`,
together with chain maps `P₁ → P₂ → P₃` lifting `f` and `g`.

The differential on P₂ is block-triangular:
  d₂(n) = [[d₁(n), α(n)], [0, d₃(n)]]
where α(n) : P₃(n+1) → P₁(n) are correction terms satisfying
  d₃(n+1) ≫ α(n) + α(n+1) ≫ d₁(n) = 0
(a chain homotopy condition ensuring d₂² = 0). -/

/-- The section `X₃ → X₂` used at degree 0: since `P₃(0)` is projective and
`g : X₂ → X₃` is epi, there is a lift of `P₃.π.f 0 : P₃(0) → X₃` through `g`. -/
def liftToX₂ {S : ShortComplex C} (hS : S.ShortExact)
    (P₃ : ProjectiveResolution S.X₃) : P₃.complex.X 0 ⟶ S.X₂ := by
  have := hS.epi_g
  exact Projective.factorThru (P₃.π.f 0) S.g

omit [MonoidalCategory C] [MonoidalPreadditive C] [HasProjectiveResolutions C] in
@[simp]
theorem liftToX₂_comp_g {S : ShortComplex C} (hS : S.ShortExact)
    (P₃ : ProjectiveResolution S.X₃) :
    liftToX₂ hS P₃ ≫ S.g = P₃.π.f 0 := by
  simp [liftToX₂, Projective.factorThru_comp]

/-- The augmentation map `P₁(0) ⊕ P₃(0) → X₂`:
sends `(a, b)` to `f(ε₁(a)) + lift(b)` where `ε₁ : P₁(0) → X₁` is the augmentation
and `lift : P₃(0) → X₂` is the projective lift. -/
def horseshoeAug {S : ShortComplex C} (hS : S.ShortExact)
    (P₁ : ProjectiveResolution S.X₁) (P₃ : ProjectiveResolution S.X₃) :
    P₁.complex.X 0 ⊞ P₃.complex.X 0 ⟶ S.X₂ :=
  biprod.desc (P₁.π.f 0 ≫ S.f) (liftToX₂ hS P₃)

/-! ### Correction terms for the horseshoe differential

The correction terms `α(n) : P₃(n+1) → P₁(n)` are constructed inductively:
- `α(0)` is chosen so that `d₃(0) ≫ liftToX₂ + α(0) ≫ P₁.π.f 0 ≫ f = 0`,
  using projectivity of `P₃(1)` and exactness of `0 → X₁ → X₂ → X₃ → 0`.
- `α(n+1)` is chosen so that `d₃(n+1) ≫ α(n) + α(n+1) ≫ d₁(n) = 0`,
  using projectivity of `P₃(n+2)` and exactness of P₁ at degree n. -/

/-- The base case correction term `α(0) : P₃(1) → P₁(0)`.
Extracted so its properties can be used in the inductive construction. -/
def horseshoeCorrection₀ {S : ShortComplex C} (hS : S.ShortExact)
    (P₁ : ProjectiveResolution S.X₁) (P₃ : ProjectiveResolution S.X₃) :
    P₃.complex.X 1 ⟶ P₁.complex.X 0 := by
  have := P₃.projective 1
  have := hS.mono_f
  exact Projective.factorThru
    (hS.exact.lift (-(P₃.complex.d 1 0 ≫ liftToX₂ hS P₃)) (by
      simp [liftToX₂_comp_g]))
    (P₁.π.f 0)

omit [MonoidalCategory C] [MonoidalPreadditive C] [HasProjectiveResolutions C] in
/-- Key property of `horseshoeCorrection₀`:
`d₃(2,1) ≫ α(0) ≫ π.f 0 = 0`, which enables the inductive step. -/
theorem horseshoeCorrection₀_property {S : ShortComplex C} (hS : S.ShortExact)
    (P₁ : ProjectiveResolution S.X₁) (P₃ : ProjectiveResolution S.X₃) :
    P₃.complex.d 2 1 ≫ horseshoeCorrection₀ hS P₁ P₃ ≫ P₁.π.f 0 = 0 := by
  have := hS.mono_f
  unfold horseshoeCorrection₀
  rw [Projective.factorThru_comp]
  apply (cancel_mono S.f).mp
  simp [Category.assoc, ShortComplex.Exact.lift_f,
    P₃.complex.d_comp_d_assoc]

/-- The inductive invariant for the horseshoe correction construction.
- At `n = 0`: `d₃(2,1) ≫ α ≫ P₁.π.f 0 = 0`
- At `n + 1`: `d₃(n+3,n+2) ≫ α ≫ d₁(n+1,n) = 0` -/
@[simp]
def horseshoeCorrectionProp {S : ShortComplex C}
    (P₁ : ProjectiveResolution S.X₁) (P₃ : ProjectiveResolution S.X₃) :
    (n : ℕ) → (α : P₃.complex.X (n + 1) ⟶ P₁.complex.X n) → Prop
  | 0, α => P₃.complex.d 2 1 ≫ α ≫ P₁.π.f 0 = 0
  | n + 1, α => P₃.complex.d (n + 3) (n + 2) ≫ α ≫ P₁.complex.d (n + 1) n = 0

/-- The correction terms bundled with the inductive invariant. -/
private def horseshoeCorrectionAux {S : ShortComplex C} (hS : S.ShortExact)
    (P₁ : ProjectiveResolution S.X₁) (P₃ : ProjectiveResolution S.X₃) :
    ∀ n : ℕ, { α : P₃.complex.X (n + 1) ⟶ P₁.complex.X n //
      horseshoeCorrectionProp P₁ P₃ n α }
  | 0 => ⟨horseshoeCorrection₀ hS P₁ P₃, by
      simp only [horseshoeCorrectionProp]
      exact horseshoeCorrection₀_property hS P₁ P₃⟩
  | 1 => by
    have ⟨α₀, hα₀⟩ := horseshoeCorrectionAux hS P₁ P₃ 0
    simp only [horseshoeCorrectionProp] at hα₀
    have := P₃.projective 2
    refine ⟨P₁.exact₀.liftFromProjective (-(P₃.complex.d 2 1 ≫ α₀))
      (by rw [Preadditive.neg_comp, neg_eq_zero]; simp only [Nat.reduceAdd,
        ChainComplex.single₀_obj_zero, Category.assoc]; exact hα₀), ?_⟩
    simp only [horseshoeCorrectionProp]
    rw [ShortComplex.Exact.liftFromProjective_comp]
    simp [P₃.complex.d_comp_d_assoc]
  | n + 2 => by
    obtain ⟨αprev, hprev⟩ := horseshoeCorrectionAux hS P₁ P₃ (n + 1)
    simp only [horseshoeCorrectionProp] at hprev
    have := P₃.projective (n + 3)
    refine ⟨(P₁.exact_succ n).liftFromProjective (-(P₃.complex.d (n + 3) (n + 2) ≫ αprev))
      (by rw [Preadditive.neg_comp, neg_eq_zero]; simp only [Category.assoc]; exact hprev), ?_⟩
    simp only [horseshoeCorrectionProp]
    rw [ShortComplex.Exact.liftFromProjective_comp]
    simp [P₃.complex.d_comp_d_assoc]

/-- The correction terms `α(n) : P₃(n+1) → P₁(n)` for the horseshoe differential.
These satisfy `d₃(n+1) ≫ α(n) + α(n+1) ≫ d₁(n) = 0` (chain homotopy condition)
and the augmentation compatibility `d₃(0) ≫ liftToX₂ + α(0) ≫ P₁.π.f 0 ≫ f = 0`. -/
def horseshoeCorrection {S : ShortComplex C} (hS : S.ShortExact)
    (P₁ : ProjectiveResolution S.X₁) (P₃ : ProjectiveResolution S.X₃)
    (n : ℕ) : P₃.complex.X (n + 1) ⟶ P₁.complex.X n :=
  (horseshoeCorrectionAux hS P₁ P₃ n).1

omit [MonoidalCategory C] [MonoidalPreadditive C] [HasProjectiveResolutions C] in
/-- The augmentation compatibility for the correction terms:
`d₃(0) ≫ liftToX₂ + α(0) ≫ P₁.π.f 0 ≫ f = 0`. -/
lemma horseshoeCorrection_aug {S : ShortComplex C} (hS : S.ShortExact)
    (P₁ : ProjectiveResolution S.X₁) (P₃ : ProjectiveResolution S.X₃) :
    P₃.complex.d 1 0 ≫ liftToX₂ hS P₃ +
      horseshoeCorrection hS P₁ P₃ 0 ≫ P₁.π.f 0 ≫ S.f = 0 := by
  unfold horseshoeCorrection horseshoeCorrectionAux horseshoeCorrection₀
  simp [ShortComplex.Exact.lift_f]

omit [MonoidalCategory C] [MonoidalPreadditive C] [HasProjectiveResolutions C] in
/-- The chain homotopy condition for the correction terms:
`d₃(n+1) ≫ α(n) + α(n+1) ≫ d₁(n) = 0`. -/
lemma horseshoeCorrection_chain {S : ShortComplex C} (hS : S.ShortExact)
    (P₁ : ProjectiveResolution S.X₁) (P₃ : ProjectiveResolution S.X₃) (n : ℕ) :
    P₃.complex.d (n + 2) (n + 1) ≫ horseshoeCorrection hS P₁ P₃ n +
      horseshoeCorrection hS P₁ P₃ (n + 1) ≫ P₁.complex.d (n + 1) n = 0 := by
  simp only [horseshoeCorrection]
  cases n with
  | zero =>
    change P₃.complex.d 2 1 ≫ (horseshoeCorrectionAux hS P₁ P₃ 0).1 +
      (horseshoeCorrectionAux hS P₁ P₃ 1).1 ≫ P₁.complex.d 1 0 = 0
    simp only [horseshoeCorrectionAux]
    rw [ShortComplex.Exact.liftFromProjective_comp]
    simp
  | succ n =>
    change P₃.complex.d (n + 3) (n + 2) ≫ (horseshoeCorrectionAux hS P₁ P₃ (n + 1)).1 +
      (horseshoeCorrectionAux hS P₁ P₃ (n + 2)).1 ≫ P₁.complex.d (n + 2) (n + 1) = 0
    simp only [horseshoeCorrectionAux]
    rw [ShortComplex.Exact.liftFromProjective_comp]
    simp

/-! ### Horseshoe complex construction

We build the chain complex with objects `P₁(n) ⊕ P₃(n)` and block-triangular differentials
`biprod.map d₁ d₃ + biprod.snd ≫ α ≫ biprod.inl`. -/

/-- The differential of the horseshoe complex:
`d₂(n) = biprod.map d₁(n) d₃(n) + biprod.snd ≫ α(n) ≫ biprod.inl`
which in matrix form is `[[d₁, α], [0, d₃]]`. -/
def horseshoeDiff {S : ShortComplex C} (hS : S.ShortExact)
    (P₁ : ProjectiveResolution S.X₁) (P₃ : ProjectiveResolution S.X₃) (n : ℕ) :
    P₁.complex.X (n + 1) ⊞ P₃.complex.X (n + 1) ⟶ P₁.complex.X n ⊞ P₃.complex.X n :=
  biprod.map (P₁.complex.d (n + 1) n) (P₃.complex.d (n + 1) n) +
    biprod.snd ≫ horseshoeCorrection hS P₁ P₃ n ≫ biprod.inl


lemma horseshoeDiffCompEq0 {S : ShortComplex C} (hS : S.ShortExact)
    (P₁ : ProjectiveResolution S.X₁) (P₃ : ProjectiveResolution S.X₃) (n : ℕ) :
    horseshoeDiff hS P₁ P₃ (n+1) ≫ horseshoeDiff hS P₁ P₃ (n) = 0 := by
    unfold horseshoeDiff
    simp?
    apply (biprod.hom_ext _ _)
    case h₀ =>
      simp only [Preadditive.add_comp, Category.assoc, BinaryBicone.inl_fst, Category.comp_id,
        zero_comp]
      rw [← Preadditive.comp_add,
        add_comm (horseshoeCorrection hS P₁ P₃ (n + 1) ≫ _),
        horseshoeCorrection_chain, comp_zero]
    case h₁ =>
      simp [Preadditive.add_comp, Category.assoc]
/-- The horseshoe chain complex with objects `P₁(n) ⊕ P₃(n)` and
block-triangular differentials. -/
def horseshoeComplex {S : ShortComplex C} (hS : S.ShortExact)
    (P₁ : ProjectiveResolution S.X₁) (P₃ : ProjectiveResolution S.X₃) :
    ChainComplex C ℕ := by
  exact ChainComplex.of
    (fun n => P₁.complex.X n ⊞ P₃.complex.X n)
    (fun n => horseshoeDiff hS P₁ P₃ n)
    (fun n => by
      simp only
      apply (horseshoeDiffCompEq0 hS P₁ P₃ _)
    )


/-- The differential of `horseshoeComplex` is `horseshoeDiff`. -/
theorem horseshoeComplex_d {S : ShortComplex C} (hS : S.ShortExact)
    (P₁ : ProjectiveResolution S.X₁) (P₃ : ProjectiveResolution S.X₃) (n : ℕ) :
    (horseshoeComplex hS P₁ P₃).d (n + 1) n = horseshoeDiff hS P₁ P₃ n :=
  ChainComplex.of_d _ _ _ n

/-- `biprod.inl` commutes with the horseshoe differential (since the correction
is in the upper-right block, `inl ≫ d₂ = d₁ ≫ inl`). -/
theorem horseshoeComplex_inl_comm {S : ShortComplex C} (hS : S.ShortExact)
    (P₁ : ProjectiveResolution S.X₁) (P₃ : ProjectiveResolution S.X₃) (n : ℕ) :
    biprod.inl ≫ (horseshoeComplex hS P₁ P₃).d (n + 1) n =
      P₁.complex.d (n + 1) n ≫ biprod.inl := by
  rw [horseshoeComplex_d]
  simp [horseshoeDiff]

/-- `biprod.snd` commutes with the horseshoe differential (since the correction
is in the upper-right block, `d₂ ≫ snd = snd ≫ d₃`). -/
theorem horseshoeComplex_snd_comm {S : ShortComplex C} (hS : S.ShortExact)
    (P₁ : ProjectiveResolution S.X₁) (P₃ : ProjectiveResolution S.X₃) (n : ℕ) :
    (horseshoeComplex hS P₁ P₃).d (n + 1) n ≫ biprod.snd =
      biprod.snd ≫ P₃.complex.d (n + 1) n := by
  rw [horseshoeComplex_d]
  simp [horseshoeDiff]

/-- The augmentation `horseshoeComplex → single₀(X₂)`. -/
def horseshoeπ {S : ShortComplex C} (hS : S.ShortExact)
    (P₁ : ProjectiveResolution S.X₁) (P₃ : ProjectiveResolution S.X₃) :
    horseshoeComplex hS P₁ P₃ ⟶ (ChainComplex.single₀ C).obj S.X₂ :=
  (ChainComplex.toSingle₀Equiv _ _).symm ⟨horseshoeAug hS P₁ P₃, by
    rw [horseshoeComplex_d, horseshoeDiff, horseshoeAug]
    -- d₂(0) ≫ aug = (biprod.map d₁ d₃ + inr ≫ α ≫ inl) ≫ biprod.desc (ε₁ ≫ f) (lift) = 0
    apply biprod.hom_ext'
    · -- inl component: d₁ ≫ ε₁ ≫ f = 0
      simp?
    · -- inr component: d₃ ≫ lift + α(0) ≫ ε₁ ≫ f = 0
      simp only [Nat.reduceAdd, ChainComplex.single₀_obj_zero, Preadditive.add_comp, Category.assoc,
        biprod.inl_desc, Preadditive.comp_add, biprod.inr_map_assoc, biprod.inr_desc,
        BinaryBicone.inr_snd_assoc, comp_zero]
      exact horseshoeCorrection_aug hS P₁ P₃⟩

/-- Each object in the horseshoe complex is projective. -/
instance horseshoeComplex_projective {S : ShortComplex C} (hS : S.ShortExact)
    (P₁ : ProjectiveResolution S.X₁) (P₃ : ProjectiveResolution S.X₃)
    (n : ℕ) : Projective ((horseshoeComplex hS P₁ P₃).X n) := by
  change Projective (P₁.complex.X n ⊞ P₃.complex.X n)
  have := P₁.projective n
  have := P₃.projective n
  infer_instance

/-- The horseshoe chain complex is exact at degree `n + 1`. -/
theorem horseshoeComplex_exactAt_succ {S : ShortComplex C} (hS : S.ShortExact)
    (P₁ : ProjectiveResolution S.X₁)
    (P₃ : ProjectiveResolution S.X₃)
    (n : ℕ) :
    (horseshoeComplex hS P₁ P₃).ExactAt (n + 1) := by
  sorry

/-- The projective resolution of `X₂` with `P₂(n) = P₁(n) ⊕ P₃(n)`,
constructed via the horseshoe lemma. -/
def horseshoeResolution {S : ShortComplex C} (hS : S.ShortExact)
    (P₁ : ProjectiveResolution S.X₁)
    (P₃ : ProjectiveResolution S.X₃) :
    ProjectiveResolution S.X₂ where
  complex := horseshoeComplex hS P₁ P₃
  projective n := horseshoeComplex_projective hS P₁ P₃ n
  π := horseshoeπ hS P₁ P₃
  quasiIso := ⟨fun n => by
    cases n with
    | zero =>
      rw [ChainComplex.quasiIsoAt₀_iff, ShortComplex.quasiIso_iff_of_zeros']
      · sorry
      all_goals rfl
    | succ n =>
      rw [quasiIsoAt_iff_exactAt']
      · exact horseshoeComplex_exactAt_succ hS P₁ P₃ n
      · exact ChainComplex.exactAt_succ_single_obj _ _⟩

/-! ## Step 2: The degreewise split SES of chain complexes

The maps `P₁ →[inl] P₂ →[snd] P₃` form a short exact sequence of chain complexes
that is degreewise split (since P₂(n) = P₁(n) ⊕ P₃(n) by construction).

Note: `biprod.inl` is a chain map because the correction term is in the upper-right block,
so `inl ≫ d₂ = d₁ ≫ inl`. Similarly `biprod.snd` is a chain map because
`d₂ ≫ snd = snd ≫ d₃`. -/

/-- The chain map `P₁ → P₂` given by inclusion into the first component. -/
def horseshoeInl {S : ShortComplex C} (hS : S.ShortExact)
    (P₁ : ProjectiveResolution S.X₁)
    (P₃ : ProjectiveResolution S.X₃) :
    P₁.complex ⟶ (horseshoeResolution hS P₁ P₃).complex where
  f n := biprod.inl
  comm' i j hij := by
    obtain ⟨rfl⟩ : j + 1 = i := by
      simp only [ComplexShape.down_Rel] at hij; omega
    exact horseshoeComplex_inl_comm hS P₁ P₃ j

/-- The chain map `P₂ → P₃` given by projection onto the second component. -/
def horseshoeSnd {S : ShortComplex C} (hS : S.ShortExact)
    (P₁ : ProjectiveResolution S.X₁)
    (P₃ : ProjectiveResolution S.X₃) :
    (horseshoeResolution hS P₁ P₃).complex ⟶ P₃.complex where
  f n := biprod.snd
  comm' i j hij := by
    obtain ⟨rfl⟩ : j + 1 = i := by
      simp only [ComplexShape.down_Rel] at hij; omega
    exact (horseshoeComplex_snd_comm hS P₁ P₃ j).symm

/-- The chain map `P₁ →[inl] P₂` lifts `S.f`. -/
theorem horseshoeInl_commutes {S : ShortComplex C} (hS : S.ShortExact)
    (P₁ : ProjectiveResolution S.X₁)
    (P₃ : ProjectiveResolution S.X₃) :
    horseshoeInl hS P₁ P₃ ≫ (horseshoeResolution hS P₁ P₃).π =
      P₁.π ≫ (ChainComplex.single₀ C).map S.f := by
  ext
  simp [comp_f, horseshoeInl, horseshoeResolution, horseshoeπ, horseshoeAug,
    ChainComplex.toSingle₀Equiv]

/-- The chain map `P₂ →[snd] P₃` lifts `S.g`. -/
theorem horseshoeSnd_commutes {S : ShortComplex C} (hS : S.ShortExact)
    (P₁ : ProjectiveResolution S.X₁)
    (P₃ : ProjectiveResolution S.X₃) :
    horseshoeSnd hS P₁ P₃ ≫ P₃.π =
      (horseshoeResolution hS P₁ P₃).π ≫ (ChainComplex.single₀ C).map S.g := by
  ext
  -- Use biprod.hom_ext' to decompose maps from the biproduct
  simp only [comp_f, horseshoeSnd, horseshoeResolution, horseshoeπ, horseshoeAug,
    ChainComplex.toSingle₀Equiv]
  apply biprod.hom_ext'
  · simp [S.zero]
  · simp

/-- The short complex of chain complexes `P₁ → P₂ → P₃`. -/
def horseshoeSES {S : ShortComplex C} (hS : S.ShortExact)
    (P₁ : ProjectiveResolution S.X₁)
    (P₃ : ProjectiveResolution S.X₃) :
    ShortComplex (HomologicalComplex C (ComplexShape.down ℕ)) :=
  ShortComplex.mk
    (horseshoeInl hS P₁ P₃)
    (horseshoeSnd hS P₁ P₃)
    (by
      ext n
      simp [horseshoeInl, horseshoeSnd])

/-- The degreewise splitting of the horseshoe SES. -/
def horseshoeSES_splitting {S : ShortComplex C} (hS : S.ShortExact)
    (P₁ : ProjectiveResolution S.X₁)
    (P₃ : ProjectiveResolution S.X₃) (n : ℕ) :
    ((horseshoeSES hS P₁ P₃).map (eval C _ n)).Splitting := by
  refine ShortComplex.Splitting.ofIso
    (ShortComplex.Splitting.ofHasBinaryBiproduct (P₁.complex.X n) (P₃.complex.X n))
    (ShortComplex.isoMk (Iso.refl _) (Iso.refl _) (Iso.refl _) ?_ ?_)
  · simp [horseshoeSES, horseshoeInl]
  · simp [horseshoeSES, horseshoeSnd]

/-- The horseshoe SES is short exact. This is immediate since it is
degreewise split (P₂(n) = P₁(n) ⊕ P₃(n) with inl and snd). -/
theorem horseshoeSES_shortExact {S : ShortComplex C} (hS : S.ShortExact)
    (P₁ : ProjectiveResolution S.X₁)
    (P₃ : ProjectiveResolution S.X₃) :
    (horseshoeSES hS P₁ P₃).ShortExact :=
  HomologicalComplex.shortExact_of_degreewise_shortExact _ fun n => by
    have σ := horseshoeSES_splitting hS P₁ P₃ n
    exact {
      exact := σ.exact
      mono_f := σ.mono_f
      epi_g := σ.epi_g
    }

/-! ## Step 3: Tensor with M -/

/-- Apply `M ⊗ -` degreewise to a chain complex. -/
abbrev tensorComplex (M : C) (P : ChainComplex C ℕ) : ChainComplex C ℕ :=
  (((tensoringLeft C).obj M).mapHomologicalComplex _).obj P

/-- The SES of chain complexes obtained by tensoring the horseshoe SES with M.
Since the horseshoe SES is degreewise split, tensoring preserves exactness. -/
def tensoredSES {S : ShortComplex C} (hS : S.ShortExact) (M : C)
    (P₁ : ProjectiveResolution S.X₁)
    (P₃ : ProjectiveResolution S.X₃) :
    ShortComplex (HomologicalComplex C (ComplexShape.down ℕ)) :=
  ((((tensoringLeft C).obj M).mapHomologicalComplex _).mapShortComplex).obj
    (horseshoeSES hS P₁ P₃)

/-- The tensored SES is short exact because the horseshoe SES is degreewise split. -/
theorem tensoredSES_shortExact {S : ShortComplex C} (hS : S.ShortExact) (M : C)
    (P₁ : ProjectiveResolution S.X₁)
    (P₃ : ProjectiveResolution S.X₃) :
    (tensoredSES hS M P₁ P₃).ShortExact := by
  apply HomologicalComplex.shortExact_of_degreewise_shortExact
  intro n
  -- The tensored SES at degree n is (horseshoe SES at degree n) mapped through (M ⊗ -)
  -- which is a split short exact sequence
  have σ := (horseshoeSES_splitting hS P₁ P₃ n).map ((tensoringLeft C).obj M)
  -- The two short complexes are isomorphic
  have e : ((horseshoeSES hS P₁ P₃).map (eval C _ n)).map ((tensoringLeft C).obj M) ≅
      (tensoredSES hS M P₁ P₃).map (eval C _ n) :=
    ShortComplex.isoMk (Iso.refl _) (Iso.refl _) (Iso.refl _) (by aesop_cat) (by aesop_cat)
  have hse := ShortComplex.Splitting.ofIso σ e
  exact {
    exact := hse.exact
    mono_f := hse.mono_f
    epi_g := hse.epi_g
  }

/-! ## Step 4: Apply the homology LES -/

/-- The 6-term exact sequence of homology groups from the tensored horseshoe SES. -/
def homologyLES {S : ShortComplex C} (hS : S.ShortExact) (M : C)
    (P₁ : ProjectiveResolution S.X₁)
    (P₃ : ProjectiveResolution S.X₃)
    (i j : ℕ) (hij : (ComplexShape.down ℕ).Rel i j) :
    ComposableArrows C 5 :=
  composableArrows₅ (tensoredSES_shortExact hS M P₁ P₃) i j hij

theorem homologyLES_exact {S : ShortComplex C} (hS : S.ShortExact) (M : C)
    (P₁ : ProjectiveResolution S.X₁)
    (P₃ : ProjectiveResolution S.X₃)
    (i j : ℕ) (hij : (ComplexShape.down ℕ).Rel i j) :
    (homologyLES hS M P₁ P₃ i j hij).Exact :=
  composableArrows₅_exact (tensoredSES_shortExact hS M P₁ P₃) i j hij

/-! ## Step 5: Identify homology of M ⊗ Pᵢ with Tor -/

/-- The homology of `M ⊗ P` at degree `n` is `Tor_n(M, X)`. -/
def homologyTensorIso {X : C} (M : C) (P : ProjectiveResolution X) (n : ℕ) :
    (tensorComplex M P.complex).homology n ≅ ((Tor C n).obj M).obj X :=
  (P.isoLeftDerivedObj ((tensoringLeft C).obj M) n).symm

/-! ## Step 6: Final assembly -/

/-- The 6-term exact sequence of Tor groups. -/
def torLES {S : ShortComplex C} (hS : S.ShortExact) (M : C)
    (n₀ n₁ : ℕ) (h : n₀ + 1 = n₁) :
    ComposableArrows C 5 := by
  have P₁ := (HasProjectiveResolution.out (Z := S.X₁)).some
  have P₃ := (HasProjectiveResolution.out (Z := S.X₃)).some
  have hij : (ComplexShape.down ℕ).Rel n₁ n₀ := by
    simp [ComplexShape.down_Rel]; omega
  exact homologyLES hS M P₁ P₃ n₁ n₀ hij

/-- The 6-term Tor sequence is exact. -/
theorem torLES_exact {S : ShortComplex C} (hS : S.ShortExact) (M : C)
    (n₀ n₁ : ℕ) (h : n₀ + 1 = n₁) :
    (torLES hS M n₀ n₁ h).Exact := by
  simp only [torLES]
  exact homologyLES_exact hS M _ _ _ _ _

end HomologyLean.TorLES
