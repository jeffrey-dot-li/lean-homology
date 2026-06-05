import HomologyLean.SingularHomology.BisimplicialNormalizedDefs
import Mathlib.Data.Finsupp.Basic
import Mathlib.Algebra.Category.ModuleCat.Abelian
import Mathlib.Algebra.Category.ModuleCat.Adjunctions

/-!
# Eilenberg–Mac Lane derived-operator API for the normalized Eilenberg–Zilber homotopy

This file builds the **tiny, local derived-operator API** needed to formalize Eilenberg–Mac Lane's
*recursive* construction of the Eilenberg–Zilber homotopy `Φ` (Eilenberg–Mac Lane II, Thm 2.1a,
the identity `∂Φ + Φ∂ = ∇f − i` modulo norms). It is the input to
`homotopyNormalizedAlexanderWhitneyShuffle` in `BisimplicialNormalized.lean`.

We deliberately **do not** use the explicit closed-form homotopy (`emHomotopy` in `Bisimplicial.lean`);
the literature only ever proves the contraction identity via the recursion + derived operators, so
we follow EM directly.

## Design

EM's "natural operators" `M : (K×L)_s → (K×L)_q` (their (2.10)) are, on a bisimplicial object `X`,
exactly finite `ℤ`-linear combinations of **letters**: a pair of `SimplexCategory` maps
`(β, γ) : ⟦q⟧ ⟶ ⟦s⟧` acting on the diagonal `F₂.obj X = diag X` by

`(X.obj ⟦s⟧).map γ.op ≫ (X.map β.op).app ⟦q⟧ : X_{s,s} ⟶ X_{q,q}`.

* `OpLetter s q` — one such pair, `DerivedOp s q := OpLetter s q →₀ ℤ` — a formal `ℤ`-combination.
* `DerivedOp.realize X` — realize a formal operator as an actual degreewise hom on `F₂.obj X`.
* `DerivedOp.prime` — EM's derived operator `M ↦ M'` (prepend the 0-th coface `δ⁰` to each letter).
* `DerivedOp.Frontal` — every letter fixes the bottom vertex (avoids the 0-th face `F₀`).

"Modulo norms" is represented (per the project's `PInfty` strategy) by postcomposing with
`retractionN₂ X = PInftyToNormalizedMooreComplex (diag X)`: a term is a *norm* iff it dies after
`≫ retractionN₂`.
-/

open AlgebraicTopology AlgebraicTopology.DoldKan CategoryTheory.Limits
open scoped Simplicial
open HomologyLean.SingularHomology

namespace CategoryTheory

namespace BisimplicialObject

variable {C : Type*} [Category C] [Abelian C]

/-! ### Operators as formal `ℤ`-combinations of letters -/

/-- A **letter**: a pair of `SimplexCategory` maps `⟦q⟧ ⟶ ⟦s⟧`. The `fst` map acts on the
horizontal (first / `K`) simplicial variable and `snd` on the vertical (second / `L`) one.
Realized on a bisimplicial object it gives a single summand `X_{s,s} ⟶ X_{q,q}` of an EM
natural operator (their (2.10)). -/
structure OpLetter (s q : ℕ) where
  /-- Horizontal (`K`-side) `SimplexCategory` map. -/
  fst : (⦋q⦌ : SimplexCategory) ⟶ ⦋s⦌
  /-- Vertical (`L`-side) `SimplexCategory` map. -/
  snd : (⦋q⦌ : SimplexCategory) ⟶ ⦋s⦌

noncomputable instance (s q : ℕ) : DecidableEq (OpLetter s q) := Classical.decEq _

/-- An EM natural operator `(K×L)_s → (K×L)_q` (their (2.10)): a finite `ℤ`-linear combination of
letters, with uniqueness of representation supplied by carrying the representation as data. -/
abbrev DerivedOp (s q : ℕ) := OpLetter s q →₀ ℤ

/-- Realize a single letter as a degreewise hom on the diagonal complex `F₂.obj X`. -/
noncomputable def OpLetter.realize {s q : ℕ} (X : BisimplicialObject C) (l : OpLetter s q) :
    (F₂.obj X).X s ⟶ (F₂.obj X).X q :=
  (X.obj (Opposite.op ⦋s⦌)).map l.snd.op ≫ (X.map l.fst.op).app (Opposite.op ⦋q⦌)

/-- Realize a formal operator as a degreewise hom on `F₂.obj X` (`ℤ`-linear extension of
`OpLetter.realize`). -/
noncomputable def DerivedOp.realize {s q : ℕ} (X : BisimplicialObject C) (M : DerivedOp s q) :
    (F₂.obj X).X s ⟶ (F₂.obj X).X q :=
  M.sum fun l c => c • l.realize X

/-! ### The derived operator `M ↦ M'` (EM (2.10)) -/

/-- The 0-th-coface shift of a monotone map: `0 ↦ 0`, `j+1 ↦ θ(j)+1`. This is EM's `δ⁰`
prepending used to define the derived operator. -/
def primeHom {s q : ℕ} (θ : (⦋q⦌ : SimplexCategory) ⟶ ⦋s⦌) :
    (⦋q + 1⦌ : SimplexCategory) ⟶ ⦋s + 1⦌ :=
  SimplexCategory.mkHom
    { toFun := fun j =>
        ⟨min (if (j : ℕ) = 0 then 0
              else (SimplexCategory.Hom.toOrderHom θ
                ⟨(j : ℕ) - 1, (by have := j.isLt; omega : (j : ℕ) - 1 < q + 1)⟩ : ℕ) + 1) (s + 1),
          by omega⟩
      monotone' := by
        intro a b hab
        have hab' : (a : ℕ) ≤ (b : ℕ) := hab
        simp only [Fin.mk_le_mk]
        split_ifs with ha hb hb
        · omega
        · omega
        · omega
        · have hmono : (SimplexCategory.Hom.toOrderHom θ
              ⟨(a : ℕ) - 1, (by have := a.isLt; omega : (a : ℕ) - 1 < q + 1)⟩ : ℕ) ≤
              (SimplexCategory.Hom.toOrderHom θ
              ⟨(b : ℕ) - 1, (by have := b.isLt; omega : (b : ℕ) - 1 < q + 1)⟩ : ℕ) :=
            (SimplexCategory.Hom.toOrderHom θ).monotone (by simp only [Fin.mk_le_mk]; omega)
          omega }

/-- The derived operator on a single letter: prime both `SimplexCategory` maps. -/
def OpLetter.prime {s q : ℕ} (l : OpLetter s q) : OpLetter (s + 1) (q + 1) :=
  ⟨primeHom l.fst, primeHom l.snd⟩

/-- EM's **derived operator** `M ↦ M'` (their (2.10)): prime every letter, `ℤ`-linearly. -/
noncomputable def DerivedOp.prime {s q : ℕ} (M : DerivedOp s q) : DerivedOp (s + 1) (q + 1) :=
  Finsupp.mapDomain OpLetter.prime M

/-! ### Composition of operators (vertical, on the diagonal) -/

/-- Composition of letters: `comp l₂ l₁` realizes to `realize l₁ ≫ realize l₂` (apply `l₁` then
`l₂`). Horizontal and vertical maps compose independently. -/
def OpLetter.comp {s q r : ℕ} (l₂ : OpLetter q r) (l₁ : OpLetter s q) : OpLetter s r :=
  ⟨l₂.fst ≫ l₁.fst, l₂.snd ≫ l₁.snd⟩

/-- `ℤ`-bilinear composition of operators (apply `M₁` then `M₂`). -/
noncomputable def DerivedOp.comp {s q r : ℕ} (M₂ : DerivedOp q r) (M₁ : DerivedOp s q) :
    DerivedOp s r :=
  M₁.sum fun l₁ c₁ => M₂.sum fun l₂ c₂ => Finsupp.single (l₂.comp l₁) (c₁ * c₂)

/-! ### Functoriality / `ℤ`-linearity of `realize`

These let the abstract operator identities (`prime_comp_truncBoundary`, `lastFace_comp_prime`,
`boundary_comp_D0`, …) be pushed to genuine hom identities on `F₂.obj X`, so the EM induction can
run at the operator level and only be realized at the end. -/

@[simp] lemma realize_zero {s q : ℕ} (X : BisimplicialObject C) :
    (0 : DerivedOp s q).realize X = 0 := by
  simp [DerivedOp.realize]

@[simp] lemma realize_single {s q : ℕ} (X : BisimplicialObject C) (l : OpLetter s q) (c : ℤ) :
    DerivedOp.realize X (Finsupp.single l c) = c • l.realize X := by
  simp [DerivedOp.realize, Finsupp.sum_single_index]

lemma realize_add {s q : ℕ} (X : BisimplicialObject C) (M N : DerivedOp s q) :
    (M + N).realize X = M.realize X + N.realize X := by
  simp [DerivedOp.realize, Finsupp.sum_add_index', zero_smul, add_smul]

lemma realize_neg {s q : ℕ} (X : BisimplicialObject C) (M : DerivedOp s q) :
    (-M).realize X = -(M.realize X) := by
  simp [DerivedOp.realize, Finsupp.sum_neg_index, neg_smul, Finset.sum_neg_distrib]

lemma realize_sub {s q : ℕ} (X : BisimplicialObject C) (M N : DerivedOp s q) :
    (M - N).realize X = M.realize X - N.realize X := by
  simp [sub_eq_add_neg, realize_add, realize_neg]

private noncomputable def realizeAddMonoidHom {s q : ℕ} (X : BisimplicialObject C) :
    DerivedOp s q →+ ((F₂.obj X).X s ⟶ (F₂.obj X).X q) where
  toFun M := M.realize X
  map_zero' := realize_zero X
  map_add' := realize_add X

lemma realize_zsmul {s q : ℕ} (X : BisimplicialObject C) (c : ℤ) (M : DerivedOp s q) :
    (c • M).realize X = c • M.realize X :=
  map_zsmul (realizeAddMonoidHom X) c M

/-- A single composed letter realizes to the composition of the realizations (the Pattern-5
bifunctor merge: interleave the horizontal/vertical legs via naturality of `X.map _`). -/
private lemma OpLetter.realize_comp {s q r : ℕ} (X : BisimplicialObject C) (l₂ : OpLetter q r)
    (l₁ : OpLetter s q) :
    (l₂.comp l₁).realize X = l₁.realize X ≫ l₂.realize X := by
  unfold OpLetter.realize OpLetter.comp
  simp only [op_comp, Functor.map_comp]
  rw [NatTrans.comp_app]
  slice_lhs 2 3 => rw [(X.map l₁.fst.op).naturality l₂.snd.op]
  simp only [Category.assoc]

/-- `comp` is additive in its right argument. -/
private lemma DerivedOp.comp_add_right {s q r : ℕ} (M₂ : DerivedOp q r) (M N : DerivedOp s q) :
    M₂.comp (M + N) = M₂.comp M + M₂.comp N := by
  simp only [DerivedOp.comp]
  rw [Finsupp.sum_add_index']
  · intro a; simp
  · intro a b₁ b₂; simp only [add_mul, Finsupp.single_add]; rw [Finsupp.sum_add]

/-- `comp` is additive in its left argument. -/
private lemma DerivedOp.add_comp {s q r : ℕ} (M N : DerivedOp q r) (K : DerivedOp s q) :
    (M + N).comp K = M.comp K + N.comp K := by
  simp only [DerivedOp.comp]
  rw [← Finsupp.sum_add]
  apply Finsupp.sum_congr
  intro l₁ _
  rw [Finsupp.sum_add_index']
  · intro a; simp
  · intro a b₁ b₂; simp only [mul_add, Finsupp.single_add]

/-- `comp` on a right `single`. -/
private lemma DerivedOp.comp_single_right {s q r : ℕ} (M₂ : DerivedOp q r) (l₁ : OpLetter s q)
    (c : ℤ) :
    M₂.comp (Finsupp.single l₁ c) = M₂.sum fun l₂ c₂ => Finsupp.single (l₂.comp l₁) (c * c₂) := by
  rw [DerivedOp.comp, Finsupp.sum_single_index (by simp)]

/-- `comp` of two `single`s. -/
private lemma DerivedOp.single_comp_single {s q r : ℕ} (l₂ : OpLetter q r) (l₁ : OpLetter s q)
    (c₂ c₁ : ℤ) :
    DerivedOp.comp (Finsupp.single l₂ c₂) (Finsupp.single l₁ c₁) =
      Finsupp.single (l₂.comp l₁) (c₁ * c₂) := by
  rw [DerivedOp.comp_single_right, Finsupp.sum_single_index (by simp)]

/-- `realize` turns operator composition into hom composition (contravariantly: apply `M₁` then
`M₂`). The functoriality fact that drives the operator-level induction. Proved by reducing to the
single-single case (`OpLetter.realize_comp`) via bilinearity of `comp` and additivity of
`realize`. -/
lemma realize_comp {s q r : ℕ} (X : BisimplicialObject C) (M₂ : DerivedOp q r) (M₁ : DerivedOp s q) :
    (M₂.comp M₁).realize X = M₁.realize X ≫ M₂.realize X := by
  induction M₁ using Finsupp.induction with
  | zero => simp [DerivedOp.comp]
  | single_add l₁ c₁ f _ _ ih =>
    rw [DerivedOp.comp_add_right, realize_add, ih, realize_add, Preadditive.add_comp]
    congr 1
    clear ih
    induction M₂ using Finsupp.induction with
    | zero => simp [DerivedOp.comp]
    | single_add l₂ c₂ g _ _ ih₂ =>
      rw [DerivedOp.add_comp, realize_add, ih₂, realize_add, Preadditive.comp_add]
      congr 1
      simp only [DerivedOp.single_comp_single, realize_single, OpLetter.realize_comp,
        Preadditive.zsmul_comp, Preadditive.comp_zsmul, smul_smul]
      rw [mul_comm c₂ c₁]

/-- The identity letter realizes to the identity hom. -/
@[simp] lemma realize_single_id {q : ℕ} (X : BisimplicialObject C) :
    DerivedOp.realize X (Finsupp.single ⟨𝟙 _, 𝟙 _⟩ 1 : DerivedOp q q) = 𝟙 ((F₂.obj X).X q) := by
  rw [realize_single]
  unfold OpLetter.realize
  simp [op_id, Functor.map_id, NatTrans.id_app, Category.id_comp, one_smul]

/-! ### Distinguished operators: degeneracy `D₀`, faces, boundaries -/

/-- The 0-th degeneracy operator `D₀ = s₀ × s₀ : (K×L)_q → (K×L)_{q+1}` of EM (2.13). -/
noncomputable def D0op (q : ℕ) : DerivedOp q (q + 1) :=
  Finsupp.single ⟨SimplexCategory.σ 0, SimplexCategory.σ 0⟩ 1

/-- The `i`-th diagonal degeneracy operator `Dᵢ = sᵢ × sᵢ : (K×L)_q → (K×L)_{q+1}`. -/
noncomputable def degenOp (q : ℕ) (i : Fin (q + 1)) : DerivedOp q (q + 1) :=
  Finsupp.single ⟨SimplexCategory.σ i, SimplexCategory.σ i⟩ 1

/-- The `i`-th face operator `F_i = δ_i × δ_i : (K×L)_{q+1} → (K×L)_q`. -/
noncomputable def faceOp (q : ℕ) (i : Fin (q + 2)) : DerivedOp (q + 1) q :=
  Finsupp.single ⟨SimplexCategory.δ i, SimplexCategory.δ i⟩ 1

/-- The **last face** `F₀` in EM's `∂ = F₀ − ∂'` decomposition — here the 0-th face `F_0`. -/
noncomputable def lastFaceOp (q : ℕ) : DerivedOp (q + 1) q :=
  faceOp q 0

/-- The **truncated boundary** `∂' = Σ_{i≥1} (-1)^{i-1} F_i` (the part of the boundary omitting the
0-th face), so that the full boundary is `∂ = F₀ − ∂'`. -/
noncomputable def truncBoundaryOp (q : ℕ) : DerivedOp (q + 1) q :=
  ∑ i : Fin (q + 1), ((-1 : ℤ) ^ (i : ℕ)) • faceOp q i.succ

/-- The full simplicial boundary operator `∂ = Σ_i (-1)^i F_i : (K×L)_{q+1} → (K×L)_q`. -/
noncomputable def boundaryOp (q : ℕ) : DerivedOp (q + 1) q :=
  ∑ i : Fin (q + 2), ((-1 : ℤ) ^ (i : ℕ)) • faceOp q i

/-! ### Frontality -/

/-- A `SimplexCategory` map is **frontal** if it fixes the bottom vertex `0` (equivalently its
operator word avoids the 0-th face `F₀`). -/
def IsFrontalHom {a b : ℕ} (f : (⦋a⦌ : SimplexCategory) ⟶ ⦋b⦌) : Prop :=
  SimplexCategory.Hom.toOrderHom f 0 = 0

/-- An operator is **frontal** (EM) if every letter in its support is frontal in both variables.
This is the property of **derived (primed) operators** — `primeHom` fixes `0`, so any `M.prime` is
frontal in this strong sense (`prime_frontal`). It is what the homotopy identity (2.3) consumes
(via `prime_comp_D0_of_frontal`). -/
def DerivedOp.Frontal {s q : ℕ} (M : DerivedOp s q) : Prop :=
  ∀ l ∈ M.support, IsFrontalHom l.fst ∧ IsFrontalHom l.snd

/-- An operator is **first-variable frontal** if every letter's horizontal (`K`-side) map is
frontal. This is the *weaker* property that `h = ∇f` actually has (EM line 213: in `f` the `0`-th
face `F₀` is always in the second factor, so only the first-variable maps `β` are frontal). Note
the vertical maps of `h` are **not** frontal in general (they begin with `ι_back`, which sends
`0 ↦ p`). This weaker notion is only needed for the optional annihilation property `fΦ = 0` (2.4),
not for the homotopy identity (2.3). -/
def DerivedOp.FrontalFst {s q : ℕ} (M : DerivedOp s q) : Prop :=
  ∀ l ∈ M.support, IsFrontalHom l.fst

/-! ### The realized operators agree with the chain-complex data

These tie the formal operators to the actual differentials / maps on `F₂.obj X`, so the abstract
operator identities below can be transported to statements about `Homotopy.comm`. -/

/-- The realized `i`-th face is the `i`-th face of the diagonal simplicial object: the
horizontal/vertical legs of `⟨δ i, δ i⟩` reassemble into `(diag X).δ i` via naturality of
`X.map (δ i).op`. -/
lemma realize_faceOp (X : BisimplicialObject C) (q : ℕ) (i : Fin (q + 2)) :
    (faceOp q i).realize X = (diag.obj X).δ i := by
  rw [faceOp, realize_single, one_smul, OpLetter.realize, SimplicialObject.δ, diag_obj_map]
  exact (X.map (SimplexCategory.δ i).op).naturality (SimplexCategory.δ i).op

/-- The realized boundary operator is the differential of `F₂.obj X`. -/
lemma realize_boundaryOp (X : BisimplicialObject C) (q : ℕ) :
    (boundaryOp q).realize X = (F₂.obj X).d (q + 1) q := by
  rw [show (F₂.obj X).d (q + 1) q
      = (AlternatingFaceMapComplex.obj (diag.obj X)).d (q + 1) q from rfl,
    AlternatingFaceMapComplex.obj_d_eq,
    show (boundaryOp q).realize X = realizeAddMonoidHom X (boundaryOp q) from rfl,
    boundaryOp, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_zsmul, show realizeAddMonoidHom X (faceOp q i) = (faceOp q i).realize X from rfl,
    realize_faceOp]

/-- `∂ = F₀ − ∂'` (EM, just above (2.13)): the full boundary splits as the 0-th face minus the
truncated boundary. -/
lemma boundaryOp_eq (q : ℕ) :
    boundaryOp q = lastFaceOp q - truncBoundaryOp q := by
  rw [boundaryOp, Fin.sum_univ_succ, lastFaceOp, truncBoundaryOp, sub_eq_add_neg,
    ← Finset.sum_neg_distrib]
  congr 1
  · simp
  · refine Finset.sum_congr rfl fun i _ => ?_
    rw [Fin.val_succ, pow_succ, mul_neg, mul_one, neg_zsmul]

/-! ### Algebra of the derived operator `prime`

`prime` is additive and **multiplicative** (`(β∘γ)' = β'∘γ'`), and on faces it shifts the index
(`prime(δ_i) = δ_{i+1}`). Consequently EM's truncated boundary is *literally* the derived operator
of the boundary: `∂' = prime(∂)` (`prime_boundaryOp`). These are exactly what make EM's family
identity `∂'M' = M'∂'` hold — it is just `prime` applied (via `prime_comp`) to the chain-map
condition `∂M = M∂`, with no ad-hoc index juggling. This is why we no longer state a separate
(mis-indexed) `prime_comp_truncBoundary`. -/

@[simp] lemma prime_zero {s q : ℕ} : (0 : DerivedOp s q).prime = 0 := by
  simp [DerivedOp.prime]

lemma prime_add {s q : ℕ} (M N : DerivedOp s q) : (M + N).prime = M.prime + N.prime := by
  simp [DerivedOp.prime, Finsupp.mapDomain_add]

/-- The 0-th coface shift is **multiplicative**: `(g ≫ f)' = g' ≫ f'`. The combinatorial core of
`prime`-multiplicativity (a `SimplexCategory` identity, no `Finsupp`). -/
lemma primeHom_comp {s q r : ℕ} (g : (⦋r⦌ : SimplexCategory) ⟶ ⦋q⦌)
    (f : (⦋q⦌ : SimplexCategory) ⟶ ⦋s⦌) :
    primeHom (g ≫ f) = primeHom g ≫ primeHom f := by
  apply SimplexCategory.Hom.ext
  apply OrderHom.ext
  funext j
  simp only [primeHom, SimplexCategory.mkHom, SimplexCategory.comp_toOrderHom,
    SimplexCategory.Hom.toOrderHom_mk, OrderHom.comp_coe, OrderHom.coe_mk, Function.comp_apply,
    SimplexCategory.len_mk]
  apply Fin.ext
  by_cases hj : (j : ℕ) = 0
  · simp [hj]
  · generalize_proofs h1 h2 h3
    simp only [if_neg hj]
    have hbq : ((SimplexCategory.Hom.toOrderHom g) ⟨(j : ℕ) - 1, h1⟩ : ℕ) < q + 1 := Fin.isLt _
    rw [if_neg (by omega)]
    congr 2
    congr 1
    congr 1
    apply Fin.ext
    simp only [Fin.val_mk]
    omega

/-- Letter-level multiplicativity of `prime`: `(l₂ ∘ l₁)' = l₂' ∘ l₁'`. -/
lemma OpLetter.prime_comp {s q r : ℕ} (l₂ : OpLetter q r) (l₁ : OpLetter s q) :
    (l₂.comp l₁).prime = l₂.prime.comp l₁.prime := by
  simp only [OpLetter.prime, OpLetter.comp, primeHom_comp]

/-- **`prime` is multiplicative** (`(β∘γ)' = β'∘γ'`), so `(M₂ ∘ M₁)' = M₂' ∘ M₁'`. The key fact
behind EM's `∂'M' = M'∂'`. Reduced to the single–single case `OpLetter.prime_comp` by bilinearity
of `comp` and additivity of `prime`. -/
lemma prime_comp {s q r : ℕ} (M₂ : DerivedOp q r) (M₁ : DerivedOp s q) :
    (M₂.comp M₁).prime = M₂.prime.comp M₁.prime := by
  induction M₁ using Finsupp.induction with
  | zero => simp [DerivedOp.comp, DerivedOp.prime]
  | single_add l₁ c₁ f _ _ ih =>
    rw [DerivedOp.comp_add_right, prime_add, ih, prime_add, DerivedOp.comp_add_right]
    congr 1
    clear ih
    induction M₂ using Finsupp.induction with
    | zero => simp [DerivedOp.comp, DerivedOp.prime]
    | single_add l₂ c₂ g _ _ ih₂ =>
      rw [DerivedOp.add_comp, prime_add, ih₂, prime_add, DerivedOp.add_comp]
      congr 1
      simp only [DerivedOp.single_comp_single, DerivedOp.prime, Finsupp.mapDomain_single,
        OpLetter.prime_comp]

/-- `primeHom` shifts the face map index: `prime(δ_i) = δ_{i+1}`. The combinatorial core of
`prime_faceOp`. -/
lemma primeHom_δ {q : ℕ} (i : Fin (q + 2)) :
    primeHom (SimplexCategory.δ i) = SimplexCategory.δ i.succ := by
  apply SimplexCategory.Hom.ext
  apply OrderHom.ext
  funext j
  apply Fin.ext
  simp only [primeHom, SimplexCategory.mkHom, SimplexCategory.Hom.toOrderHom_mk, OrderHom.coe_mk,
    SimplexCategory.len_mk]
  dsimp [SimplexCategory.δ, Fin.succAboveOrderEmb]
  simp only [Fin.succAbove, Fin.lt_def, Fin.val_castSucc, Fin.val_succ, Fin.coe_pred]
  have hj := j.isLt
  simp only [SimplexCategory.len_mk] at hj
  split_ifs <;>
    (try simp_all only [Fin.le_def, Fin.lt_def, Fin.ext_iff, Fin.val_zero, Fin.val_castSucc,
      Fin.val_succ, Fin.val_mk]) <;> omega

/-- **`prime` shifts faces**: `prime(δ_i) = δ_{i+1}` (prepending the `0`-th vertex pushes the
omitted vertex up by one). -/
lemma prime_faceOp (q : ℕ) (i : Fin (q + 2)) :
    (faceOp q i).prime = faceOp (q + 1) i.succ := by
  simp only [faceOp, DerivedOp.prime, Finsupp.mapDomain_single, OpLetter.prime, primeHom_δ]

/-- `primeHom` shifts the degeneracy map index: `prime(σ_i) = σ_{i+1}` (prepending the `0`-th vertex
pushes the doubled vertex up by one). The degeneracy analog of `primeHom_δ`. -/
lemma primeHom_σ {q : ℕ} (i : Fin (q + 1)) :
    primeHom (SimplexCategory.σ i) = SimplexCategory.σ i.succ := by
  apply SimplexCategory.Hom.ext
  apply OrderHom.ext
  funext j
  apply Fin.ext
  simp only [primeHom, SimplexCategory.mkHom, SimplexCategory.Hom.toOrderHom_mk, OrderHom.coe_mk,
    SimplexCategory.len_mk]
  dsimp [SimplexCategory.σ, Fin.predAbove]
  have hj := j.isLt
  simp only [SimplexCategory.len_mk] at hj
  simp only [Fin.lt_def, Fin.val_castSucc, Fin.val_succ]
  split_ifs <;> simp_all only [Fin.val_pred, Fin.coe_castPred] <;> omega

/-- **`prime` shifts degeneracies**: `prime(σ_i) = σ_{i+1}` (`D_i = (D_{i-1})'`). The operator-level
input to EM (2.12): a diagonal degeneracy `D_i` for `i ≥ 1` is the `prime` of the lower `D_{i-1}`. -/
lemma prime_degenOp (q : ℕ) (i : Fin (q + 1)) :
    (degenOp q i).prime = degenOp (q + 1) i.succ := by
  simp only [degenOp, DerivedOp.prime, Finsupp.mapDomain_single, OpLetter.prime, primeHom_σ]

/-- `prime` bundled as an additive hom, so it distributes over `Finset.sum` (`map_sum`) and
`zsmul` (`map_zsmul`). -/
private noncomputable def primeAddHom {s q : ℕ} :
    DerivedOp s q →+ DerivedOp (s + 1) (q + 1) where
  toFun := DerivedOp.prime
  map_zero' := prime_zero
  map_add' := prime_add

/-- **`∂' = prime(∂)`** (EM): the truncated boundary is the derived operator of the full boundary.
Note the degree shift — `prime` of the degree-`q` boundary is the truncated boundary at degree
`q+1` (this is the index offset that the literal EM transcription hides). -/
lemma prime_boundaryOp (q : ℕ) :
    (boundaryOp q).prime = truncBoundaryOp (q + 1) := by
  simp only [boundaryOp, truncBoundaryOp]
  rw [show (∑ i : Fin (q + 2), ((-1 : ℤ) ^ (i : ℕ)) • faceOp q i).prime
      = primeAddHom (∑ i : Fin (q + 2), ((-1 : ℤ) ^ (i : ℕ)) • faceOp q i) from rfl,
    map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_zsmul, show primeAddHom (faceOp q i) = (faceOp q i).prime from rfl, prime_faceOp]

/-! ### Core derived-operator identities (EM I.3, used in the (2.13) induction) -/

/-- `primeHom θ` is frontal: it fixes the bottom vertex `0` (`primeHom` sends `0 ↦ 0`). -/
lemma primeHom_frontal {s q : ℕ} (θ : (⦋q⦌ : SimplexCategory) ⟶ ⦋s⦌) :
    IsFrontalHom (primeHom θ) := by
  simp [IsFrontalHom, primeHom]

/-- The derived operator preserves frontality (EM: `M'` is always frontal, since `primeHom` fixes
`0`). -/
lemma prime_frontal {s q : ℕ} (M : DerivedOp s q) : (M.prime).Frontal := by
  intro l hl
  have hl' := Finsupp.mapDomain_support hl
  rw [Finset.mem_image] at hl'
  obtain ⟨l', _, rfl⟩ := hl'
  exact ⟨primeHom_frontal _, primeHom_frontal _⟩

/-- For a **frontal** map (`θ 0 = 0`), the prepended vertex collapses against `σ 0`:
`primeHom θ ≫ σ 0 = σ 0 ≫ θ`. The combinatorial core of `prime_comp_D0_of_frontal`; frontality
is exactly what makes the two sides agree at the bottom vertex. -/
lemma primeHom_comp_degenZero {s q : ℕ} (θ : (⦋q⦌ : SimplexCategory) ⟶ ⦋s⦌)
    (hθ : IsFrontalHom θ) :
    primeHom θ ≫ SimplexCategory.σ (0 : Fin (s + 1))
      = SimplexCategory.σ (0 : Fin (q + 1)) ≫ θ := by
  apply SimplexCategory.Hom.ext
  apply OrderHom.ext
  funext j
  refine Fin.cases ?_ (fun k => ?_) j
  · -- `j = 0`: both sides land on the bottom vertex; `σ 0` and `primeHom` send `0 ↦ 0`, and
    -- `θ 0 = 0` (frontality) closes `0 = ↑(θ 0)`.
    apply Fin.ext
    simp only [IsFrontalHom] at hθ
    simp only [SimplexCategory.len_mk, SimplexCategory.comp_toOrderHom, OrderHom.comp_coe,
      Function.comp_apply]
    exact (congrArg Fin.val hθ).symm
  · -- `j = k.succ`: `primeHom θ` gives `θ(k) + 1`, then `σ 0` (always `0 < θ(k)+1`) drops back to
    -- `θ(k) = min (θ k) s`, matching `θ (σ 0 (k.succ)) = θ k`.
    apply Fin.ext
    simp [primeHom, SimplexCategory.σ, Fin.predAbove]
    have hk := (SimplexCategory.Hom.toOrderHom θ k).isLt
    simp only [SimplexCategory.len_mk] at hk
    split_ifs <;> simp_all [Fin.lt_def]

/-- **Frontal ⟹ priming commutes with `D₀`** (EM, from Lemma I.3.3: `(β')^* D₀ = D₀ β^*`).
For a frontal operator, `M' ∘ D₀ = D₀ ∘ M`. -/
lemma prime_comp_D0_of_frontal {s q : ℕ} (M : DerivedOp s q) (hM : M.Frontal) :
    (M.prime).comp (D0op s) = (D0op q).comp M := by
  induction M using Finsupp.induction with
  | zero => simp [DerivedOp.prime, DerivedOp.comp]
  | single_add l c f hlf hc ih =>
    have hl := hM l (by
      rw [Finsupp.mem_support_iff, Finsupp.add_apply, Finsupp.single_eq_same,
        Finsupp.notMem_support_iff.mp hlf, add_zero]
      exact hc)
    have hf : DerivedOp.Frontal f := fun l' hl' => hM l' (by
      rw [Finsupp.mem_support_iff, Finsupp.add_apply,
        Finsupp.single_eq_of_ne (by rintro rfl; exact hlf hl'), zero_add,
        ← Finsupp.mem_support_iff]
      exact hl')
    rw [prime_add, DerivedOp.add_comp, DerivedOp.comp_add_right, ih hf]
    congr 1
    rw [DerivedOp.prime, Finsupp.mapDomain_single, D0op, D0op,
      DerivedOp.single_comp_single, DerivedOp.single_comp_single, one_mul, mul_one]
    congr 1
    simp only [OpLetter.comp, OpLetter.prime, primeHom_comp_degenZero l.fst hl.1,
      primeHom_comp_degenZero l.snd hl.2]

/-- The 0-th face "eats" the prepended vertex: `δ 0 ≫ primeHom θ = θ ≫ δ 0`. The combinatorial
core of `lastFace_comp_prime`. -/
lemma faceZero_comp_primeHom {s q : ℕ} (θ : (⦋q⦌ : SimplexCategory) ⟶ ⦋s⦌) :
    SimplexCategory.δ (0 : Fin (q + 2)) ≫ primeHom θ
      = θ ≫ SimplexCategory.δ (0 : Fin (s + 2)) := by
  apply SimplexCategory.Hom.ext
  apply OrderHom.ext
  funext j
  apply Fin.ext
  simp only [primeHom, SimplexCategory.mkHom, SimplexCategory.comp_toOrderHom,
    SimplexCategory.Hom.toOrderHom_mk, OrderHom.comp_coe, OrderHom.coe_mk, Function.comp_apply,
    SimplexCategory.len_mk]
  -- Unfold the two `δ 0` cofaces to `Fin.succAbove 0 = Fin.succ`, then `simp` evaluates the
  -- `primeHom` `if`/`min` (both legs send `j ↦ θ(j) + 1`); the leftover `↑(θ j) ≤ s` is `isLt`.
  dsimp only [SimplexCategory.δ, Fin.succAboveOrderEmb, OrderEmbedding.coe_ofStrictMono,
    Function.Embedding.coeFn_mk]
  simp only [SimplexCategory.mkHom, Fin.succAbove_zero, SimplexCategory.Hom.toOrderHom_mk,
    OrderEmbedding.toOrderHom_coe, OrderEmbedding.coe_ofStrictMono, Fin.val_succ,
    Nat.add_eq_zero_iff, Fin.val_eq_zero_iff, one_ne_zero, and_false, ↓reduceIte,
    add_tsub_cancel_right, Fin.eta, Nat.add_min_add_right, Nat.add_right_cancel_iff, inf_eq_left]
  have hj := (SimplexCategory.Hom.toOrderHom θ j).isLt
  simp only [SimplexCategory.len_mk] at hj
  omega

/-- **`F₀ M' = M F₀`** (EM, Lemma I.3.3): dropping the bottom face commutes with priming. The one
derived-operator/boundary identity that is *not* a consequence of multiplicativity, since the
outer `F₀` is unprimed. -/
lemma lastFace_comp_prime {s q : ℕ} (M : DerivedOp s q) :
    (lastFaceOp q).comp (M.prime) = M.comp (lastFaceOp s) := by
  induction M using Finsupp.induction with
  | zero => simp [DerivedOp.prime, DerivedOp.comp]
  | single_add l c f _ _ ih =>
    rw [prime_add, DerivedOp.comp_add_right, ih, DerivedOp.add_comp]
    congr 1
    rw [DerivedOp.prime, Finsupp.mapDomain_single, lastFaceOp, faceOp, lastFaceOp, faceOp,
      DerivedOp.single_comp_single, DerivedOp.single_comp_single, mul_one, one_mul]
    congr 1
    simp only [OpLetter.comp, OpLetter.prime, faceZero_comp_primeHom]

/-- Post-composition with `D₀` on the right, bundled additively so `map_sum`/`map_zsmul` distribute
it over the boundary sum. -/
private noncomputable def compRightD0 (q : ℕ) :
    DerivedOp (q + 2) (q + 1) →+ DerivedOp (q + 1) (q + 1) where
  toFun M := M.comp (D0op (q + 1))
  map_zero' := by simp [DerivedOp.comp]
  map_add' M N := DerivedOp.add_comp M N _

/-- Pre-composition with `D₀` on the left, bundled additively. -/
private noncomputable def compLeftD0 (q : ℕ) :
    DerivedOp (q + 1) q →+ DerivedOp (q + 1) (q + 1) where
  toFun M := (D0op q).comp M
  map_zero' := by simp [DerivedOp.comp]
  map_add' M N := DerivedOp.comp_add_right (D0op q) M N

/-- The `i ≥ 2` simplicial identity `F_{k+2} D₀ = D₀ F_{k+1}` at the operator level
(`δ_{k+2} ≫ σ_0 = σ_0 ≫ δ_{k+1}`). -/
private lemma faceSuccSucc_comp_D0 (q : ℕ) (k : Fin (q + 1)) :
    (faceOp (q + 1) k.succ.succ).comp (D0op (q + 1))
      = (D0op q).comp (faceOp q k.succ) := by
  rw [faceOp, D0op, D0op, faceOp, DerivedOp.single_comp_single,
    DerivedOp.single_comp_single, mul_one]
  congr 1
  simp only [OpLetter.comp]
  congr 1 <;>
    exact SimplexCategory.δ_comp_σ_of_gt (i := k.succ) (j := 0) (by simp [Fin.lt_def])

/-- The two unit faces `F_0 D₀ = F_1 D₀ = 1` (`δ_0 ≫ σ_0 = δ_1 ≫ σ_0 = 𝟙`); used to cancel the
first two terms of `∂ D₀`. -/
private lemma face_zero_comp_D0 (q : ℕ) :
    (faceOp (q + 1) (0 : Fin (q + 3))).comp (D0op (q + 1))
      = (Finsupp.single ⟨𝟙 _, 𝟙 _⟩ 1 : DerivedOp (q + 1) (q + 1)) := by
  rw [faceOp, D0op, DerivedOp.single_comp_single, mul_one]
  congr 1

private lemma face_one_comp_D0 (q : ℕ) :
    (faceOp (q + 1) (0 : Fin (q + 2)).succ).comp (D0op (q + 1))
      = (Finsupp.single ⟨𝟙 _, 𝟙 _⟩ 1 : DerivedOp (q + 1) (q + 1)) := by
  rw [faceOp, D0op, DerivedOp.single_comp_single, mul_one]
  congr 1
  simp only [OpLetter.comp]
  congr 1 <;> exact SimplexCategory.δ_comp_σ_succ

/-- Simplicial identity `∂ D₀ = D₀ ∂'` (operator level). EM's line 179 writes this as
`∂ D₀ = 1 − D₀ ∂'`, but that quantity is `∂' D₀`; with `∂ = F₀ − ∂'` the bottom two faces
`F₀ D₀ = F₁ D₀ = 1` cancel, leaving `∂ D₀ = D₀ ∂'`. -/
lemma boundary_comp_D0 (q : ℕ) :
    (boundaryOp (q + 1)).comp (D0op (q + 1)) =
      (D0op q).comp (truncBoundaryOp q) := by
  have hL : (boundaryOp (q + 1)).comp (D0op (q + 1))
      = ∑ i : Fin (q + 3), ((-1 : ℤ) ^ (i : ℕ)) • (faceOp (q + 1) i).comp (D0op (q + 1)) := by
    rw [boundaryOp,
      show (∑ i : Fin (q + 3), ((-1 : ℤ) ^ (i : ℕ)) • faceOp (q + 1) i).comp (D0op (q + 1))
        = compRightD0 q (∑ i : Fin (q + 3), ((-1 : ℤ) ^ (i : ℕ)) • faceOp (q + 1) i) from rfl,
      map_sum]
    exact Finset.sum_congr rfl fun i _ => map_zsmul (compRightD0 q) _ _
  have hR : (D0op q).comp (truncBoundaryOp q)
      = ∑ k : Fin (q + 1), ((-1 : ℤ) ^ (k : ℕ)) • (D0op q).comp (faceOp q k.succ) := by
    rw [truncBoundaryOp,
      show (D0op q).comp (∑ k : Fin (q + 1), ((-1 : ℤ) ^ (k : ℕ)) • faceOp q k.succ)
        = compLeftD0 q (∑ k : Fin (q + 1), ((-1 : ℤ) ^ (k : ℕ)) • faceOp q k.succ) from rfl,
      map_sum]
    exact Finset.sum_congr rfl fun k _ => map_zsmul (compLeftD0 q) _ _
  rw [hL, hR, Fin.sum_univ_succ, Fin.sum_univ_succ, face_zero_comp_D0, face_one_comp_D0]
  simp only [Fin.val_zero, Fin.val_succ, Nat.zero_add, pow_zero, pow_one, one_smul,
    neg_one_zsmul]
  rw [add_neg_cancel_left]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [faceSuccSucc_comp_D0]
  congr 1
  rw [pow_succ, pow_succ]
  ring

/-! ### "Maps norms into norms" via `PInfty` (project strategy, plan lines 106–116)

A *norm* (for the homotopy `Φ`) is a **diagonal** degenerate term, i.e. an element of `D(K×L)`,
the degeneracy subcomplex defining `K×_N L = (K×L)_N` (EM md line 75). EM's "maps norms into norms /
equal modulo norms" is realized by postcomposing with `retractionN₂ = PInftyToNormalizedMooreComplex
(diag X)`, which kills exactly these.

**No fork** (resolved against the paper): EM places `Φ` *in `K×_N L`* (md lines 81/83), and every
norm in the `∂Φ+Φ∂` argument is a `D(K×L)` diagonal degeneracy (md lines 157/161/167) — precisely
what `retractionN₂` kills. The single-direction norms `a⊗Db`, `Da⊗b` (md line 75) belong to the
*other* side `K_N⊗L_N` of the equivalence and only concern `f`/`∇` mapping norms into norms (md
lines 122–126), **not** the `Φ` identity. The kill mechanism below is therefore sufficient; the
earlier "bi-normalization" worry conflated the two notions. -/

/-- The realization of a **diagonal letter** `⟨θ, θ⟩` is the diagonal map `(diag X).map θ.op`
(`realize_faceOp` generalized off the face case): the horizontal/vertical legs reassemble by
naturality of `X.map θ.op`. -/
lemma realize_diagLetter (X : BisimplicialObject C) {s q : ℕ}
    (θ : (⦋q⦌ : SimplexCategory) ⟶ ⦋s⦌) :
    DerivedOp.realize X (Finsupp.single (⟨θ, θ⟩ : OpLetter s q) 1) = (diag.obj X).map θ.op := by
  rw [realize_single, one_smul, OpLetter.realize, diag_obj_map]
  exact (X.map θ.op).naturality θ.op

/-- **EM's "norm" killed by `retractionN₂`.** A *diagonal* degeneracy `⟨θ, θ⟩` with `θ` non-mono
dies after `≫ retractionN₂`: its realization is `(diag X).map θ.op`, killed by
`degeneracy_comp_PInfty` (Moore-inclusion mono-cancel, Pattern 1).

NB: this is the **diagonal**-degeneracy form, which is what `retractionN₂ = PInfty(diag X)` can
kill. (A single-direction degeneracy `⟨𝟙, θ⟩` need *not* be diagonally degenerate, but — see the
section note — those are not the norms the `Φ` identity needs.) `θ` non-mono ⟹ `θ` factors through
some `σ_j`, so `(diag X).map θ.op` is a degeneracy of `diag X`, killed by `degeneracy_comp_PInfty`
(Moore-inclusion mono-cancel, Pattern 1). -/
lemma realize_diagLetter_comp_retractionN₂_eq_zero_of_not_mono {s q : ℕ} (X : BisimplicialObject C)
    (θ : (⦋q⦌ : SimplexCategory) ⟶ ⦋s⦌) (hθ : ¬ Mono θ) :
    DerivedOp.realize X (Finsupp.single (⟨θ, θ⟩ : OpLetter s q) 1) ≫ (retractionN₂ X).f q = 0 := by
  rw [realize_diagLetter]
  -- `(diag X).map θ.op` is a degeneracy of `diag X` (θ non-mono); factor `PInfty = retr ≫ incl`
  -- and cancel the mono Moore inclusion (Pattern 1).
  have h := degeneracy_comp_PInfty (diag.obj X) q θ hθ
  rw [← PInftyToNormalizedMooreComplex_comp_inclusionOfMooreComplexMap (diag.obj X),
    HomologicalComplex.comp_f, ← Category.assoc] at h
  haveI : Mono ((inclusionOfMooreComplexMap (diag.obj X)).f q) := by
    rw [inclusionOfMooreComplexMap_f]; infer_instance
  exact zero_of_comp_mono _ h

/-- **Generalized norm-kill: a diagonal degeneracy on the *left* (last-applied) kills anything.**
If a derived operator factors as `⟨θ, θ⟩ ∘ N` with `θ` non-mono, then `realize (⟨θ,θ⟩.comp N) ≫
retractionN₂ = 0`. By `realize_comp` the degeneracy `realize ⟨θ,θ⟩` lands adjacent to `retractionN₂`
(`realize (M₂.comp N) = realize N ≫ realize M₂`), so the base diagonal kill applies after
`realize N`. This is the form the EM induction consumes: norm terms like `D₀Φ = ⟨σ₀,σ₀⟩ ∘ Φ` and
`Φ'D_i = δ^i D_{i-1}` are diagonal degeneracies post-composed with arbitrary operators. -/
lemma realize_comp_diagLetter_not_mono_comp_retractionN₂ {r s q : ℕ} (X : BisimplicialObject C)
    (θ : (⦋q⦌ : SimplexCategory) ⟶ ⦋s⦌) (hθ : ¬ Mono θ) (N : DerivedOp r s) :
    DerivedOp.realize X (DerivedOp.comp (Finsupp.single (⟨θ, θ⟩ : OpLetter s q) 1) N) ≫
        (retractionN₂ X).f q = 0 := by
  rw [realize_comp, Category.assoc,
    realize_diagLetter_comp_retractionN₂_eq_zero_of_not_mono X θ hθ, Limits.comp_zero]

/-! ### The Eilenberg–Mac Lane homotopy `h = ∇f` and the recursion (2.13) -/

/- EM's operator `h = ∇f : (K×L) → (K×L)` (our `alexanderWhitney ≫ shuffleMap`)
as a universal (`X`-independent) derived operator, obtained from the AW/shuffle representations
(the `awComponent ≫ ezComponent` Pattern-5 merge).

**Concreteness is needed only through `realize_hOp` and the low-degree values (EM (2.11)).** The
homotopy-identity induction (2.3) treats `hOp` *opaquely*, consuming only the universal
`prime`/`comp` laws and `prime_frontal`; it never unfolds `hOp`'s letters. (Mirrors EM, who
define `h := ∇f` and only ever use its definition and properties; see `realize_hOp`.) -/
/-- A single summand of `h = ∇f`: split `q = p + (q - p)`, apply the AW front/back
faces, then apply one `(p, q-p)` shuffle. The two `eqToHom`s transport across
`p + (q-p) = q`. -/
noncomputable def hLetter (q : ℕ) (p : Fin (q + 1)) (μ : Shuffle (p : ℕ) (q - p)) :
    OpLetter q q where
  fst :=
    eqToHom (congrArg SimplexCategory.mk (by omega : q = (p : ℕ) + (q - p))) ≫
      shuffleFstHom μ ≫ ι_front (p : ℕ) (q - p) ≫
        eqToHom (congrArg SimplexCategory.mk (by omega : (p : ℕ) + (q - p) = q))
  snd :=
    eqToHom (congrArg SimplexCategory.mk (by omega : q = (p : ℕ) + (q - p))) ≫
      shuffleSndHom μ ≫ ι_back (p : ℕ) (q - p) ≫
        eqToHom (congrArg SimplexCategory.mk (by omega : (p : ℕ) + (q - p) = q))

/-- `h = ∇f` as a derived operator: sum over the Alexander-Whitney split and then over
shuffles. -/
noncomputable def hOp (q : ℕ) : DerivedOp q q :=
  ∑ p : Fin (q + 1), ∑ μ : Shuffle (p : ℕ) (q - p),
    Finsupp.single (hLetter q p μ) μ.sign

omit [Abelian C] in
private lemma awShuffleLetter_core (X : BisimplicialObject C) (p r : ℕ) (μ : Shuffle p r) :
    (X.map (ι_front p r).op).app (Opposite.op ⦋p + r⦌) ≫
        (X.obj (Opposite.op ⦋p⦌)).map (ι_back p r).op ≫
          (X.obj (Opposite.op ⦋p⦌)).map (shuffleSndHom μ).op ≫
            (X.map (shuffleFstHom μ).op).app (Opposite.op ⦋p + r⦌) =
      (X.obj (Opposite.op ⦋p + r⦌)).map (shuffleSndHom μ ≫ ι_back p r).op ≫
        (X.map (shuffleFstHom μ ≫ ι_front p r).op).app (Opposite.op ⦋p + r⦌) := by
  simp only [op_comp, Functor.map_comp, Category.assoc]
  slice_lhs 2 3 => rw [← Functor.map_comp, ← op_comp]
  slice_lhs 1 2 =>
    rw [← (X.map (ι_front p r).op).naturality (shuffleSndHom μ ≫ ι_back p r).op]
  simp only [op_comp, Functor.map_comp, Category.assoc]
  slice_lhs 3 4 => rw [← NatTrans.comp_app]

private lemma hLetter_realize_of_add_eq (X : BisimplicialObject C) (p r q : ℕ)
    (h : p + r = q) (μ : Shuffle p r) :
    (OpLetter.mk
      (eqToHom (congrArg SimplexCategory.mk h.symm) ≫ shuffleFstHom μ ≫ ι_front p r ≫
        eqToHom (congrArg SimplexCategory.mk h))
      (eqToHom (congrArg SimplexCategory.mk h.symm) ≫ shuffleSndHom μ ≫ ι_back p r ≫
        eqToHom (congrArg SimplexCategory.mk h))).realize X =
      eqToHom (by
        simp only [F₂, Functor.comp_obj, alternatingFaceMapComplex_obj_X, diag_obj_obj]
        rw [← h]) ≫
        awComponent X p r ≫
          ((X.obj (Opposite.op ⦋p⦌)).map (shuffleSndHom μ).op ≫
            (X.map (shuffleFstHom μ).op).app (Opposite.op ⦋p + r⦌)) ≫
          eqToHom (by
            simp only [F₂, Functor.comp_obj, alternatingFaceMapComplex_obj_X, diag_obj_obj]
            rw [← h]) := by
  subst q
  simp only [OpLetter.realize, awComponent, eqToHom_refl, Category.id_comp, Category.comp_id]
  simpa only [Category.assoc] using (awShuffleLetter_core X p r μ).symm

-- TODO: Combine awShuffleLetter_core, hLetter_realize_of_add_eq, hLetter_realize
/-- Realization of one `hLetter` summand is the corresponding `awComponent ≫ ezComponent` shuffle
summand. This is the Pattern-5 merge of the AW front/back faces with the shuffle degeneracies. -/
lemma hLetter_realize (X : BisimplicialObject C) (q : ℕ) (p : Fin (q + 1))
    (μ : Shuffle (p : ℕ) (q - p)) :
    (hLetter q p μ).realize X =
      eqToHom (by simp [Nat.add_sub_cancel' (Nat.lt_succ_iff.mp p.isLt)]) ≫
        awComponent X p (q - p) ≫
          ((X.obj (Opposite.op ⦋(p : ℕ)⦌)).map (shuffleSndHom μ).op ≫
            (X.map (shuffleFstHom μ).op).app (Opposite.op ⦋(p : ℕ) + (q - p)⦌)) ≫
          eqToHom (by simp [Nat.add_sub_cancel' (Nat.lt_succ_iff.mp p.isLt)]) := by
  have hpq : (p : ℕ) + (q - p) = q :=
    Nat.add_sub_cancel' (Nat.lt_succ_iff.mp p.isLt)
  simpa [hLetter, hpq] using hLetter_realize_of_add_eq X (p : ℕ) (q - p) q hpq μ

/-- `hOp` realizes to the composite `alexanderWhitney ≫ shuffleMap = ∇f` on `F₂.obj X`. -/
lemma realize_hOp (X : BisimplicialObject C) (q : ℕ) :
    (hOp q).realize X = (alexanderWhitney X ≫ shuffleMap X).f q := by
  have hrealize :
      (hOp q).realize X =
        ∑ p : Fin (q + 1), ∑ μ : Shuffle (p : ℕ) (q - p),
          μ.sign • (hLetter q p μ).realize X := by
    change realizeAddMonoidHom X (hOp q) = _
    rw [hOp, map_sum]
    refine Finset.sum_congr rfl fun p _ => ?_
    rw [map_sum]
    refine Finset.sum_congr rfl fun μ _ => ?_
    simp [realizeAddMonoidHom, realize_single]
  rw [hrealize, HomologicalComplex.comp_f]
  simp only [alexanderWhitney, shuffleMap, id_eq, Preadditive.sum_comp, Category.assoc,
    HomologicalComplex₂.ι_totalDesc]
  simp only [hLetter_realize, ezComponent, Preadditive.comp_sum, Preadditive.sum_comp,
    Preadditive.comp_zsmul, Preadditive.zsmul_comp, Category.assoc]


/-- **The Eilenberg–Mac Lane homotopy `Φ`** as a derived operator, defined by EM's recursion (2.13):
`Φ₀ = 0` and `Φ_{q} = − Φ'_{q-1} + h'_{q} D₀` for `q > 0`. Here `Φ_q : (K×L)_q → (K×L)_{q+1}`. -/
noncomputable def phiOp : (q : ℕ) → DerivedOp q (q + 1)
  | 0 => 0
  | (q + 1) => -(phiOp q).prime + (hOp (q + 1)).prime.comp (D0op (q + 1))

/-- Composition of frontal `SimplexCategory` maps is frontal (`0 ↦ 0 ↦ 0`). -/
lemma IsFrontalHom.comp {a b c : ℕ} {f : (⦋a⦌ : SimplexCategory) ⟶ ⦋b⦌}
    {g : (⦋b⦌ : SimplexCategory) ⟶ ⦋c⦌} (hf : IsFrontalHom f) (hg : IsFrontalHom g) :
    IsFrontalHom (f ≫ g) := by
  simp only [IsFrontalHom, SimplexCategory.comp_toOrderHom, OrderHom.comp_coe,
    Function.comp_apply] at *
  rw [hf, hg]

/-- The zero operator is (vacuously) frontal. -/
lemma DerivedOp.Frontal.zero {s q : ℕ} : (0 : DerivedOp s q).Frontal := by
  intro l hl
  simp only [Finsupp.support_zero, Finset.notMem_empty] at hl

/-- A single frontal letter gives a frontal operator. -/
lemma DerivedOp.Frontal.single {s q : ℕ} (l : OpLetter s q) (c : ℤ)
    (hl : IsFrontalHom l.fst ∧ IsFrontalHom l.snd) :
    DerivedOp.Frontal (Finsupp.single l c) := by
  intro l' hl'
  rw [Finset.mem_singleton.mp (Finsupp.support_single_subset hl')]
  exact hl

/-- Frontality is preserved by negation (same support). -/
lemma DerivedOp.Frontal.neg {s q : ℕ} {M : DerivedOp s q} (hM : M.Frontal) : (-M).Frontal :=
  fun l hl => hM l (by simpa using hl)

/-- Frontality is preserved by addition (support ⊆ union). -/
lemma DerivedOp.Frontal.add {s q : ℕ} {M N : DerivedOp s q} (hM : M.Frontal) (hN : N.Frontal) :
    (M + N).Frontal := by
  intro l hl
  rcases Finset.mem_union.mp (Finsupp.support_add hl) with h | h
  · exact hM l h
  · exact hN l h

/-- Frontality is preserved by right composition with a single frontal letter. -/
lemma DerivedOp.Frontal.comp_single {s q r : ℕ} {M : DerivedOp q r} (hM : M.Frontal)
    (l₁ : OpLetter s q) (c₁ : ℤ) (hl₁ : IsFrontalHom l₁.fst ∧ IsFrontalHom l₁.snd) :
    (M.comp (Finsupp.single l₁ c₁)).Frontal := by
  induction M using Finsupp.induction with
  | zero =>
      rw [show DerivedOp.comp (0 : DerivedOp q r) (Finsupp.single l₁ c₁) = 0 from by
        simp [DerivedOp.comp]]
      exact DerivedOp.Frontal.zero
  | single_add l₂ c₂ g hlg hc₂ ih =>
      have hl₂ := hM l₂ (by
        rw [Finsupp.mem_support_iff, Finsupp.add_apply, Finsupp.single_eq_same,
          Finsupp.notMem_support_iff.mp hlg, add_zero]
        exact hc₂)
      have hg : DerivedOp.Frontal g := fun l' hl' => hM l' (by
        rw [Finsupp.mem_support_iff, Finsupp.add_apply,
          Finsupp.single_eq_of_ne (by rintro rfl; exact hlg hl'), zero_add,
          ← Finsupp.mem_support_iff]
        exact hl')
      rw [DerivedOp.add_comp, DerivedOp.single_comp_single]
      exact (DerivedOp.Frontal.single (l₂.comp l₁) (c₁ * c₂)
        ⟨hl₂.1.comp hl₁.1, hl₂.2.comp hl₁.2⟩).add (ih hg)

/-- `Φ` is frontal: `Φ₀ = 0` is vacuously frontal; the step `Φ_{q+1} = −Φ'_q + h'_{q+1} D₀` is a
sum of a primed operator (frontal by `prime_frontal`, no induction hypothesis needed) and a primed
operator composed with the frontal degeneracy `D₀ = ⟨σ₀,σ₀⟩`. -/
lemma phiOp_frontal (q : ℕ) : (phiOp q).Frontal := by
  cases q with
  | zero => exact DerivedOp.Frontal.zero
  | succ q =>
      have hσ : IsFrontalHom (SimplexCategory.σ (0 : Fin (q + 1 + 1))) := by
        simp [IsFrontalHom, SimplexCategory.σ, Fin.predAbove]
      rw [phiOp, D0op]
      exact ((prime_frontal _).neg).add ((prime_frontal _).comp_single _ 1 ⟨hσ, hσ⟩)

/-! ### Packaging the homotopy on `F₂` (raw, modulo norms) -/

/-- `Φ` packaged as a degree-`+1` `Homotopy.hom` family on `F₂.obj X` (the unnormalized diagonal):
`phiOp i` realized (transported along `j = i+1`) on the single nonzero entry, `0` elsewhere. -/
noncomputable def phiHomRaw (X : BisimplicialObject C) (i j : ℕ) :
    (F₂.obj X).X i ⟶ (F₂.obj X).X j :=
  if h : j = i + 1 then (phiOp i).realize X ≫ eqToHom (by rw [h]) else 0

lemma phiHomRaw_zero (X : BisimplicialObject C) (i j : ℕ)
    (hij : ¬ (ComplexShape.down ℕ).Rel j i) : phiHomRaw X i j = 0 :=
  dif_neg fun h => hij (by rw [ComplexShape.down_Rel]; omega)

/-- `prevD` of `phiHomRaw` is the realized operator `∂Φ` (apply `Φ` then `∂`):
`prevD n (phiHomRaw X) = (phiOp n).realize X ≫ (boundaryOp n).realize X`. -/
lemma prevD_phiHomRaw (X : BisimplicialObject C) (n : ℕ) :
    prevD n (phiHomRaw X) = DerivedOp.realize X ((boundaryOp n).comp (phiOp n)) := by
  rw [prevD_eq (phiHomRaw X) (show (ComplexShape.down ℕ).Rel (n + 1) n from rfl), phiHomRaw,
    dif_pos rfl, eqToHom_refl, Category.comp_id, realize_comp, ← realize_boundaryOp]

/-- `dNext` of `phiHomRaw` (at `n+1`) is the realized operator `Φ∂` (apply `∂` then `Φ`):
`dNext (n+1) (phiHomRaw X) = (boundaryOp n).realize X ≫ (phiOp n).realize X`. -/
lemma dNext_phiHomRaw (X : BisimplicialObject C) (n : ℕ) :
    dNext (n + 1) (phiHomRaw X) = DerivedOp.realize X ((phiOp n).comp (boundaryOp n)) := by
  rw [dNext_eq (phiHomRaw X) (show (ComplexShape.down ℕ).Rel (n + 1) n from rfl), phiHomRaw,
    dif_pos rfl, eqToHom_refl, Category.comp_id, realize_comp, ← realize_boundaryOp]

/-- The identity operator `i = 𝟙 × 𝟙 : (K×L)_q → (K×L)_q` (EM's `i`). Realizes to `𝟙`
(`realize_single_id`). -/
noncomputable def idOp (q : ℕ) : DerivedOp q q := Finsupp.single ⟨𝟙 _, 𝟙 _⟩ 1

/-! #### Abstract properties of `h = ∇f` consumed by the EM induction (treat `hOp` opaquely)

EM (markdown lines 155, 167, 192, 161) only ever uses `h` through derived-operator properties,
never its explicit letters. We isolate them here as the (currently `sorry`'d) inputs to (5b). -/

/-- The represented simplicial type `Δ[s] : b ↦ (⦋b⦌ ⟶ ⦋s⦌)` (the `SimplexCategory` Yoneda). -/
private def ysimp (s : ℕ) : SimplexCategoryᵒᵖ ⥤ Type := yoneda.obj (⦋s⦌ : SimplexCategory)

/-- The bi-represented **bisimplicial type** at `(s, s)`: `(a, b) ↦ (⦋a⦌ ⟶ ⦋s⦌) × (⦋b⦌ ⟶ ⦋s⦌)`,
the horizontal map acting on the first factor and the vertical on the second. -/
private def bitype (s : ℕ) : BisimplicialObject (Type) where
  obj a :=
    { obj := fun b => (ysimp s).obj a × (ysimp s).obj b
      map := fun {b b'} g p => (p.1, (ysimp s).map g p.2)
      map_id := by intro b; ext p <;> simp
      map_comp := by intro b b' b'' g g'; ext p <;> simp }
  map := fun {a a'} f =>
    { app := fun b p => ((ysimp s).map f p.1, p.2)
      naturality := by intro b b' g; ext p <;> simp }
  map_id := by intro a; ext b p <;> simp
  map_comp := by intro a a' a'' f f'; ext b p <;> simp

/-- Postcompose a (bi)simplicial type with the free `ℤ`-module functor. -/
private noncomputable def freeWhisker :
    (SimplexCategoryᵒᵖ ⥤ Type) ⥤ (SimplexCategoryᵒᵖ ⥤ ModuleCat.{0} ℤ) :=
  (Functor.whiskeringRight SimplexCategoryᵒᵖ Type (ModuleCat.{0} ℤ)).obj (ModuleCat.free ℤ)

/-- A **universal bisimplicial object** detecting all derived operators out of degree `s`:
the free `ℤ`-module on the bi-represented bisimplicial set at `(s, s)`. Realizing a derived
operator against it recovers it as a `Finsupp`, so `realize (univOp s)` is injective
(`realize_univOp_injective`). -/
noncomputable def univOp (s : ℕ) : BisimplicialObject (ModuleCat.{0} ℤ) :=
  bitype s ⋙ freeWhisker

/-- The underlying pair of `SimplexCategory` maps of a letter. Injective (a letter *is* its pair),
so it indexes the free `ℤ`-module realizing `univOp`. -/
private def opToPair {s q : ℕ} (l : OpLetter s q) :
    ((⦋q⦌ : SimplexCategory) ⟶ ⦋s⦌) × ((⦋q⦌ : SimplexCategory) ⟶ ⦋s⦌) := (l.fst, l.snd)

private lemma opToPair_injective {s q : ℕ} :
    Function.Injective (opToPair (s := s) (q := q)) := by
  intro l l' h
  cases l; cases l'
  simpa only [opToPair, Prod.mk.injEq, OpLetter.mk.injEq] using h

/-- The universal generator `(𝟙, 𝟙) ∈ X_{s,s}` for `X = univOp s`. -/
private noncomputable def univGen (s : ℕ) : (F₂.obj (univOp s)).X s :=
  ModuleCat.freeMk (R := ℤ) ((𝟙 (⦋s⦌ : SimplexCategory)), (𝟙 (⦋s⦌ : SimplexCategory)))

private lemma realize_univOp_single_gen_one {s q : ℕ} (l : OpLetter s q) :
    (DerivedOp.realize (univOp s) (Finsupp.single l 1)) (univGen s)
      = ModuleCat.freeMk (R := ℤ) (opToPair l) := by
  rw [realize_single, one_smul]
  simp only [OpLetter.realize, univOp, freeWhisker, univGen, Functor.comp_obj, Functor.comp_map,
    Functor.whiskeringRight_obj_obj, Functor.whiskeringRight_obj_map,
    Functor.whiskerRight_app, ModuleCat.comp_apply, bitype, ysimp,
    yoneda_obj_map, Quiver.Hom.unop_op, opToPair]
  erw [ModuleCat.free_map_apply, ModuleCat.free_map_apply]
  simp

private lemma realize_univOp_single_gen {s q : ℕ} (l : OpLetter s q) (c : ℤ) :
    (DerivedOp.realize (univOp s) (Finsupp.single l c)) (univGen s)
      = Finsupp.single (opToPair l) c := by
  rw [show (Finsupp.single l c : DerivedOp s q) = c • Finsupp.single l 1 from by
        rw [Finsupp.smul_single, smul_eq_mul, mul_one], realize_zsmul]
  rw [show (ConcreteCategory.hom (c • DerivedOp.realize (univOp s) (Finsupp.single l 1)))
        (univGen s)
        = c • (ConcreteCategory.hom (DerivedOp.realize (univOp s) (Finsupp.single l 1)))
          (univGen s) from rfl,
    realize_univOp_single_gen_one, ModuleCat.freeMk, Finsupp.smul_single, smul_eq_mul, mul_one]

/-- Realizing `M` on `univOp` and evaluating at the universal generator recovers `M` (reindexed
along the letter-to-pair bijection): `realize (univOp s) M (gen) = mapDomain opToPair M`. -/
private lemma realize_univOp_gen {s q : ℕ} (M : DerivedOp s q) :
    (DerivedOp.realize (univOp s) M) (univGen s) = Finsupp.mapDomain opToPair M := by
  induction M using Finsupp.induction with
  | zero => rw [realize_zero, Finsupp.mapDomain_zero]; rfl
  | single_add l c f _ _ ih =>
      rw [realize_add,
        show (ConcreteCategory.hom (DerivedOp.realize (univOp s) (Finsupp.single l c)
              + DerivedOp.realize (univOp s) f)) (univGen s)
            = (ConcreteCategory.hom (DerivedOp.realize (univOp s) (Finsupp.single l c)))
                (univGen s)
              + (ConcreteCategory.hom (DerivedOp.realize (univOp s) f)) (univGen s) from rfl,
        realize_univOp_single_gen, ih, Finsupp.mapDomain_add, Finsupp.mapDomain_single]

/-- `realize` against the universal object is **injective**: a derived operator is determined by
its realization on `univOp`. This is the faithfulness principle that lets us deduce formal
`DerivedOp` identities from their (realized) chain-level counterparts. -/
lemma realize_univOp_injective {s q : ℕ} :
    Function.Injective (fun M : DerivedOp s q => M.realize (univOp s)) := by
  intro M N h
  have hg := congrArg
    (fun φ : (F₂.obj (univOp s)).X s ⟶ (F₂.obj (univOp s)).X q =>
      (ConcreteCategory.hom φ) (univGen s)) h
  simp only [realize_univOp_gen] at hg
  exact Finsupp.mapDomain_injective opToPair_injective hg

/-- **`∂ h = h ∂` (EM line 155, `∂*h' = h'∂*`).** `h = ∇f` is a chain map, so `boundaryOp` commutes
with `hOp`. Proof: `realize` against the universal object is injective, and on the realized side
this is just the chain-map condition `comm` of `alexanderWhitney ≫ shuffleMap`. -/
lemma boundaryOp_comp_hOp (q : ℕ) :
    (boundaryOp q).comp (hOp (q + 1)) = (hOp q).comp (boundaryOp q) := by
  apply realize_univOp_injective
  change ((boundaryOp q).comp (hOp (q + 1))).realize (univOp (q + 1))
    = ((hOp q).comp (boundaryOp q)).realize (univOp (q + 1))
  rw [realize_comp, realize_comp, realize_hOp, realize_hOp, realize_boundaryOp]
  exact (alexanderWhitney (univOp (q + 1)) ≫ shuffleMap (univOp (q + 1))).comm (q + 1) q

