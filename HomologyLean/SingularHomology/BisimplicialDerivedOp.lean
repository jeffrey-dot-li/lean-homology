import HomologyLean.SingularHomology.BisimplicialNormalizedDefs
import Mathlib.Data.Finsupp.Basic

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

/-- **`∂ h = h ∂` (EM line 155, `∂*h' = h'∂*`).** `h = ∇f` is a chain map, so `boundaryOp` commutes
with `hOp`. -/
lemma boundaryOp_comp_hOp (q : ℕ) :
    (boundaryOp q).comp (hOp (q + 1)) = (hOp q).comp (boundaryOp q) := by
  sorry

/-- **`F₀ h' = h F₀` (EM, Lemma I.3.3).** Just `lastFace_comp_prime` specialized to `hOp`. -/
lemma lastFace_comp_hPrime (q : ℕ) :
    (lastFaceOp q).comp ((hOp q).prime) = (hOp q).comp (lastFaceOp q) :=
  lastFace_comp_prime (hOp q)

/-- **Base case (EM line 169, `q = 0`).** `h₀ = i` modulo norms: `∇f` is the identity in degree 0
(`AW`/`∇` are inverse there). -/
lemma hOp_zero_comp_retraction (X : BisimplicialObject C) :
    DerivedOp.realize X (hOp 0) ≫ (retractionN₂ X).f 0 =
      DerivedOp.realize X (idOp 0) ≫ (retractionN₂ X).f 0 := by
  rw [realize_hOp, idOp, realize_single_id, awShuffle_f_zero, HomologicalComplex.id_f]

/-! #### Exact-identity backbone for the EM induction (5b)

The induction is run as an **exact** `DerivedOp` equation `IsNorm (Φ∂ + ∂Φ + i − h)`, where `IsNorm`
is a *structural* norm class (diagonal-degeneracy and EM (2.12) `h`-degeneracy generators, closed
under `+`/`neg`). Being structural, it is **provably closed under `prime`** (`IsNorm.prime`), so the
*exact* IH primes cleanly — sidestepping the (non-existent) `realize(M') ≫ retr ↔ realize(M) ≫ retr`
bridge. Norms are killed only at the very end via `IsNorm.kill`. -/

/-- Right composition `· .comp N` bundled additively (general `compRightD0`). -/
private noncomputable def compRightHom {s q r : ℕ} (M₂ : DerivedOp q r) :
    DerivedOp s q →+ DerivedOp s r where
  toFun N := M₂.comp N
  map_zero' := by simp [DerivedOp.comp]
  map_add' := DerivedOp.comp_add_right M₂

/-- Left composition `M ↦ M.comp K` bundled additively. -/
private noncomputable def compLeftHom {s q r : ℕ} (M₁ : DerivedOp s q) :
    DerivedOp q r →+ DerivedOp s r where
  toFun M₂ := M₂.comp M₁
  map_zero' := by simp [DerivedOp.comp]
  map_add' M N := DerivedOp.add_comp M N M₁

lemma DerivedOp.comp_neg {s q r : ℕ} (M₂ : DerivedOp q r) (N : DerivedOp s q) :
    M₂.comp (-N) = -(M₂.comp N) := map_neg (compRightHom M₂) N

lemma DerivedOp.neg_comp {s q r : ℕ} (M : DerivedOp q r) (K : DerivedOp s q) :
    (-M).comp K = -(M.comp K) := map_neg (compLeftHom K) M

lemma DerivedOp.comp_sub {s q r : ℕ} (M₂ : DerivedOp q r) (M N : DerivedOp s q) :
    M₂.comp (M - N) = M₂.comp M - M₂.comp N := map_sub (compRightHom M₂) M N

lemma DerivedOp.sub_comp {s q r : ℕ} (M N : DerivedOp q r) (K : DerivedOp s q) :
    (M - N).comp K = M.comp K - N.comp K := map_sub (compLeftHom K) M N

lemma prime_neg {s q : ℕ} (M : DerivedOp s q) : (-M).prime = -M.prime :=
  map_neg primeAddHom M

/-- Associativity of letter composition (`≫`-associativity in each coordinate). -/
private lemma OpLetter.comp_assoc {s q r p : ℕ} (l₃ : OpLetter r p) (l₂ : OpLetter q r)
    (l₁ : OpLetter s q) : (l₃.comp l₂).comp l₁ = l₃.comp (l₂.comp l₁) := by
  simp only [OpLetter.comp, Category.assoc]

/-- Associativity of `DerivedOp.comp` (reduces to `single_comp_single` + bilinearity). -/
lemma DerivedOp.comp_assoc {s q r p : ℕ} (M₃ : DerivedOp r p) (M₂ : DerivedOp q r)
    (M₁ : DerivedOp s q) : (M₃.comp M₂).comp M₁ = M₃.comp (M₂.comp M₁) := by
  induction M₁ using Finsupp.induction with
  | zero => simp [DerivedOp.comp]
  | single_add l₁ c₁ f _ _ ih =>
    rw [DerivedOp.comp_add_right, ih, DerivedOp.comp_add_right, DerivedOp.comp_add_right]
    congr 1
    clear ih
    induction M₂ using Finsupp.induction with
    | zero => simp [DerivedOp.comp]
    | single_add l₂ c₂ g _ _ ih₂ =>
      rw [DerivedOp.comp_add_right, DerivedOp.add_comp, ih₂, DerivedOp.add_comp,
        DerivedOp.comp_add_right]
      congr 1
      clear ih₂
      induction M₃ using Finsupp.induction with
      | zero => simp [DerivedOp.comp]
      | single_add l₃ c₃ h _ _ ih₃ =>
        rw [DerivedOp.add_comp, DerivedOp.add_comp, ih₃, DerivedOp.add_comp]
        congr 1
        rw [DerivedOp.single_comp_single, DerivedOp.single_comp_single,
          DerivedOp.single_comp_single, DerivedOp.single_comp_single, OpLetter.comp_assoc]
        congr 1
        ring

@[simp] lemma DerivedOp.zero_comp {s q r : ℕ} (N : DerivedOp s q) :
    DerivedOp.comp (0 : DerivedOp q r) N = 0 := by simp [DerivedOp.comp]

/-- `k`-fold derived operator `M ↦ M'⋯'`. (`prime` is type-changing, so this is a manual recursion,
not `Function.iterate`.) -/
noncomputable def DerivedOp.primeIter {s q : ℕ} :
    (k : ℕ) → DerivedOp s q → DerivedOp (s + k) (q + k)
  | 0, M => M
  | k + 1, M => (DerivedOp.primeIter k M).prime

@[simp] lemma DerivedOp.primeIter_succ {s q : ℕ} (k : ℕ) (M : DerivedOp s q) :
    DerivedOp.primeIter (k + 1) M = (DerivedOp.primeIter k M).prime := rfl

/-- `primeIter` distributes over `comp` (iterated `prime_comp`): `(M₂ ∘ M₁)⁽ᵏ⁾ = M₂⁽ᵏ⁾ ∘ M₁⁽ᵏ⁾`. -/
lemma DerivedOp.primeIter_comp {s q r : ℕ} (k : ℕ) (M₂ : DerivedOp q r) (M₁ : DerivedOp s q) :
    DerivedOp.primeIter k (M₂.comp M₁)
      = (DerivedOp.primeIter k M₂).comp (DerivedOp.primeIter k M₁) := by
  induction k with
  | zero => rfl
  | succ k ih =>
      rw [DerivedOp.primeIter_succ, ih, prime_comp, DerivedOp.primeIter_succ,
        DerivedOp.primeIter_succ]

/-- A `DerivedOp` is a **norm** (EM, for the diagonal `K×_N L`), defined *structurally* so that
closure under `prime` is manifest (no `realize`-bridge needed). Generators: diagonal degeneracies
`⟨θ,θ⟩∘N` (`¬Mono θ`), closed under `+`/`neg`. (`C`-free; killed under `retractionN₂` via
`IsNorm.kill`.) -/
inductive IsNorm : {s q : ℕ} → DerivedOp s q → Prop where
  | zero {s q : ℕ} : IsNorm (0 : DerivedOp s q)
  | add {s q : ℕ} {M N : DerivedOp s q} : IsNorm M → IsNorm N → IsNorm (M + N)
  | neg {s q : ℕ} {M : DerivedOp s q} : IsNorm M → IsNorm (-M)
  | diagDegen {r s q : ℕ} (θ : (⦋q⦌ : SimplexCategory) ⟶ ⦋s⦌) (hθ : ¬ Mono θ) (N : DerivedOp r s) :
      IsNorm (DerivedOp.comp (Finsupp.single (⟨θ, θ⟩ : OpLetter s q) 1) N)

/-- `prime` of a diagonal letter `⟨θ,θ⟩` is the diagonal of `primeHom θ`. -/
lemma prime_single_diag {s q : ℕ} (θ : (⦋q⦌ : SimplexCategory) ⟶ ⦋s⦌) :
    DerivedOp.prime (Finsupp.single (⟨θ, θ⟩ : OpLetter s q) 1)
      = Finsupp.single (⟨primeHom θ, primeHom θ⟩ : OpLetter (s + 1) (q + 1)) 1 := by
  simp [DerivedOp.prime, Finsupp.mapDomain_single, OpLetter.prime]

/-- `primeHom` preserves non-monicity: `primeHom θ` is injective iff `θ` is, and `Mono` in
`SimplexCategory` is injectivity. -/
lemma primeHom_not_mono {s q : ℕ} {θ : (⦋q⦌ : SimplexCategory) ⟶ ⦋s⦌} (hθ : ¬ Mono θ) :
    ¬ Mono (primeHom θ) := by
  rw [SimplexCategory.mono_iff_injective] at hθ ⊢
  intro hinj
  apply hθ
  intro a b hab
  have key : ∀ c : Fin (q + 1),
      (SimplexCategory.Hom.toOrderHom (primeHom θ)) c.succ
        = (SimplexCategory.Hom.toOrderHom θ c).succ := by
    intro c
    apply Fin.ext
    have hle : (SimplexCategory.Hom.toOrderHom θ c : ℕ) ≤ s :=
      Nat.lt_succ_iff.mp (SimplexCategory.Hom.toOrderHom θ c).isLt
    simp only [primeHom, SimplexCategory.mkHom, SimplexCategory.Hom.toOrderHom_mk, OrderHom.coe_mk,
      SimplexCategory.len_mk, Fin.val_succ]
    rw [if_neg (by omega : ¬ ((c : ℕ) + 1 = 0))]
    simp only [Nat.add_sub_cancel, Fin.eta]
    omega
  have hsucc : (SimplexCategory.Hom.toOrderHom (primeHom θ)) a.succ
      = (SimplexCategory.Hom.toOrderHom (primeHom θ)) b.succ := by
    rw [key, key, hab]
  exact Fin.succ_injective _ (hinj hsucc)

/-- `prime` fixes the identity map: `primeHom 𝟙 = 𝟙` (`0 ↦ 0`, `j+1 ↦ 𝟙(j)+1 = j+1`). -/
lemma primeHom_id (q : ℕ) : primeHom (𝟙 (⦋q⦌ : SimplexCategory)) = 𝟙 _ := by
  apply SimplexCategory.Hom.ext
  apply OrderHom.ext
  funext j
  apply Fin.ext
  have hj : (j : ℕ) ≤ q + 1 := Nat.lt_succ_iff.mp j.isLt
  simp only [primeHom, SimplexCategory.mkHom, SimplexCategory.Hom.toOrderHom_mk, OrderHom.coe_mk,
    SimplexCategory.len_mk, SimplexCategory.id_toOrderHom, OrderHom.id_coe, id_eq]
  split_ifs with h <;> omega

/-- `i' = i` (md 173–175, implicit in priming the IH's `−c_q`): the derived operator of the
identity is the identity. -/
lemma prime_idOp (q : ℕ) : (idOp q).prime = idOp (q + 1) := by
  rw [idOp, prime_single_diag, primeHom_id, idOp]

/-- **`F₀ D₀ = i`** (`δ_0 ≫ σ_0 = 𝟙`): the last face undoes the 0-th degeneracy. Repackages the
existing `face_zero_comp_D0` (`lastFaceOp = faceOp _ 0`). -/
lemma lastFace_comp_D0 (q : ℕ) :
    (lastFaceOp (q + 1)).comp (D0op (q + 1)) = idOp (q + 1) := by
  rw [lastFaceOp, idOp]
  exact face_zero_comp_D0 q

/-- Right unit for `DerivedOp.comp`: `M ∘ i = M` (`l ≫ 𝟙 = l` in each coordinate). -/
lemma comp_idOp {s q : ℕ} (M : DerivedOp s q) : M.comp (idOp s) = M := by
  induction M using Finsupp.induction with
  | zero => simp [DerivedOp.comp]
  | single_add l c f _ _ ih =>
      rw [DerivedOp.add_comp, ih]
      congr 1
      rw [idOp, DerivedOp.single_comp_single, one_mul]
      congr 1
      simp only [OpLetter.comp, Category.comp_id]

/-- **`F₀ h' D₀ = h` (EM line 192).** `F₀ h' D₀ = (h F₀) D₀ = h (F₀ D₀) = h`, using
`lastFace_comp_hPrime` and `F₀ D₀ = i` (`δ_0 ≫ σ_0 = 𝟙`). -/
lemma lastFace_comp_hPrime_comp_D0 (q : ℕ) :
    (lastFaceOp (q + 1)).comp (((hOp (q + 1)).prime).comp (D0op (q + 1))) = hOp (q + 1) := by
  rw [← DerivedOp.comp_assoc, lastFace_comp_hPrime, DerivedOp.comp_assoc, lastFace_comp_D0,
    comp_idOp]

/-! #### EM (2.12): `f` and `∇` preserve norms ⟹ `h = ∇f` preserves norms

EM (2.12) is a *composition* fact: `f = AW` and `∇ = shuffleMap` each carry the (diagonal)
degenerate subcomplex into the (bi-)degenerate subcomplex, so `h = ∇f` does too. The two halves are
genuine Dold–Kan combinatorial inputs (Phase-4-level); the composite `h`-statement then follows
*for free* via `realize_hOp`.

* **`∇`-half (6b):** `retractionN₁_inclusionN₁_shuffleMap_retractionN₂` — a degenerate-`F₁` element
  (image of `1 − retractionN₁ ≫ inclusionN₁`) is sent by `∇` to a degenerate diagonal element,
  killed by `retractionN₂`.
* **`f`-half:** `alexanderWhitney_diagDegen_comp_retractionN₁` — a diagonal degeneracy `⟨θ,θ⟩`
  followed by `AW` lands in the degenerate part of `F₁`, killed by `retractionN₁`. -/

/-- If a simplex operator `f : ⦋n+1⦌ ⟶ Δ'` identifies the adjacent pair `a.castSucc, a.succ`
(i.e. it is "constant across the `a`-th step"), then it factors through the codegeneracy `σ a`:
`f = σ a ≫ (δ a.castSucc ≫ f)`. The section `δ a.castSucc` undoes `σ a` away from the collapsed
pair (`Fin.succAbove_predAbove`), and on the pair the hypothesis `hf` patches it. -/
private lemma factor_through_σ {n : ℕ} {Δ' : SimplexCategory} (a : Fin (n + 1))
    (f : (⦋n + 1⦌ : SimplexCategory) ⟶ Δ')
    (hf : f.toOrderHom a.castSucc = f.toOrderHom a.succ) :
    f = SimplexCategory.σ a ≫ SimplexCategory.δ a.castSucc ≫ f := by
  apply SimplexCategory.Hom.ext
  apply OrderHom.ext
  funext x
  simp only [SimplexCategory.comp_toOrderHom, OrderHom.comp_coe, Function.comp_apply,
    SimplexCategory.σ, SimplexCategory.δ, SimplexCategory.mkHom, SimplexCategory.Hom.toOrderHom_mk,
    OrderHom.coe_mk]
  change _ = (SimplexCategory.Hom.toOrderHom f) (a.castSucc.succAbove (a.predAbove x))
  by_cases hx : x = a.castSucc
  · subst hx
    rw [Fin.predAbove_castSucc_self, Fin.succAbove_castSucc_self]
    exact hf
  · rw [Fin.succAbove_predAbove hx]

/-- A codegeneracy `σ a` is never a monomorphism (it identifies the adjacent pair `a.castSucc`,
`a.succ`). -/
private lemma sigma_not_mono {n : ℕ} (a : Fin (n + 1)) : ¬ Mono (SimplexCategory.σ a) := by
  rw [SimplexCategory.mono_iff_injective]
  intro hinj
  have key : a.castSucc = a.succ := by
    apply hinj
    show a.predAbove a.castSucc = a.predAbove a.succ
    rw [Fin.predAbove_castSucc_self, Fin.predAbove_succ_self]
  exact absurd key (ne_of_lt Fin.castSucc_lt_succ)

/-- **Shared per-summand kill (degeneracy ⟹ diagonal degeneracy).** A single Eilenberg–Zilber
summand `(X_⦋s⦌).map v.op ≫ (X.map h.op)_⦋n+1⦌`, in which the horizontal leg `h` and the vertical
leg `v` are *both constant across the `a`-th step* (`a.castSucc ↦ a.succ`), factors through the
diagonal codegeneracy `(diag X).map (σ a).op` and is therefore annihilated by `PInfty`. This is the
direction-agnostic core: the inner kill feeds it `v = sndHom ≫ σ_i` (constant by `exists_snd_step`),
the outer kill feeds it `h = fstHom ≫ σ_i`. -/
private lemma summand_kill {N s t : ℕ} (X : BisimplicialObject C)
    (h : (⦋N⦌ : SimplexCategory) ⟶ ⦋s⦌) (v : (⦋N⦌ : SimplexCategory) ⟶ ⦋t⦌)
    (a : Fin N)
    (hh : (SimplexCategory.Hom.toOrderHom h) a.castSucc = (SimplexCategory.Hom.toOrderHom h) a.succ)
    (hv : (SimplexCategory.Hom.toOrderHom v) a.castSucc =
      (SimplexCategory.Hom.toOrderHom v) a.succ) :
    (X.obj (Opposite.op ⦋s⦌)).map v.op ≫ (X.map h.op).app (Opposite.op ⦋N⦌) ≫
      (PInfty : F₂.obj X ⟶ F₂.obj X).f N = 0 := by
  obtain ⟨n, rfl⟩ : ∃ n, N = n + 1 := ⟨N - 1, by
    have : 0 < N := Nat.pos_of_ne_zero (by rintro rfl; exact a.elim0); omega⟩
  have hfh := factor_through_σ a h hh
  have hfv := factor_through_σ a v hv
  set h' : (⦋n⦌ : SimplexCategory) ⟶ ⦋s⦌ := SimplexCategory.δ a.castSucc ≫ h with hh'_def
  set v' : (⦋n⦌ : SimplexCategory) ⟶ ⦋t⦌ := SimplexCategory.δ a.castSucc ≫ v with hv'_def
  have hvop : v.op = v'.op ≫ (SimplexCategory.σ a).op := by rw [hfv, op_comp]
  have hhop : h.op = h'.op ≫ (SimplexCategory.σ a).op := by rw [hfh, op_comp]
  -- the diagonal-degeneracy tail is killed by `PInfty`
  have hbr : (X.obj (Opposite.op ⦋n⦌)).map (SimplexCategory.σ a).op ≫
      (X.map (SimplexCategory.σ a).op).app (Opposite.op ⦋n + 1⦌)
      = (diag.obj X).map (SimplexCategory.σ a).op := by
    rw [(X.map (SimplexCategory.σ a).op).naturality, ← diag_obj_map]
  have hkill : (X.obj (Opposite.op ⦋n⦌)).map (SimplexCategory.σ a).op ≫
      (X.map (SimplexCategory.σ a).op).app (Opposite.op ⦋n + 1⦌) ≫
      (PInfty : F₂.obj X ⟶ F₂.obj X).f (n + 1) = 0 := by
    rw [← Category.assoc, hbr]
    exact degeneracy_comp_PInfty (diag.obj X) (n + 1) (SimplexCategory.σ a) (sigma_not_mono a)
  rw [hvop, hhop, Functor.map_comp, Functor.map_comp, NatTrans.comp_app]
  simp only [Category.assoc]
  rw [(X.map h'.op).naturality_assoc, hkill]
  simp

/-- **EZ–degeneracy kill, inner (vertical) direction (the per-summand combinatorial core).**
A `(p, m+1)`-shuffle component of a chain that is *degenerate in the inner simplicial direction*
(in the image of the inner degeneracy `s_i = (X_⦋p⦌).map (σ i).op : X_{p,m} → X_{p,m+1}`) is sent by
the Eilenberg–Zilber component to a *diagonally* degenerate chain, hence annihilated by `PInfty`.

EM Lemma I.5.3 content: `∇ ∘ (1 ⊗ s_i) = s_? ∘ ∇'` lands in a diagonal degeneracy. -/
lemma ezComponent_inner_degeneracy_comp_PInfty (X : BisimplicialObject C)
    (p m : ℕ) (i : Fin (m + 1)) :
    (X.obj (Opposite.op ⦋p⦌)).map (SimplexCategory.σ i).op ≫ ezComponent X p (m + 1) ≫
        (PInfty : F₂.obj X ⟶ F₂.obj X).f (p + (m + 1)) = 0 := by
  rw [ezComponent, Preadditive.sum_comp, Preadditive.comp_sum]
  apply Finset.sum_eq_zero
  intro μ _
  obtain ⟨a, ha1, ha2, ha3⟩ := Shuffle.exists_snd_step μ i.val (by have := i.isLt; omega)
  have hh : (SimplexCategory.Hom.toOrderHom (shuffleFstHom μ)) a.castSucc
          = (SimplexCategory.Hom.toOrderHom (shuffleFstHom μ)) a.succ := by
    simp only [shuffleFstHom, SimplexCategory.Hom.toOrderHom_mk, OrderHom.comp_coe,
      Function.comp_apply, OrderHom.fst_coe]
    exact ha3
  have hv : (SimplexCategory.Hom.toOrderHom (shuffleSndHom μ ≫ SimplexCategory.σ i)) a.castSucc
          = (SimplexCategory.Hom.toOrderHom (shuffleSndHom μ ≫ SimplexCategory.σ i)) a.succ := by
    simp only [SimplexCategory.comp_toOrderHom, OrderHom.comp_coe, Function.comp_apply,
      shuffleSndHom, SimplexCategory.Hom.toOrderHom_mk, OrderHom.snd_coe]
    have e1 : (μ.1 a.castSucc).2 = i.castSucc := Fin.ext (by rw [Fin.coe_castSucc]; omega)
    have e2 : (μ.1 a.succ).2 = i.succ := Fin.ext (by rw [Fin.val_succ]; omega)
    show (SimplexCategory.Hom.toOrderHom (SimplexCategory.σ i)) (μ.1 a.castSucc).2
       = (SimplexCategory.Hom.toOrderHom (SimplexCategory.σ i)) (μ.1 a.succ).2
    rw [e1, e2]
    show i.predAbove i.castSucc = i.predAbove i.succ
    rw [Fin.predAbove_castSucc_self, Fin.predAbove_succ_self]
  have hcomp : X _⦋p⦌.map (SimplexCategory.σ i).op ≫
      (X _⦋p⦌.map (shuffleSndHom μ).op ≫
        (X.map (shuffleFstHom μ).op).app (Opposite.op ⦋p + (m + 1)⦌)) ≫
      (PInfty : F₂.obj X ⟶ F₂.obj X).f (p + (m + 1)) = 0 := by
    simp only [Category.assoc]
    rw [← Category.assoc (X _⦋p⦌.map (SimplexCategory.σ i).op), ← Functor.map_comp, ← op_comp]
    exact summand_kill X (shuffleFstHom μ) (shuffleSndHom μ ≫ SimplexCategory.σ i) a hh hv
  rw [Preadditive.zsmul_comp, Preadditive.comp_zsmul, hcomp, smul_zero]

/-- **EZ–degeneracy kill, outer (horizontal) direction (the per-summand combinatorial core).**
An `(a+1, q)`-shuffle component of a chain that is *degenerate in the outer simplicial direction*
(in the image of the outer degeneracy `s_i = (X.map (σ i).op).app ⦋q⦌ : X_{a,q} → X_{a+1,q}`) is sent
by the Eilenberg–Zilber component to a *diagonally* degenerate chain, hence annihilated by `PInfty`.

EM Lemma I.5.3 content: `∇ ∘ (s_i ⊗ 1) = s_? ∘ ∇'` lands in a diagonal degeneracy. -/
lemma ezComponent_outer_degeneracy_comp_PInfty (X : BisimplicialObject C)
    (a q : ℕ) (i : Fin (a + 1)) :
    (X.map (SimplexCategory.σ i).op).app (Opposite.op ⦋q⦌) ≫ ezComponent X (a + 1) q ≫
        (PInfty : F₂.obj X ⟶ F₂.obj X).f (a + 1 + q) = 0 := by
  rw [ezComponent, Preadditive.sum_comp, Preadditive.comp_sum]
  apply Finset.sum_eq_zero
  intro μ _
  obtain ⟨b, hb1, hb2, hb3⟩ := Shuffle.exists_fst_step μ i.val (by have := i.isLt; omega)
  have hh : (SimplexCategory.Hom.toOrderHom (shuffleFstHom μ ≫ SimplexCategory.σ i)) b.castSucc
          = (SimplexCategory.Hom.toOrderHom (shuffleFstHom μ ≫ SimplexCategory.σ i)) b.succ := by
    simp only [SimplexCategory.comp_toOrderHom, OrderHom.comp_coe, Function.comp_apply,
      shuffleFstHom, SimplexCategory.Hom.toOrderHom_mk, OrderHom.fst_coe]
    have e1 : (μ.1 b.castSucc).1 = i.castSucc := Fin.ext (by rw [Fin.coe_castSucc]; omega)
    have e2 : (μ.1 b.succ).1 = i.succ := Fin.ext (by rw [Fin.val_succ]; omega)
    show (SimplexCategory.Hom.toOrderHom (SimplexCategory.σ i)) (μ.1 b.castSucc).1
       = (SimplexCategory.Hom.toOrderHom (SimplexCategory.σ i)) (μ.1 b.succ).1
    rw [e1, e2]
    show i.predAbove i.castSucc = i.predAbove i.succ
    rw [Fin.predAbove_castSucc_self, Fin.predAbove_succ_self]
  have hv : (SimplexCategory.Hom.toOrderHom (shuffleSndHom μ)) b.castSucc
          = (SimplexCategory.Hom.toOrderHom (shuffleSndHom μ)) b.succ := by
    simp only [shuffleSndHom, SimplexCategory.Hom.toOrderHom_mk, OrderHom.comp_coe,
      Function.comp_apply, OrderHom.snd_coe]
    exact hb3
  have hcomp : (X.map (SimplexCategory.σ i).op).app (Opposite.op ⦋q⦌) ≫
      (X _⦋a + 1⦌.map (shuffleSndHom μ).op ≫
        (X.map (shuffleFstHom μ).op).app (Opposite.op ⦋a + 1 + q⦌)) ≫
      (PInfty : F₂.obj X ⟶ F₂.obj X).f (a + 1 + q) = 0 := by
    have happ : (X.map (SimplexCategory.σ i).op).app (Opposite.op ⦋a + 1 + q⦌) ≫
        (X.map (shuffleFstHom μ).op).app (Opposite.op ⦋a + 1 + q⦌)
        = (X.map (shuffleFstHom μ ≫ SimplexCategory.σ i).op).app (Opposite.op ⦋a + 1 + q⦌) := by
      rw [← NatTrans.comp_app, ← Functor.map_comp, ← op_comp]
    simp only [Category.assoc]
    rw [← (X.map (SimplexCategory.σ i).op).naturality_assoc,
      ← Category.assoc ((X.map (SimplexCategory.σ i).op).app (Opposite.op ⦋a + 1 + q⦌)), happ]
    exact summand_kill X (shuffleFstHom μ ≫ SimplexCategory.σ i) (shuffleSndHom μ) b hh hv
  rw [Preadditive.zsmul_comp, Preadditive.comp_zsmul, hcomp, smul_zero]

/-- **Inner `QInfty`-degeneracy kill.** The inner (vertical) `QInfty` projector at degree `q`,
precomposed with the Eilenberg–Zilber component and the diagonal `PInfty`, vanishes. Each summand of
the Mathlib `decomposition_Q` ends in an inner degeneracy `(X_⦋p⦌).σ`, killed by
`ezComponent_inner_degeneracy_comp_PInfty`. -/
private lemma QInfty_inner_ezComponent_PInfty (X : BisimplicialObject C) (p q : ℕ) :
    (QInfty (X := X.obj (Opposite.op ⦋p⦌))).f q ≫ ezComponent X p q ≫
        (PInfty : F₂.obj X ⟶ F₂.obj X).f (p + q) = 0 := by
  cases q with
  | zero => rw [QInfty_f_0, zero_comp]
  | succ m =>
    rw [QInfty_f, decomposition_Q m (m + 1), Preadditive.sum_comp]
    apply Finset.sum_eq_zero
    intro i _
    have hkill : (X.obj (Opposite.op ⦋p⦌)).map (SimplexCategory.σ (Fin.rev i)).op ≫
        ezComponent X p (m + 1) ≫ (PInfty : F₂.obj X ⟶ F₂.obj X).f (p + (m + 1)) = 0 :=
      ezComponent_inner_degeneracy_comp_PInfty X p m (Fin.rev i)
    simp only [SimplicialObject.σ, Category.assoc, hkill, comp_zero]

/-- **Outer `QInfty`-degeneracy kill.** The outer (horizontal) `QInfty` projector at degree `p`
(evaluated at inner degree `q`), precomposed with the Eilenberg–Zilber component and the diagonal
`PInfty`, vanishes. Each summand of the Mathlib `decomposition_Q` ends in an outer degeneracy
`(X.map (σ _).op).app ⦋q⦌`, killed by `ezComponent_outer_degeneracy_comp_PInfty`. -/
private lemma QInfty_outer_ezComponent_PInfty (X : BisimplicialObject C) (p q : ℕ) :
    ((QInfty (X := X)).f p).app (Opposite.op ⦋q⦌) ≫ ezComponent X p q ≫
        (PInfty : F₂.obj X ⟶ F₂.obj X).f (p + q) = 0 := by
  cases p with
  | zero => rw [QInfty_f_0]; simp
  | succ a =>
    rw [QInfty_f, decomposition_Q a (a + 1), NatTrans.app_sum, Preadditive.sum_comp]
    apply Finset.sum_eq_zero
    intro i _
    have hkill : (X.map (SimplexCategory.σ (Fin.rev i)).op).app (Opposite.op ⦋q⦌) ≫
        ezComponent X (a + 1) q ≫ (PInfty : F₂.obj X ⟶ F₂.obj X).f (a + 1 + q) = 0 :=
      ezComponent_outer_degeneracy_comp_PInfty X a q (Fin.rev i)
    rw [NatTrans.comp_app, NatTrans.comp_app, Category.assoc, Category.assoc]
    rw [SimplicialObject.σ, hkill, comp_zero, comp_zero]

/-- **EM Lemma I.5.3, complement form (the genuine Dold–Kan combinatorial content).** The
*degenerate* part of `F₁` — the image of the complementary projector `𝟙 − retractionN₁ ≫ inclusionN₁`
(a chain degenerate in some bisimplicial direction) — is sent by `∇ = shuffleMap` to a chain that is
degenerate in the diagonal, hence annihilated by `PInfty`.

This is the **dual** of the already-proven normalized-side statement
`higherFacesVanish_inclusionN₁_shuffleMap` (`BisimplicialNormalized.lean`): that one shows `∇` of a
bi-normalized chain has no degenerate diagonal component; this one shows `∇` of a degenerate chain is
*entirely* degenerate.

Expected proof (Route A, degeneracy-based): `ext n` + `HomologicalComplex₂.total.hom_ext` reduces to
each bidegree `(p, q)`; on the summand the complement `𝟙 − PInfty^out_p ⊗ PInfty^in_q` decomposes
(via `1 − ab = (1 − a) + a(1 − b)` and the Mathlib `QInfty` degeneracy decomposition) into the inner-
and outer-degenerate parts, killed by `ezComponent_inner_degeneracy_comp_PInfty` and
`ezComponent_outer_degeneracy_comp_PInfty` respectively. -/
lemma degenerate_shuffleMap_comp_PInfty (X : BisimplicialObject C) :
    (𝟙 (F₁.obj X) - retractionN₁ X ≫ inclusionN₁ X) ≫ shuffleMap X ≫
        (PInfty : F₂.obj X ⟶ F₂.obj X) = 0 := by
  ext n
  rw [HomologicalComplex.comp_f, HomologicalComplex.zero_f]
  apply HomologicalComplex₂.total.hom_ext
  intro p q hpq
  simp only [ComplexShape.π_def] at hpq
  subst hpq
  rw [comp_zero]
  set ι := HomologicalComplex₂.ιTotal (doubleComplex X) (ComplexShape.down ℕ) p q (p + q)
    (by simp [ComplexShape.π_def]) with hι
  have hr : ι ≫ (retractionN₁ X ≫ inclusionN₁ X).f (p + q)
      = (((PInfty (X := X)).f p).app (Opposite.op ⦋q⦌) ≫
          (PInfty (X := X.obj (Opposite.op ⦋p⦌))).f q) ≫ ι := by
    rw [hι, retractionN₁, inclusionN₁, ← Functor.map_comp, HomologicalComplex₂.totalFunctor_map,
      HomologicalComplex₂.ιTotal_map]
    congr 1
    simp only [HomologicalComplex.comp_f, Functor.mapHomologicalComplex_map_f,
      NatTrans.mapHomologicalComplex_app_f, mooreRetraction, mooreInclusion]
    slice_lhs 2 3 => rw [← HomologicalComplex.comp_f, ← Functor.map_comp,
      ← HomologicalComplex.comp_f, PInftyToNormalizedMooreComplex_comp_inclusionOfMooreComplexMap]
    rw [← HomologicalComplex.comp_f, ← HomologicalComplex.comp_f,
      ← alternatingFaceMapComplex_map_f, ← HomologicalComplex.comp_f]
    congr 1
    rw [← Category.assoc]
    erw [← PInftyToNormalizedMooreComplex_naturality]
    rw [Category.assoc, PInftyToNormalizedMooreComplex_comp_inclusionOfMooreComplexMap]
    rfl
  have he : ι ≫ (𝟙 (F₁.obj X) - retractionN₁ X ≫ inclusionN₁ X).f (p + q)
      = (𝟙 _ - (((PInfty (X := X)).f p).app (Opposite.op ⦋q⦌) ≫
          (PInfty (X := X.obj (Opposite.op ⦋p⦌))).f q)) ≫ ι := by
    rw [HomologicalComplex.sub_f_apply, Preadditive.comp_sub, Preadditive.sub_comp, hr]
    simp
  rw [← Category.assoc, he, Category.assoc]
  -- (𝟙 - Pout ≫ Pin) ≫ (ι ≫ (∇ ≫ PInfty).f) = 0
  rw [HomologicalComplex.comp_f]
  dsimp only [shuffleMap]
  rw [HomologicalComplex₂.ι_totalDesc_assoc]
  simp only [eqToHom_refl, Category.comp_id]
  have hPin : (PInfty (X := X.obj (Opposite.op ⦋p⦌))).f q
      = 𝟙 _ - (QInfty (X := X.obj (Opposite.op ⦋p⦌))).f q := by
    rw [eq_sub_iff_add_eq]
    exact PInfty_f_add_QInfty_f (X := X.obj (Opposite.op ⦋p⦌)) q
  have hPout : ((PInfty (X := X)).f p).app (Opposite.op ⦋q⦌)
      = 𝟙 _ - ((QInfty (X := X)).f p).app (Opposite.op ⦋q⦌) := by
    have key := congrArg (fun f => NatTrans.app f (Opposite.op ⦋q⦌))
      (PInfty_f_add_QInfty_f (X := X) p)
    rw [eq_sub_iff_add_eq]; exact key
  rw [Preadditive.sub_comp]
  erw [Category.id_comp]
  rw [sub_eq_zero, Category.assoc, hPin, Preadditive.sub_comp]
  erw [Category.id_comp]
  rw [QInfty_inner_ezComponent_PInfty, sub_zero, hPout, Preadditive.sub_comp]
  erw [Category.id_comp]
  rw [QInfty_outer_ezComponent_PInfty, sub_zero]

/-- **Dold–Kan round-trip absorption, `PInfty` form.** The `PInfty`-idempotent round-trip
`retractionN₁ ≫ inclusionN₁` on `F₁` is absorbed under `shuffleMap … ≫ PInfty` on the diagonal `F₂`:
the degenerate-`F₁` correction `(1 − retractionN₁ ≫ inclusionN₁)` is sent by `∇` to a degenerate
element of the diagonal, which `PInfty` annihilates. Pure `Preadditive` plumbing over the genuine
content `degenerate_shuffleMap_comp_PInfty`. -/
@[reassoc]
lemma retractionN₁_inclusionN₁_shuffleMap_PInfty (X : BisimplicialObject C) :
    retractionN₁ X ≫ inclusionN₁ X ≫ shuffleMap X ≫ (PInfty : F₂.obj X ⟶ F₂.obj X)
      = shuffleMap X ≫ PInfty := by
  have key := degenerate_shuffleMap_comp_PInfty X
  rw [Preadditive.sub_comp, Category.id_comp, sub_eq_zero] at key
  rw [← Category.assoc]
  exact key.symm

/-- **`∇`-norm, `retractionN₂` form** (the (6b) `PInfty` absorption, repackaged with the diagonal
retraction by cancelling the split-mono `inclusionN₂`). -/
@[reassoc]
lemma retractionN₁_inclusionN₁_shuffleMap_retractionN₂ (X : BisimplicialObject C) :
    retractionN₁ X ≫ inclusionN₁ X ≫ shuffleMap X ≫ retractionN₂ X
      = shuffleMap X ≫ retractionN₂ X := by
  haveI : Mono (inclusionN₂ X) := by rw [inclusionN₂]; infer_instance
  rw [← cancel_mono (inclusionN₂ X)]
  simp only [Category.assoc]
  rw [inclusionN₂, retractionN₂, PInftyToNormalizedMooreComplex_comp_inclusionOfMooreComplexMap]
  simp only [Functor.comp_obj, normalizedMooreComplex_obj, HomologicalComplex₂.totalFunctor_obj,
    retractionN₁_inclusionN₁_shuffleMap_PInfty X]

/-- **`f = AW` preserves norms** (EM (2.12), the `f` half). A diagonal degeneracy `⟨θ,θ⟩`
(`θ` non-mono) followed by `alexanderWhitney` lands in the degenerate part of `F₁`, killed by the
bi-normalized retraction `retractionN₁`. **Genuine Dold–Kan combinatorial input** (Phase-4-level):
`AW`'s front/back-face split of a degenerate diagonal simplex is degenerate in at least one factor.
-/
lemma alexanderWhitney_diagDegen_comp_retractionN₁ {s q : ℕ} (X : BisimplicialObject C)
    (θ : (⦋q⦌ : SimplexCategory) ⟶ ⦋s⦌) (hθ : ¬ Mono θ) :
    DerivedOp.realize X (Finsupp.single (⟨θ, θ⟩ : OpLetter s q) 1) ≫
        (alexanderWhitney X).f q ≫ (retractionN₁ X).f q = 0 := by
  sorry

/-- **`h = ∇f` preserves norms — for free.** A diagonal degeneracy `⟨θ,θ⟩` (`θ` non-mono) followed
by `hOp` dies under `retractionN₂`. Assembled from the `f`-half
(`alexanderWhitney_diagDegen_comp_retractionN₁`) and the `∇`-half (6b,
`retractionN₁_inclusionN₁_shuffleMap_retractionN₂`) via `realize_hOp` (`h = AW ≫ ∇`). -/
lemma hOp_diagDegen_comp_retractionN₂ {s q : ℕ} (X : BisimplicialObject C)
    (θ : (⦋q⦌ : SimplexCategory) ⟶ ⦋s⦌) (hθ : ¬ Mono θ) :
    DerivedOp.realize X ((hOp q).comp (Finsupp.single (⟨θ, θ⟩ : OpLetter s q) 1)) ≫
        (retractionN₂ X).f q = 0 := by
  -- `realize (h ∘ ⟨θ,θ⟩) = ⟨θ,θ⟩ ≫ h`, and `h = AW ≫ ∇`; split the chain maps levelwise.
  rw [realize_comp, realize_hOp]
  simp only [HomologicalComplex.comp_f, Category.assoc]
  -- `∇`-half (levelwise): insert `retractionN₁ ≫ inclusionN₁` between `AW` and `∇`.
  have h6 := HomologicalComplex.congr_hom (retractionN₁_inclusionN₁_shuffleMap_retractionN₂ X) q
  simp only [HomologicalComplex.comp_f] at h6
  rw [← h6]
  -- `f`-half: the leading `⟨θ,θ⟩ ≫ AW ≫ retractionN₁` is already zero.
  slice_lhs 1 3 => rw [alexanderWhitney_diagDegen_comp_retractionN₁ X θ hθ]
  simp only [Limits.zero_comp]

/-- **`h = ∇f` kills *any* norm** — the `IsNorm`-generalized form of `hOp_diagDegen_comp_retractionN₂`.
For any `M` in the diagonal degenerate subcomplex (`IsNorm M`), `h` followed by the diagonal
retraction `ρ₂` vanishes. Structural induction over `IsNorm`: the linear cases are
`realize`-linearity; `diagDegen` peels the leading degeneracy via `comp_assoc` and reduces to the
single-letter `hOp_diagDegen_comp_retractionN₂`. -/
lemma hOp_diagDegen_comp_retractionN₂' {s q : ℕ} (X : BisimplicialObject C)
    (M : DerivedOp s q) (hM : IsNorm M) :
    DerivedOp.realize X ((hOp q).comp M) ≫ (retractionN₂ X).f q = 0 := by
  induction hM with
  | zero => simp [DerivedOp.comp, realize_zero]
  | add _ _ ihM ihN =>
      rw [DerivedOp.comp_add_right, realize_add, Preadditive.add_comp, ihM, ihN, add_zero]
  | neg _ ihM =>
      rw [DerivedOp.comp_neg, realize_neg, Preadditive.neg_comp, ihM, neg_zero]
  | diagDegen θ hθ N =>
      rw [← DerivedOp.comp_assoc, realize_comp, Category.assoc,
        hOp_diagDegen_comp_retractionN₂ X θ hθ, Limits.comp_zero]

/- ⚠️ DELETE-LATER (superseded by the bi-graded `BiIsNorm` route, see the §"Bi-graded
   (tensor-side) derived operators" section + its integration TODO near `end BisimplicialObject`).

   The following lemmas are the **analytic décalage descent** — paper-INDEPENDENT, not in EM. The
   `IsNorm.hPrimeDegen` generator and its kill lemma `hPrimeIter_hPrimeDegen_comp_retractionN₂` have
   already been removed (`phi_op_isNorm` collapses to pure `diagDegen`), so this whole chain is now
   **unused** and only retained pending the bi-graded `BiIsNorm` cleanup.

   • Tier A — dead / fully superseded, nothing depends on them:
       `realize_prime_comp_lastFace`, `alexanderWhitney_prime_comp_retractionN₁`,
       `realize_prime_hOp_mod_norm`, `frontal_lastFace_PInfty_kill` (the lone open `sorry` on this
       route), `prime_preserves_PInfty_kill`, `prime_preserves_retractionN₂_kill`.
   • KEEP: `lastFace_comp_prime` / `lastFace_comp_hPrime{,_comp_D0}` (exact-induction backbone),
       `hOp_diagDegen_comp_retractionN₂` (+ its `f`-half `alexanderWhitney_diagDegen_comp_retractionN₁`,
       still consumed), `IsNorm`/`IsNorm.prime`/`IsNorm.kill`, `DerivedOp.primeIter`, `prime_degenOp`. -/

/-- **Realized `F₀`-naturality of `prime`** (the realize-level `realize_prime` characterization).
The realization of EM's Lemma I.3.3 operator identity `lastFace_comp_prime` (`F₀ M' = M F₀`): the
primed operator `M'` intertwines the bottom face `F₀ = realize (lastFaceOp _)` with `M`. Together
with frontality of `M'` (`prime_frontal`: `M'` fixes the bottom vertex `0`), this **characterizes**
`realize X M.prime` — it is the unique frontal lift of `realize X M` along `F₀`.

Provable in one step: `← realize_comp` on both sides, then `lastFace_comp_prime`. -/
lemma realize_prime_comp_lastFace {s q : ℕ} (X : BisimplicialObject C) (M : DerivedOp s q) :
    DerivedOp.realize X M.prime ≫ DerivedOp.realize X (lastFaceOp q)
      = DerivedOp.realize X (lastFaceOp s) ≫ DerivedOp.realize X M := by
  simp only [← realize_comp, lastFace_comp_prime]

/-- **`f = AW` commutes with priming, modulo the `F₁` Moore retraction** (the realize-level
*décalage of `f`*). EM (md 122–126, 213): `f` maps norms to norms *uniformly in dimension*, with
the bottom face `F₀` always landing in the second tensor factor; so the derived operator obtained
by priming the diagonal input agrees with `f` one dimension up once the degenerate part of `F₁` is
projected away. Here `f = alexanderWhitney` and `ρ₁ = retractionN₁` (first-factor normalization).

This is the `f`-half of "`h` commutes with prime mod norms"; combined with the (level-uniform)
`∇`-half `retractionN₁_inclusionN₁_shuffleMap_retractionN₂` it yields `realize_prime_hOp_mod_norm`.
-/
lemma alexanderWhitney_prime_comp_retractionN₁ (X : BisimplicialObject C) (q : ℕ) :
    DerivedOp.realize X ((hOp q).prime) ≫ (alexanderWhitney X).f (q + 1) ≫ (retractionN₁ X).f (q + 1)
      = DerivedOp.realize X (hOp (q + 1)) ≫ (alexanderWhitney X).f (q + 1)
          ≫ (retractionN₁ X).f (q + 1) := by
  sorry




-- /-- **`prime` preserves the `PInfty`-kill**, in `PInfty` form. If `realize X M` lands in the
-- `PInfty`-degenerate part (`≫ PInfty = 0`), then so does `realize X M.prime`.

-- Pure plumbing over the décalage-descent primitive `frontal_lastFace_PInfty_kill`, instantiated at
-- `N = M.prime`: `M.prime` is frontal (`prime_frontal`) and its bottom face recovers `realize X M`
-- (`realize_prime_comp_lastFace`). -/
-- lemma prime_preserves_PInfty_kill {s q : ℕ} (X : BisimplicialObject C) (M : DerivedOp s q)
--     (h : DerivedOp.realize X M ≫ (PInfty : F₂.obj X ⟶ F₂.obj X).f q = 0) :
--     DerivedOp.realize X M.prime ≫ (PInfty : F₂.obj X ⟶ F₂.obj X).f (q + 1) = 0 :=
--   frontal_lastFace_PInfty_kill X M M.prime (prime_frontal M)
--     (realize_prime_comp_lastFace X M) h

-- /-- **One-directional `prime`–norm bridge** — the analytic EM (2.12) primitive (now unused; its
-- former consumer `hPrimeIter_hPrimeDegen_comp_retractionN₂` was removed with `IsNorm.hPrimeDegen`).
-- If a derived operator's realization dies under `retractionN₂` (its image is diagonally
-- Moore-degenerate), then so does its `prime`'s.

-- **Reduced** to `prime_preserves_PInfty_kill` by the `retractionN₂` ↔ `PInfty` dictionary: `ρ₂ ≫ ι₂ =
-- PInfty` (`PInftyToNormalizedMooreComplex_comp_inclusionOfMooreComplexMap`) and `ι₂` is a (Moore)
-- mono, so `· ≫ ρ₂ = 0 ↔ · ≫ PInfty = 0`. -/
-- lemma prime_preserves_retractionN₂_kill {s q : ℕ} (X : BisimplicialObject C) (M : DerivedOp s q)
--     (h : DerivedOp.realize X M ≫ (retractionN₂ X).f q = 0) :
--     DerivedOp.realize X M.prime ≫ (retractionN₂ X).f (q + 1) = 0 := by
--   have hfac : ∀ n, (retractionN₂ X).f n ≫ (inclusionN₂ X).f n
--       = (PInfty : F₂.obj X ⟶ F₂.obj X).f n := fun n => by
--     rw [inclusionN₂, retractionN₂, ← HomologicalComplex.comp_f,
--       PInftyToNormalizedMooreComplex_comp_inclusionOfMooreComplexMap]
--   haveI : Mono ((inclusionN₂ X).f (q + 1)) := by
--     rw [inclusionN₂, inclusionOfMooreComplexMap_f]; infer_instance
--   have hP : DerivedOp.realize X M ≫ (PInfty : F₂.obj X ⟶ F₂.obj X).f q = 0 := by
--     rw [← hfac q, ← Category.assoc, h, Limits.zero_comp]
--   have hP' := prime_preserves_PInfty_kill X M hP
--   refine zero_of_comp_mono ((inclusionN₂ X).f (q + 1)) ?_
--   rw [Category.assoc, hfac (q + 1)]; exact hP'

/-- A `subtraction` convenience: `IsNorm M → IsNorm N → IsNorm (M - N)`. -/
lemma IsNorm.sub {s q : ℕ} {M N : DerivedOp s q} (hM : IsNorm M) (hN : IsNorm N) :
    IsNorm (M - N) := by rw [sub_eq_add_neg]; exact hM.add hN.neg

/-- A norm absorbs arbitrary right composition (the degeneracy stays on the output side). -/
lemma IsNorm.comp_right {s s' q : ℕ} {M : DerivedOp s q} (hM : IsNorm M) (N : DerivedOp s' s) :
    IsNorm (M.comp N) := by
  induction hM generalizing s' with
  | zero => rw [DerivedOp.zero_comp]; exact IsNorm.zero
  | add _ _ ihM ihN => rw [DerivedOp.add_comp]; exact (ihM N).add (ihN N)
  | neg _ ihM => rw [DerivedOp.neg_comp]; exact (ihM N).neg
  | diagDegen θ hθ N₀ => rw [DerivedOp.comp_assoc]; exact IsNorm.diagDegen θ hθ _

/-- **Every norm dies under `retractionN₂`** (for every `X`). Structural induction: linear cases are
`realize`-linearity; the two generators are the (2)-diagonal kill and EM (2.12). -/
lemma IsNorm.kill {s q : ℕ} {M : DerivedOp s q} (h : IsNorm M) (X : BisimplicialObject C) :
    DerivedOp.realize X M ≫ (retractionN₂ X).f q = 0 := by
  induction h with
  | zero => rw [realize_zero, Limits.zero_comp]
  | add _ _ ihM ihN => rw [realize_add, Preadditive.add_comp, ihM, ihN, add_zero]
  | neg _ ihM => rw [realize_neg, Preadditive.neg_comp, ihM, neg_zero]
  | diagDegen θ hθ N => exact realize_comp_diagLetter_not_mono_comp_retractionN₂ X θ hθ N

/-- **The norm class is closed under `prime`** — structural: `prime` maps each generator to a
generator (`⟨θ,θ⟩∘N ↦ ⟨primeHom θ,primeHom θ⟩∘N'` via
`prime_single_diag`+`primeHom_not_mono`; the `h' Dᵢ` generator with `k` primes ↦ the one
with `k+1`). This is what lets the *exact* IH be primed in `phi_op_isNorm`. -/
lemma IsNorm.prime {s q : ℕ} {M : DerivedOp s q} (h : IsNorm M) : IsNorm M.prime := by
  induction h with
  | zero => rw [prime_zero]; exact IsNorm.zero
  | add _ _ ihM ihN => rw [prime_add]; exact ihM.add ihN
  | neg _ ihM => rw [prime_neg]; exact ihM.neg
  | diagDegen θ hθ N =>
      rw [prime_comp, prime_single_diag]
      exact IsNorm.diagDegen (primeHom θ) (primeHom_not_mono hθ) N.prime

private lemma simplex_one_hom_ext {f g : (⦋1⦌ : SimplexCategory) ⟶ ⦋1⦌}
    (h : ∀ j, SimplexCategory.Hom.toOrderHom f j = SimplexCategory.Hom.toOrderHom g j) :
    f = g := by
  apply SimplexCategory.Hom.ext
  apply OrderHom.ext
  funext j
  exact h j

private lemma hLetter_one_zero :
    hLetter 1 0 (default : Shuffle 0 1) =
      ⟨SimplexCategory.σ 0 ≫ SimplexCategory.δ 1, 𝟙 _⟩ := by
  simp only [hLetter, Nat.reduceAdd, Fin.isValue, Fin.coe_ofNat_eq_mod, Nat.zero_mod, Nat.sub_zero,
    eqToHom_refl, shuffleFstHom, SimplexCategory.len_mk, ι_front, SimplexCategory.mkHom,
    Fin.val_eq_zero, Fin.zero_eta, Category.comp_id, Category.id_comp, shuffleSndHom, ι_back,
    zero_add, Fin.eta, OpLetter.mk.injEq]
  constructor
  · apply simplex_one_hom_ext
    intro j
    fin_cases j <;> rfl
  · apply simplex_one_hom_ext
    intro j
    fin_cases j <;> rfl

private lemma hLetter_one_one :
    hLetter 1 1 (default : Shuffle 1 0) =
      ⟨𝟙 _, SimplexCategory.σ 0 ≫ SimplexCategory.δ 0⟩ := by
  simp only [hLetter, Nat.reduceAdd, Fin.isValue, Fin.coe_ofNat_eq_mod, Nat.reduceMod,
    Nat.add_one_sub_one, Nat.add_zero, eqToHom_refl, shuffleFstHom, SimplexCategory.len_mk, ι_front,
    SimplexCategory.mkHom, Fin.eta, Category.comp_id, Category.id_comp, shuffleSndHom, ι_back,
    Nat.mod_succ, Fin.val_eq_zero, add_zero, Fin.mk_one, OpLetter.mk.injEq]
  constructor
  · apply simplex_one_hom_ext
    intro j
    fin_cases j <;> rfl
  · apply simplex_one_hom_ext
    intro j
    fin_cases j <;> rfl

private lemma phi_op_zero_eq_diagDegen :
    (phiOp 0).comp (boundaryOp 0) + (boundaryOp 1).comp (phiOp 1) + idOp 1 - hOp 1 =
      (D0op 0).comp (faceOp 0 1) := by
  simp only [Nat.reduceAdd, phiOp, DerivedOp.zero_comp, prime_zero, neg_zero, zero_add, Fin.isValue]
  rw [boundaryOp_eq 1, DerivedOp.sub_comp, lastFace_comp_hPrime_comp_D0 0]
  abel_nf
  simp [truncBoundaryOp, hOp, D0op, faceOp, idOp, hLetter_one_zero, hLetter_one_one,
    DerivedOp.prime, OpLetter.prime, DerivedOp.add_comp, DerivedOp.comp_add_right,
    DerivedOp.neg_comp,
    DerivedOp.single_comp_single, Finsupp.mapDomain_add, Finsupp.mapDomain_single,
    Shuffle.sign_default_zero_left,
    Shuffle.sign_default_zero_right, OpLetter.comp, primeHom_comp, primeHom_δ, primeHom_σ,
    primeHom_id, Category.assoc]
  have hδ₁σ₀ :
      SimplexCategory.δ (1 : Fin 3) ≫ SimplexCategory.σ (0 : Fin 2) = 𝟙 ⦋1⦌ := by
    apply simplex_one_hom_ext; intro j; fin_cases j <;> rfl
  have hδ₂σ₀ :
      SimplexCategory.δ (2 : Fin 3) ≫ SimplexCategory.σ (0 : Fin 2) =
        SimplexCategory.σ (0 : Fin 1) ≫ SimplexCategory.δ (1 : Fin 2) := by
    apply simplex_one_hom_ext; intro j; fin_cases j <;> rfl
  have hδ₁σ₁σ₀δ₁ :
      SimplexCategory.δ (1 : Fin 3) ≫ SimplexCategory.σ (1 : Fin 2) ≫
          SimplexCategory.σ (0 : Fin 1) ≫ SimplexCategory.δ (1 : Fin 2) =
        SimplexCategory.σ (0 : Fin 1) ≫ SimplexCategory.δ (1 : Fin 2) := by
    apply simplex_one_hom_ext; intro j; fin_cases j <;> rfl
  have hδ₂σ₁σ₀δ₁ :
      SimplexCategory.δ (2 : Fin 3) ≫ SimplexCategory.σ (1 : Fin 2) ≫
          SimplexCategory.σ (0 : Fin 1) ≫ SimplexCategory.δ (1 : Fin 2) =
        SimplexCategory.σ (0 : Fin 1) ≫ SimplexCategory.δ (1 : Fin 2) := by
    apply simplex_one_hom_ext; intro j; fin_cases j <;> rfl
  have hδ₁σ₁ :
      SimplexCategory.δ (1 : Fin 3) ≫ SimplexCategory.σ (1 : Fin 2) = 𝟙 ⦋1⦌ := by
    apply simplex_one_hom_ext; intro j; fin_cases j <;> rfl
  have hδ₂σ₁ :
      SimplexCategory.δ (2 : Fin 3) ≫ SimplexCategory.σ (1 : Fin 2) = 𝟙 ⦋1⦌ := by
    apply simplex_one_hom_ext; intro j; fin_cases j <;> rfl
  simp [hδ₁σ₀, hδ₂σ₀, hδ₁σ₁σ₀δ₁, hδ₂σ₁σ₀δ₁, hδ₁σ₁, hδ₂σ₁]
  abel

private lemma sigma_zero_not_mono : ¬ Mono (SimplexCategory.σ (0 : Fin 1)) := by
  rw [SimplexCategory.mono_iff_injective]
  intro h
  have h01 := h (show
    (SimplexCategory.Hom.toOrderHom (SimplexCategory.σ (0 : Fin 1))) (0 : Fin 2) =
      (SimplexCategory.Hom.toOrderHom (SimplexCategory.σ (0 : Fin 1))) (1 : Fin 2) from rfl)
  norm_num at h01

/-- **Base case (EM `q = 1`, degree 1)**, md 169–171: the degree-1 homotopy identity, as a norm.
Needs EM (2.11)'s explicit degree-1 value of `h` (item 4) — an `hOp` low-degree input. -/
lemma phi_op_isNorm_zero :
    IsNorm ((phiOp 0).comp (boundaryOp 0) + (boundaryOp 1).comp (phiOp 1) + idOp 1 - hOp 1) := by
  rw [phi_op_zero_eq_diagDegen, D0op]
  exact IsNorm.diagDegen (SimplexCategory.σ (0 : Fin 1)) sigma_zero_not_mono (faceOp 0 1)

/-- **The EM homotopy operator `Φ∂ + ∂Φ + i − h` satisfies the `prime`-recursion exactly** (no norm
remainder), md 177–194. The whole "modulo norms" content of the homotopy identity collapses into the
base degree (`phi_op_isNorm_zero`); the inductive step is pure operator algebra.

Cancellations: write `∂ = F₀ − ∂'` (`boundaryOp_eq`), `Φ_{·+1} = −Φ' + h'D₀` (`phiOp`). Then
* `Φ'F₀` (from `Φ∂`) cancels `−Φ'F₀` (from `∂Φ`, via `lastFace_comp_prime` `F₀Φ' = ΦF₀`), and likewise
  the `h'D₀F₀` terms cancel;
* `h'D₀∂'`, `∂'h'D₀`, and the surviving `h'` cancel using the primed chain-map law `∂'h' = h'∂'`
  (`boundaryOp_comp_hOp`), `∂'D₀ = i − D₀∂'` (`boundary_comp_D0` + `F₀D₀ = i`), and the right unit. -/
lemma phi_op_succ_eq (q : ℕ) :
    (phiOp (q + 1)).comp (boundaryOp (q + 1)) + (boundaryOp (q + 1 + 1)).comp (phiOp (q + 1 + 1)) +
        idOp (q + 1 + 1) - hOp (q + 1 + 1) =
      ((phiOp q).comp (boundaryOp q) + (boundaryOp (q + 1)).comp (phiOp (q + 1)) +
        idOp (q + 1) - hOp (q + 1)).prime := by
  simp only [sub_eq_add_neg, prime_add, prime_neg]
  rw [prime_comp, prime_comp, prime_boundaryOp, prime_boundaryOp, prime_idOp]
  conv_lhs => simp only [phiOp, boundaryOp_eq]
  simp only [DerivedOp.sub_comp, DerivedOp.comp_sub, DerivedOp.neg_comp, DerivedOp.comp_neg,
    DerivedOp.add_comp, DerivedOp.comp_add_right]
  rw [lastFace_comp_prime, lastFace_comp_hPrime_comp_D0]
  conv_rhs => simp only [phiOp]
  -- md 179: `∂'₂·h''D₀ = h' − h'D₀·∂'` (the only non-cancelling content)
  have stepA : (truncBoundaryOp (q + 1 + 1)).comp ((hOp (q + 1 + 1)).prime)
      = (hOp (q + 1)).prime.comp (truncBoundaryOp (q + 1 + 1)) := by
    have h2 := congrArg DerivedOp.prime (boundaryOp_comp_hOp (q + 1))
    simp only [prime_comp, prime_boundaryOp] at h2
    exact h2
  have stepC : (truncBoundaryOp (q + 1 + 1)).comp (D0op (q + 1 + 1))
      = idOp (q + 1 + 1) - (D0op (q + 1)).comp (truncBoundaryOp (q + 1)) := by
    have hb := boundary_comp_D0 (q + 1)
    rw [boundaryOp_eq (q + 1 + 1), DerivedOp.sub_comp, lastFace_comp_D0] at hb
    rw [← hb]; abel
  have hkey : (truncBoundaryOp (q + 1 + 1)).comp ((hOp (q + 1 + 1)).prime.comp (D0op (q + 1 + 1)))
      = (hOp (q + 1)).prime
        - ((hOp (q + 1)).prime.comp (D0op (q + 1))).comp (truncBoundaryOp (q + 1)) := by
    rw [← DerivedOp.comp_assoc, stepA, DerivedOp.comp_assoc, stepC, DerivedOp.comp_sub, comp_idOp,
      ← DerivedOp.comp_assoc]
  rw [hkey]
  simp only [DerivedOp.add_comp, DerivedOp.neg_comp]
  abel

/-- **(5b) exact-identity form**: `Φ∂ + ∂Φ + i − h` is a norm, for every degree `q+1`. By
`induction` the inductive step is just `phi_op_succ_eq` + `IsNorm.prime` on the IH (the homotopy
identity holds *exactly* up the `prime` tower); all norm content is in `phi_op_isNorm_zero`. -/
lemma phi_op_isNorm (q : ℕ) :
    IsNorm ((phiOp q).comp (boundaryOp q) + (boundaryOp (q + 1)).comp (phiOp (q + 1)) +
      idOp (q + 1) - hOp (q + 1)) := by
  induction q with
  | zero => exact phi_op_isNorm_zero
  | succ q ih => rw [phi_op_succ_eq q]; exact ih.prime

/-- **(5b) The EM induction, operator level, modulo norms**, at degree `q+1` (markdown 177–194):
`Φ∂ + ∂Φ + i ≡ h` (i.e. EM's `∂Φ + Φ∂ = h − i`; matches `Homotopy.comm` for
`Homotopy (AW≫∇) (𝟙)`). Proved by induction on `q`, replaying EM's computation:
`∂ = F₀ − ∂'` (`boundaryOp_eq`); `∂Φ = −∂'Φ' + h'∂D₀` with `∂D₀ = D₀∂'` (`boundary_comp_D0`);
`Φ∂' = −Φ'∂' + h'D₀∂'` (recursion `phiOp`); `F₀Φ = −F₀Φ' + h` (`lastFace_comp_hPrime_comp_D0`);
combine via `∂ = F₀ − ∂'`, priming the IH with `prime_comp`/`prime_add`.

Norm kill (no fork — see item 2): all norm terms are `D(K×L)` diagonal degeneracies.
`D₀Φ`, `Φ'D_i = δ^i D_{i-1}` die by `realize_comp_diagLetter_not_mono_comp_retractionN₂` (diagonal
degeneracy on the left); `h'D₀`-composites die by `hOp_prime_comp_D0_comp_comp_retractionN₂`
(EM (2.12)). -/
lemma phi_comm_op (X : BisimplicialObject C) (q : ℕ) :
    (DerivedOp.realize X ((phiOp q).comp (boundaryOp q)) +
        DerivedOp.realize X ((boundaryOp (q + 1)).comp (phiOp (q + 1))) +
        DerivedOp.realize X (idOp (q + 1))) ≫ (retractionN₂ X).f (q + 1) =
      DerivedOp.realize X (hOp (q + 1)) ≫ (retractionN₂ X).f (q + 1) := by
  have h := (phi_op_isNorm q).kill X
  rw [realize_sub, realize_add, realize_add, Preadditive.sub_comp] at h
  exact sub_eq_zero.mp h

/-- **EM's homotopy identity `∂Φ + Φ∂ = ∇f − i` modulo norms**, in `dNext`/`prevD` form and
postcomposed with `retractionN₂` (the "modulo norms"). This is the inductive heart of EM Thm 2.1a
(markdown lines 169–194). -/
lemma phi_comm_retraction (X : BisimplicialObject C) (n : ℕ) :
    (dNext n (phiHomRaw X) + prevD n (phiHomRaw X) +
        (𝟙 (F₂.obj X) : (F₂.obj X) ⟶ (F₂.obj X)).f n) ≫ (retractionN₂ X).f n =
      (alexanderWhitney X ≫ shuffleMap X).f n ≫ (retractionN₂ X).f n := by
  have hid : ∀ m : ℕ, (𝟙 (F₂.obj X) : (F₂.obj X) ⟶ (F₂.obj X)).f m
      = DerivedOp.realize X (idOp m) := by
    intro m; rw [HomologicalComplex.id_f, idOp, realize_single_id]
  cases n with
  | zero =>
      have hp : prevD 0 (phiHomRaw X) = 0 := by
        rw [prevD_phiHomRaw]; simp [phiOp, realize_comp]
      have hd : dNext 0 (phiHomRaw X) = 0 := by rw [dNext]; simp
      rw [hp, hd]
      simp only [zero_add]
      rw [hid, ← realize_hOp]
      exact (hOp_zero_comp_retraction X).symm
  | succ m =>
      rw [dNext_phiHomRaw, prevD_phiHomRaw, hid, ← realize_hOp]
      exact phi_comm_op X m

/-! ### Descent to the normalized diagonal `N₂` -/

/-- The normalized Moore complex `N₂` is a retract of `F₂`: `inclusionN₂ ≫ retractionN₂ = 𝟙`. -/
@[reassoc]
lemma inclusionN₂_comp_retractionN₂ (X : BisimplicialObject C) :
    inclusionN₂ X ≫ retractionN₂ X = 𝟙 (N₂.obj X) := by
  rw [inclusionN₂, retractionN₂]
  exact (AlgebraicTopology.DoldKan.splitMonoInclusionOfMooreComplexMap (diag.obj X)).id

/-- `Φ` conjugated onto the normalized diagonal `N₂.obj X` (EM's homotopy on `K ×_N L`):
`inclusionN₂ ≫ phiOp.realize ≫ retractionN₂`. -/
noncomputable def phiHomNorm (X : BisimplicialObject C) (i j : ℕ) :
    (N₂.obj X).X i ⟶ (N₂.obj X).X j :=
  if h : j = i + 1 then
    (inclusionN₂ X).f i ≫ (phiOp i).realize X ≫ eqToHom (by rw [h]) ≫ (retractionN₂ X).f j
  else 0

lemma phiHomNorm_zero (X : BisimplicialObject C) (i j : ℕ)
    (hij : ¬ (ComplexShape.down ℕ).Rel j i) : phiHomNorm X i j = 0 :=
  dif_neg fun h => hij (by rw [ComplexShape.down_Rel]; omega)

/-- `phiHomNorm` is the conjugate of `phiHomRaw` by `inclusionN₂ … retractionN₂`. -/
lemma phiHomNorm_eq (X : BisimplicialObject C) (i j : ℕ) :
    phiHomNorm X i j = (inclusionN₂ X).f i ≫ phiHomRaw X i j ≫ (retractionN₂ X).f j := by
  by_cases h : j = i + 1
  · simp only [phiHomNorm, phiHomRaw, dif_pos h, Category.assoc]
  · simp only [phiHomNorm, phiHomRaw, dif_neg h, Limits.comp_zero, Limits.zero_comp]

/-- `phiHomNorm` as an explicit family (for the `dNext`/`prevD` conjugation lemmas). -/
private lemma phiHomNorm_funext (X : BisimplicialObject C) :
    phiHomNorm X = fun a b => (inclusionN₂ X).f a ≫ phiHomRaw X a b ≫ (retractionN₂ X).f b := by
  funext a b; exact phiHomNorm_eq X a b

/-- `dNext` commutes with the `inclusionN₂ … retractionN₂` conjugation (both are chain maps). -/
lemma dNext_phiHomNorm (X : BisimplicialObject C) (i : ℕ) :
    dNext i (phiHomNorm X) =
      (inclusionN₂ X).f i ≫ dNext i (phiHomRaw X) ≫ (retractionN₂ X).f i := by
  rw [phiHomNorm_funext, dNext_comp_left, dNext_comp_right]

/-- `prevD` commutes with the `inclusionN₂ … retractionN₂` conjugation (both are chain maps). -/
lemma prevD_phiHomNorm (X : BisimplicialObject C) (j : ℕ) :
    prevD j (phiHomNorm X) =
      (inclusionN₂ X).f j ≫ prevD j (phiHomRaw X) ≫ (retractionN₂ X).f j := by
  rw [phiHomNorm_funext, prevD_comp_left, prevD_comp_right]


/-- **(6b)** The normalized `AW ≫ ∇` is the `N₂`-conjugate of the unnormalized `AW ≫ ∇`.
Unfolding the definitions, `normalizedAlexanderWhitney ≫ normalizedShuffleMap`
`= ι₂ ≫ AW ≫ (retractionN₁ ≫ inclusionN₁) ≫ ∇ ≫ ρ₂`; the inner Dold–Kan round-trip
`retractionN₁ ≫ inclusionN₁` (the `PInfty` idempotent on `F₁`) is absorbed, leaving
`ι₂ ≫ (AW ≫ ∇) ≫ ρ₂`. -/
lemma normalizedAW_shuffle_eq (X : BisimplicialObject C) :
    normalizedAlexanderWhitney X ≫ normalizedShuffleMap X
      = inclusionN₂ X ≫ (alexanderWhitney X ≫ shuffleMap X) ≫ retractionN₂ X := by
  rw [normalizedAlexanderWhitney, normalizedShuffleMap]
  simp only [Category.assoc]
  haveI : Mono (inclusionN₂ X) := by rw [inclusionN₂]; infer_instance
  rw [← cancel_mono (inclusionN₂ X)]
  simp only [Category.assoc]
  rw [inclusionN₂, retractionN₂, PInftyToNormalizedMooreComplex_comp_inclusionOfMooreComplexMap]
  simp only [Functor.comp_obj, normalizedMooreComplex_obj, HomologicalComplex₂.totalFunctor_obj,
    retractionN₁_inclusionN₁_shuffleMap_PInfty X]

/-- **`AW ≫ ∇ ≃ 𝟙` on the normalized diagonal `N₂`** via the Eilenberg–Mac Lane homotopy `Φ`
(EM Thm 2.1a, `∂Φ + Φ∂ = ∇f − i`). This is the contraction homotopy that discharges the remaining
`sorry` in `homotopyNormalizedAlexanderWhitneyShuffle` (`BisimplicialNormalized.lean`). -/
noncomputable def homotopyAWShuffleNormalized (X : BisimplicialObject C) :
    Homotopy (normalizedAlexanderWhitney X ≫ normalizedShuffleMap X) (𝟙 (N₂.obj X)) where
  hom := phiHomNorm X
  zero := phiHomNorm_zero X
  comm := by
    intro i
    -- `𝟙 N₂` factors through `F₂`: `(𝟙 N₂).f i = ι₂.f i ≫ ρ₂.f i` (`inclusionN₂_comp_retractionN₂`).
    have hid : (𝟙 (N₂.obj X) : (N₂.obj X) ⟶ (N₂.obj X)).f i
        = (inclusionN₂ X).f i ≫ (retractionN₂ X).f i := by
      rw [← HomologicalComplex.comp_f, inclusionN₂_comp_retractionN₂]
    -- Conjugate everything onto `F₂` (6a/6b), then replace `(AW≫∇)≫ρ₂` by the EM identity (5c).
    rw [normalizedAW_shuffle_eq, dNext_phiHomNorm, prevD_phiHomNorm, hid,
      HomologicalComplex.comp_f, HomologicalComplex.comp_f, ← phi_comm_retraction X i]
    -- Both sides are now `ι₂ ≫ (…) ≫ ρ₂`; distribute the sum and kill the `𝟙` term.
    simp only [Preadditive.comp_add, Preadditive.add_comp, Category.assoc,
      HomologicalComplex.id_f, Category.id_comp]

#print axioms homotopyAWShuffleNormalized

/-! ### Bi-graded (tensor-side) derived operators — EM-faithful `prime` route

Following EM `pdfs/mcl2_sections_1_2.md:135`–`147`: a natural operator `M : K_p ⊗ L_s → K_q ⊗ L_r`
on the **tensor product** `K ⊗ L` (modelled by our total complex `F₁`), written uniquely (EM
(2.10), md 141) as a `ℤ`-combination of `β*a_p ⊗ γ*b_s` with *independent* monotone legs
`β : [p] → [q]`, `γ : [r] → [s]`. The derived operator `M ↦ M'` (EM (2.10), md 143–145)
`δ⁰`-shifts both legs.

This **generalizes** the diagonal `OpLetter`/`DerivedOp`, which is the special case `p = s`,
`q = r`: EM's `K × L` is the diagonal bidegree of `K ⊗ L`. The point of the tensor layer is EM's
*structural* proof that `f` and `∇` map norms into norms (md 122–133), hence so does `h = ∇f`
(md 155), yielding EM (2.12) (`h' Dᵢ ∈ D(K × L)`, md 161) **with no analytic décalage descent** —
replacing `frontal_lastFace_PInfty_kill` / `prime_preserves_*_kill` and the
`alexanderWhitney_diagDegen_comp_retractionN₁` sorry. -/

/-- A **bi-graded letter** (EM (2.10) summand, `md 141`): a pair of independent `SimplexCategory`
legs for a natural operator `X_{p,s} ⟶ X_{q,r}` on the tensor side. `fst` is the `K`-leg (outer
simplicial variable), `snd` the `L`-leg (inner). The diagonal `OpLetter s q` is `BiOpLetter s s q q`. -/
structure BiOpLetter (p s q r : ℕ) where
  /-- `K`-side (outer) leg, inducing `X_{p,·} → X_{q,·}` contravariantly. -/
  fst : (⦋q⦌ : SimplexCategory) ⟶ ⦋p⦌
  /-- `L`-side (inner) leg, inducing `X_{·,s} → X_{·,r}` contravariantly. -/
  snd : (⦋r⦌ : SimplexCategory) ⟶ ⦋s⦌

noncomputable instance (p s q r : ℕ) : DecidableEq (BiOpLetter p s q r) := Classical.decEq _

/-- A bi-graded EM operator `K_p ⊗ L_s → K_q ⊗ L_r` (EM (2.10), `md 137`–`141`): a finite
`ℤ`-linear combination of bi-graded letters. -/
abbrev BiDerivedOp (p s q r : ℕ) := BiOpLetter p s q r →₀ ℤ

/-- Realize a single bi-graded letter as a hom between bidegree summands `X_{p,s} ⟶ X_{q,r}` of the
double complex (EM (2.10), `md 141`). The diagonal `OpLetter.realize` is the case `p = s`, `q = r`. -/
noncomputable def BiOpLetter.realizeComponent {p s q r : ℕ} (X : BisimplicialObject C)
    (l : BiOpLetter p s q r) :
    (X.obj (Opposite.op ⦋p⦌)).obj (Opposite.op ⦋s⦌) ⟶
      (X.obj (Opposite.op ⦋q⦌)).obj (Opposite.op ⦋r⦌) :=
  (X.obj (Opposite.op ⦋p⦌)).map l.snd.op ≫ (X.map l.fst.op).app (Opposite.op ⦋r⦌)

/-- The derived operator on a bi-graded letter (EM (2.10), `md 143`–`145`): `δ⁰`-shift both legs.
Reuses the diagonal `primeHom`, since priming acts one leg at a time. -/
def BiOpLetter.prime {p s q r : ℕ} (l : BiOpLetter p s q r) :
    BiOpLetter (p + 1) (s + 1) (q + 1) (r + 1) :=
  ⟨primeHom l.fst, primeHom l.snd⟩

/-- EM's **bi-graded derived operator** `M ↦ M'` (EM (2.10), `md 143`–`145`): prime every letter. -/
noncomputable def BiDerivedOp.prime {p s q r : ℕ} (M : BiDerivedOp p s q r) :
    BiDerivedOp (p + 1) (s + 1) (q + 1) (r + 1) :=
  Finsupp.mapDomain BiOpLetter.prime M

/-- The `k`-fold bigraded derived operator `M ↦ M⁽ᵏ⁾` (EM `md 143`–`145`, iterated). The tensor-side
analogue of `DerivedOp.primeIter`, used to carry EM's `(MN)' = M'N'` (`md 206`) up the tower. -/
noncomputable def BiDerivedOp.primeIter {p s q r : ℕ} :
    (k : ℕ) → BiDerivedOp p s q r → BiDerivedOp (p + k) (s + k) (q + k) (r + k)
  | 0, M => M
  | k + 1, M => (BiDerivedOp.primeIter k M).prime

@[simp] lemma BiDerivedOp.primeIter_succ {p s q r : ℕ} (k : ℕ) (M : BiDerivedOp p s q r) :
    BiDerivedOp.primeIter (k + 1) M = (BiDerivedOp.primeIter k M).prime := rfl

/-- Composition of bi-graded letters (apply `l₁` then `l₂`); legs compose independently
(EM I.3 derived-operator algebra, used for `f' ∇' = (f∇)'` at `md 206`). -/
def BiOpLetter.comp {p s p' s' q r : ℕ} (l₂ : BiOpLetter p' s' q r) (l₁ : BiOpLetter p s p' s') :
    BiOpLetter p s q r :=
  ⟨l₂.fst ≫ l₁.fst, l₂.snd ≫ l₁.snd⟩

/-- `ℤ`-bilinear composition of bi-graded operators (apply `M₁` then `M₂`). -/
noncomputable def BiDerivedOp.comp {p s p' s' q r : ℕ} (M₂ : BiDerivedOp p' s' q r)
    (M₁ : BiDerivedOp p s p' s') : BiDerivedOp p s q r :=
  M₁.sum fun l₁ c₁ => M₂.sum fun l₂ c₂ => Finsupp.single (l₂.comp l₁) (c₁ * c₂)

/-! #### Norms on the tensor side `D(K ⊗ L)`

EM's degenerate subcomplex `D(K ⊗ L)` (the "norms", `md 122`, `md 157`) is generated by operators
with a **leading degeneracy in either factor** (a non-monotone-injective leg). This is the
*one-sided* structure that the diagonal `IsNorm` (leading *diagonal* degeneracy `⟨θ,θ⟩`) cannot
express — and exactly why the tensor layer is needed. -/

/-- A bi-graded operator is a **tensor norm** (`∈ D(K ⊗ L)`, EM `md 122`/`md 157`) if it is built
from letters with a leading degeneracy in the `K`-leg (`degenFst`) or `L`-leg (`degenSnd`), closed
under `+`/`neg`. Structural, so closure under `prime` is manifest (`BiIsNorm.prime`). -/
inductive BiIsNorm : {p s q r : ℕ} → BiDerivedOp p s q r → Prop where
  | zero {p s q r : ℕ} : BiIsNorm (0 : BiDerivedOp p s q r)
  | add {p s q r : ℕ} {M N : BiDerivedOp p s q r} : BiIsNorm M → BiIsNorm N → BiIsNorm (M + N)
  | neg {p s q r : ℕ} {M : BiDerivedOp p s q r} : BiIsNorm M → BiIsNorm (-M)
  | degenFst {p s p' s' q r : ℕ} (θ : (⦋q⦌ : SimplexCategory) ⟶ ⦋p'⦌) (hθ : ¬ Mono θ)
      (φ : (⦋r⦌ : SimplexCategory) ⟶ ⦋s'⦌) (N : BiDerivedOp p s p' s') :
      BiIsNorm (BiDerivedOp.comp (Finsupp.single (⟨θ, φ⟩ : BiOpLetter p' s' q r) 1) N)
  | degenSnd {p s p' s' q r : ℕ} (θ : (⦋q⦌ : SimplexCategory) ⟶ ⦋p'⦌)
      (φ : (⦋r⦌ : SimplexCategory) ⟶ ⦋s'⦌) (hφ : ¬ Mono φ) (N : BiDerivedOp p s p' s') :
      BiIsNorm (BiDerivedOp.comp (Finsupp.single (⟨θ, φ⟩ : BiOpLetter p' s' q r) 1) N)

/-- Multiplicativity of priming on the tensor side: `(M₂ M₁)' = M₂' M₁'` (EM I.3, `md 206`:
`h' ∇' = (h∇)'`). The tensor-side analogue of `prime_comp`. -/
lemma BiOpLetter.prime_comp {p s p' s' q r : ℕ} (l₂ : BiOpLetter p' s' q r)
    (l₁ : BiOpLetter p s p' s') : (l₂.comp l₁).prime = l₂.prime.comp l₁.prime := by
  simp only [BiOpLetter.prime, BiOpLetter.comp, primeHom_comp]

private lemma BiDerivedOp.comp_add_right {p s p' s' q r : ℕ} (M₂ : BiDerivedOp p' s' q r)
    (M N : BiDerivedOp p s p' s') : M₂.comp (M + N) = M₂.comp M + M₂.comp N := by
  simp only [BiDerivedOp.comp]
  rw [Finsupp.sum_add_index']
  · intro a; simp
  · intro a b₁ b₂; simp only [add_mul, Finsupp.single_add]; rw [Finsupp.sum_add]

private lemma BiDerivedOp.add_comp {p s p' s' q r : ℕ} (M N : BiDerivedOp p' s' q r)
    (K : BiDerivedOp p s p' s') : (M + N).comp K = M.comp K + N.comp K := by
  simp only [BiDerivedOp.comp]
  rw [← Finsupp.sum_add]
  apply Finsupp.sum_congr
  intro l₁ _
  rw [Finsupp.sum_add_index']
  · intro a; simp
  · intro a b₁ b₂; simp only [mul_add, Finsupp.single_add]

private lemma BiDerivedOp.comp_single_right {p s p' s' q r : ℕ} (M₂ : BiDerivedOp p' s' q r)
    (l₁ : BiOpLetter p s p' s') (c : ℤ) :
    M₂.comp (Finsupp.single l₁ c) = M₂.sum fun l₂ c₂ => Finsupp.single (l₂.comp l₁) (c * c₂) := by
  rw [BiDerivedOp.comp, Finsupp.sum_single_index (by simp)]

private lemma BiDerivedOp.single_comp_single {p s p' s' q r : ℕ} (l₂ : BiOpLetter p' s' q r)
    (l₁ : BiOpLetter p s p' s') (c₂ c₁ : ℤ) :
    BiDerivedOp.comp (Finsupp.single l₂ c₂) (Finsupp.single l₁ c₁) =
      Finsupp.single (l₂.comp l₁) (c₁ * c₂) := by
  rw [BiDerivedOp.comp_single_right, Finsupp.sum_single_index (by simp)]

private lemma BiDerivedOp.prime_add {p s q r : ℕ} (M N : BiDerivedOp p s q r) :
    (M + N).prime = M.prime + N.prime := by
  simp [BiDerivedOp.prime, Finsupp.mapDomain_add]

@[simp] private lemma BiDerivedOp.comp_zero_right {p s p' s' q r : ℕ}
    (M₂ : BiDerivedOp p' s' q r) : M₂.comp (0 : BiDerivedOp p s p' s') = 0 := by
  simp [BiDerivedOp.comp]

@[simp] private lemma BiDerivedOp.zero_comp_left {p s p' s' q r : ℕ}
    (M₁ : BiDerivedOp p s p' s') : (0 : BiDerivedOp p' s' q r).comp M₁ = 0 := by
  simp [BiDerivedOp.comp]

/-- Associativity of bi-graded letter composition (legs compose associatively). -/
lemma BiOpLetter.comp_assoc {p s p' s' p'' s'' q r : ℕ} (l₃ : BiOpLetter p'' s'' q r)
    (l₂ : BiOpLetter p' s' p'' s'') (l₁ : BiOpLetter p s p' s') :
    (l₃.comp l₂).comp l₁ = l₃.comp (l₂.comp l₁) := by
  simp only [BiOpLetter.comp, Category.assoc]

/-- Associativity of bi-graded operator composition. Reduced to `BiOpLetter.comp_assoc` by
trilinearity (`Finsupp.induction` on each argument). -/
lemma BiDerivedOp.comp_assoc {p s p' s' p'' s'' q r : ℕ} (M₃ : BiDerivedOp p'' s'' q r)
    (M₂ : BiDerivedOp p' s' p'' s'') (M₁ : BiDerivedOp p s p' s') :
    (M₃.comp M₂).comp M₁ = M₃.comp (M₂.comp M₁) := by
  induction M₁ using Finsupp.induction with
  | zero => simp
  | single_add l₁ c₁ f _ _ ih =>
    rw [BiDerivedOp.comp_add_right, BiDerivedOp.comp_add_right, BiDerivedOp.comp_add_right, ih]
    congr 1
    clear ih
    induction M₂ using Finsupp.induction with
    | zero => simp
    | single_add l₂ c₂ g _ _ ih₂ =>
      rw [BiDerivedOp.add_comp, BiDerivedOp.comp_add_right, BiDerivedOp.add_comp,
        BiDerivedOp.comp_add_right, ih₂]
      congr 1
      clear ih₂
      induction M₃ using Finsupp.induction with
      | zero => simp
      | single_add l₃ c₃ h _ _ ih₃ =>
        rw [BiDerivedOp.add_comp, BiDerivedOp.add_comp, BiDerivedOp.add_comp, ih₃]
        congr 1
        simp only [BiDerivedOp.single_comp_single, BiOpLetter.comp_assoc]
        ring_nf

/-- `comp` distributes over a finite sum in its left argument. -/
lemma BiDerivedOp.sum_comp {ι : Type*} {p s p' s' q r : ℕ} (t : Finset ι)
    (F : ι → BiDerivedOp p' s' q r) (K : BiDerivedOp p s p' s') :
    (∑ i ∈ t, F i).comp K = ∑ i ∈ t, (F i).comp K := by
  classical
  induction t using Finset.induction with
  | empty => simp
  | @insert a t ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, BiDerivedOp.add_comp, ih]

/-- `prime` distributes over a finite sum. -/
lemma BiDerivedOp.prime_sum {ι : Type*} {p s q r : ℕ} (t : Finset ι)
    (F : ι → BiDerivedOp p s q r) :
    (∑ i ∈ t, F i).prime = ∑ i ∈ t, (F i).prime := by
  classical
  induction t using Finset.induction with
  | empty => simp [BiDerivedOp.prime]
  | @insert a t ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, BiDerivedOp.prime_add, ih]

/-- `primeIter k` distributes over a finite sum. -/
lemma BiDerivedOp.primeIter_sum {ι : Type*} {p s q r : ℕ} (k : ℕ) (t : Finset ι)
    (F : ι → BiDerivedOp p s q r) :
    BiDerivedOp.primeIter k (∑ i ∈ t, F i) = ∑ i ∈ t, BiDerivedOp.primeIter k (F i) := by
  induction k with
  | zero => simp [BiDerivedOp.primeIter]
  | succ k ih =>
      simp only [BiDerivedOp.primeIter_succ, ih, BiDerivedOp.prime_sum]

/-- **`prime` is multiplicative on the tensor side** (EM `md 206`, `h'∇' = (h∇)'`): `(M₂ ∘ M₁)' =
M₂' ∘ M₁'`. The bigraded analogue of `prime_comp`; reduced to the single–single case
`BiOpLetter.prime_comp` by bilinearity of `comp` and additivity of `prime`. -/
lemma BiDerivedOp.prime_comp {p s p' s' q r : ℕ} (M₂ : BiDerivedOp p' s' q r)
    (M₁ : BiDerivedOp p s p' s') : (M₂.comp M₁).prime = M₂.prime.comp M₁.prime := by
  induction M₁ using Finsupp.induction with
  | zero => simp [BiDerivedOp.comp, BiDerivedOp.prime]
  | single_add l₁ c₁ f _ _ ih =>
    rw [BiDerivedOp.comp_add_right, BiDerivedOp.prime_add, ih, BiDerivedOp.prime_add,
      BiDerivedOp.comp_add_right]
    congr 1
    clear ih
    induction M₂ using Finsupp.induction with
    | zero => simp [BiDerivedOp.comp, BiDerivedOp.prime]
    | single_add l₂ c₂ g _ _ ih₂ =>
      rw [BiDerivedOp.add_comp, BiDerivedOp.prime_add, ih₂, BiDerivedOp.prime_add,
        BiDerivedOp.add_comp]
      congr 1
      simp only [BiDerivedOp.single_comp_single, BiDerivedOp.prime, Finsupp.mapDomain_single,
        BiOpLetter.prime_comp]

/-- **`prime` preserves tensor norms** (EM `md 143`–`145` + `md 161`'s "Therefore"): `δ⁰`-shifting a
leading degeneracy keeps a leading degeneracy (`primeHom_not_mono`). This is the structural fact
that makes EM (2.12) free. -/
lemma BiIsNorm.prime {p s q r : ℕ} {M : BiDerivedOp p s q r} (h : BiIsNorm M) :
    BiIsNorm M.prime := by
  sorry

/-! #### Realization of a (homogeneous) bi-graded operator + linearity

A `BiDerivedOp p s q r` has fixed bidegrees, so its realization is a single summand map
`X_{p,s} ⟶ X_{q,r}` (the `ℤ`-linear extension of `realizeComponent`). Mirrors `DerivedOp.realize`
and its linearity stack. -/

/-- Realize a homogeneous bi-graded operator as a bidegree-summand map `X_{p,s} ⟶ X_{q,r}`. -/
noncomputable def BiDerivedOp.realize {p s q r : ℕ} (X : BisimplicialObject C)
    (M : BiDerivedOp p s q r) :
    (X.obj (Opposite.op ⦋p⦌)).obj (Opposite.op ⦋s⦌) ⟶
      (X.obj (Opposite.op ⦋q⦌)).obj (Opposite.op ⦋r⦌) :=
  M.sum fun l c => c • l.realizeComponent X

@[simp] lemma BiDerivedOp.realize_zero {p s q r : ℕ} (X : BisimplicialObject C) :
    BiDerivedOp.realize X (0 : BiDerivedOp p s q r) = 0 := by
  simp [BiDerivedOp.realize]

@[simp] lemma BiDerivedOp.realize_single {p s q r : ℕ} (X : BisimplicialObject C)
    (l : BiOpLetter p s q r) (c : ℤ) :
    BiDerivedOp.realize X (Finsupp.single l c) = c • l.realizeComponent X := by
  simp [BiDerivedOp.realize, Finsupp.sum_single_index]

lemma BiDerivedOp.realize_add {p s q r : ℕ} (X : BisimplicialObject C)
    (M N : BiDerivedOp p s q r) :
    BiDerivedOp.realize X (M + N) = BiDerivedOp.realize X M + BiDerivedOp.realize X N := by
  sorry

lemma BiDerivedOp.realize_neg {p s q r : ℕ} (X : BisimplicialObject C)
    (M : BiDerivedOp p s q r) :
    BiDerivedOp.realize X (-M) = -(BiDerivedOp.realize X M) := by
  sorry

/-- `realize` distributes over a finite sum. -/
lemma BiDerivedOp.realize_sum {ι : Type*} {p s q r : ℕ} (X : BisimplicialObject C)
    (t : Finset ι) (F : ι → BiDerivedOp p s q r) :
    BiDerivedOp.realize X (∑ i ∈ t, F i) = ∑ i ∈ t, BiDerivedOp.realize X (F i) := by
  classical
  induction t using Finset.induction with
  | empty => simp
  | @insert a t ha ih =>
      rw [Finset.sum_insert ha, Finset.sum_insert ha, BiDerivedOp.realize_add, ih]

/-- `realize` turns bi-graded composition into hom composition (apply `M₁` then `M₂`). The
tensor-side analogue of `realize_comp`; proved by reducing to the single-single case
(`realizeComponent` of `BiOpLetter.comp`) via bilinearity. -/
lemma BiDerivedOp.realize_comp {p s p' s' q r : ℕ} (X : BisimplicialObject C)
    (M₂ : BiDerivedOp p' s' q r) (M₁ : BiDerivedOp p s p' s') :
    BiDerivedOp.realize X (M₂.comp M₁) = BiDerivedOp.realize X M₁ ≫ BiDerivedOp.realize X M₂ := by
  sorry

/-! #### `BiIsNorm.killComponent` — a tensor norm dies under the bi-Moore retraction

The tensor analogue of `IsNorm.kill` (`realize_comp_diagLetter_not_mono_comp_retractionN₂`): a
tensor-norm operator `M : BiDerivedOp p s q r`, realized into the `(q,r)` summand of `F₁` (via
`ιTotal`) and hit by the bi-normalized retraction `retractionN₁`, vanishes. This is the linchpin
that makes EM's structural (2.12) (`md 161`) work: `f`/`∇` send norms to one-sided-degenerate
letters, which `retractionN₁` (`PInfty ⊗ PInfty`) kills factorwise. -/

/-- The `(q,r)`-summand injection into `F₁` at total degree `q + r`. -/
noncomputable abbrev ιF₁ (X : BisimplicialObject C) (q r : ℕ) :
    (X.obj (Opposite.op ⦋q⦌)).obj (Opposite.op ⦋r⦌) ⟶ (F₁.obj X).X (q + r) :=
  HomologicalComplex₂.ιTotal (doubleComplex X) (ComplexShape.down ℕ) q r (q + r) (by
    simp only [ComplexShape.π_def])

/-- **Single-letter kill, `K`-leg** (genuine Dold–Kan input, EM `md 122`): a letter whose `K`-leg
`fst` is non-injective realizes to a map *ending* (output side) in a `K`-degeneracy `s_i`, killed by
the first `PInfty` factor of `retractionN₁`. The bi-graded analogue of
`realize_diagLetter_comp_retractionN₂_eq_zero_of_not_mono`, restricted to one factor. -/
lemma biLetter_fst_not_mono_comp_retractionN₁ {p s q r : ℕ} (X : BisimplicialObject C)
    (l : BiOpLetter p s q r) (h : ¬ Mono l.fst) :
    l.realizeComponent X ≫ ιF₁ X q r ≫ (retractionN₁ X).f (q + r) = 0 := by
  sorry

/-- **Single-letter kill, `L`-leg** (genuine Dold–Kan input, EM `md 122`): dual of
`biLetter_fst_not_mono_comp_retractionN₁` for the inner (`L`) factor, killed by the second `PInfty`
factor of `retractionN₁`. -/
lemma biLetter_snd_not_mono_comp_retractionN₁ {p s q r : ℕ} (X : BisimplicialObject C)
    (l : BiOpLetter p s q r) (h : ¬ Mono l.snd) :
    l.realizeComponent X ≫ ιF₁ X q r ≫ (retractionN₁ X).f (q + r) = 0 := by
  sorry

/-- **A tensor norm dies under the bi-Moore retraction** (the linchpin, EM (2.12) `md 161`).
Structural induction over `BiIsNorm`: linear cases by `realize`-linearity; the `degenFst`/`degenSnd`
generators peel the leading one-sided degeneracy via `realize_comp` and kill it factorwise with the
single-letter primitives. -/
lemma BiIsNorm.killComponent {p s q r : ℕ} (X : BisimplicialObject C) {M : BiDerivedOp p s q r}
    (h : BiIsNorm M) :
    BiDerivedOp.realize X M ≫ ιF₁ X q r ≫ (retractionN₁ X).f (q + r) = 0 := by
  induction h with
  | zero => rw [BiDerivedOp.realize_zero, Limits.zero_comp]
  | add _ _ ihM ihN =>
      rw [BiDerivedOp.realize_add, Preadditive.add_comp, ihM, ihN, add_zero]
  | neg _ ihM => rw [BiDerivedOp.realize_neg, Preadditive.neg_comp, ihM, neg_zero]
  | degenFst θ hθ φ N =>
      rw [BiDerivedOp.realize_comp, BiDerivedOp.realize_single, one_smul, Category.assoc,
        biLetter_fst_not_mono_comp_retractionN₁ X ⟨θ, φ⟩ hθ, Limits.comp_zero]
  | degenSnd θ φ hφ N =>
      rw [BiDerivedOp.realize_comp, BiDerivedOp.realize_single, one_smul, Category.assoc,
        biLetter_snd_not_mono_comp_retractionN₁ X ⟨θ, φ⟩ hφ, Limits.comp_zero]

/-! #### `f` (= AW) and `∇` (= shuffle) as bi-graded operators, and the EM norm-preservation -/

/-- EM's `f`-letter `⟨ι_front, ι_back⟩` (EM (2.8), `md 113`): the `(p,q)`-summand of Alexander–
Whitney, from diagonal bidegree `(p+q, p+q)` to tensor bidegree `(p, q)`. -/
def awLetter (p q : ℕ) : BiOpLetter (p + q) (p + q) p q := ⟨ι_front p q, ι_back p q⟩

/-- **`awComponent` is the realization of EM's `f`-letter** `awLetter` (EM (2.8)/(2.9),
`md 113`–`118`). Bridges the existing `awComponent` to the tensor-operator algebra (cf. the
`realize_hOp` merge): `awComponent` and `realizeComponent` differ only by a naturality swap. -/
lemma awComponent_eq_realizeComponent (X : BisimplicialObject C) (p q : ℕ) :
    awComponent X p q = (awLetter p q).realizeComponent X := by
  sorry

/-- **`alexanderWhitney` realized via the bi-graded `f`-letters** (EM (2.9), `md 116`–`118`):
`f` at degree `n` is the sum over target bidegrees `(p, n−p)` of the realized `awLetter`s, injected
into `F₁` via `ιTotal`. Sigma-indexed over `p : Fin (n+1)` — the chosen total-realization shape.
Pure plumbing over `awComponent_eq_realizeComponent` + the definition of `alexanderWhitney`. -/
lemma alexanderWhitney_f_eq_sum (X : BisimplicialObject C) (n : ℕ) :
    (alexanderWhitney X).f n
      = ∑ p : Fin (n + 1),
          eqToHom (by simp [Nat.add_sub_cancel' (Nat.lt_succ_iff.mp p.isLt)]) ≫
            (awLetter (p : ℕ) (n - p)).realizeComponent X ≫
              HomologicalComplex₂.ιTotal (doubleComplex X) (ComplexShape.down ℕ) p (n - p) n (by
                simp only [ComplexShape.π_def, Nat.add_sub_cancel' (Nat.lt_succ_iff.mp p.isLt)]) := by
  dsimp [alexanderWhitney]
  simp_rw [awComponent_eq_realizeComponent]

/-- EM's shuffle map `∇` as a bi-graded operator (EM I.5.7, `md 200`): the signed sum over
`(p,q)`-shuffles of the letters `⟨shuffleFstHom μ, shuffleSndHom μ⟩`, from tensor bidegree `(p, q)`
to the diagonal `(p+q, p+q)`. -/
noncomputable def ezBiOp (p q : ℕ) : BiDerivedOp p q (p + q) (p + q) :=
  ∑ μ : Shuffle p q, Finsupp.single ⟨shuffleFstHom μ, shuffleSndHom μ⟩ μ.sign

/-- Diagonal inclusion of a letter: `OpLetter s q` is the diagonal `BiOpLetter s s q q`. -/
def OpLetter.toBi {s q : ℕ} (l : OpLetter s q) : BiOpLetter s s q q := ⟨l.fst, l.snd⟩

/-- Diagonal inclusion of operators `DerivedOp s q ↪ BiDerivedOp s s q q` (EM: `K × L` is the
diagonal bidegree of `K ⊗ L`, `md 147`). -/
noncomputable def DerivedOp.toBi {s q : ℕ} (M : DerivedOp s q) : BiDerivedOp s s q q :=
  Finsupp.mapDomain OpLetter.toBi M

/-- **`realize` is compatible with the diagonal inclusion**: the `F₂`-realization of a diagonal
operator equals the bigraded `(s,s)→(q,q)`-summand realization of its image. Holds essentially
definitionally, since `OpLetter.realize` and `BiOpLetter.realizeComponent` share the same formula on
the diagonal. The bridge that lets the diagonal sub-bridge be computed in the bigraded algebra. -/
lemma DerivedOp.realize_toBi {s q : ℕ} (X : BisimplicialObject C) (M : DerivedOp s q) :
    DerivedOp.realize X M = BiDerivedOp.realize X M.toBi := by
  sorry

/-- `toBi` commutes with `prime` (both are `⟨primeHom·, primeHom·⟩` leg-wise). -/
lemma DerivedOp.toBi_prime {s q : ℕ} (M : DerivedOp s q) :
    (M.prime).toBi = (M.toBi).prime := by
  rw [DerivedOp.prime, DerivedOp.toBi, DerivedOp.toBi, BiDerivedOp.prime,
    ← Finsupp.mapDomain_comp, ← Finsupp.mapDomain_comp]
  congr 1

/-- `toBi` commutes with `comp` (both `comp`s are `⟨l₂.fst ≫ l₁.fst, l₂.snd ≫ l₁.snd⟩` leg-wise). -/
lemma DerivedOp.toBi_comp {s q r : ℕ} (M₂ : DerivedOp q r) (M₁ : DerivedOp s q) :
    (M₂.comp M₁).toBi = (M₂.toBi).comp (M₁.toBi) := by
  sorry

/-- `toBi` commutes with `primeIter` (no index cast: `DerivedOp (s+k) (q+k) ↪ BiDerivedOp …` matches
`primeIter k` of `BiDerivedOp s s q q`). -/
lemma DerivedOp.toBi_primeIter {s q : ℕ} (k : ℕ) (M : DerivedOp s q) :
    (DerivedOp.primeIter k M).toBi = BiDerivedOp.primeIter k (M.toBi) := by
  induction k with
  | zero => rfl
  | succ k ih =>
      rw [DerivedOp.primeIter_succ, BiDerivedOp.primeIter_succ, DerivedOp.toBi_prime, ih]

/-- **`h = ∇ f` as a bigraded operator identity** (EM `md 200`–`206`). Under the diagonal inclusion,
`hOp` is the sum over the internal tensor bidegrees `(p, q − p)` of `∇ₚ ∘ fₚ` (`ezBiOp ∘ awLetter`).
This is the *operator-level* (not realization-level) factorization of `h`: because each `hLetter` leg
is literally `shuffle ≫ ι` (= a `∇`-leg after an `f`-leg), `hOp` already **is** the composite in the
bigraded algebra. It is the key that lets priming distribute as EM's `h' = ∇'f'` via
`BiDerivedOp.prime_comp`, with the diagonal `prime` matching the bigraded one leg-wise
(`primeHom_comp`). -/
lemma hOp_toBi_eq (q : ℕ) :
    (hOp q).toBi =
      ∑ p : Fin (q + 1),
        (Nat.add_sub_cancel' (Nat.lt_succ_iff.mp p.isLt) ▸
          (ezBiOp (p : ℕ) (q - p)).comp (Finsupp.single (awLetter (p : ℕ) (q - p)) 1)) := by
  sorry

/-- **`ezComponent` is the realization of the `∇`-operator `ezBiOp`** (EM I.5.7, `md 200`). Bridges
the existing `ezComponent` to the tensor-operator algebra. -/
lemma ezComponent_eq_realize_ezBiOp (X : BisimplicialObject C) (p q : ℕ) :
    ezComponent X p q
      = (ezBiOp p q).sum fun l c => c • l.realizeComponent X := by
  sorry

/-- **`shuffleMap` realized via `ezBiOp`** (EM I.5.7, `md 200`), per total-complex summand: the
`(p,q)`-injection into `F₁` followed by `∇` recovers the realized `ezBiOp`. Sigma-indexing is dual
to `alexanderWhitney_f_eq_sum` — here `∇` maps *out* of the total complex, so it is pinned summand-
wise by `ιTotal ≫ totalDesc`. Pure plumbing over `ezComponent_eq_realize_ezBiOp`. -/
lemma ιTotal_comp_shuffleMap_f (X : BisimplicialObject C) (p q : ℕ) :
    HomologicalComplex₂.ιTotal (doubleComplex X) (ComplexShape.down ℕ) p q (p + q) (by
        simp only [ComplexShape.π_def]) ≫ (shuffleMap X).f (p + q)
      = ((ezBiOp p q).sum fun l c => c • l.realizeComponent X) ≫
          eqToHom (by simp [F₂]) := by
  simp only [shuffleMap, HomologicalComplex₂.ι_totalDesc, ezComponent_eq_realize_ezBiOp]

/-- **`f` maps norms into norms** (EM `md 122`–`126`, via the FD-rules (2.6)/(2.7) at `md 99`–`109`):
post-composing the `f`-letter with a diagonal degeneracy `Dⱼ` (non-mono `θ`) lands in `D(K ⊗ L)`.
For `i ≤ j` the `L`-factor is a norm (2.6); for `i > j` the `K`-factor is (2.7). -/
lemma awLetter_comp_diagDegen_biIsNorm (p q m : ℕ)
    (θ : (⦋p + q⦌ : SimplexCategory) ⟶ ⦋m⦌) (hθ : ¬ Mono θ) :
    BiIsNorm (BiDerivedOp.comp
      (Finsupp.single (awLetter p q) 1)
      (Finsupp.single (⟨θ, θ⟩ : BiOpLetter m m (p + q) (p + q)) 1)) := by
  sorry

/-- **`∇` carries a tensor norm to a diagonal norm** (EM Lemma I.5.3, `md 91`; `md 206`): a tensor
norm `M` (landing in the `(p,q)`-summand of `F₁`), pushed by `∇ = shuffleMap` onto the diagonal `F₂`
and retracted by `ρ₂`, vanishes. This is the `∇`-half of "`h = ∇f` maps norms to norms" — the bridge
`D(K ⊗ L) → D(K × L)`.

**No new combinatorial input:** pure plumbing over `BiIsNorm.killComponent` and the 6b lemma
`retractionN₁_inclusionN₁_shuffleMap_retractionN₂` (`(1 − P) ≫ ∇ ≫ ρ₂ = 0` for the Dold–Kan
idempotent `P = retractionN₁ ≫ inclusionN₁` on `F₁`). A `killComponent`-killed element lies in
`ker(retractionN₁) = im(1 − P)`, hence is annihilated by `∇ ≫ ρ₂`. -/
lemma biIsNorm_comp_shuffleMap_retractionN₂ (X : BisimplicialObject C) {p q p' s' : ℕ}
    (M : BiDerivedOp p' s' p q) (hM : BiIsNorm M) :
    BiDerivedOp.realize X M ≫ ιF₁ X p q ≫ (shuffleMap X).f (p + q) ≫ (retractionN₂ X).f (p + q)
      = 0 := by
  -- 6b at degree `p+q`: `r₁ ≫ i₁ ≫ ∇ ≫ ρ₂ = ∇ ≫ ρ₂` (`P ≫ ∇ρ₂ = ∇ρ₂`).
  have h6 := HomologicalComplex.congr_hom (retractionN₁_inclusionN₁_shuffleMap_retractionN₂ X) (p + q)
  simp only [HomologicalComplex.comp_f] at h6
  -- Replace `∇ ≫ ρ₂` by `r₁ ≫ i₁ ≫ ∇ ≫ ρ₂`, exposing the `killComponent` prefix `… ≫ r₁`.
  rw [← h6]
  -- Group `realize M ≫ ιF₁ ≫ r₁` (= 0 by `killComponent`) and kill the whole product.
  slice_lhs 1 3 => rw [hM.killComponent X]
  simp only [Limits.zero_comp]

/-- A **bigraded operator is frontal** (EM): every letter fixes the bottom vertex `0` in both legs.
Bigraded analogue of `DerivedOp.Frontal`. The shuffle `∇ = ezBiOp` is frontal (`ezBiOp_frontal`),
which is exactly what EM `md 206` invokes ("since `∇` is a frontal operator …"). -/
def BiDerivedOp.Frontal {p s q r : ℕ} (M : BiDerivedOp p s q r) : Prop :=
  ∀ l ∈ M.support, IsFrontalHom l.fst ∧ IsFrontalHom l.snd

/-- The **tensor-side zeroth degeneracy** `D₀ = ⟨σ₀, σ₀⟩ : X_{p,s} → X_{p+1,s+1}`. Bigraded analogue
of `D0op`; the operator EM's frontality décalage `∇'D₀ = D∇` commutes past `∇'`. -/
noncomputable def BiD0op (p s : ℕ) : BiDerivedOp p s (p + 1) (s + 1) :=
  Finsupp.single ⟨SimplexCategory.σ 0, SimplexCategory.σ 0⟩ 1

/-- **Every primed bigraded operator is frontal** — bigraded analogue of `prime_frontal`. Since
`BiOpLetter.prime` applies `primeHom` to both legs and `primeHom` fixes the bottom vertex `0`
(`primeHom_frontal`), every letter of `M.prime` is frontal in both variables, regardless of `M`. -/
lemma BiDerivedOp.prime_frontal {p s q r : ℕ} (M : BiDerivedOp p s q r) :
    (M.prime).Frontal := by
  intro l hl
  have hl' := Finsupp.mapDomain_support hl
  rw [Finset.mem_image] at hl'
  obtain ⟨l', _, rfl⟩ := hl'
  exact ⟨primeHom_frontal _, primeHom_frontal _⟩

/-- **`∇` is frontal** (EM `md 206`, "since `∇` is a frontal operator"). Each shuffle letter
`⟨shuffleFstHom μ, shuffleSndHom μ⟩` fixes the bottom vertex in both legs, because a `(p,q)`-shuffle
path starts at the origin (`μ 0 = (0,0)`), so both projections send `0 ↦ 0`. (Likely needs leg
sub-lemmas `shuffleFstHom`/`shuffleSndHom` applied at `0`.) -/
lemma ezBiOp_frontal (p q : ℕ) : (ezBiOp p q).Frontal := by
  sorry

/-- **Frontal ⟹ priming commutes with `D₀`, bigraded** (EM `md 206`, from Lemma I.3.3
`(β')^* D₀ = D₀ β^*`). For a frontal bigraded operator, `M' ∘ D₀ = D₀ ∘ M`. The bigraded analogue of
`prime_comp_D0_of_frontal`; specialized to `∇` (`ezBiOp_frontal`) it is EM's frontality décalage
`∇'D₀ = D∇`, the engine of EM (2.12). Proof should mirror `prime_comp_D0_of_frontal`: bilinear
`Finsupp.induction`, reducing to the letter identity `primeHom_comp_degenZero` on each leg. -/
lemma BiDerivedOp.prime_comp_D0_of_frontal {p s q r : ℕ} (M : BiDerivedOp p s q r)
    (hM : M.Frontal) :
    (M.prime).comp (BiD0op p s) = (BiD0op q r).comp M := by
  sorry

/-- **An operator that factors through the bi-normalization carries tensor norms to `ρ₂`-killed
terms.** This — *not* frontality — is the property that makes `∇` (and its primes) annihilate tensor
norms (EM `md 155`, Lemma I.5.3). The *killing* is entirely `BiIsNorm.killComponent` (a tensor norm
dies under the bi-Moore retraction `retractionN₁`); the operator `N` only has to expose that
`retractionN₁` in front of `ρ₂`, which is exactly the 6b property
`retractionN₁_inclusionN₁_shuffleMap_retractionN₂` that `∇` enjoys.

Frontality alone is **insufficient**: the identity `⟨𝟙,𝟙⟩` is frontal, but `id ∘ M = M` leaves a
one-sided tensor degeneracy that `ρ₂ = PInfty(diag)` (diagonal-only) does not cancel. The genuine
hypothesis `hfac` is that `realize N ≫ ρ₂` admits an `ιF₁ ≫ retractionN₁` prefix. -/
lemma comp_biIsNorm_retractionN₂_of_factorsRetractionN₁ {a b p s m : ℕ}
    (X : BisimplicialObject C) (N : BiDerivedOp p s m m)
    (G : (N₁.obj X).X (p + s) ⟶ (N₂.obj X).X m)
    (hfac : BiDerivedOp.realize X N ≫ (retractionN₂ X).f m
        = ιF₁ X p s ≫ (retractionN₁ X).f (p + s) ≫ G)
    (M : BiDerivedOp a b p s) (hM : BiIsNorm M) :
    BiDerivedOp.realize X (N.comp M) ≫ (retractionN₂ X).f m = 0 := by
  -- `realize (N ∘ M) ≫ ρ₂ = realize M ≫ (realize N ≫ ρ₂) = realize M ≫ ιF₁ ≫ r₁ ≫ G`; the
  -- prefix `realize M ≫ ιF₁ ≫ r₁` is `0` by `killComponent` (a tensor norm dies under `r₁`).
  rw [BiDerivedOp.realize_comp, Category.assoc, hfac]
  slice_lhs 1 3 => rw [hM.killComponent X]
  rw [Limits.zero_comp]

/-- **A single primed shuffle bi-letter factors through the bi-normalization** — the per-letter core
of `primeIter_ezBiOp_factorsRetractionN₁`. One shuffle bi-letter `⟨shuffleFstHom μ, shuffleSndHom μ⟩`,
primed `j+1` times and composed with `ρ₂`, admits an `ιF₁ ≫ retractionN₁` prefix. This is where the
frontality / FD-rules of the primed (δ⁰-shifted) shuffle letter (EM `md 159`–`161`) are used. -/
lemma primeIter_single_shuffleLetter_factorsRetractionN₁
    (X : BisimplicialObject C) (p q j : ℕ) (μ : Shuffle p q) :
    ∃ Gμ, BiDerivedOp.realize X
            (BiDerivedOp.primeIter (j + 1)
              (Finsupp.single ⟨shuffleFstHom μ, shuffleSndHom μ⟩ μ.sign))
          ≫ (retractionN₂ X).f (p + q + (j + 1))
        = ιF₁ X (p + (j + 1)) (q + (j + 1))
            ≫ (retractionN₁ X).f (p + (j + 1) + (q + (j + 1))) ≫ Gμ := by
  -- `primeIter (j+1) M = (primeIter j M).prime`, and every primed operator is frontal.
  have hfrontal :
      (BiDerivedOp.primeIter (j + 1)
        (Finsupp.single ⟨shuffleFstHom μ, shuffleSndHom μ⟩ μ.sign)).Frontal :=
    BiDerivedOp.prime_frontal _
  sorry

/-- **The primed shuffle factors through the bi-normalization** — EM Lemma I.5.3 (`∇` induces a
chain map on the normalized complexes, `md 91`), extended to the primed `∇^{(j)}` via the (2.10)
derived-operator calculus (the "Therefore" of `md 159`–`161`). Concretely: `∇^{(j)} ≫ ρ₂` admits an
`ιF₁ ≫ retractionN₁` prefix — it factors through the tensor-side bi-Moore retraction. This is the
single genuinely-EM ingredient behind "primed `∇` maps norms to norms": once it holds, killing tensor
norms is automatic (`comp_biIsNorm_retractionN₂_of_factorsRetractionN₁`, via `killComponent`).

For `j = 0` it is the 6b identity `retractionN₁_inclusionN₁_shuffleMap_retractionN₂` +
`ιTotal_comp_shuffleMap_f` (`G = inclusionN₁ ≫ shuffleMap ≫ retractionN₂` composed appropriately).
The primed levels are the derived-operator extension — the part EM gets for free from
naturality-in-dimension of the FD-rules (the combinatorial fact our `prime` mirrors). -/
lemma primeIter_ezBiOp_factorsRetractionN₁ (X : BisimplicialObject C) (p q j : ℕ) :
    ∃ G : (N₁.obj X).X (p + j + (q + j)) ⟶ (N₂.obj X).X (p + q + j),
      BiDerivedOp.realize X (BiDerivedOp.primeIter j (ezBiOp p q))
          ≫ (retractionN₂ X).f (p + q + j)
        = ιF₁ X (p + j) (q + j) ≫ (retractionN₁ X).f (p + j + (q + j)) ≫ G := by
  cases j with
  | zero =>
      simp only [Nat.add_zero]
      -- `G = i₁ ≫ ∇ ≫ ρ₂`; then `ιF₁ ≫ r₁ ≫ G = ιF₁ ≫ (r₁ ≫ i₁ ≫ ∇ ≫ ρ₂) = ιF₁ ≫ ∇ ≫ ρ₂`
      -- (6b `retractionN₁_inclusionN₁_shuffleMap_retractionN₂`), matching `realize ∇ ≫ ρ₂` (`hez`).
      refine ⟨(inclusionN₁ X).f (p + q) ≫ (shuffleMap X).f (p + q) ≫ (retractionN₂ X).f (p + q),
        ?_⟩
      have hez : BiDerivedOp.realize X (BiDerivedOp.primeIter 0 (ezBiOp p q))
            ≫ (retractionN₂ X).f (p + q)
          = ιF₁ X p q ≫ (shuffleMap X).f (p + q) ≫ (retractionN₂ X).f (p + q) := by
        rw [← Category.assoc, ιTotal_comp_shuffleMap_f]
        simp [BiDerivedOp.realize, BiDerivedOp.primeIter]
      have h6 := HomologicalComplex.congr_hom
        (retractionN₁_inclusionN₁_shuffleMap_retractionN₂ X) (p + q)
      simp only [HomologicalComplex.comp_f] at h6
      rw [hez, h6]
  | succ j =>
      -- Expand `∇ = ∑_μ ⟨shuffleFst μ, shuffleSnd μ⟩` and distribute `primeIter`/`realize`/`≫ ρ₂`
      -- through the shuffle-sum, exposing the per-letter (δ⁰-shifted) shuffle terms.
      simp only [ezBiOp, BiDerivedOp.primeIter_sum, BiDerivedOp.realize_sum, Preadditive.sum_comp]
      -- Assemble `G = ∑_μ Gμ`; reduces to a per-letter factorization of each primed shuffle bi-letter.
      suffices h : ∀ μ : Shuffle p q,
          ∃ Gμ, BiDerivedOp.realize X
                  (BiDerivedOp.primeIter (j + 1)
                    (Finsupp.single ⟨shuffleFstHom μ, shuffleSndHom μ⟩ μ.sign))
                ≫ (retractionN₂ X).f (p + q + (j + 1))
              = ιF₁ X (p + (j + 1)) (q + (j + 1))
                  ≫ (retractionN₁ X).f (p + (j + 1) + (q + (j + 1))) ≫ Gμ by
        choose G hG using h
        exact ⟨∑ μ, G μ, by simp only [hG, Preadditive.comp_sum]⟩
      exact fun μ => primeIter_single_shuffleLetter_factorsRetractionN₁ X p q j μ

/-- **`∇` primed `j` times still kills tensor norms** — the `prime`-tower generalization of
`biIsNorm_comp_shuffleMap_retractionN₂` (the case `j = 0`). No induction: the primed shuffle factors
through the bi-normalization (`primeIter_ezBiOp_factorsRetractionN₁`), so a tensor norm is killed by
`comp_biIsNorm_retractionN₂_of_factorsRetractionN₁` (the `killComponent` mechanism). EM `md 155`–`161`
(Lemma I.5.3 + the (2.10) "Therefore"). -/
lemma realize_primeIter_ezBiOp_comp_biIsNorm_retractionN₂ (X : BisimplicialObject C)
    {a b p q : ℕ} (j : ℕ) (M : BiDerivedOp a b (p + j) (q + j)) (hM : BiIsNorm M) :
    BiDerivedOp.realize X ((BiDerivedOp.primeIter j (ezBiOp p q)).comp M)
      ≫ (retractionN₂ X).f (p + q + j) = 0 := by
  obtain ⟨G, hG⟩ := primeIter_ezBiOp_factorsRetractionN₁ X p q j
  exact comp_biIsNorm_retractionN₂_of_factorsRetractionN₁ X _ G hG M hM

/-- **Bigraded degeneracy index-shift** (bigraded analogue of `prime_degenOp`): priming the diagonal
degeneracy letter `⟨σᵢ, σᵢ⟩` shifts the index, `(Dᵢ)′ = D_{i+1}`. Combinatorial core is `primeHom_σ`
(`primeHom (σ i) = σ i.succ`); proof mirrors `prime_single_diag`. With `BiDerivedOp.prime_comp` this
gives `M′ Dᵢ = (M D_{i-1})′` on the bigraded diagonal degeneracies. -/
lemma BiDerivedOp.prime_diagDegen {q : ℕ} (i : Fin (q + 1)) :
    BiDerivedOp.prime
        (Finsupp.single
          (⟨SimplexCategory.σ i, SimplexCategory.σ i⟩ : BiOpLetter q q (q + 1) (q + 1)) 1)
      = Finsupp.single
          (⟨SimplexCategory.σ i.succ, SimplexCategory.σ i.succ⟩ :
            BiOpLetter (q + 1) (q + 1) (q + 1 + 1) (q + 1 + 1)) 1 := by
  simp [BiDerivedOp.prime, Finsupp.mapDomain_single, BiOpLetter.prime, primeHom_σ]

/-- **Priming preserves `ρ₂`-kill, bigraded** (bigraded analogue of `prime_preserves_retractionN₂_kill`,
EM `md 161`'s "prime of a norm is a norm"). If a bigraded operator with diagonal target dies under
`ρ₂`, so does its prime. This is the analytic descent bridge; it is what turns `(M D_{i-1})′ ≫ ρ₂ = 0`
into `(M D_{i-1}) ≫ ρ₂ = 0`. -/
lemma BiDerivedOp.prime_preserves_retractionN₂_kill {a b n : ℕ} (X : BisimplicialObject C)
    (M : BiDerivedOp a b n n)
    (h : BiDerivedOp.realize X M ≫ (retractionN₂ X).f n = 0) :
    BiDerivedOp.realize X (BiDerivedOp.prime M) ≫ (retractionN₂ X).f (n + 1) = 0 := by
  sorry

/-- **A diagonal degeneracy `Dᵢ = ⟨σᵢ, σᵢ⟩` (via `degenOp`) is a tensor norm.** `degenOp q i` injected
into the bigraded world by `.toBi` is the single diagonal degeneracy letter, a `BiIsNorm` generator
(`degenFst`, since `σ i` is non-mono) with identity tail. -/
lemma biIsNorm_degenOp_toBi {q : ℕ} (i : Fin (q + 1)) :
    BiIsNorm (degenOp q i).toBi := by
  have hσ : ¬ Mono (SimplexCategory.σ i) := by
    intro h
    have := SimplexCategory.len_le_of_mono (SimplexCategory.σ i)
    simp only [SimplexCategory.len_mk] at this
    omega
  have hdeg : (degenOp q i).toBi
      = Finsupp.single (⟨SimplexCategory.σ i, SimplexCategory.σ i⟩ :
          BiOpLetter q q (q + 1) (q + 1)) 1 := by
    simp [degenOp, DerivedOp.toBi, OpLetter.toBi, Finsupp.mapDomain_single]
  rw [hdeg]
  have h := BiIsNorm.degenFst (SimplexCategory.σ i) hσ (SimplexCategory.σ i)
    (Finsupp.single (⟨𝟙 (⦋q⦌ : SimplexCategory), 𝟙 (⦋q⦌ : SimplexCategory)⟩ :
      BiOpLetter q q q q) 1)
  rw [BiDerivedOp.single_comp_single] at h
  simpa [BiOpLetter.comp] using h

/-- **`∇′ Dᵢ` is diagonally degenerate** (EM (2.12), `md 161`). `Dᵢ` is the **diagonal** degeneracy
`⟨σᵢ, σᵢ⟩` of the cartesian product `K×L` (EM `md 124`: `Dⱼ(a×b) = Dⱼa × Dⱼb`), acting on the
diagonal slice `(K×L)_q = K_q × L_q` (so both legs are at degree `q`, matching EM's argument
`a_q × b_q`). The once-primed shuffle `∇′ = (ezBiOp q q).prime`, applied to `Dᵢ`, dies under the
diagonal retraction `ρ₂`. Stands alongside the existing lemmas; restructuring to route the general
lemma through it comes later. -/
lemma ezBiOp_prime_comp_diagDegen_retractionN₂ {q : ℕ}
    (X : BisimplicialObject C) (i : Fin (q + 1)) :
    BiDerivedOp.realize X
        ((ezBiOp q q).prime.comp (degenOp q i).toBi)
      ≫ (retractionN₂ X).f (q + q + 1) = 0 := by
  rcases eq_or_ne i 0 with hi | hi
  · sorry
  · obtain ⟨q', rfl⟩ : ∃ q', q = q' + 1 := by
      rcases Nat.eq_zero_or_pos q with hq | hq
      · subst hq; exact absurd (Fin.fin_one_eq_zero i) hi
      · exact ⟨q - 1, by omega⟩
    rw [show ((degenOp (q' + 1) i).toBi)
          = BiDerivedOp.prime ((degenOp (q') (i.pred hi)).toBi) from by
          simp only [degenOp, DerivedOp.toBi, OpLetter.toBi, Finsupp.mapDomain_single]
          rw [BiDerivedOp.prime_diagDegen, Fin.succ_pred], ← BiDerivedOp.prime_comp]
    refine BiDerivedOp.prime_preserves_retractionN₂_kill X _ ?_
    rw [BiDerivedOp.realize_comp, Category.assoc]
    have hez : BiDerivedOp.realize X (ezBiOp (q' + 1) (q' + 1))
          ≫ (retractionN₂ X).f (q' + 1 + (q' + 1))
        = ιF₁ X (q' + 1) (q' + 1) ≫ (shuffleMap X).f (q' + 1 + (q' + 1))
            ≫ (retractionN₂ X).f (q' + 1 + (q' + 1)) := by
      rw [← Category.assoc, ιTotal_comp_shuffleMap_f]
      simp [BiDerivedOp.realize]
    rw [hez]
    refine biIsNorm_comp_shuffleMap_retractionN₂ X _ ?_
    exact biIsNorm_degenOp_toBi (i.pred hi)

/-- **`∇` of a (primed) tensor norm dies under `ρ₂`** — the `ezBiOp`→`shuffleMap` form of
`biIsNorm_comp_shuffleMap_retractionN₂`. For a tensor norm `N`, the bigraded composite `∇ ∘ N`
(`∇ = ezBiOp`), primed `k+1` times, realizes to zero after `ρ₂`. Reduces (via `BiDerivedOp.prime_comp`
+ `BiDerivedOp.primeIter_comp` to put it in `∇^{(k+1)} ∘ N^{(k+1)}` form, with `N^{(k+1)}` a norm by
`BiIsNorm.prime`) to the `prime`-tower kill `realize_primeIter_ezBiOp_comp_biIsNorm_retractionN₂` at
`j = k+1`. EM `md 206` (`h'∇' = ∇'`). -/
lemma ezBiOp_comp_biIsNorm_primeIter_retractionN₂ (X : BisimplicialObject C) {a b p q : ℕ}
    (k : ℕ) (N : BiDerivedOp a b p q) (hN : BiIsNorm N) :
    BiDerivedOp.realize X (BiDerivedOp.primeIter k (((ezBiOp p q).comp N).prime))
      ≫ (retractionN₂ X).f (p + q + 1 + k) = 0 := by
  sorry

/-- Cast-free repackaging of one `hOp_toBi_eq` summand for the sub-bridge: with the diagonal degree
`n = p + r` supplied as `e`, `∇ₚ ∘ fₚ ∘ D` (primed `k` times) dies under `ρ₂`. `subst`-ing `e`
removes the transport, then `comp_assoc` exposes the tensor norm `fₚ ∘ D` for the `∇`-kill bridge. -/
private lemma realize_primeIter_ezBiOp_aw_comp_prime_retractionN₂ (X : BisimplicialObject C)
    {m p r n : ℕ} (e : p + r = n) (k : ℕ) (D : BiDerivedOp m m n n)
    (hN : BiIsNorm (BiDerivedOp.comp (Finsupp.single (awLetter p r) 1) (e ▸ D))) :
    BiDerivedOp.realize X (BiDerivedOp.primeIter k
        (((e ▸ ((ezBiOp p r).comp (Finsupp.single (awLetter p r) 1))).comp D).prime))
      ≫ (retractionN₂ X).f (n + 1 + k) = 0 := by
  subst e
  rw [BiDerivedOp.comp_assoc]
  exact ezBiOp_comp_biIsNorm_primeIter_retractionN₂ X k _ hN

/-- Transport-only: a `single` letter pushed across a degree equality `e : p + r = n` is the `single`
of the transported letter (memory `transport-cast.md`: `subst`-eliminate the dependent `▸`). -/
private lemma biDerivedOp_cast_single {m p r n : ℕ} (e : p + r = n)
    (l : BiOpLetter m m n n) (c : ℤ) :
    (e ▸ Finsupp.single l c : BiDerivedOp m m (p + r) (p + r))
      = Finsupp.single (e ▸ l : BiOpLetter m m (p + r) (p + r)) c := by
  subst e; rfl

/-- Transport-only: a diagonal letter `⟨f, g⟩` pushed across `e : p + r = n` transports each leg. -/
private lemma biOpLetter_cast_diag {m p r n : ℕ} (e : p + r = n)
    (f g : (⦋n⦌ : SimplexCategory) ⟶ ⦋m⦌) :
    (e ▸ (⟨f, g⟩ : BiOpLetter m m n n) : BiOpLetter m m (p + r) (p + r))
      = ⟨(e ▸ f : (⦋p + r⦌ : SimplexCategory) ⟶ ⦋m⦌),
          (e ▸ g : (⦋p + r⦌ : SimplexCategory) ⟶ ⦋m⦌)⟩ := by
  subst e; rfl

/-- Transport-only: transport preserves non-mono-ness (it is an iso conjugation). -/
private lemma not_mono_cast {m n n' : ℕ} (e : n = n')
    (θ : (⦋n⦌ : SimplexCategory) ⟶ ⦋m⦌) (h : ¬ Mono θ) :
    ¬ Mono (e ▸ θ : (⦋n'⦌ : SimplexCategory) ⟶ ⦋m⦌) := by
  subst e; exact h

/-- A degeneracy `σⱼ : ⦋q+1⦌ ⟶ ⦋q⦌` is never mono (it drops a dimension). -/
private lemma not_mono_σ {q : ℕ} (j : Fin (q + 1)) : ¬ Mono (SimplexCategory.σ j) := by
  intro h
  have := SimplexCategory.len_le_of_mono (SimplexCategory.σ j)
  simp only [SimplexCategory.len_mk] at this
  omega

/-- **The final sub-bridge — EM (2.12), `md 159`–`161`, in `prime`-tower form.** The primed operator
`h' Dⱼ = (h ∘ Dⱼ)'` (and its whole tower `(h' Dⱼ)⁽ᵏ⁾`) dies under `ρ₂`. This is the genuinely new
structural primitive of the EM-faithful route — the place where "priming commutes with the `∇f`
factorization" is discharged. Stated with the leading `.prime` baked in so it matches EM's `h'Dᵢ`
literally (and so the keystone reduces to it cast-free).

**Intended proof (must NOT induct via a per-step `prime`-preserves-kill — that would reintroduce the
analytic `prime_preserves_retractionN₂_kill`).** Uniformly in `k`:
* `h = ∇ f` (`realize_hOp`); `f ∘ Dⱼ` realizes as `∇` of a **tensor norm** `BiIsNorm`
  (`awLetter_comp_diagDegen_biIsNorm`).
* Priming acts through the bigraded factorization (EM `md 206`, `(MN)' = M'N'`, `BiOpLetter.prime_comp`):
  `(h ∘ Dⱼ)^{(k+1)}` realizes as `∇` of the `(k+1)`-times-primed tensor norm, still a `BiIsNorm`
  (`BiIsNorm.prime`).
* Each level then dies by `biIsNorm_comp_shuffleMap_retractionN₂` (the `∇`-half).
The un-primed base `h ∘ Dⱼ ∈ D(K×L)` is `hOp_diagDegen_comp_retractionN₂`. -/
lemma realize_primeIter_hOp_comp_degenOp_prime_comp_retractionN₂ {q : ℕ} (X : BisimplicialObject C)
    (k : ℕ) (j : Fin (q + 1)) :
    DerivedOp.realize X (DerivedOp.primeIter k (((hOp (q + 1)).comp (degenOp q j)).prime))
      ≫ (retractionN₂ X).f (q + 1 + 1 + k) = 0 := by
  rw [DerivedOp.realize_toBi, DerivedOp.toBi_primeIter, DerivedOp.toBi_prime,
    DerivedOp.toBi_comp, hOp_toBi_eq, BiDerivedOp.sum_comp, BiDerivedOp.prime_sum,
    BiDerivedOp.primeIter_sum, BiDerivedOp.realize_sum, Preadditive.sum_comp]
  apply Finset.sum_eq_zero
  intro p _
  have hp : (↑p : ℕ) + (q + 1 - ↑p) = q + 1 := Nat.add_sub_cancel' (Nat.lt_succ_iff.mp p.isLt)
  refine realize_primeIter_ezBiOp_aw_comp_prime_retractionN₂ X hp k (degenOp q j).toBi ?_
  -- `(degenOp q j).toBi` is the single diagonal degeneracy letter `⟨σⱼ, σⱼ⟩`. Push the degree cast
  -- through `single` and the letter (transport-only helpers), then it is `f ∘ Dⱼ` — a tensor norm.
  have hdeg : (degenOp q j).toBi
      = Finsupp.single (⟨SimplexCategory.σ j, SimplexCategory.σ j⟩ :
          BiOpLetter q q (q + 1) (q + 1)) 1 := by
    simp [degenOp, DerivedOp.toBi, OpLetter.toBi, Finsupp.mapDomain_single]
  rw [hdeg, biDerivedOp_cast_single, biOpLetter_cast_diag]
  all_goals first
    | exact hp
    | exact awLetter_comp_diagDegen_biIsNorm (↑p) (q + 1 - ↑p) q _
        (not_mono_cast hp.symm (SimplexCategory.σ j) (not_mono_σ j))

/-- **EM (2.12), `md 159`–`161` — the keystone, structural.** `h' Dᵢ` (with `i ≠ 0`) — and its whole
`prime`-tower `(h' Dᵢ)^{(m)}` — dies under the diagonal retraction `ρ₂`. This is the *structural*
replacement for the analytic décalage descent (`prime_preserves_retractionN₂_kill` →
`frontal_lastFace_PInfty_kill`): it consumes EM's "Therefore" (`md 159`) directly.

This is exactly the `N`-free `key` currently proved analytically inside
`hPrimeIter_hPrimeDegen_comp_retractionN₂`; once filled, that lemma reduces to
`rw [realize_comp, Category.assoc, this, Limits.comp_zero]` and the entire Tier-A/Tier-B analytic
chain can be deleted.

**Intended structural proof (EM `md 155`→`161`, no `prime`-preservation-of-kill):**
* `h' Dᵢ = (h D_{i-1})'` — `prime_degenOp` (`Dᵢ = D_{i-1}'`) + multiplicativity `prime_comp`; the
  whole `primeIter m` tower is then `(h D_{i-1})^{(m+1)}`.
* `h = ∇ f` (`realize_hOp`) and `f D_{i-1}` is a **tensor norm** (`awLetter_comp_diagDegen_biIsNorm`),
  so `h D_{i-1}` realizes as `∇` of a `BiIsNorm` (`biIsNorm_comp_shuffleMap_retractionN₂` gives the
  un-primed kill).
* **The one genuinely new sub-bridge (TODO):** priming commutes with this `∇`-factorization, i.e.
  `realize ((∇-of-BiIsNorm)^{(m)})` is again `∇'⁽ᵐ⁾` of the `m`-times-primed `BiIsNorm`
  (`BiIsNorm.prime`, EM `md 206` `h'∇' = (h∇)'`). Then each level dies by
  `biIsNorm_comp_shuffleMap_retractionN₂` on the primed tensor norm. -/
lemma realize_primeIter_hOp_prime_degen_comp_retractionN₂ {q : ℕ} (X : BisimplicialObject C)
    (m : ℕ) (i : Fin (q + 1)) (hi : i ≠ 0) :
    DerivedOp.realize X (DerivedOp.primeIter m ((hOp q).prime.comp (degenOp q i)))
      ≫ (retractionN₂ X).f (q + 1 + m) = 0 := by
  -- `i ≠ 0` forces `q ≥ 1`; write `q = q' + 1` so `Dᵢ = (D_{i-1})'` (`prime_degenOp`) is available.
  obtain ⟨q', rfl⟩ : ∃ q', q = q' + 1 := by
    rcases Nat.eq_zero_or_pos q with hq | hq
    · subst hq; exact absurd (Fin.fin_one_eq_zero i) hi
    · exact ⟨q - 1, by omega⟩
  -- `h' Dᵢ = (h D_{i-1})'` (`prime_degenOp` + multiplicativity `prime_comp`); the operator under the
  -- tower becomes `((h ∘ D_{i-1}))'`, matching the sub-bridge's `.prime` form at the same indices.
  rw [show (degenOp (q' + 1) i) = (degenOp q' (i.pred hi)).prime from by
        rw [prime_degenOp, Fin.succ_pred], ← prime_comp]
  exact realize_primeIter_hOp_comp_degenOp_prime_comp_retractionN₂ X m (i.pred hi)

/- TODO (integration — sigma-indexed total realization chosen: no global `realizeTotal`; the
   bidegree sum lives in the `f`/`∇` bridges `alexanderWhitney_f_eq_sum` / `ιTotal_comp_shuffleMap_f`
   over `Fin (n+1)`, matching the existing `alexanderWhitney`/`shuffleMap` defs):
   1. `BiOpLetter.realizeComponent`-linearity + `realizeComponent_comp` (mirror `OpLetter.realize_comp`).
   2. `BiIsNorm.killComponent` — a tensor-norm letter, realized on a summand and post-composed with
      the bidegree-`(q,r)` component of the bi-Moore retraction `retractionN₁`, vanishes (leading
      degeneracy ⟹ killed by `PInfty`; tensor analogue of `realize_comp_diagLetter_not_mono…`).
      EM `md 122`.
   3. Replace `alexanderWhitney_diagDegen_comp_retractionN₁` (retiring the analytic half of
      `hOp_diagDegen_comp_retractionN₂`) using `alexanderWhitney_f_eq_sum` +
      `awLetter_comp_diagDegen_biIsNorm` + `BiIsNorm.killComponent`.
   4. Replace `prime_preserves_retractionN₂_kill` (and delete `frontal_lastFace_PInfty_kill`,
      `prime_preserves_PInfty_kill`, `realize_prime_*`, `alexanderWhitney_prime_comp_retractionN₁`)
      by: `h = ∇f` ⇒ `h Dᵢ ∈ D(K×L)` (step 3 + `ezBiOp_comp_biIsNorm…`), then `h' Dᵢ = (h D_{i-1})'`
      (`prime_degenOp` + `BiOpLetter.prime_comp`) ∈ `D(K×L)` by `BiIsNorm.prime` — EM (2.12), `md 161`. -/

end BisimplicialObject

end CategoryTheory

/-!
## EM homotopy `Φ` remaining-work checklist

The scaffold matches Eilenberg–Mac Lane Thm 2.1a (`mcl2_sections_1_2.md:163`–`194`): `Φ` is the
recursive derived operator (2.13), "modulo norms" is `≫ retractionN₂`, and the abstract
derived-operator identities are now EM-faithful (`∂' = prime ∂`, `prime` multiplicative). Items are
ordered by dependency. The one genuinely hard mathematical step is **(5)**, the EM induction; the
one genuinely hard combinatorial step is **(4)**, extracting `hOp`'s representation.

### Phase 0 — `Finsupp` plumbing for `realize`/`prime` (mechanical, low risk)

- [x] **(0a)** `realize_zero`, `realize_single`, `realize_add`, `realize_neg`, `realize_sub`,
      `realize_zsmul`. Standard `Finsupp.sum`/`Finsupp.sum_single_index`/`Finsupp.sum_add_index'`
      facts; `realize_single` is the base case the rest reduce to. `realize_single_id` then follows
      from `realize_single` + `OpLetter.realize` of `⟨𝟙,𝟙⟩` (both `X.map`/`X.obj.map` of `op (𝟙)` are
      `𝟙`, so `1 • 𝟙 = 𝟙`).
- [x] **(0b)** `realize_comp` — push `DerivedOp.comp`'s double `Finsupp.sum` through `realize`,
      reduce to the **letter** identity `(l₂.comp l₁).realize X = l₁.realize X ≫ l₂.realize X`. That
      letter identity is the **Pattern-5 bifunctor merge** (`api/dold-kan-moore-retraction.md`):
      `← NatTrans.comp_app`, `← Functor.map_comp`, `← op_comp`, plus one `naturality` to interleave
      the horizontal/vertical legs. (Reusable; this is the workhorse for everything downstream.)
- [x] **(0c)** `prime_zero`, `prime_add` — `Finsupp.mapDomain_zero` / `Finsupp.mapDomain_add`.

### Phase 1 — simplicial identities on letters (combinatorial, low–medium)

- [x] **(1a)** `prime_comp` (multiplicativity). Reduced (via bilinear `Finsupp.induction` to the
      single–single case) to the letter fact `OpLetter.prime_comp`, then to `primeHom_comp`
      (`primeHom (g ≫ f) = primeHom g ≫ primeHom f`), proved by `Hom.ext`/`OrderHom.ext`/`Fin.ext`,
      `by_cases ↑j = 0`, and `generalize_proofs` + `if_neg` + `congr`/`omega` (avoid `split_ifs`: it
      over-splits on the `if ↑j = 0` buried in the index proof term).
- [x] **(1b)** `prime_faceOp` (`prime δ_i = δ_{i+1}`). `SimplexCategory.Hom.ext` + `Fin.cases` +
      `Fin.succAbove` arithmetic + `omega`. Feeds (1c).
- [x] **(1c)** `prime_boundaryOp` (`∂' = prime ∂`). `prime` is additive (`prime_add`) + `prime_zsmul`
      (add if needed) over the boundary sum, then `prime_faceOp` reindexes `Σ(-1)^i δ_i` to
      `Σ(-1)^i δ_{i+1} = truncBoundaryOp (q+1)` (`Fin.sum_univ_succ`/`Finset.sum` reindex).
- [x] **(1d)** `boundaryOp_eq` (`∂ = F₀ − ∂'`). Split `boundaryOp`'s `Σ_{i : Fin (q+2)}` off the `i=0`
      term (`Fin.sum_univ_succ`): `i=0` is `lastFaceOp`; the rest is `−truncBoundaryOp` after pulling
      out `(-1)^{i+1}` (sign reindex).
- [x] **(1e)** `realize_boundaryOp` (`realize ∂ = (F₂.obj X).d`). Expand `(F₂.obj X).d` via
      `alternatingFaceMapComplex`/`AlternatingFaceMapComplex.objD` (`SimplicialObject.δ`) and match
      the diagonal face `(diag X).δ_i` to `faceOp i`'s realization (the `diag_obj_map` split into
      horizontal+vertical, as in `Bisimplicial.lean:1148`–`1175`).

### Phase 2 — norms via `PInfty` (medium, patterns exist)

- [x] **(2)** `realize_diagLetter_comp_retractionN₂_eq_zero_of_not_mono` (was
      `realize_comp_retractionN₂_eq_zero_of_not_mono`). **Restated.** `retractionN₂ = PInfty(diag X)`
      kills only **diagonal** degeneracies, so the hypothesis is `⟨θ, θ⟩` with `¬Mono θ` (the EM
      norm = product degeneracy `(s_i a', s_i b')`). Proof: `realize_diagLetter` (realize `⟨θ,θ⟩` =
      `(diag X).map θ.op` via naturality, like `realize_faceOp`) + `degeneracy_comp_PInfty` +
      Moore-inclusion mono-cancel (Pattern 1).
      **FORK RESOLVED** (against the paper): no bi-normalization is needed. EM places `Φ` *in
      `K×_N L`* (md 81/83) and every norm in the `∂Φ+Φ∂` argument is a `D(K×L)` **diagonal**
      degeneracy (md 157/161/167) — exactly what `retractionN₂` kills. The single-direction norms
      `a⊗Db`/`Da⊗b` (md 75) live on the *other* side `K_N⊗L_N` and only concern `f`/`∇` (md 122–126),
      not `Φ`. The old single-direction statement was simply the wrong lemma.
      **Generalized** to the form the induction actually consumes:
      `realize_comp_diagLetter_not_mono_comp_retractionN₂` — a diagonal degeneracy `⟨θ,θ⟩` (`¬Mono θ`)
      on the **left** (last-applied, hence adjacent to `retractionN₂` after `realize_comp`) kills any
      right factor `N`. **DONE** — `realize_diagLetter` (Pattern 7a naturality) + base kill
      (`degeneracy_comp_PInfty` + mono Moore-inclusion cancel, Pattern 1) + the generalized form all
      proved. This covers `D₀Φ = ⟨σ₀,σ₀⟩∘Φ` and `Φ'D_i = δ^i D_{i-1}` directly. The remaining norm
      type — `h'D₀`,
      where the degeneracy is applied *first* but the result is still degenerate (genuine property of
      `∇f`) — is the abstract `hOp` property `hOp_prime_comp_D0_comp_retractionN₂` (EM (2.12), md 161),
      with right-composable corollary `hOp_prime_comp_D0_comp_comp_retractionN₂` (**proved** from it).

### Phase 3 — derived-operator core identities (EM I.3) (medium)

- [x] **(3a)** `prime_frontal` — `primeHom` sends `0 ↦ 0` by definition, so every primed letter is
      frontal in both variables. `Finsupp.mapDomain` support ⊆ image; `simp [IsFrontalHom, primeHom]`.
      (Easy; do early — it's what the induction's frontality needs, replacing the false `hOp` both-var
      frontality.)
- [x] **(3b)** `lastFace_comp_prime` (`F₀ M' = M F₀`, I.3.3). Reduce to the letter identity
      `δ 0 ≫ primeHom θ = θ ≫ δ 0` (the unprimed `F₀` "eats" the prepended vertex). `Hom.ext` +
      `Fin.cases` + `omega`. **The one identity not from multiplicativity.**
- [x] **(3c)** **DONE** — `prime_comp_D0_of_frontal` (`M' D₀ = D₀ M` for frontal `M`, I.3.3). Letter
      identity `σ 0 ≫ primeHom θ = θ ≫ σ 0` (`primeHom_comp_degenZero`) **using** `IsFrontalHom θ`
      (`θ 0 = 0`); without frontality it fails at the bottom vertex. `Finsupp.induction` + the letter
      identity. (Also added the degeneracy index-shift `primeHom_σ`/`prime_degenOp` for EM (2.12).)
- [x] **(3d)** `boundary_comp_D0` (`∂ D₀ = D₀ ∂'`). NB: EM line 179 writes this as `∂ D₀ = 1 − D₀ ∂'`,
      but that quantity is `∂' D₀`; since `∂ = F₀ − ∂'` the bottom two faces `F₀ D₀ = F₁ D₀ = 1`
      cancel, so the true identity is `∂ D₀ = D₀ ∂'`. Proved at the operator level: distribute `comp`
      over the boundary sum (`compRightD0`/`compLeftD0` `AddMonoidHom`s + `map_sum`/`map_zsmul`), peel
      the `i=0,1` terms (`δ_0 σ_0 = δ_1 σ_0 = 𝟙`, which cancel), and match the tail via
      `δ_{i} σ_0 = σ_0 δ_{i-1}` (`δ_comp_σ_of_gt`).

### Phase 4 — `hOp` representation (hard, isolated; see "characterize" discussion)

- [x] **(4a)** **DONE** — Define `hOp q` explicitly as `Σ_{p,μ} μ.sign • single (hLetter q p μ)`,
      where `hLetter` is `⟨shuffleFstHom μ ≫ ι_front, shuffleSndHom μ ≫ ι_back⟩` with the arithmetic
      `eqToHom` transports for `p + (q - p) = q`. This is the formal AW split followed by one EZ shuffle.
- [~] **(4b)** **PLUMBING DONE, MERGE SORRY REMAINS** — `realize_hOp`
      (`realize (hOp q) = (alexanderWhitney X ≫ shuffleMap X).f q`) is proved from
      `awShuffle_f_eq_sum` (`Bisimplicial.lean:1318`) and the drafted bridge `hLetter_realize`.
      The only remaining work is `hLetter_realize`: the Pattern-5 merge showing one concrete
      `hLetter` realizes to the corresponding `awComponent ≫ ezComponent` shuffle summand.
- [ ] **(4c)** `hOp_frontalFst` — `ι_front` fixes `0`, so the horizontal words are frontal.
      **Optional** (only for `fΦ = 0`, 2.4); skip unless needed.
- [x] **(4d)** **DONE** — `phiOp_frontal`: `cases q`; `phiOp 0 = 0` is vacuously frontal
      (`DerivedOp.Frontal.zero`); the `succ` step is `−h' + h'·D₀`, each summand frontal via
      `prime_frontal` for the `h'` and `IsFrontalHom (σ 0)` for the `D₀` factor. Added the
      `Frontal`-algebra helpers `IsFrontalHom.comp`, `DerivedOp.Frontal.{zero,single,neg,add,comp_single}`.

### Phase 5 — the EM induction (the crux, hard) — `mcl2_sections_1_2.md:177`–`194`

- [x] **(5a)** Helpers `dNext_phiHomRaw` / `prevD_phiHomRaw`: rewrite `dNext (n+1)`/`prevD n` of
      `phiHomRaw` as a single `realize` of a `DerivedOp`, via `dNext_eq`/`prevD_eq`,
      `phiHomRaw` (`dif_pos rfl` + `eqToHom_refl`), `realize_comp`, `← realize_boundaryOp`. NB the
      correct assignment (from the Mathlib `dNext`/`prevD` defs on `down ℕ`) is
      `prevD n = realize ((boundaryOp n).comp (phiOp n))` (`∂Φ`) and
      `dNext (n+1) = realize ((phiOp n).comp (boundaryOp n))` (`Φ∂`) — the reverse of this checklist's
      original loose labeling.
- [x] **(5b-i)** **DONE — the exact-identity induction machinery** (the actual EM computation,
      markdown 177–194), treating `hOp` *opaquely*. Reformulated as an *exact* `DerivedOp` equation
      (no `realize`/`retractionN₂`, no "mod norms"):
      - `phi_op_succ_eq` (**proved**): `P(q+1) = (P(q))'` *exactly*, where
        `P(q) = (phiOp q).comp (boundaryOp q) + (boundaryOp (q+1)).comp (phiOp (q+1)) + idOp (q+1)
        − hOp (q+1)` (`= Φ∂ + ∂Φ + i − h`). Replays EM: `∂ = F₀ − ∂'` (`boundaryOp_eq`), `phiOp`
        recursion; the `F₀` terms cancel via `lastFace_comp_prime` (`F₀Φ' = ΦF₀`) +
        `lastFace_comp_hPrime_comp_D0` (`F₀h'D₀ = h`); the lone surviving identity is md 179
        `∂'₂·h''D₀ = h' − h'D₀·∂'` (`hkey`), from the primed chain-map law `∂'h' = h'∂'` (prime of
        `boundaryOp_comp_hOp`) and `∂'D₀ = i − D₀∂'` (`boundary_comp_D0` + `F₀D₀ = i`); then `abel`.
        ⚠️ KEY FINDING: there is **no norm remainder in the inductive step** — the entire
        "mod norms" content collapses into the base degree (5b-ii).
      - `phi_op_isNorm` (**proved**): `IsNorm (P(q))` for all `q`, by `induction`; `succ` step is
        `rw [phi_op_succ_eq]; exact ih.prime` (uses `IsNorm.prime`, structural `prime`-closure).
      - `phi_comm_op` (**proved**): the degree-`q+1` mod-norms form `Φ∂ + ∂Φ + i ≡ h` (via
        `≫ retractionN₂`), as pure plumbing `(phi_op_isNorm q).kill X` + linearity of `realize`.
        ⚠️ NB the statement fixes an old sign/direction bug (`h`/`i` were swapped vs `Homotopy.comm`
        for `Homotopy (AW≫∇) (𝟙)`: `(AW≫∇).f n = dNext + prevD + (𝟙).f n`).
      - New supporting lemmas all **proved**: `prime_idOp` (`i' = i`), `primeHom_id`,
        `lastFace_comp_D0` (`F₀D₀ = i`), `comp_idOp` (right unit), `lastFace_comp_hPrime`
        (`F₀h' = hF₀`, via `lastFace_comp_prime`).
- [ ] **(5b-ii)** **REMAINING — the opaque `hOp` inputs** (consumed as black boxes by 5b-i; each
      genuinely needs `hOp`'s definition / EM (2.11), i.e. depends on Phase 4):
      - `phi_op_isNorm_zero` — **base case** `IsNorm (P(0))` (degree 1, EM md 169–171). This is where
        *all* the mod-norms content lives; needs EM (2.11)'s explicit degree-1 value of `h` (**item 4**).
      - `boundaryOp_comp_hOp` (`∂h = h∂`, `h` is a chain map, EM 155).
      - `lastFace_comp_hPrime_comp_D0` (`F₀h'D₀ = h`, EM 192).
      - `hOp_zero_comp_retraction` (`q=0` retraction base, EM 169).
      - `hPrimeIter_hPrimeDegen_comp_retractionN₂` (EM (2.12), paper-shaped `h' Dᵢ` kill, feeds
        `IsNorm.kill`). The argument follows EM's "Therefore" (md 155→161):
        * **`h`-norm fact (proved):** `hOp_diagDegen_comp_retractionN₂` — `h` after a diagonal
          degeneracy dies under `ρ₂`. Itself decomposed into the `f`-half
          `alexanderWhitney_diagDegen_comp_retractionN₁` (**sorry**, genuine Dold–Kan: AW of a
          degenerate diagonal lands in degenerate `F₁`) and the `∇`-half (6b,
          `retractionN₁_inclusionN₁_shuffleMap_retractionN₂`), glued by `realize_hOp`.
        * **degeneracy index-shift (proved):** `prime_degenOp` (`Dᵢ = (D_{i-1})'`, via new
          `primeHom_σ : primeHom (σ i) = σ i.succ`) + multiplicativity `prime_comp` give
          `h' Dᵢ = (h D_{i-1})'`.
        * **prime-preservation (EM "prime of a norm is a norm", md 161/167) — CHOSEN ROUTE:
          bi-graded tensor-side derived operator.** EM justify this *structurally*, not
          analytically: a norm is a sum of leading-degeneracy operators, and priming (`δ⁰`-shift)
          sends a degeneracy to a degeneracy (`primeHom_not_mono`). Critically, the degeneracy in
          `h∘D` is **one-sided / off-diagonal** — it lives in the tensor product `K⊗L` (= `F₁`),
          becoming a *diagonal* norm only after `∇`. EM can prime it for free because their derived
          operator `M ↦ M'` is defined on the **tensor side** too (md 135–147: `M : K_p⊗L_s →
          K_q⊗L_r`, `M'` by `δ⁰`-shift; they use `f'`, `∇'`, `(MN)'=M'N'`, md 200–206). Our
          `DerivedOp`/`prime` lives **only on the diagonal `F₂`**, so we cannot mirror this yet.
          **TO DO (the build):** introduce a bi-graded derived operator on `F₁` (independent
          degrees in the two factors — our `OpLetter` is already a pair `⟨β,γ⟩`, so this generalizes
          the diagonal `s↦q` restriction), with `prime`/`realize`-on-`F₁`; express `f = AW` and
          `∇ = shuffleMap` as such operators with `f'`,`∇'`; prove "f/∇ map one-sided norms to
          norms" as *operator identities* (EM (2.6)/(2.7)). Then `h' Dᵢ = (h D_{i-1})'` lands in
          the (diagonal) norm **termwise**, with no descent lemma. See plan §"Bi-graded tensor-side
          derived operator (EM-faithful prime route)".
        * **INTERIM analytic stand-ins (paper-independent — to be retired by the build above):**
          `prime_preserves_retractionN₂_kill`/`prime_preserves_PInfty_kill` reduce to the abstract
          décalage descent `frontal_lastFace_PInfty_kill` ("frontal + bottom-face-degenerate ⟹
          degenerate", via Moore `Q∞`/`hσ` — **not in EM**), or to the closer-to-EM but still
          analytic `realize_prime_hOp_mod_norm` (`h' = h_{q+1}` mod norms) + its `f`-half
          `alexanderWhitney_prime_comp_retractionN₁`. All of these are **deletable** once the
          bi-graded structural route lands.
- [x] **(5c)** **DONE** — `phi_comm_retraction`: assemble (5a)+(5b) and `realize_hOp`; pure plumbing.
      `succ m` reduces (via `dNext_phiHomRaw`/`prevD_phiHomRaw`/`realize_single_id`/`← realize_hOp`) to
      `phi_comm_op X m`; `zero` uses `dNext 0 = prevD 0 = 0` + `hOp_zero_comp_retraction`.

### Phase 6 — descent to `N₂` (medium)

- [x] **(6a)** **DONE** — `phiHomNorm_eq` (`phiHomNorm = ι₂ ≫ phiHomRaw ≫ ρ₂`), `dNext_phiHomNorm`/
      `prevD_phiHomNorm` (the inclusion/retraction are chain maps, so they commute with `dNext`/`prevD`
      via `dNext_comp_left/right`, `prevD_comp_left/right`), and `inclusionN₂_comp_retractionN₂`
      (`ι₂ ≫ ρ₂ = 𝟙 N₂`).
- [~] **(6b)** **SCAFFOLDED** — `normalizedAW_shuffle_eq` (**proved**): `normAW ≫ norm∇ =`
      `ι₂ ≫ (AW ≫ ∇) ≫ ρ₂`. Unfolds (defs + `Category.assoc`) to
      `ι₂ ≫ AW ≫ (ρ₁ ≫ ι₁) ≫ ∇ ≫ ρ₂`; the inner Dold–Kan round-trip `ρ₁ ≫ ι₁` is absorbed by
      `retractionN₁_inclusionN₁_shuffleMap_retractionN₂` (**proved**: cancel the split-mono `ι₂` then
      fold `ρ₂ ≫ ι₂ = PInfty`). ⚠️ NB the naive "`AW ≫ ρ₁ ≫ ι₁ = AW`" (AW lands bi-normalized) is
      **FALSE** — the slack is on the `ρ₂` side, not AW. Lone remaining `sorry`:
      - `retractionN₁_inclusionN₁_shuffleMap_PInfty` — `ρ₁ ≫ ι₁ ≫ ∇ ≫ PInfty = ∇ ≫ PInfty` on `F₂`.
        Genuine Dold–Kan combinatorics: `(1 − ρ₁ι₁)` projects onto degenerate-`F₁`, `∇` (a sum of
        degeneracies `⟨σ,σ⟩`) carries it to a degenerate diagonal simplex, killed by `PInfty`. Likely
        needs a per-shuffle-summand kill lemma via `degeneracy_comp_PInfty` (memory Patterns 1/2/4),
        comparable in size to `shuffleMap_alexanderWhitney_comp_retractionN₁`.
- [x] **(6c)** **DONE** — `homotopyAWShuffleNormalized.comm`: pure plumbing, assembled from (6a)+(6b)
      +`phi_comm_retraction` (5c). `rw [normalizedAW_shuffle_eq, dNext_phiHomNorm, prevD_phiHomNorm,
      hid, comp_f, comp_f, ← phi_comm_retraction]` reduces both sides to `ι₂ ≫ (…) ≫ ρ₂`; then
      `simp [Preadditive.comp_add, Preadditive.add_comp, id_f, id_comp]` distributes and matches.
- [ ] **(6d)** Wire into `BisimplicialNormalized.lean:745`:
      `homotopyNormalizedAlexanderWhitneyShuffle X := homotopyAWShuffleNormalized X` (add the import).

### Suggested order

`0 → 1 → 3a → 2` (independent foundations), then `3b–3d`, then `5a`, then the crux `5b/5c`, then
`6`. Defer `4` (the `hOp` representation) as long as possible — keep it `sorry` while `5b` is
developed against the *opaque* `hOp` + `realize_hOp` + `prime_frontal`, exactly as EM treat `h`.
-/
