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
    simp
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

/-- EM's operator `h = ∇f : (K×L) → (K×L)` (our `alexanderWhitney ≫ shuffleMap`) as a universal
(`X`-independent) derived operator, obtained from the AW/shuffle representations (the `awComponent ≫
ezComponent` Pattern-5 merge).

**Concreteness is needed only through `realize_hOp` and the low-degree values (EM (2.11)).** The
homotopy-identity induction (2.3) treats `hOp` *opaquely*, consuming only the universal `prime`/`comp`
laws and `prime_frontal`; it never unfolds `hOp`'s letters. (Mirrors EM, who define `h := ∇f` and
only ever use its definition and properties — see `realize_hOp` discussion.) -/
noncomputable def hOp (q : ℕ) : DerivedOp q q := sorry

/-- `hOp` realizes to the composite `alexanderWhitney ≫ shuffleMap = ∇f` on `F₂.obj X`. -/
lemma realize_hOp (X : BisimplicialObject C) (q : ℕ) :
    (hOp q).realize X = (alexanderWhitney X ≫ shuffleMap X).f q := by
  sorry

/-- `h = ∇f` is **first-variable** frontal only (EM, line 213: in `f` the 0-th face `F₀` is always
in the second factor, so the `β`/horizontal maps are frontal; the vertical maps are *not*). Used
only for the optional annihilation property `fΦ = 0` (2.4) — **not** needed for the homotopy
identity (2.3), where the relevant frontality comes from `prime_frontal` on the primed operators
`h'`, `Φ'`. -/
lemma hOp_frontalFst (q : ℕ) : (hOp q).FrontalFst := by
  sorry

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

/-- **`F₀ h' D₀ = h` (EM line 192).** `F₀ h' D₀ = (h F₀) D₀ = h (F₀ D₀) = h`, using
`lastFace_comp_hPrime` and `F₀ D₀ = i` (`δ_0 ≫ σ_0 = 𝟙`). -/
lemma lastFace_comp_hPrime_comp_D0 (q : ℕ) :
    (lastFaceOp (q + 1)).comp (((hOp (q + 1)).prime).comp (D0op (q + 1))) = hOp (q + 1) := by
  sorry

/-- **Base case (EM line 169, `q = 0`).** `h₀ = i` modulo norms: `∇f` is the identity in degree 0
(`AW`/`∇` are inverse there). -/
lemma hOp_zero_comp_retraction (X : BisimplicialObject C) :
    DerivedOp.realize X (hOp 0) ≫ (retractionN₂ X).f 0 =
      DerivedOp.realize X (idOp 0) ≫ (retractionN₂ X).f 0 := by
  sorry

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

/-- **Dold–Kan round-trip absorption, `PInfty` form.** The `PInfty`-idempotent round-trip
`retractionN₁ ≫ inclusionN₁` on `F₁` is absorbed under `shuffleMap … ≫ PInfty` on the diagonal `F₂`:
the degenerate-`F₁` correction `(1 − retractionN₁ ≫ inclusionN₁)` is sent by `∇` to a degenerate
element of the diagonal, which `PInfty` annihilates. -/
@[reassoc]
lemma retractionN₁_inclusionN₁_shuffleMap_PInfty (X : BisimplicialObject C) :
    retractionN₁ X ≫ inclusionN₁ X ≫ shuffleMap X ≫ (PInfty : F₂.obj X ⟶ F₂.obj X)
      = shuffleMap X ≫ PInfty := by
  sorry

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
`retractionN₁_inclusionN₁_shuffleMap_retractionN₂`) via `realize_hOp` (`h = AW ≫ ∇`). This is the
`k = 0` base of `hPrimeIter_diagDegen_comp_retractionN₂`. -/
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

/-- **EM (2.12), general form** — the single abstract `hOp` input feeding the norm class: `h` with
any number of primes, applied after a diagonal degeneracy `⟨θ,θ⟩` (`¬Mono θ`), lands in the diagonal
Moore-degenerate part and so dies under `retractionN₂`. (`prime`-stable: `prime` bumps `k` and shifts
`θ ↦ primeHom θ`, still a diagonal degeneracy.) -/
lemma hPrimeIter_diagDegen_comp_retractionN₂ {m r s : ℕ} (X : BisimplicialObject C) (k : ℕ)
    (θ : (⦋m + k⦌ : SimplexCategory) ⟶ ⦋s⦌) (hθ : ¬ Mono θ) (N : DerivedOp r s) :
    DerivedOp.realize X
        (((DerivedOp.primeIter k (hOp m)).comp
          (Finsupp.single (⟨θ, θ⟩ : OpLetter s (m + k)) 1)).comp N) ≫
      (retractionN₂ X).f (m + k) = 0 := by
  induction k with
  | zero =>
      -- `primeIter 0 (hOp m) = hOp m`, so this is the `k = 0` base `hOp_diagDegen_comp_retractionN₂`
      -- pushed past the trailing `N` via `realize_comp` (which absorbs the leading `realize N`).
      have key : ((DerivedOp.primeIter 0 (hOp m)).comp
          (Finsupp.single (⟨θ, θ⟩ : OpLetter s (m + 0)) 1)).realize X ≫
            (retractionN₂ X).f (m + 0) = 0 :=
        hOp_diagDegen_comp_retractionN₂ X θ hθ
      rw [realize_comp, Category.assoc, key, Limits.comp_zero]
  | succ k ih =>
      sorry

/-- A `DerivedOp` is a **norm** (EM, for the diagonal `K×_N L`), defined *structurally* so that
closure under `prime` is manifest (no `realize`-bridge needed). Generators: diagonal degeneracies
`⟨θ,θ⟩∘N` (`¬Mono θ`) and EM (2.12) `h`-degeneracies `(h-with-`k`-primes)∘⟨θ,θ⟩∘N`, closed under
`+`/`neg`. (`C`-free; killed under `retractionN₂` via `IsNorm.kill`.) -/
inductive IsNorm : {s q : ℕ} → DerivedOp s q → Prop where
  | zero {s q : ℕ} : IsNorm (0 : DerivedOp s q)
  | add {s q : ℕ} {M N : DerivedOp s q} : IsNorm M → IsNorm N → IsNorm (M + N)
  | neg {s q : ℕ} {M : DerivedOp s q} : IsNorm M → IsNorm (-M)
  | diagDegen {r s q : ℕ} (θ : (⦋q⦌ : SimplexCategory) ⟶ ⦋s⦌) (hθ : ¬ Mono θ) (N : DerivedOp r s) :
      IsNorm (DerivedOp.comp (Finsupp.single (⟨θ, θ⟩ : OpLetter s q) 1) N)
  | hPrimeDiag {m r s : ℕ} (k : ℕ) (θ : (⦋m + k⦌ : SimplexCategory) ⟶ ⦋s⦌) (hθ : ¬ Mono θ)
      (N : DerivedOp r s) :
      IsNorm (((DerivedOp.primeIter k (hOp m)).comp
        (Finsupp.single (⟨θ, θ⟩ : OpLetter s (m + k)) 1)).comp N)

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
  | hPrimeDiag k θ hθ N₀ => rw [DerivedOp.comp_assoc]; exact IsNorm.hPrimeDiag k θ hθ _

/-- **Every norm dies under `retractionN₂`** (for every `X`). Structural induction: linear cases are
`realize`-linearity; the two generators are the (2)-diagonal kill and EM (2.12). -/
lemma IsNorm.kill {s q : ℕ} {M : DerivedOp s q} (h : IsNorm M) (X : BisimplicialObject C) :
    DerivedOp.realize X M ≫ (retractionN₂ X).f q = 0 := by
  induction h with
  | zero => rw [realize_zero, Limits.zero_comp]
  | add _ _ ihM ihN => rw [realize_add, Preadditive.add_comp, ihM, ihN, add_zero]
  | neg _ ihM => rw [realize_neg, Preadditive.neg_comp, ihM, neg_zero]
  | diagDegen θ hθ N => exact realize_comp_diagLetter_not_mono_comp_retractionN₂ X θ hθ N
  | hPrimeDiag k θ hθ N => exact hPrimeIter_diagDegen_comp_retractionN₂ X k θ hθ N

/-- **The norm class is closed under `prime`** — now *structural*: `prime` maps each generator to a
generator (`⟨θ,θ⟩∘N ↦ ⟨primeHom θ,primeHom θ⟩∘N'` via `prime_single_diag`+`primeHom_not_mono`;
the `h`-degeneracy with `k` primes ↦ the one with `k+1`). This is what lets the *exact* IH be primed
in `phi_op_isNorm`. -/
lemma IsNorm.prime {s q : ℕ} {M : DerivedOp s q} (h : IsNorm M) : IsNorm M.prime := by
  induction h with
  | zero => rw [prime_zero]; exact IsNorm.zero
  | add _ _ ihM ihN => rw [prime_add]; exact ihM.add ihN
  | neg _ ihM => rw [prime_neg]; exact ihM.neg
  | diagDegen θ hθ N =>
      rw [prime_comp, prime_single_diag]
      exact IsNorm.diagDegen (primeHom θ) (primeHom_not_mono hθ) N.prime
  | hPrimeDiag k θ hθ N =>
      rw [prime_comp, prime_comp, prime_single_diag]
      exact IsNorm.hPrimeDiag (k + 1) (primeHom θ) (primeHom_not_mono hθ) N.prime

/-- **Base case (EM `q = 1`, degree 1)**, md 169–171: the degree-1 homotopy identity, as a norm.
Needs EM (2.11)'s explicit degree-1 value of `h` (item 4) — an `hOp` low-degree input. -/
lemma phi_op_isNorm_zero :
    IsNorm ((phiOp 0).comp (boundaryOp 0) + (boundaryOp 1).comp (phiOp 1) + idOp 1 - hOp 1) := by
  sorry

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
- [ ] **(3c)** `prime_comp_D0_of_frontal` (`M' D₀ = D₀ M` for frontal `M`, I.3.3). Letter identity
      `σ 0 ≫ primeHom θ = θ ≫ σ 0` **using** `IsFrontalHom θ` (`θ 0 = 0`); without frontality it
      fails at the bottom vertex. `Hom.ext` + `Fin.cases` + `omega`, casing on `θ 0 = 0`.
- [x] **(3d)** `boundary_comp_D0` (`∂ D₀ = D₀ ∂'`). NB: EM line 179 writes this as `∂ D₀ = 1 − D₀ ∂'`,
      but that quantity is `∂' D₀`; since `∂ = F₀ − ∂'` the bottom two faces `F₀ D₀ = F₁ D₀ = 1`
      cancel, so the true identity is `∂ D₀ = D₀ ∂'`. Proved at the operator level: distribute `comp`
      over the boundary sum (`compRightD0`/`compLeftD0` `AddMonoidHom`s + `map_sum`/`map_zsmul`), peel
      the `i=0,1` terms (`δ_0 σ_0 = δ_1 σ_0 = 𝟙`, which cancel), and match the tail via
      `δ_{i} σ_0 = σ_0 δ_{i-1}` (`δ_comp_σ_of_gt`).

### Phase 4 — `hOp` representation (hard, isolated; see "characterize" discussion)

- [ ] **(4a)** Define `hOp q` as the explicit `Σ_{p,μ} μ.sign • single ⟨ι_front ≫ fstHom, ι_back ≫
      sndHom⟩` (the `awComponent ≫ ezComponent` merge). *Or* obtain it by `Classical.choice` of an
      existence statement and only ever use (4b)/(4c).
- [ ] **(4b)** `realize_hOp` (`realize (hOp q) = (alexanderWhitney X ≫ shuffleMap X).f q`). The
      Pattern-5 merge again, summed over splits/shuffles; mirrors `awShuffle_f_eq_sum`
      (`Bisimplicial.lean:1318`) composed with the EZ side.
- [ ] **(4c)** `hOp_frontalFst` — `ι_front` fixes `0`, so the horizontal words are frontal.
      **Optional** (only for `fΦ = 0`, 2.4); skip unless needed.
- [ ] **(4d)** `phiOp_frontal` — induction on `q`: `phiOp 0 = 0` is vacuously frontal; the step is a
      sum of primed operators, each frontal by `prime_frontal` (+ `Frontal` closed under `+`/`comp`/
      `zsmul`/`single`-support). Needs small `Frontal`-algebra helper lemmas (add as you go).

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
      - `hPrimeIter_diagDegen_comp_retractionN₂` (EM (2.12), general `h`-degeneracy kill, feeds
        `IsNorm.kill`).
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
