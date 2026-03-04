/-
This file was edited by Aristotle (https://aristotle.harmonic.fun).

Lean version: leanprover/lean4:v4.24.0
Mathlib version: f897ebcf72cd16f89ab4577d0c826cd14afaafc7
This project request had uuid: 50b54e27-aba5-4286-9db7-cdfc0d8f251f

To cite Aristotle, tag @Aristotle-Harmonic on GitHub PRs/issues, and add as co-author to commits:
Co-authored-by: Aristotle (Harmonic) <aristotle-harmonic@harmonic.fun>

The following was proved by Aristotle:

- lemma invCount_add_invCount_swap {p q : ℕ} (u : Shuffle p q) :
    u.invCount + (u.swap).invCount = p * q
-/

import Mathlib.Tactic
import Mathlib.GroupTheory.Perm.Sign
import Mathlib.Order.Fin.Basic


noncomputable section

namespace HomologyLean.SingularHomology

/-! ### Shuffles -/

/-- The finite chain object `0 ≤ 1 ≤ ··· ≤ k` in `PoSet`, represented by `Fin (k+1)`. -/
abbrev Index (k : ℕ) := Fin (k + 1)

/-- A `(p,q)`-shuffle as an injective monotone map
`Index (p + q) ⟶ Index p × Index q` in `PoSet`. -/
abbrev Shuffle (p q : ℕ) :=
  { φ : Index (p + q) →o (Index p × Index q) // Function.Injective φ }

namespace Shuffle

/-- Canonical inclusion of `Fin p` into `Fin (p + q)`. -/
def left {p q : ℕ} (_μ : Shuffle p q) : Fin p → Fin (p + q) := fun i =>
  ⟨i, by omega⟩

/-- Canonical inclusion of `Fin q` into `Fin (p + q)` shifted by `p`. -/
def right {p q : ℕ} (_μ : Shuffle p q) : Fin q → Fin (p + q) := fun j =>
  ⟨p + j, by omega⟩

/-- There are finitely many (p,q)-shuffles: exactly `Nat.choose (p + q) p`. -/
noncomputable instance instFintype (p q : ℕ) : Fintype (Shuffle p q) := by
  classical
  have : Finite (Index (p + q) →o (Index p × Index q)) := by
    classical
    refine Finite.of_injective (fun f : Index (p + q) →o (Index p × Index q) => f.toFun) ?_
    intro f g h
    ext x
    repeat simp at h; simp [h]
  exact Fintype.ofFinite (Shuffle p q)

-- TODO: Actually show order is Nat.choose (p + q) p
/-- The **number of inversions** of a shuffle. -/
def invCount {p q : ℕ} (μ : Shuffle p q) : ℕ :=
  ∑ r : Fin (p + q),
    if ((μ.1 (Fin.castSucc r)).1 < (μ.1 (Fin.succ r)).1) then
      ((μ.1 (Fin.castSucc r)).2).1
    else 0

/-- The sign of a shuffle: `(-1)^k` where `k` is the number of inversions. -/
def sign {p q : ℕ} (μ : Shuffle p q) : ℤ :=
  (-1 : ℤ) ^ μ.invCount

/-- Swap the two coordinates of a shuffle, yielding a `(q,p)`-shuffle. -/
def swap {p q : ℕ} (μ : Shuffle p q) : Shuffle q p := by
  classical
  let e : Index (q + p) ≃o Index (p + q) :=
    Fin.castOrderIso (by simp [Nat.add_comm, Nat.add_assoc])
  refine ⟨?_, ?_⟩
  · refine
      { toFun := fun x => (μ.1 (e x)).swap
        monotone' := ?_ }
    intro a b hab
    have h := μ.1.monotone (e.monotone hab)
    rcases h with ⟨h₁, h₂⟩
    exact ⟨h₂, h₁⟩
  · intro a b hab
    have hab' : μ.1 (e a) = μ.1 (e b) := by
      simpa using congrArg Prod.swap hab
    have : e a = e b := μ.2 hab'
    exact e.injective this

@[simp]
theorem swap_swap {p q : ℕ} (μ : Shuffle p q) : swap (swap μ) = μ := by
  classical
  apply Subtype.ext
  ext x
  repeat simp [swap]

/-- Swapping coordinates gives an equivalence `Shuffle p q ≃ Shuffle q p`. -/
def swapEquiv (p q : ℕ) : Shuffle p q ≃ Shuffle q p where
  toFun := swap
  invFun := swap
  left_inv μ := by simp
  right_inv μ := by simp

/-! #### Lattice path structure -/

/-- The coordinate sum `fst + snd` is strictly monotone along a shuffle path. -/
private lemma coordSum_lt {p q : ℕ} (u : Shuffle p q)
    {i j : Fin (p + q + 1)} (hij : i < j) :
    (u.1 i).1.val + (u.1 i).2.val < (u.1 j).1.val + (u.1 j).2.val := by
  have hmono := u.1.monotone (le_of_lt hij)
  have hinj : u.1 i ≠ u.1 j := fun h => (ne_of_lt hij) (u.2 h)
  obtain ⟨h1, h2⟩ := hmono
  -- Extract val-level inequalities for omega
  have h1v : (u.1 i).1.val ≤ (u.1 j).1.val := h1
  have h2v : (u.1 i).2.val ≤ (u.1 j).2.val := h2
  rcases Nat.lt_or_eq_of_le h1v with h1' | h1'
  · omega
  · rcases Nat.lt_or_eq_of_le h2v with h2' | h2'
    · omega
    · exact absurd (Prod.ext (Fin.ext h1') (Fin.ext h2')) hinj

/-- At every position `r`, the coordinate sum equals `r.val`. -/
private lemma coordSum_eq {p q : ℕ} (u : Shuffle p q) (r : Fin (p + q + 1)) :
    (u.1 r).1.val + (u.1 r).2.val = r.val := by
  have castSucc_lt_succ : ∀ i : Fin (p + q), i.castSucc < i.succ := by
    intro i; simp [Fin.lt_def]
  apply le_antisymm
  · -- Upper bound by reverse induction: g(last) ≤ p + q, g(r) < g(r+1) ≤ r+1
    induction r using Fin.reverseInduction with
    | last =>
      have := (u.1 (Fin.last (p + q))).1.isLt
      have := (u.1 (Fin.last (p + q))).2.isLt
      simp [Fin.val_last]; omega
    | cast i ih =>
      have hlt := coordSum_lt u (castSucc_lt_succ i)
      simp only [Fin.val_succ, Fin.val_castSucc] at ih ⊢; omega
  · -- Lower bound by forward induction: g(0) ≥ 0, g(r+1) > g(r) ≥ r
    induction r using Fin.induction with
    | zero => exact Nat.zero_le _
    | succ i ih =>
      have hlt := coordSum_lt u (castSucc_lt_succ i)
      simp only [Fin.val_succ, Fin.val_castSucc] at ih ⊢; omega

/-- At each step of a shuffle, exactly one coordinate increases by 1. -/
private lemma shuffle_step {p q : ℕ} (u : Shuffle p q) (r : Fin (p + q)) :
    ((u.1 r.castSucc).1.val + 1 = (u.1 r.succ).1.val ∧
     (u.1 r.castSucc).2.val = (u.1 r.succ).2.val) ∨
    ((u.1 r.castSucc).1.val = (u.1 r.succ).1.val ∧
     (u.1 r.castSucc).2.val + 1 = (u.1 r.succ).2.val) := by
  have hmono := u.1.monotone (show r.castSucc ≤ r.succ from by simp [Fin.le_def])
  obtain ⟨h1, h2⟩ := hmono
  have h1v : (u.1 r.castSucc).1.val ≤ (u.1 r.succ).1.val := h1
  have h2v : (u.1 r.castSucc).2.val ≤ (u.1 r.succ).2.val := h2
  have hsum1 := coordSum_eq u r.castSucc
  have hsum2 := coordSum_eq u r.succ
  simp only [Fin.val_succ, Fin.val_castSucc] at hsum1 hsum2
  omega

/-- First coordinate increases iff second doesn't at each step. -/
private lemma shuffle_fst_lt_iff_not_snd_lt {p q : ℕ} (u : Shuffle p q) (r : Fin (p + q)) :
    (u.1 r.castSucc).1.val < (u.1 r.succ).1.val ↔
    ¬ ((u.1 r.castSucc).2.val < (u.1 r.succ).2.val) := by
  rcases shuffle_step u r with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> omega

/-- The swap of a shuffle at position x gives the swapped coordinates of u at the same position. -/
private lemma swap_apply_fst {p q : ℕ} (u : Shuffle p q) (x : Fin (q + p + 1)) :
    ((u.swap).1 x).1.val = (u.1 (x.cast (by omega))).2.val := by
  simp [swap, Fin.castOrderIso, Prod.swap]

private lemma swap_apply_snd {p q : ℕ} (u : Shuffle p q) (x : Fin (q + p + 1)) :
    ((u.swap).1 x).2.val = (u.1 (x.cast (by omega))).1.val := by
  simp [swap, Fin.castOrderIso, Prod.swap]

/-- Reindex swap's invCount to a sum over `Fin (p + q)` in terms of u's coordinates. -/
private lemma invCount_swap_eq {p q : ℕ} (u : Shuffle p q) :
    (u.swap).invCount = ∑ s : Fin (p + q),
      if (u.1 (Fin.castSucc s)).2 < (u.1 (Fin.succ s)).2
      then (u.1 (Fin.castSucc s)).1.val
      else 0 := by
  simp only [invCount]
  -- Establish Fin-level equalities for swap's coordinates
  have hswap1 : ∀ x : Fin (q + p + 1),
      ((u.swap).1 x).1 = (u.1 (x.cast (by omega))).2 :=
    fun x => Fin.ext (swap_apply_fst u x)
  have hswap2 : ∀ x : Fin (q + p + 1),
      ((u.swap).1 x).2 = (u.1 (x.cast (by omega))).1 :=
    fun x => Fin.ext (swap_apply_snd u x)
  simp_rw [hswap1, hswap2]
  -- Reindex from Fin(q+p) to Fin(p+q) via finCongr
  refine Fintype.sum_equiv (finCongr (by omega)) _ _ fun s => ?_
  have hcs : Fin.cast (show q + p + 1 = p + q + 1 from by omega) s.castSucc =
             (finCongr (show q + p = p + q from by omega) s).castSucc :=
    Fin.ext (by simp [finCongr])
  have hss : Fin.cast (show q + p + 1 = p + q + 1 from by omega) s.succ =
             (finCongr (show q + p = p + q from by omega) s).succ :=
    Fin.ext (by simp [finCongr])
  simp_rw [hcs, hss]

/-- Telescoping sum for ℕ-valued functions. -/
private lemma nat_sum_telescope : ∀ (n : ℕ) (g : ℕ → ℕ), (∀ i, i < n → g i ≤ g (i + 1)) →
    ∑ i ∈ Finset.range n, (g (i + 1) - g i) = g n - g 0 := by
  intro n
  induction n with
  | zero => intro g _; simp
  | succ k ih =>
    intro g hg
    rw [Finset.sum_range_succ, ih g (fun m hm => hg m (by omega))]
    have h1 := hg k (by omega)
    have h2 : g 0 ≤ g k := by
      suffices h : ∀ j, j ≤ k → g 0 ≤ g j from h k le_rfl
      intro j hj
      induction j with
      | zero => exact le_refl _
      | succ m ihm => exact le_trans (ihm (Nat.le_of_succ_le hj)) (hg m (by omega))
    omega

/- Total inversions of a shuffle and its swap equal `p * q`. -/
noncomputable section AristotleLemmas

/-
A shuffle path starts at (0,0).
-/
open HomologyLean.SingularHomology

lemma Shuffle.apply_zero {p q : ℕ} (u : Shuffle p q) : u.1 0 = (0, 0) := by
  -- Since u is injective and monotone, it must map the least element 0 to itself.
  have h_least : ∀ x : Fin (p + q + 1), (u.1 x).1.val + (u.1 x).2.val = x.val := by
    -- Apply the lemma that states the coordinate sum equals the position for any shuffle.
    apply coordSum_eq;
  specialize h_least 0; aesop;

/-
A shuffle path ends at (p,q).
-/
open HomologyLean.SingularHomology

lemma Shuffle.apply_last {p q : ℕ} (u : Shuffle p q) : u.1 (Fin.last (p + q)) = (Fin.last p, Fin.last q) := by
  have := @coordSum_eq p q u ( Fin.last ( p + q ) );
  exact Prod.ext ( Fin.ext ( by linarith! [ Fin.is_lt ( u.1 ( Fin.last ( p + q ) ) |>.1 ), Fin.is_lt ( u.1 ( Fin.last ( p + q ) ) |>.2 ) ] ) ) ( Fin.ext ( by linarith! [ Fin.is_lt ( u.1 ( Fin.last ( p + q ) ) |>.1 ), Fin.is_lt ( u.1 ( Fin.last ( p + q ) ) |>.2 ) ] ) )

/-
Express invCount as a sum of y * dx.
-/
open HomologyLean.SingularHomology

lemma Shuffle.invCount_eq_sum_mul_diff {p q : ℕ} (u : Shuffle p q) :
    u.invCount = ∑ r : Fin (p + q), (u.1 r.castSucc).2.val * ((u.1 r.succ).1.val - (u.1 r.castSucc).1.val) := by
      refine' Finset.sum_congr rfl fun i hi => _;
      have := shuffle_step u i;
      grind

/-
Express swap.invCount as a sum of x * dy.
-/
open HomologyLean.SingularHomology

lemma Shuffle.swap_invCount_eq_sum_mul_diff {p q : ℕ} (u : Shuffle p q) :
    (u.swap).invCount = ∑ r : Fin (p + q), (u.1 r.castSucc).1.val * ((u.1 r.succ).2.val - (u.1 r.castSucc).2.val) := by
      rw [ invCount_swap_eq, Finset.sum_congr rfl ];
      intro x hx; split_ifs <;> simp_all +decide [ Nat.sub_eq_iff_eq_add ] ;
      have := shuffle_step u x;
      grind

/-
The change in the product of coordinates equals y*dx + x*dy.
-/
open HomologyLean.SingularHomology

lemma Shuffle.xy_diff_eq_sum_mixed {p q : ℕ} (u : Shuffle p q) (r : Fin (p + q)) :
    (u.1 r.succ).1.val * (u.1 r.succ).2.val - (u.1 r.castSucc).1.val * (u.1 r.castSucc).2.val =
    (u.1 r.castSucc).2.val * ((u.1 r.succ).1.val - (u.1 r.castSucc).1.val) +
    (u.1 r.castSucc).1.val * ((u.1 r.succ).2.val - (u.1 r.castSucc).2.val) := by
      rw [ Nat.mul_sub_left_distrib, Nat.mul_sub_left_distrib ];
      cases shuffle_step u r <;> simp_all +decide [ mul_comm ]

end AristotleLemmas

lemma invCount_add_invCount_swap {p q : ℕ} (u : Shuffle p q) :
    u.invCount + (u.swap).invCount = p * q := by
  -- The sum of the differences in the product of coordinates is a telescoping sum, so most terms cancel out.
  have h_telescope : ∑ r : Fin (p + q), ((u.1 (Fin.succ r)).1.val * (u.1 (Fin.succ r)).2.val - (u.1 (Fin.castSucc r)).1.val * (u.1 (Fin.castSucc r)).2.val) = (u.1 (Fin.last (p + q))).1.val * (u.1 (Fin.last (p + q))).2.val - (u.1 0).1.val * (u.1 0).2.val := by
    have h_telescope : ∀ (n : ℕ) (f : Fin (n + 1) → ℕ), (∀ i : Fin n, f (Fin.castSucc i) ≤ f (Fin.succ i)) → ∑ i : Fin n, (f (Fin.succ i) - f (Fin.castSucc i)) = f (Fin.last n) - f 0 := by
      intro n f hf; induction' n with n ih <;> simp_all +decide [ Fin.sum_univ_castSucc ] ;
      convert congr_arg₂ ( · + · ) ( ih ( fun i => f i.castSucc ) ( fun i => hf ( Fin.castSucc i ) ) ) rfl using 1;
      simp +zetaDelta at *;
      rw [ tsub_add_eq_add_tsub ];
      · rw [ Nat.add_sub_of_le ];
        exact hf ( Fin.last _ );
      · exact Fin.inductionOn ( Fin.last n |> Fin.castSucc ) ( by norm_num ) fun i hi => by linarith! [ hf i ] ;
    convert h_telescope ( p + q ) ( fun i => ( u.1 i ).1.val * ( u.1 i ).2.val ) _ using 1;
    exact fun i => mul_le_mul' ( u.1.monotone ( Nat.le_succ _ ) |>.1 ) ( u.1.monotone ( Nat.le_succ _ ) |>.2 );
  convert h_telescope using 1;
  · rw [ Shuffle.invCount_eq_sum_mul_diff, Shuffle.swap_invCount_eq_sum_mul_diff, ← Finset.sum_add_distrib ];
    exact Finset.sum_congr rfl fun _ _ => by rw [ Shuffle.xy_diff_eq_sum_mixed ] ;
  · rw [ eq_tsub_iff_add_eq_of_le ] <;> norm_num [ Shuffle.apply_zero, Shuffle.apply_last ]

/-- Swapping a `(p,q)`-shuffle changes the sign by the Koszul factor `(-1)^(p*q)`. -/
theorem sign_eq_negOnePow_mul_swap_sign {p q : ℕ} (u : Shuffle p q) :
    u.sign = (-1 : ℤ) ^ (p * q) * (u.swap).sign := by
  have h := invCount_add_invCount_swap u
  simp only [sign]
  conv_rhs => rw [show (p * q : ℕ) = u.invCount + (u.swap).invCount from h.symm]
  rw [pow_add, mul_assoc]
  suffices (-1 : ℤ) ^ (u.swap).invCount * (-1 : ℤ) ^ (u.swap).invCount = 1 by
    rw [this, mul_one]
  rw [← mul_pow]
  norm_num

/-! #### Shuffle (0,0) -/

/-- For `Shuffle 0 0`, the domain and codomain are both `Fin 1`, so every shuffle
has the same underlying map: the unique monotone injection to `(0, 0)`. -/
lemma unique_0_0 (μ : Shuffle 0 0) :
    μ.1 = ⟨fun _ => (0, 0), fun _ _ _ => le_refl _⟩ := by
  ext x
  · simp [Fin.eq_zero (μ.1 x).1]
  · simp [Fin.eq_zero (μ.1 x).2]

/-- There is exactly one `(0,0)`-shuffle. -/
instance subsingleton_0_0 : Subsingleton (Shuffle 0 0) :=
  ⟨fun μ ν => Subtype.ext (by rw [unique_0_0 μ, unique_0_0 ν])⟩

/-- The unique `(0,0)`-shuffle. -/
def default_0_0 : Shuffle 0 0 :=
  ⟨⟨fun _ => (0, 0), fun _ _ _ => le_refl _⟩,
    fun _ _ _ => Fin.ext (by simp [Fin.eq_zero])⟩

/-- The unique `(0,0)`-shuffle has sign 1. -/
lemma sign_0_0 : (default_0_0 : Shuffle 0 0).sign = 1 := by
  simp [sign, invCount]

/-! #### Face-shuffle decomposition (Leibniz rule infrastructure)

**Why "remove step" doesn't work.**  An earlier attempt defined `removeLeftStep μ r`
by removing vertex `r` from the shuffle path whenever step `r` is a left step.
This is wrong: the face map `δ_r` removes **vertex** `r`, which merges the steps
on either side of `r`. If those steps have different types (one left, one right),
the merged step is a **diagonal** (both coordinates increase), which cannot be a
valid shuffle step.

Example: the `(1,1)`-shuffle `(0,0) → (1,0) → (1,1)` has step 0 = Left,
step 1 = Right.  Removing vertex 1 = `(1,0)` gives `(0,0) → (1,1)`, a diagonal.
This doesn't factor as `ν ≫ (δⱼ × id)` for any shuffle `ν`.  The factorization
only works for "LL" vertices (both adjacent steps are left) or "RR" vertices.

**The insert approach.**  Instead of decomposing the LHS face terms, we work from
the RHS and **inject** into the LHS.  Given a `(p, q+1)`-shuffle `ν` and a face
index `j : Fin (p+2)`, we construct a `(p+1, q+1)`-shuffle `insertLeftStep ν j`
by lifting ν's first coordinate via `Fin.succAbove j` (skipping value `j`) and
inserting a new left step where the first coordinate crosses `j`.

The proof of `universalSimplexCrossProduct_boundary` then proceeds:
1. Show the RHS terms inject into the LHS via `insertLeftStep` / `insertRightStep`.
2. Show the remaining LHS terms (diagonal terms) cancel via a sign-reversing
   involution `swapDiagonalSteps`.
-/

/-- Whether step `r` of shuffle `μ` is a "left step" (first coordinate increments). -/
def isLeftStep {p q : ℕ} (μ : Shuffle p q) (r : Fin (p + q)) : Prop :=
  (μ.1 r.castSucc).1.val < (μ.1 r.succ).1.val

instance isLeftStep_decidable {p q : ℕ} (μ : Shuffle p q) (r : Fin (p + q)) :
    Decidable (isLeftStep μ r) :=
  inferInstanceAs (Decidable (_ < _))

/-! ##### Insertion maps (RHS → LHS direction) -/

/-- Insert a left step at face index `j`, turning a `(p, q)`-shuffle into a
`(p+1, q)`-shuffle.  The original path from `(0,0)` to `(p, q)` is embedded
into a path from `(0,0)` to `(p+1, q)` by applying `Fin.succAbove j` to the
first coordinate and inserting a new left step where the first coordinate
crosses `j`. -/
def insertLeftStep {p q : ℕ} (ν : Shuffle p q) (j : Fin (p + 2)) :
    Shuffle (p + 1) q := by
  sorry

/-- The vertex index in the `(p+1, q)`-shuffle's domain where the new left step
was inserted. Removing this vertex via `δ` recovers the original shuffle. -/
def insertLeftIndex {p q : ℕ} (ν : Shuffle p q) (j : Fin (p + 2)) :
    Fin (p + q + 2) := by
  sorry

/-- Insert a right step at face index `k`, turning a `(p, q)`-shuffle into a
`(p, q+1)`-shuffle.  Applies `Fin.succAbove k` to the second coordinate and
inserts a new right step where the second coordinate crosses `k`. -/
def insertRightStep {p q : ℕ} (ν : Shuffle p q) (k : Fin (q + 2)) :
    Shuffle p (q + 1) := by
  sorry

/-- The vertex index where the new right step was inserted. -/
def insertRightIndex {p q : ℕ} (ν : Shuffle p q) (k : Fin (q + 2)) :
    Fin (p + q + 2) := by
  sorry

/-- Inserting a left step and removing the inserted vertex recovers the original
shuffle with `Fin.succAbove j` applied to the first coordinate.
(Purely combinatorial: no `SimplexCategory` or topology needed.) -/
lemma insertLeftStep_face {p q : ℕ} (ν : Shuffle p q) (j : Fin (p + 2)) :
    ∀ (k : Index (p + q)),
      (insertLeftStep ν j).1 (Fin.succAbove
        (⟨(insertLeftIndex ν j).val, by omega⟩ : Fin ((p + 1) + q + 1))
        (k.cast (by omega))) =
      (j.succAbove (ν.1 k).1, (ν.1 k).2) := by
  sorry

/-- Inserting a right step and removing the inserted vertex recovers the original
shuffle with `Fin.succAbove k` applied to the second coordinate. -/
lemma insertRightStep_face {p q : ℕ} (ν : Shuffle p q) (k : Fin (q + 2)) :
    ∀ (i : Index (p + q)),
      (insertRightStep ν k).1 (Fin.succAbove
        (⟨(insertRightIndex ν k).val, by omega⟩ : Fin (p + (q + 1) + 1))
        (i.cast (by omega))) =
      ((ν.1 i).1, k.succAbove (ν.1 i).2) := by
  sorry

/-- The insert-left map `(j, ν) ↦ (insertLeftStep ν j, insertLeftIndex ν j)` is
injective: distinct `(j, ν)` pairs produce distinct `(μ, vertex)` pairs. -/
lemma insertLeftStep_injective {p q : ℕ}
    (j₁ j₂ : Fin (p + 2)) (ν₁ ν₂ : Shuffle p q)
    (hμ : insertLeftStep ν₁ j₁ = insertLeftStep ν₂ j₂)
    (hr : insertLeftIndex ν₁ j₁ = insertLeftIndex ν₂ j₂) :
    j₁ = j₂ ∧ ν₁ = ν₂ := by
  sorry

/-- The insert-right map is injective. -/
lemma insertRightStep_injective {p q : ℕ}
    (k₁ k₂ : Fin (q + 2)) (ν₁ ν₂ : Shuffle p q)
    (hμ : insertRightStep ν₁ k₁ = insertRightStep ν₂ k₂)
    (hr : insertRightIndex ν₁ k₁ = insertRightIndex ν₂ k₂) :
    k₁ = k₂ ∧ ν₁ = ν₂ := by
  sorry

/-- Sign relation for left insertion:
`(insertLeftStep ν j).sign * (-1)^(insertLeftIndex ν j) = (-1)^j * ν.sign`. -/
lemma sign_insertLeftStep {p q : ℕ}
    (ν : Shuffle p q) (j : Fin (p + 2)) :
    (insertLeftStep ν j).sign * (-1 : ℤ) ^ (insertLeftIndex ν j).val =
    (-1 : ℤ) ^ j.val * ν.sign := by
  sorry

/-- Sign relation for right insertion:
`(insertRightStep ν k).sign * (-1)^(insertRightIndex ν k) =
 (-1)^p * (-1)^k * ν.sign`. -/
lemma sign_insertRightStep {p q : ℕ}
    (ν : Shuffle p q) (k : Fin (q + 2)) :
    (insertRightStep ν k).sign * (-1 : ℤ) ^ (insertRightIndex ν k).val =
    (-1 : ℤ) ^ p * ((-1 : ℤ) ^ k.val * ν.sign) := by
  sorry

/-! ##### Diagonal cancellation

The LHS terms not in the image of `insertLeftStep` or `insertRightStep` are
"diagonal" terms: they arise from vertex removals where the steps on either
side have different types (one left, one right).  These cancel pairwise via
a sign-reversing involution that swaps the two steps around the removed vertex. -/

/-- A `(μ, r)` pair is a **diagonal term** if vertex `r` has one adjacent left
step and one adjacent right step (in either order LR or RL).
Boundary vertices (r = 0 or r = last) are never diagonal. -/
def isDiagonalVertex {p q : ℕ} (μ : Shuffle (p + 1) (q + 1))
    (r : Index (p + 1 + (q + 1))) : Prop :=
  if h₁ : 0 < r.val then
    if h₂ : r.val < (p + 1) + (q + 1) then
      (isLeftStep μ ⟨r.val - 1, by omega⟩ ∧ ¬ isLeftStep μ ⟨r.val, h₂⟩) ∨
      (¬ isLeftStep μ ⟨r.val - 1, by omega⟩ ∧ isLeftStep μ ⟨r.val, h₂⟩)
    else False
  else False

instance isDiagonalVertex_decidable {p q : ℕ} (μ : Shuffle (p + 1) (q + 1)) :
    DecidablePred (isDiagonalVertex μ) := by
  intro r; unfold isDiagonalVertex; split_ifs <;> infer_instance

/-! ##### Insertion–diagonal interface

The insertion maps produce exactly the non-diagonal terms of the boundary sum.
Each insertion lands in the non-diagonal set, together they cover it, and
their images are disjoint. -/

/-- Left insertion always produces a non-diagonal vertex: the two steps
adjacent to the inserted vertex are both left steps (LL pattern). -/
lemma insertLeftStep_not_diagonal {p q : ℕ}
    (ν : Shuffle p (q + 1)) (j : Fin (p + 2)) :
    ¬isDiagonalVertex (insertLeftStep ν j)
      ((insertLeftIndex ν j).cast (by omega)) := by
  sorry

/-- Right insertion always produces a non-diagonal vertex: the two steps
adjacent to the inserted vertex are both right steps (RR pattern). -/
lemma insertRightStep_not_diagonal {p q : ℕ}
    (ν : Shuffle (p + 1) q) (k : Fin (q + 2)) :
    ¬isDiagonalVertex (insertRightStep ν k)
      ((insertRightIndex ν k).cast (by omega)) := by
  sorry

/-- Every non-diagonal vertex of a `(p+1,q+1)`-shuffle is in the image of
either `insertLeftStep` (from a `(p, q+1)`-shuffle and face index `j`) or
`insertRightStep` (from a `(p+1, q)`-shuffle and face index `k`).

This covers interior LL/RR vertices and boundary vertices (r = 0 or r = last). -/
lemma nondiag_mem_insertLeft_or_insertRight {p q : ℕ}
    (μ : Shuffle (p + 1) (q + 1)) (r : Index ((p + 1) + (q + 1)))
    (hr : ¬isDiagonalVertex μ r) :
    (∃ (j : Fin (p + 2)) (ν : Shuffle p (q + 1)),
      μ = insertLeftStep ν j ∧ (insertLeftIndex ν j).val = r.val) ∨
    (∃ (k : Fin (q + 2)) (ν : Shuffle (p + 1) q),
      μ = insertRightStep ν k ∧ (insertRightIndex ν k).val = r.val) := by
  sorry

/-- The images of `insertLeftStep` and `insertRightStep` are disjoint:
no `(p+1,q+1)`-shuffle with a given vertex index can arise from both
a left insertion and a right insertion. -/
lemma insertLeft_insertRight_disjoint {p q : ℕ}
    (j : Fin (p + 2)) (ν₁ : Shuffle p (q + 1))
    (k : Fin (q + 2)) (ν₂ : Shuffle (p + 1) q)
    (hμ : insertLeftStep ν₁ j = insertRightStep ν₂ k)
    (hr : (insertLeftIndex ν₁ j).val = (insertRightIndex ν₂ k).val) :
    False := by
  sorry

/-- Left insertion produces a left-type vertex: the step at (or just before)
the inserted vertex is a left step.  Here `isLeftType` checks `isLeftStep`
at index `min r.val ((p+1)+(q+1)-1)`. -/
lemma insertLeftStep_isLeftType {p q : ℕ}
    (ν : Shuffle p (q + 1)) (j : Fin (p + 2)) :
    isLeftStep (insertLeftStep ν j)
      ⟨min (insertLeftIndex ν j).val ((p + 1) + (q + 1) - 1), by omega⟩ := by
  sorry

/-- Right insertion produces a non-left-type vertex: the step at (or just before)
the inserted vertex is a right step, not a left step. -/
lemma insertRightStep_not_isLeftType {p q : ℕ}
    (ν : Shuffle (p + 1) q) (k : Fin (q + 2)) :
    ¬isLeftStep (insertRightStep ν k)
      ⟨min (insertRightIndex ν k).val ((p + 1) + (q + 1) - 1), by omega⟩ := by
  sorry

/-- The sign-reversing involution on diagonal terms.  Given a `(p+1, q+1)`-shuffle
`μ` and a diagonal vertex `r`, swap the steps adjacent to `r` (replacing an LR
corner with RL or vice versa).  This produces a new shuffle `μ'` such that:
- `μ' ∘ δ_r = μ ∘ δ_r` (same underlying map after vertex removal)
- `μ'.sign = -μ.sign` (opposite sign, from the inversion count change) -/
def swapDiagonalSteps {p q : ℕ} (μ : Shuffle (p + 1) (q + 1))
    (r : Index (p + 1 + (q + 1))) (hr : isDiagonalVertex μ r) :
    Shuffle (p + 1) (q + 1) := by
  sorry

/-- The swap involution preserves the diagonal vertex property. -/
lemma swapDiagonalSteps_vertex {p q : ℕ}
    (μ : Shuffle (p + 1) (q + 1)) (r : Index (p + 1 + (q + 1)))
    (hr : isDiagonalVertex μ r) :
    isDiagonalVertex (swapDiagonalSteps μ r hr) r := by
  sorry

/-- The swap is an involution. -/
lemma swapDiagonalSteps_involutive {p q : ℕ}
    (μ : Shuffle (p + 1) (q + 1)) (r : Index (p + 1 + (q + 1)))
    (hr : isDiagonalVertex μ r) :
    swapDiagonalSteps (swapDiagonalSteps μ r hr) r
      (swapDiagonalSteps_vertex μ r hr) = μ := by
  sorry

/-- The swap preserves the underlying OrderHom when composed with any OrderHom
that avoids the diagonal vertex. -/
lemma swapDiagonalSteps_same_map {p q n : ℕ}
    (μ : Shuffle (p + 1) (q + 1)) (r : Index (p + 1 + (q + 1)))
    (hr : isDiagonalVertex μ r) (φ : Fin n →o Index (p + 1 + (q + 1)))
    (hφ : ∀ k, φ k ≠ r) :
    (swapDiagonalSteps μ r hr).1.comp φ = μ.1.comp φ := by
  sorry

/-- The swap negates the signed coefficient. -/
lemma swapDiagonalSteps_neg_sign {p q : ℕ}
    (μ : Shuffle (p + 1) (q + 1)) (r : Index (p + 1 + (q + 1)))
    (hr : isDiagonalVertex μ r) :
    (swapDiagonalSteps μ r hr).sign * (-1 : ℤ) ^ r.val =
    -(μ.sign * (-1 : ℤ) ^ r.val) := by
  sorry

/-- The swap involution is never the identity: swapping two steps of different
type always produces a distinct shuffle. -/
lemma swapDiagonalSteps_ne {p q : ℕ}
    (μ : Shuffle (p + 1) (q + 1)) (r : Index (p + 1 + (q + 1)))
    (hr : isDiagonalVertex μ r) :
    swapDiagonalSteps μ r hr ≠ μ := by
  sorry

end Shuffle

/-- Double sum cancellation via a sign-reversing involution on the first index.
Given a predicate `p` on `α × β`, a function `f : α → β → M`, and an involution
`g : α → α` (depending on `b` and a proof of `p a b`) that negates `f` and preserves `p`,
the filtered double sum vanishes. -/
lemma sum_sum_involution_zero {α β M : Type*}
    [Fintype α] [Fintype β] [AddCommGroup M]
    (p : α → β → Prop) [∀ a, DecidablePred (p a)]
    (f : α → β → M)
    (g : (a : α) → (b : β) → p a b → α)
    (hg_pred : ∀ a b h, p (g a b h) b)
    (hg_invol : ∀ a b h, g (g a b h) b (hg_pred a b h) = a)
    (hg_neg : ∀ a b h, f (g a b h) b = -f a b)
    (hg_ne : ∀ a b h, g a b h ≠ a) :
    (∑ a : α, Finset.sum (Finset.univ.filter (p a)) (f a)) = 0 := by
  sorry

end HomologyLean.SingularHomology
