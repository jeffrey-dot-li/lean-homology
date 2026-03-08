/-
This file was edited by Aristotle (https://aristotle.harmonic.fun).

Lean version: leanprover/lean4:v4.24.0
Mathlib version: f897ebcf72cd16f89ab4577d0c826cd14afaafc7
This project request had uuid: 835e988f-99c7-4b44-a6a3-e4cd095f31dc

To cite Aristotle, tag @Aristotle-Harmonic on GitHub PRs/issues, and add as co-author to commits:
Co-authored-by: Aristotle (Harmonic) <aristotle-harmonic@harmonic.fun>

The following was proved by Aristotle:

- private lemma insertLeftIndex_ge {p q : ℕ} (ν : Shuffle p q) (j : Fin (p + 2)) :
    j.val ≤ (insertLeftIndex ν j).val

- private lemma insertRightIndex_ge {p q : ℕ} (ν : Shuffle p q) (k : Fin (q + 2)) :
    k.val ≤ (insertRightIndex ν k).val

- private lemma insertRightIndex_iff {p q : ℕ} (ν : Shuffle p q) (k : Fin (q + 2))
    (r : Fin (p + q + 1)) :
    (ν.1 r).2.val < k.val ↔ r.val < (insertRightIndex ν k).val

- lemma shuffle_fst_succ_le {p q : ℕ} (ν : Shuffle p q) (i : Fin (p + q + 1))
    (hi : i.val + 1 < p + q + 1) :
    (ν.1 ⟨i.val + 1, by omega⟩).1.val ≤ (ν.1 ⟨i.val, i.isLt⟩).1.val + 1

- lemma insertLeftStep_face {p q : ℕ} (ν : Shuffle p q) (j : Fin (p + 2)) :
    ∀ (k : Index (p + q)),
      (insertLeftStep ν j).1 (Fin.succAbove
        (⟨(insertLeftIndex ν j).val, by omega⟩ : Fin ((p + 1) + q + 1))
        (k.cast (by omega))) =
      (j.succAbove (ν.1 k).1, (ν.1 k).2)

- lemma insertRightStep_face {p q : ℕ} (ν : Shuffle p q) (k : Fin (q + 2)) :
    ∀ (i : Index (p + q)),
      (insertRightStep ν k).1 (Fin.succAbove
        (⟨(insertRightIndex ν k).val, by omega⟩ : Fin (p + (q + 1) + 1))
        (i.cast (by omega))) =
      ((ν.1 i).1, k.succAbove (ν.1 i).2)

- lemma insertLeftStep_injective {p q : ℕ}
    (j₁ j₂ : Fin (p + 2)) (ν₁ ν₂ : Shuffle p q)
    (hμ : insertLeftStep ν₁ j₁ = insertLeftStep ν₂ j₂)
    (hr : insertLeftIndex ν₁ j₁ = insertLeftIndex ν₂ j₂) :
    j₁ = j₂ ∧ ν₁ = ν₂

- lemma insertRightStep_injective {p q : ℕ}
    (k₁ k₂ : Fin (q + 2)) (ν₁ ν₂ : Shuffle p q)
    (hμ : insertRightStep ν₁ k₁ = insertRightStep ν₂ k₂)
    (hr : insertRightIndex ν₁ k₁ = insertRightIndex ν₂ k₂) :
    k₁ = k₂ ∧ ν₁ = ν₂

At Harmonic, we use a modified version of the `generalize_proofs` tactic.
For compatibility, we include this tactic at the start of the file.
If you add the comment "-- Harmonic `generalize_proofs` tactic" to your file, we will not do this.
-/

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
-- Harmonic `generalize_proofs` tactic
import Mathlib.Tactic
import Mathlib.GroupTheory.Perm.Sign
import Mathlib.Order.Fin.Basic


import Mathlib.Tactic.GeneralizeProofs

noncomputable section

namespace HomologyLean.SingularHomology

/-! ### Shuffles -/

/-- Backward-compatible copy of `Fin.val_castSucc` (not available in all Lean versions). -/
private theorem fin_val_castSucc (i : Fin n) : (i.castSucc : Nat) = i := rfl

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
      simp only [Fin.val_succ, fin_val_castSucc] at ih ⊢; omega
  · -- Lower bound by forward induction: g(0) ≥ 0, g(r+1) > g(r) ≥ r
    induction r using Fin.induction with
    | zero => exact Nat.zero_le _
    | succ i ih =>
      have hlt := coordSum_lt u (castSucc_lt_succ i)
      simp only [Fin.val_succ, fin_val_castSucc] at ih ⊢; omega

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
  simp only [Fin.val_succ, fin_val_castSucc] at hsum1 hsum2
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

/-! ##### Insertion indices -/

/-- The vertex index in the `(p+1, q)`-shuffle's domain where the new left step
was inserted. Removing this vertex via `δ` recovers the original shuffle.
Equals the number of vertices of `ν` whose first coordinate is `< j`. -/
def insertLeftIndex {p q : ℕ} (ν : Shuffle p q) (j : Fin (p + 2)) :
    Fin (p + q + 2) :=
  ⟨(Finset.univ.filter fun r : Fin (p + q + 1) => (ν.1 r).1.val < j.val).card, by
    exact Nat.lt_of_le_of_lt (Finset.card_filter_le _ _) (by simp)⟩

/-- The vertex index where the new right step was inserted.
Equals the number of vertices of `ν` whose second coordinate is `< k`. -/
def insertRightIndex {p q : ℕ} (ν : Shuffle p q) (k : Fin (q + 2)) :
    Fin (p + q + 2) :=
  ⟨(Finset.univ.filter fun r : Fin (p + q + 1) => (ν.1 r).2.val < k.val).card, by
    exact Nat.lt_of_le_of_lt (Finset.card_filter_le _ _) (by simp)⟩

/-! ##### Insertion helpers -/

/-- The insertion index satisfies `t ≤ j + q`: vertices with fst < j have
index ≤ (j-1) + q by `coordSum_eq`, so there are at most j + q of them. -/
private lemma insertLeftIndex_le {p q : ℕ} (ν : Shuffle p q) (j : Fin (p + 2)) :
    (insertLeftIndex ν j).val ≤ j.val + q := by
  simp only [insertLeftIndex]
  -- Inject the filter into Finset.range (j+q) via Fin.val
  calc (Finset.univ.filter fun r : Fin (p + q + 1) => (ν.1 r).1.val < j.val).card
      = ((Finset.univ.filter fun r : Fin (p + q + 1) => (ν.1 r).1.val < j.val).image
          Fin.val).card := (Finset.card_image_of_injective _ Fin.val_injective).symm
    _ ≤ (Finset.range (j.val + q)).card := by
          apply Finset.card_le_card; intro x hx
          simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and,
            Finset.mem_range] at hx ⊢
          obtain ⟨r, hr, rfl⟩ := hx
          have := coordSum_eq ν r; have := (ν.1 r).2.isLt; omega
    _ = j.val + q := Finset.card_range _

/-- Symmetric bound: the right insertion index satisfies `t ≤ p + k`. -/
private lemma insertRightIndex_le {p q : ℕ} (ν : Shuffle p q) (k : Fin (q + 2)) :
    (insertRightIndex ν k).val ≤ p + k.val := by
  simp only [insertRightIndex]
  calc (Finset.univ.filter fun r : Fin (p + q + 1) => (ν.1 r).2.val < k.val).card
      = ((Finset.univ.filter fun r : Fin (p + q + 1) => (ν.1 r).2.val < k.val).image
          Fin.val).card := (Finset.card_image_of_injective _ Fin.val_injective).symm
    _ ≤ (Finset.range (p + k.val)).card := by
          apply Finset.card_le_card; intro x hx
          simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and,
            Finset.mem_range] at hx ⊢
          obtain ⟨r, hr, rfl⟩ := hx
          have := coordSum_eq ν r; have := (ν.1 r).1.isLt; omega
    _ = p + k.val := Finset.card_range _

/-- Lower bound: the left insertion index satisfies `j ≤ t`.
Proof: any r with r.val < j has fst(r) ≤ r < j, so the filter includes all r < j. -/
private lemma insertLeftIndex_ge {p q : ℕ} (ν : Shuffle p q) (j : Fin (p + 2)) :
    j.val ≤ (insertLeftIndex ν j).val := by
  -- The set of indices where the first coordinate is less than $j$ contains at least the indices $0, 1, ..., j-1$.
  have h_filter : Finset.filter (fun r : Fin (p + q + 1) => (ν.1 r).1.val < j.val) Finset.univ ⊇ Finset.univ.filter (fun r : Fin (p + q + 1) => r.val < j.val) := by
    intro r hr;
    have := coordSum_eq ν r;
    grind;
  refine' le_trans _ ( Finset.card_mono h_filter );
  rw [ Finset.card_eq_of_bijective ];
  use fun i hi => ⟨ i, by linarith [ Fin.is_lt j ] ⟩;
  · aesop;
  · aesop;
  · aesop

/-- Symmetric lower bound: the right insertion index satisfies `k ≤ t`. -/
private lemma insertRightIndex_ge {p q : ℕ} (ν : Shuffle p q) (k : Fin (q + 2)) :
    k.val ≤ (insertRightIndex ν k).val := by
  -- Since `ν` is a monotone function, for any `r` with `r.val < k`, we have `ν.1 r ≤ r`. Therefore, the filter includes all `r < k`, so the cardinality is at least `k`.
  have h_filter : ∀ r : Fin (p + q + 1), r.val < k.val → (ν.1 r).2.val < k.val := by
    -- By the properties of ν, we know that the second coordinate of ν(r) is less than or equal to r.val.
    have h_second_coord_le_r : ∀ r : Fin (p + q + 1), (ν.1 r).2.val ≤ r.val := by
      exact fun r => by linarith [ coordSum_eq ν r ] ;
    exact fun r hr => lt_of_le_of_lt ( h_second_coord_le_r r ) hr;
  have h_filter_card : (Finset.univ.filter fun r : Fin (p + q + 1) => r.val < k.val).card ≤ (Finset.univ.filter fun r : Fin (p + q + 1) => (ν.1 r).2.val < k.val).card := by
    exact Finset.card_le_card fun x hx => by aesop;
  refine le_trans ?_ h_filter_card;
  rw [ Finset.card_eq_of_bijective ];
  use fun i hi => ⟨ i, by linarith [ Fin.is_lt k ] ⟩;
  · aesop;
  · aesop;
  · aesop

/-- The filter `{r | fst(r) < j}` is a downward-closed initial segment:
`fst(ν r) < j ↔ r.val < t` where `t = insertLeftIndex`. -/
private lemma insertLeftIndex_iff {p q : ℕ} (ν : Shuffle p q) (j : Fin (p + 2))
    (r : Fin (p + q + 1)) :
    (ν.1 r).1.val < j.val ↔ r.val < (insertLeftIndex ν j).val := by
  constructor <;> intro h;
  · -- Since ν is monotone, the set {x | x.val < t} is exactly the set of elements in the filter. Therefore, if r is in the filter, then r < t.
    have h_filter : {x : Fin (p + q + 1) | (ν.1 x).1.val < j.val} ⊇ Finset.Iio r := by
      intro x hx;
      exact lt_of_le_of_lt ( Nat.cast_le.mpr <| ν.1.monotone ( le_of_lt <| by aesop ) |> fun h => h.1 ) h;
    have h_filter_card : Finset.card (Finset.filter (fun x => (ν.1 x).1.val < j.val) Finset.univ) ≥ Finset.card (Finset.Iio r) + 1 := by
      refine' Finset.card_lt_card _;
      simp_all +decide [ Finset.ssubset_def, Finset.subset_iff ];
      exact ⟨ fun x hx => h_filter hx, r, h, le_rfl ⟩;
    aesop;
  · contrapose! h;
    exact le_trans ( Finset.card_le_card <| show Finset.filter ( fun x : Fin ( p + q + 1 ) => ( ν.1 x |>.1 : ℕ ) < j ) Finset.univ ⊆ Finset.Iio r from fun x hx => Finset.mem_Iio.mpr <| lt_of_not_ge fun hx' => by linarith [ Finset.mem_filter.mp hx, show ( ν.1 x |>.1 : ℕ ) ≥ ( ν.1 r |>.1 : ℕ ) by exact ν.1.monotone hx' |>.1 ] ) <| by simp +decide [ Finset.card_sdiff, Finset.card_range ] ;

/-- Symmetric: `snd(ν r) < k ↔ r.val < insertRightIndex`. -/

private lemma insertRightIndex_iff {p q : ℕ} (ν : Shuffle p q) (k : Fin (q + 2))
    (r : Fin (p + q + 1)) :
    (ν.1 r).2.val < k.val ↔ r.val < (insertRightIndex ν k).val := by
  convert insertLeftIndex_iff ( ν.swap ) k ( Fin.cast ( by omega ) r ) using 1;
  unfold Shuffle.insertRightIndex Shuffle.swap Shuffle.insertLeftIndex; simp +decide [ Fin.val_add, Nat.mod_eq_of_lt ] ;
  rw [ Finset.card_filter, Finset.card_filter ] ; ring!;
  convert Iff.rfl using 3 ; ring!;
  · grind;
  · simp +decide [ add_comm, Fin.cast ];
    congr! 3;
    congr! 2;
    congr! 2;
    exact?

/-! ##### Insertion maps (RHS → LHS direction) -/

/-- For an order-preserving injection into a product, the first component at consecutive
indices can increase by at most 1. -/
lemma shuffle_fst_succ_le {p q : ℕ} (ν : Shuffle p q) (i : Fin (p + q + 1))
    (hi : i.val + 1 < p + q + 1) :
    (ν.1 ⟨i.val + 1, by omega⟩).1.val ≤ (ν.1 ⟨i.val, i.isLt⟩).1.val + 1 := by
  -- By definition of `Shuffle`, we know that the first component is strictly increasing.
  have h_strict_mono : ∀ r : Fin (p + q), (ν.1 (Fin.castSucc r)).fst.val + 1 ≥ (ν.1 (Fin.succ r)).fst.val := by
    intro r
    have := coordSum_eq ν (Fin.castSucc r)
    have := coordSum_eq ν (Fin.succ r)
    simp at *;
    linarith [ show ( ν.1 ( Fin.castSucc r ) |>.2 : ℕ ) ≤ ( ν.1 ( Fin.succ r ) |>.2 : ℕ ) from by exact ( ν.1.monotone ( Nat.le_succ _ ) ) |>.2 ];
  exact h_strict_mono ⟨ i, by linarith ⟩

/-- The underlying piecewise map for `insertLeftStep`: before the insertion point,
embed the original vertex via `succAbove j`; at the insertion point, place `(j, t-j)`;
after the insertion point, embed the shifted-back vertex via `succAbove j`. -/
noncomputable def insertLeftStepFun {p q : ℕ} (ν : Shuffle p q) (j : Fin (p + 2)) :
    Fin ((p + 1) + q + 1) → Index (p + 1) × Index q :=
  let t := (insertLeftIndex ν j).val
  have ht_lt : t < p + q + 2 := (insertLeftIndex ν j).isLt
  have ht_le : t ≤ j.val + q := insertLeftIndex_le ν j
  fun r =>
    -- Before insertion: embed original vertex via succAbove j (preserves value since fst < j)
    if h : r.val < t then
      (j.succAbove (ν.1 ⟨r, by omega⟩).1, (ν.1 ⟨r, by omega⟩).2)
    -- At insertion point: new left step with fst = j, snd = t - j
    else if h2 : r.val = t then
      (j, ⟨r.val - j.val, by omega⟩)
    -- After insertion: embed shifted-back vertex via succAbove j (adds 1 since fst ≥ j)
    else
      (j.succAbove (ν.1 ⟨r - 1, by omega⟩).1, (ν.1 ⟨r - 1, by omega⟩).2)

/-- Coordinate sum of the piecewise map equals the position index. -/
private lemma insertLeftStepFun_coordSum {p q : ℕ} (ν : Shuffle p q) (j : Fin (p + 2))
    (r : Fin ((p + 1) + q + 1)) :
    (insertLeftStepFun ν j r).1.val + (insertLeftStepFun ν j r).2.val = r.val := by
  simp only [insertLeftStepFun]
  split_ifs with h1 h2
  · -- r < t: succAbove preserves value since fst < j, then use coordSum_eq
    have hfst := (insertLeftIndex_iff ν j ⟨r.val, by omega⟩).mpr h1
    simp only [Fin.succAbove]
    split
    · simp only [fin_val_castSucc]
      have := coordSum_eq ν ⟨r.val, by omega⟩
      simp at this; omega
    · rename_i hn
      exfalso
      simp only [not_lt, Fin.le_def, fin_val_castSucc] at hn
      omega
  · -- r = t: j + (t - j) = t = r
    have hge := insertLeftIndex_ge ν j
    simp; omega
  · -- r > t: succAbove adds 1 since fst ≥ j, then use coordSum_eq
    have hfst : ¬ (ν.1 ⟨r.val - 1, by omega⟩).1.val < j.val := by
      rw [insertLeftIndex_iff]; simp; omega
    simp only [Fin.succAbove]
    split
    · rename_i hlt; exfalso; simp only [Fin.lt_def, fin_val_castSucc] at hlt; omega
    · simp only [Fin.val_succ]
      have := coordSum_eq ν ⟨r.val - 1, by omega⟩
      simp at this; omega

/-- Insert a left step at face index `j`, turning a `(p, q)`-shuffle into a
`(p+1, q)`-shuffle.  The original path from `(0,0)` to `(p, q)` is embedded
into a path from `(0,0)` to `(p+1, q)` by applying `Fin.succAbove j` to the
first coordinate and inserting a new left step where the first coordinate
crosses `j`. -/
noncomputable def insertLeftStep {p q : ℕ} (ν : Shuffle p q) (j : Fin (p + 2)) :
    Shuffle (p + 1) q :=
  ⟨⟨insertLeftStepFun ν j, by
    -- Monotonicity: use coordSum to derive both coordinates weakly increasing
    intro a b hab
    simp only [Prod.le_def]
    constructor
    · -- First coordinate monotone
      suffices hsuc : ∀ r : Fin (p + 1 + q),
          (insertLeftStepFun ν j r.castSucc).1 ≤ (insertLeftStepFun ν j r.succ).1 by
        exact (Fin.monotone_iff_le_succ (f := fun r => (insertLeftStepFun ν j r).1) ).2 hsuc hab
      intro r
      simp only [insertLeftStepFun]
      split_ifs with h1 h2 h3 h4 h5
      · exact (Fin.succAbove_le_succAbove_iff.mpr (ν.1.monotone (Fin.castSucc_le_succ r)).1) -- cs < t, succ < t
      · -- cs < t, succ = t: succAbove(fst) ≤ j since fst < j
        have hfst := (insertLeftIndex_iff ν j ⟨r.val, by omega⟩).mpr h1
        simp only [Fin.succAbove]
        split
        · simp [Fin.le_def, fin_val_castSucc]; omega
        · rename_i hn; exfalso; simp only [not_lt, Fin.le_def, fin_val_castSucc] at hn; omega
      · have := Fin.val_succ r; have := fin_val_castSucc r; omega -- cs < t, succ > t (impossible)
      · have := Fin.val_succ r; have := fin_val_castSucc r; omega -- cs = t, succ < t (impossible)
      · have := Fin.val_succ r; have := fin_val_castSucc r; omega -- cs = t, succ = t (impossible)
      · -- cs = t, succ > t: j ≤ succAbove(fst) since fst ≥ j
        have hfst : ¬ (ν.1 ⟨r.val, by omega⟩).1.val < j.val := by
          rw [insertLeftIndex_iff]; simp [fin_val_castSucc] at h4; simp; omega
        push_neg at hfst
        have heq : (⟨r.succ.val - 1, by omega⟩ : Fin (p + q + 1)) = ⟨r.val, by omega⟩ := by
          ext; simp [Fin.val_succ]
        rw [heq]
        simp only [Fin.succAbove]
        split
        · rename_i hlt; exfalso; simp only [Fin.lt_def, fin_val_castSucc] at hlt; omega
        · simp [Fin.le_def, Fin.val_succ]; omega
      · have := Fin.val_succ r; have := fin_val_castSucc r; omega -- cs > t, succ < t (impossible)
      · have := Fin.val_succ r; have := fin_val_castSucc r; omega -- cs > t, succ = t (impossible)
      · exact (Fin.succAbove_le_succAbove_iff.mpr -- cs > t, succ > t
          (ν.1.monotone (by simp [Fin.le_def, fin_val_castSucc, Fin.val_succ])).1)
    · -- Second coordinate monotone
      suffices hsuc : ∀ r : Fin (p + 1 + q),
          (insertLeftStepFun ν j r.castSucc).2 ≤ (insertLeftStepFun ν j r.succ).2 by
        exact (Fin.monotone_iff_le_succ (f := fun r => (insertLeftStepFun ν j r).2)).2 hsuc hab
      intro r
      simp only [insertLeftStepFun]
      split_ifs with h1 h2 h3 h4 h5
      · exact (ν.1.monotone (Fin.castSucc_le_succ r)).2 -- castSucc < t, succ < t
      · -- castSucc < t, succ = t: snd(ν r) ≤ r+1-j
        -- Reduce to j ≤ ν(r).1 + 1 using coordSum_eq
        simp only [fin_val_castSucc, Fin.val_succ]
        have hge := insertLeftIndex_ge ν j
        have hsv := Fin.val_succ r
        have hsum := coordSum_eq ν ⟨r.val, by omega⟩
        suffices h : j.val ≤ (ν.1 ⟨r.val, by omega⟩).1.val + 1 by
          simp only [Fin.le_def] at hsum ⊢; omega
        by_cases hr : r.val + 1 = p + 1 + q
        · -- r is the last vertex: ν(r) = (p, q), so fst = p and j ≤ p + 1
          have hlast : ν.1 ⟨r.val, by omega⟩ = (Fin.last p, Fin.last q) := by
            have : (⟨r.val, by omega⟩ : Fin (p + q + 1)) = Fin.last (p + q) :=
              Fin.ext (by simp [Fin.last]; omega)
            rw [this]; exact Shuffle.apply_last ν
          have hfst : (ν.1 ⟨r.val, by omega⟩).1.val = p := by
            rw [hlast]; simp [Fin.last]
          rw [hfst]; omega
        · -- r is not the last vertex: ν(r+1).1 ≥ j (by insertLeftIndex_iff)
          -- and ν(r+1).1 ≤ ν(r).1 + 1 (by shuffle step), so j ≤ ν(r).1 + 1
          let r' : Fin (p + q + 1) := ⟨r.val + 1, by omega⟩
          have hge_j : j.val ≤ (ν.1 r').1.val := by
            by_contra hlt
            push_neg at hlt
            have h_iff := (insertLeftIndex_iff ν j r').mp hlt
            have ht : (insertLeftIndex ν j).val = r.val + 1 := by
              simp [Fin.val_succ] at hsv; omega
            change r.val + 1 < _ at h_iff
            omega
          have hstep := shuffle_step ν ⟨r.val, by omega⟩
          have hcs : (⟨r.val, by omega⟩ : Fin (p + q)).castSucc = (⟨r.val, by omega⟩ : Fin (p + q + 1)) :=
            Fin.ext (by simp [Fin.castSucc])
          have hsu : (⟨r.val, by omega⟩ : Fin (p + q)).succ = r' :=
            Fin.ext (by simp [Fin.succ, r'])
          rw [hcs, hsu] at hstep
          rcases hstep with ⟨h1, _⟩ | ⟨h1, _⟩ <;> omega
      · have := Fin.val_succ r; have := fin_val_castSucc r; omega -- cs < t, succ > t (impossible)
      · have := Fin.val_succ r; have := fin_val_castSucc r; omega -- cs = t, succ < t (impossible)
      · have := Fin.val_succ r; have := fin_val_castSucc r; omega -- cs = t, succ = t (impossible)
      ·  -- castSucc = t, succ > t
        simp
        simp only [Fin.le_def]
        have hcs := coordSum_eq ν ⟨r.val, by omega⟩
        suffices h : (ν.1 ⟨r.val, by omega⟩).1.val ≤ j.val by
          have : (⟨r.val, by omega⟩ : Fin (p + q + 1)).val = r.val := rfl
          omega
        by_cases hr : r.val = 0
        · have : (⟨r.val, by omega⟩ : Fin (p + q + 1)) = 0 := Fin.ext (by simp [hr])
          rw [this, Shuffle.apply_zero]; simp
        · let r' : Fin (p + q + 1) := ⟨r.val - 1, by omega⟩
          have hr'lt : r'.val < (insertLeftIndex ν j).val := by
            simp [r', fin_val_castSucc] at h4 ⊢; omega
          have hfst_lt : (ν.1 r').1.val < j.val :=
            (insertLeftIndex_iff ν j r').mpr hr'lt
          have hstep := shuffle_step ν ⟨r.val - 1, by omega⟩
          have hcs2 : (⟨r.val - 1, by omega⟩ : Fin (p + q)).castSucc = r' :=
            Fin.ext (by simp [Fin.castSucc, r'])
          have hsu2 : (⟨r.val - 1, by omega⟩ : Fin (p + q)).succ = ⟨r.val, by omega⟩ :=
            Fin.ext (by simp [Fin.succ]; omega)
          rw [hcs2, hsu2] at hstep
          rcases hstep with ⟨h1, _⟩ | ⟨h1, _⟩ <;> omega
      · have := Fin.val_succ r; have := fin_val_castSucc r; omega -- cs > t, succ < t (impossible)
      · have := Fin.val_succ r; have := fin_val_castSucc r; omega -- cs > t, succ = t (impossible)
      · exact (ν.1.monotone (by simp [Fin.le_def, fin_val_castSucc, Fin.val_succ])).2 -- cs > t, succ > t
      ⟩, by
    -- Injectivity: f(a) = f(b) → coordSum(f(a)) = coordSum(f(b)) → a = b
    intro a b hab
    have ha := insertLeftStepFun_coordSum ν j a
    have hb := insertLeftStepFun_coordSum ν j b
    have heq : insertLeftStepFun ν j a = insertLeftStepFun ν j b := hab
    have : (insertLeftStepFun ν j a).1.val + (insertLeftStepFun ν j a).2.val =
        (insertLeftStepFun ν j b).1.val + (insertLeftStepFun ν j b).2.val := by rw [heq]
    exact Fin.ext (by omega)⟩

/-- The underlying piecewise map for `insertRightStep`: before the insertion point,
embed the original vertex via `succAbove k` on the second coordinate; at the
insertion point, place `(t-k, k)`; after the insertion point, embed the
shifted-back vertex via `succAbove k`. -/
noncomputable def insertRightStepFun {p q : ℕ} (ν : Shuffle p q) (k : Fin (q + 2)) :
    Fin (p + (q + 1) + 1) → Index p × Index (q + 1) :=
  let t := (insertRightIndex ν k).val
  fun r =>
    if h : r.val < t then
      ((ν.1 ⟨r, by omega⟩).1, k.succAbove (ν.1 ⟨r, by omega⟩).2)
    else if h2 : r.val = t then
      (⟨r.val - k.val, by
        have := insertRightIndex_le ν k; omega⟩, k)
    else
      ((ν.1 ⟨r - 1, by omega⟩).1, k.succAbove (ν.1 ⟨r - 1, by omega⟩).2)

/-- Coordinate sum of the right-insertion piecewise map equals the position index. -/
private lemma insertRightStepFun_coordSum {p q : ℕ} (ν : Shuffle p q) (k : Fin (q + 2))
    (r : Fin (p + (q + 1) + 1)) :
    (insertRightStepFun ν k r).1.val + (insertRightStepFun ν k r).2.val = r.val := by
  simp only [insertRightStepFun]
  split_ifs with h1 h2
  · have hsnd := (insertRightIndex_iff ν k ⟨r.val, by omega⟩).mpr h1
    simp only [Fin.succAbove]
    split
    · simp only [fin_val_castSucc]
      have := coordSum_eq ν ⟨r.val, by omega⟩
      simp at this; omega
    · rename_i hn
      exfalso
      simp only [not_lt, Fin.le_def, fin_val_castSucc] at hn
      omega
  · have hge := insertRightIndex_ge ν k
    simp; omega
  · have hsnd : ¬ (ν.1 ⟨r.val - 1, by omega⟩).2.val < k.val := by
      rw [insertRightIndex_iff]; simp; omega
    simp only [Fin.succAbove]
    split
    · rename_i hlt; exfalso; simp only [Fin.lt_def, fin_val_castSucc] at hlt; omega
    · simp only [Fin.val_succ]
      have := coordSum_eq ν ⟨r.val - 1, by omega⟩
      simp at this; omega

/-- Insert a right step at face index `k`, turning a `(p, q)`-shuffle into a
`(p, q+1)`-shuffle.  Applies `Fin.succAbove k` to the second coordinate and
inserts a new right step where the second coordinate crosses `k`. -/
noncomputable def insertRightStep {p q : ℕ} (ν : Shuffle p q) (k : Fin (q + 2)) :
    Shuffle p (q + 1) :=
  ⟨⟨insertRightStepFun ν k, by
    intro a b hab
    simp only [Prod.le_def]
    constructor
    · -- First coordinate monotone
      suffices hsuc : ∀ r : Fin (p + (q + 1)),
          (insertRightStepFun ν k r.castSucc).1 ≤ (insertRightStepFun ν k r.succ).1 by
        exact (Fin.monotone_iff_le_succ (f := fun r => (insertRightStepFun ν k r).1)).2 hsuc hab
      intro r
      simp only [insertRightStepFun]
      split_ifs with h1 h2 h3 h4 h5
      · exact (ν.1.monotone (Fin.castSucc_le_succ r)).1 -- cs < t, succ < t
      · -- cs < t, succ = t: fst(ν r) ≤ r+1-k
        simp only [fin_val_castSucc, Fin.val_succ]
        have hge := insertRightIndex_ge ν k
        have hsv := Fin.val_succ r
        have hsum := coordSum_eq ν ⟨r.val, by omega⟩
        suffices h : k.val ≤ (ν.1 ⟨r.val, by omega⟩).2.val + 1 by
          simp only [Fin.le_def] at hsum ⊢; omega
        by_cases hr : r.val + 1 = p + q + 1
        · have hlast : ν.1 ⟨r.val, by omega⟩ = (Fin.last p, Fin.last q) := by
            have : (⟨r.val, by omega⟩ : Fin (p + q + 1)) = Fin.last (p + q) :=
              Fin.ext (by simp [Fin.last]; omega)
            rw [this]; exact Shuffle.apply_last ν
          have hsnd : (ν.1 ⟨r.val, by omega⟩).2.val = q := by
            rw [hlast]; simp [Fin.last]
          rw [hsnd]; omega
        · let r' : Fin (p + q + 1) := ⟨r.val + 1, by omega⟩
          have hge_k : k.val ≤ (ν.1 r').2.val := by
            by_contra hlt
            push_neg at hlt
            have h_iff := (insertRightIndex_iff ν k r').mp hlt
            have ht : (insertRightIndex ν k).val = r.val + 1 := by
              simp [Fin.val_succ] at hsv; omega
            change r.val + 1 < _ at h_iff
            omega
          have hstep := shuffle_step ν ⟨r.val, by omega⟩
          have hcs : (⟨r.val, by omega⟩ : Fin (p + q)).castSucc = (⟨r.val, by omega⟩ : Fin (p + q + 1)) :=
            Fin.ext (by simp [Fin.castSucc])
          have hsu : (⟨r.val, by omega⟩ : Fin (p + q)).succ = r' :=
            Fin.ext (by simp [Fin.succ, r'])
          rw [hcs, hsu] at hstep
          rcases hstep with ⟨_, h1⟩ | ⟨_, h1⟩ <;> omega
      · have := Fin.val_succ r; have := fin_val_castSucc r; omega
      · have := Fin.val_succ r; have := fin_val_castSucc r; omega
      · have := Fin.val_succ r; have := fin_val_castSucc r; omega
      · -- castSucc = t, succ > t
        simp
        have hcs := coordSum_eq ν ⟨r.val, by omega⟩
        have hcsv : (⟨r.val, by omega⟩ : Fin (p + q + 1)).val = r.val := rfl
        suffices h : (ν.1 ⟨r.val, by omega⟩).2.val ≤ k.val by
          have hre : (ν.1 r).1.val = (ν.1 ⟨r.val, by omega⟩).1.val := by congr 3
          simp only [Fin.le_def] at hcs ⊢; omega
        by_cases hr : r.val = 0
        · have : (⟨r.val, by omega⟩ : Fin (p + q + 1)) = 0 := Fin.ext (by simp [hr])
          rw [this, Shuffle.apply_zero]; simp
        · let r' : Fin (p + q + 1) := ⟨r.val - 1, by omega⟩
          have hr'lt : r'.val < (insertRightIndex ν k).val := by
            simp [r', fin_val_castSucc] at h4 ⊢; omega
          have hsnd_lt : (ν.1 r').2.val < k.val :=
            (insertRightIndex_iff ν k r').mpr hr'lt
          have hstep := shuffle_step ν ⟨r.val - 1, by omega⟩
          have hcs2 : (⟨r.val - 1, by omega⟩ : Fin (p + q)).castSucc = r' :=
            Fin.ext (by simp [Fin.castSucc, r'])
          have hsu2 : (⟨r.val - 1, by omega⟩ : Fin (p + q)).succ = ⟨r.val, by omega⟩ :=
            Fin.ext (by simp [Fin.succ]; omega)
          rw [hcs2, hsu2] at hstep
          rcases hstep with ⟨_, h1⟩ | ⟨_, h1⟩ <;> omega
      · have := Fin.val_succ r; have := fin_val_castSucc r; omega
      · have := Fin.val_succ r; have := fin_val_castSucc r; omega
      · exact (ν.1.monotone (by simp [Fin.le_def, fin_val_castSucc, Fin.val_succ])).1
    · -- Second coordinate monotone
      suffices hsuc : ∀ r : Fin (p + (q + 1)),
          (insertRightStepFun ν k r.castSucc).2 ≤ (insertRightStepFun ν k r.succ).2 by
        exact (Fin.monotone_iff_le_succ (f := fun r => (insertRightStepFun ν k r).2)).2 hsuc hab
      intro r
      simp only [insertRightStepFun]
      split_ifs with h1 h2 h3 h4 h5
      · exact (Fin.succAbove_le_succAbove_iff.mpr (ν.1.monotone (Fin.castSucc_le_succ r)).2) -- cs < t, succ < t
      · -- cs < t, succ = t: succAbove(snd) ≤ k since snd < k
        have hrcs : (⟨r.castSucc.val, by simp [fin_val_castSucc]; omega⟩ : Fin (p + q + 1)) =
            ⟨r.val, by omega⟩ := Fin.ext (by simp [fin_val_castSucc])
        have hsnd := (insertRightIndex_iff ν k ⟨r.val, by omega⟩).mpr h1
        simp only [Fin.succAbove]; split
        · simp only [Fin.le_def, fin_val_castSucc]
          have : (ν.1 ⟨r.castSucc.val, by simp [fin_val_castSucc]; omega⟩).2.val =
              (ν.1 ⟨r.val, by omega⟩).2.val := by rw [hrcs]
          omega
        · rename_i hn; exfalso
          simp only [not_lt, Fin.le_def, fin_val_castSucc] at hn
          have : (ν.1 ⟨r.castSucc.val, by simp [fin_val_castSucc]; omega⟩).2.val =
              (ν.1 ⟨r.val, by omega⟩).2.val := by rw [hrcs]
          omega
      · have := Fin.val_succ r; have := fin_val_castSucc r; omega
      · have := Fin.val_succ r; have := fin_val_castSucc r; omega
      · have := Fin.val_succ r; have := fin_val_castSucc r; omega
      · -- cs = t, succ > t: k ≤ succAbove(snd) since snd ≥ k
        have hsnd : ¬ (ν.1 ⟨r.val, by omega⟩).2.val < k.val := by
          rw [insertRightIndex_iff]; simp [fin_val_castSucc] at h4; simp; omega
        push_neg at hsnd
        have heq : (⟨r.succ.val - 1, by omega⟩ : Fin (p + q + 1)) = ⟨r.val, by omega⟩ := by
          ext; simp [Fin.val_succ]
        rw [heq]
        simp only [Fin.succAbove]
        split
        · rename_i hlt; exfalso; simp only [Fin.lt_def, fin_val_castSucc] at hlt; omega
        · simp only [Fin.le_def, Fin.val_succ]
          simp only [fin_val_castSucc] at h4
          omega
      · have := Fin.val_succ r; have := fin_val_castSucc r; omega
      · have := Fin.val_succ r; have := fin_val_castSucc r; omega
      · exact (Fin.succAbove_le_succAbove_iff.mpr
          (ν.1.monotone (by simp [Fin.le_def, fin_val_castSucc, Fin.val_succ])).2)
    ⟩, by
    -- Injectivity: f(a) = f(b) → coordSum(f(a)) = coordSum(f(b)) → a = b
    intro a b hab
    have ha := insertRightStepFun_coordSum ν k a
    have hb := insertRightStepFun_coordSum ν k b
    have heq : insertRightStepFun ν k a = insertRightStepFun ν k b := hab
    have : (insertRightStepFun ν k a).1.val + (insertRightStepFun ν k a).2.val =
        (insertRightStepFun ν k b).1.val + (insertRightStepFun ν k b).2.val := by rw [heq]
    exact Fin.ext (by omega)⟩

/-- Inserting a left step and removing the inserted vertex recovers the original
shuffle with `Fin.succAbove j` applied to the first coordinate.
(Purely combinatorial: no `SimplexCategory` or topology needed.) -/
lemma insertLeftStep_face {p q : ℕ} (ν : Shuffle p q) (j : Fin (p + 2)) :
    ∀ (k : Index (p + q)),
      (insertLeftStep ν j).1 (Fin.succAbove
        (⟨(insertLeftIndex ν j).val, by omega⟩ : Fin ((p + 1) + q + 1))
        (k.cast (by omega))) =
      (j.succAbove (ν.1 k).1, (ν.1 k).2) := by
  unfold HomologyLean.SingularHomology.Shuffle.insertLeftStep;
  intro k
  unfold HomologyLean.SingularHomology.Shuffle.insertLeftStepFun
  simp [Fin.succAbove] at *;
  split_ifs <;> simp_all +decide [ Fin.castSucc, Fin.succ ];
  · exact absurd ‹_› ( ne_of_lt ‹_› );
  · exact absurd ‹_› ( not_le_of_gt ‹_› );
  · exact False.elim <| ‹¬_› <| Nat.lt_of_succ_lt ‹_›;
  · split_ifs <;> simp_all +decide [ Fin.ext_iff, Fin.val_add ];
    · have := insertLeftIndex_ge ν j; have := insertLeftIndex_le ν j; simp_all +decide [ Fin.le_iff_val_le_val ] ; omega;
    · have := insertLeftIndex_iff ν j k; simp_all +decide [ Fin.le_def ] ;
      grind

/-- Inserting a right step and removing the inserted vertex recovers the original
shuffle with `Fin.succAbove k` applied to the second coordinate. -/
lemma insertRightStep_face {p q : ℕ} (ν : Shuffle p q) (k : Fin (q + 2)) :
    ∀ (i : Index (p + q)),
      (insertRightStep ν k).1 (Fin.succAbove
        (⟨(insertRightIndex ν k).val, by omega⟩ : Fin (p + (q + 1) + 1))
        (i.cast (by omega))) =
      ((ν.1 i).1, k.succAbove (ν.1 i).2) := by
  intro i
  generalize_proofs at *;
  unfold HomologyLean.SingularHomology.Shuffle.insertRightStep; simp +decide [ Fin.succAbove ] ;
  unfold HomologyLean.SingularHomology.Shuffle.insertRightStepFun; split_ifs <;> simp_all +decide [ Fin.ext_iff, Fin.val_add ] ;
  all_goals split_ifs <;> simp_all +decide [ Fin.succAbove ] ;
  any_goals split_ifs <;> simp_all +decide [ Fin.castSucc, Fin.succ ] ; omega;
  any_goals linarith [ show ( i : ℕ ) < ν.insertRightIndex k from by assumption ] ;
  · exact False.elim <| ‹¬Fin.castSucc i < ν.insertRightIndex k› <| Nat.lt_of_succ_lt ‹_›;
  · have := Fin.le_iff_val_le_val.mp ‹_›; simp_all +decide [ Fin.ext_iff ] ; omega;
  · exact absurd ‹_› ( by linarith [ show ( i : ℕ ) + 1 > ( ν.insertRightIndex k : ℕ ) from by linarith [ show ( i : ℕ ) ≥ ( ν.insertRightIndex k : ℕ ) from by assumption ] ] ) ;

/-- The insert-left map `(j, ν) ↦ (insertLeftStep ν j, insertLeftIndex ν j)` is
injective: distinct `(j, ν)` pairs produce distinct `(μ, vertex)` pairs. -/
lemma insertLeftStep_injective {p q : ℕ}
    (j₁ j₂ : Fin (p + 2)) (ν₁ ν₂ : Shuffle p q)
    (hμ : insertLeftStep ν₁ j₁ = insertLeftStep ν₂ j₂)
    (hr : insertLeftIndex ν₁ j₁ = insertLeftIndex ν₂ j₂) :
    j₁ = j₂ ∧ ν₁ = ν₂ := by
  have h_eq : ν₁.insertLeftStep j₁ = ν₂.insertLeftStep j₂ → j₁ = j₂ := by
    intro h_eq
    have h_eq_fun : ∀ r : Fin (p + 1 + q + 1), (insertLeftStepFun ν₁ j₁ r).1 = (insertLeftStepFun ν₂ j₂ r).1 := by
      intro r
      have := congr_arg (fun f => f.1 r) h_eq
      generalize_proofs at *; (
      exact congr_arg Prod.fst this
      skip)
    generalize_proofs at *; (
    have := h_eq_fun ⟨(insertLeftIndex ν₁ j₁).val, by
      exact Nat.lt_succ_of_le ( by linarith [ Fin.is_lt ( ν₁.insertLeftIndex j₁ ) ] ) ;⟩
    generalize_proofs at *; (
    unfold insertLeftStepFun at this; aesop;))
  generalize_proofs at *; exact ⟨h_eq hμ, by
    have := insertLeftStep_face ν₁ j₁; have := insertLeftStep_face ν₂ j₂; aesop;⟩;

/-- The insert-right map is injective. -/
lemma insertRightStep_injective {p q : ℕ}
    (k₁ k₂ : Fin (q + 2)) (ν₁ ν₂ : Shuffle p q)
    (hμ : insertRightStep ν₁ k₁ = insertRightStep ν₂ k₂)
    (hr : insertRightIndex ν₁ k₁ = insertRightIndex ν₂ k₂) :
    k₁ = k₂ ∧ ν₁ = ν₂ := by
  -- By comparing the coordinates of the last elements, we can conclude that k₁ = k₂.
  have hk : k₁ = k₂ := by
    unfold Shuffle.insertRightStep at hμ;
    simp_all +decide [ Fin.ext_iff, Shuffle.insertRightStepFun ];
    replace hμ := congr_fun hμ ( ν₂.insertRightIndex k₂ ) ; aesop;
  have := insertRightStep_face ν₁ k₁; have := insertRightStep_face ν₂ k₁; aesop;

/-! ##### Helper lemmas for `sign_insertLeftStep`

The proof reduces to an inversion-count identity: inserting a left step at
position `j` adds exactly `t - j` to the inversion count, where
`t = insertLeftIndex ν j`. We split the `invCount` sum at `t` using
`Fin.sum_univ_succAbove`, match the non-inserted terms against `invCount ν`,
and compute the contribution of the inserted step directly. -/

/-- The inserted step is a left step: the first coordinate increases from `j`
to `succAbove j (ν.1 t).1 > j` at the insertion vertex. -/
private lemma insertLeftStep_isLeftStep_at {p q : ℕ}
    (ν : Shuffle p q) (j : Fin (p + 2))
    (ht : (insertLeftIndex ν j).val < p + 1 + q) :
    isLeftStep (insertLeftStep ν j) ⟨(insertLeftIndex ν j).val, ht⟩ := by
  -- Unfold to: j < j.succAbove (ν.1 ⟨t, ...⟩).fst
  unfold isLeftStep; simp +decide [insertLeftStep, insertLeftStepFun]
  -- Vertex t has fst ≥ j (it's the first vertex not in the filter {fst < j})
  have hfst : ¬ (ν.1 ⟨(insertLeftIndex ν j).val, by omega⟩).1.val < j.val := by
    intro h
    have := (insertLeftIndex_iff ν j ⟨(insertLeftIndex ν j).val, by omega⟩).mp h
    simp at this
  -- succAbove j fst = fst.succ when fst ≥ j, so j < fst + 1
  simp only [Fin.succAbove]
  split
  · exfalso; simp [Fin.lt_def] at *; omega
  · simp [Fin.lt_def, Fin.val_succ] at *; omega

/-- The second coordinate at the insertion point equals `t - j`. -/
private lemma insertLeftStep_snd_at {p q : ℕ}
    (ν : Shuffle p q) (j : Fin (p + 2)) :
    ((insertLeftStep ν j).1 ⟨(insertLeftIndex ν j).val, by omega⟩).2.val =
    (insertLeftIndex ν j).val - j.val := by
  simp +decide [insertLeftStep, insertLeftStepFun]

/-- The `invCount` term at the insertion point contributes `t - j`:
`if isLeftStep μ t then μ(t).snd else 0 = t - j`. -/
private lemma insertLeftStep_invCount_term_at {p q : ℕ}
    (ν : Shuffle p q) (j : Fin (p + 2))
    (ht : (insertLeftIndex ν j).val < p + 1 + q) :
    (if ((insertLeftStep ν j).1 (Fin.castSucc ⟨(insertLeftIndex ν j).val, ht⟩)).1 <
        ((insertLeftStep ν j).1 (Fin.succ ⟨(insertLeftIndex ν j).val, ht⟩)).1
     then ((insertLeftStep ν j).1 (Fin.castSucc ⟨(insertLeftIndex ν j).val, ht⟩)).2.val
     else 0) =
    (insertLeftIndex ν j).val - j.val := by
  split_ifs with h
  · exact insertLeftStep_snd_at ν j
  · exact absurd (insertLeftStep_isLeftStep_at ν j ht) h

/-- Each non-inserted step of `insertLeftStep ν j` has the same `invCount`
contribution as the corresponding step of `ν`. For step `i` of `ν`, the
matching step in the new shuffle is `i` if `i < t`, or `i + 1` if `i ≥ t`
(where `t = insertLeftIndex ν j`).

**Proof sketch** (three cases by position of `i` relative to `t`):
- **i+1 < t** (both endpoints in 'before' region): `insertLeftStepFun` applies
  `succAbove j` to both fst coords. `Fin.succAbove_lt_succAbove_iff` shows
  the fst comparison is preserved. The snd coord is unchanged.
- **i < t ≤ i+1** (castSucc in 'before', succ at insertion point): The new
  fst comparison is `succAbove(j, ν(i).fst) < j`. Since `ν(i).fst < j`
  (by `insertLeftIndex_iff`), `succAbove = castSucc`, so the condition
  reduces to `ν(i).fst < j`. The original condition `ν(i).fst < ν(i+1).fst`
  is equivalent since `ν(i).fst < j ≤ ν(i+1).fst`. Snd is unchanged.
- **i ≥ t** (both endpoints in 'after' region): `insertLeftStepFun` shifts
  by -1, mapping back to indices `i` and `i+1` of ν. Same argument via
  `succAbove` preserving ordering. Snd unchanged.

The main difficulty is Fin proof-irrelevance: `split_ifs` creates many
branches where `⟨i.val, proof₁⟩` and `i.castSucc` need to be identified.
Use `congr 3; ext; simp [fin_val_castSucc]` to close the `.2.val` goals,
and `Fin.succAbove_lt_succAbove_iff` + `convert` for the condition goals.
`Fin.lt_def` loops with `simp` — avoid it or use `- Fin.lt_def`. -/
private lemma insertLeftStep_invCount_term_skip {p q : ℕ}
    (ν : Shuffle p q) (j : Fin (p + 2))
    (i : Fin (p + q)) :
    let t := (insertLeftIndex ν j).val
    let r : Fin (p + 1 + q) :=
      if i.val < t then ⟨i.val, by omega⟩ else ⟨i.val + 1, by omega⟩
    (if ((insertLeftStep ν j).1 r.castSucc).1 <
        ((insertLeftStep ν j).1 r.succ).1
     then ((insertLeftStep ν j).1 r.castSucc).2.val
     else 0) =
    (if (ν.1 (Fin.castSucc i)).1 < (ν.1 (Fin.succ i)).1
     then (ν.1 (Fin.castSucc i)).2.val
     else 0) := by
  set t := (insertLeftIndex ν j).val
  by_cases h1 : i.val + 1 < t
  · -- Case 1: i+1 < t (both endpoints in 'before' region)
    simp only [show i.val < t from by omega]
    simp only [if_true, insertLeftStep, insertLeftStepFun, OrderHom.coe_mk]
    have hcs_val : (⟨↑i, (by omega : ↑i < p + 1 + q)⟩ : Fin (p + 1 + q)).castSucc.val = i.val := by
      simp [Fin.val_mk]
    have hsu_val : (⟨↑i, (by omega : ↑i < p + 1 + q)⟩ : Fin (p + 1 + q)).succ.val = i.val + 1 := by
      simp [Fin.val_mk]
    split_ifs <;> try omega
    all_goals simp only [] at *
    -- Goal 1: .2 values match (Fin proof-irrelevance)
    · congr 2;
    -- Goal 2: contradiction (succAbove preserves ordering)
    · exfalso; rename_i h_sa h_not
      exact h_not (Fin.succAbove_lt_succAbove_iff.mp (by convert h_sa using 2))
    -- Goal 3: contradiction (same)
    · exfalso; rename_i h_sa h_orig
      exact h_sa (Fin.succAbove_lt_succAbove_iff.mpr (by convert h_orig using 2))
  · by_cases h2 : i.val < t
    · -- Case 2: i < t ≤ i+1 (castSucc before, succ at insertion point)
      simp only [h2]
      simp only [if_true, insertLeftStep, insertLeftStepFun, OrderHom.coe_mk]
      have hcs_val : (⟨↑i, (by omega : ↑i < p + 1 + q)⟩ : Fin (p + 1 + q)).castSucc.val = i.val := by
        simp [Fin.val_mk]
      have hsu_val : (⟨↑i, (by omega : ↑i < p + 1 + q)⟩ : Fin (p + 1 + q)).succ.val = i.val + 1 := by
        simp [Fin.val_succ, Fin.val_mk]
      split_ifs <;> try omega
      all_goals simp only [] at *
      · congr 2;
      · exfalso; rename_i h_sa h_not
        simp only [hcs_val, hsu_val] at *
        apply h_not
        -- (↑ν i.castSucc).1.val < j.val since i < t, and (↑ν i.succ).1.val ≥ j.val since ¬(i+1 < t)
        have heq1 : (⟨i.val, (by omega : i.val < p + q + 1)⟩ : Fin (p + q + 1)) = i.castSucc := by
          ext; simp
        have heq2 : (⟨i.val + 1, (by omega : i.val + 1 < p + q + 1)⟩ : Fin (p + q + 1)) = i.succ := by
          ext; simp [Fin.val_succ]
        have h_cs_lt := (insertLeftIndex_iff ν j ⟨i.val, by omega⟩).mpr (by simp; omega)
        have h_su_ge := mt (insertLeftIndex_iff ν j ⟨i.val + 1, by omega⟩).mp (by simp; omega)
        rw [heq1] at h_cs_lt; rw [heq2] at h_su_ge
        push_neg at h_su_ge
        exact Fin.lt_def.mpr (by omega)
      · exfalso; rename_i h_sa h_orig
        simp only [hcs_val, hsu_val] at *
        apply h_sa
        rw [Fin.succAbove_lt_iff_castSucc_lt]
        have heq1 : (⟨i.val, (by omega : i.val < p + q + 1)⟩ : Fin (p + q + 1)) = i.castSucc := by
          ext; simp
        have h_cs_lt := (insertLeftIndex_iff ν j ⟨i.val, by omega⟩).mpr (by simp; omega)
        rw [heq1] at h_cs_lt
        exact Fin.mk_lt_mk.mpr h_cs_lt
    · -- Case 3: i ≥ t (both endpoints in 'after' region)
      simp only [show ¬(i.val < t) from h2]
      simp only [if_false, insertLeftStep, insertLeftStepFun, OrderHom.coe_mk]
      have hcs_val : (⟨↑i + 1, (by omega : ↑i + 1 < p + 1 + q)⟩ : Fin (p + 1 + q)).castSucc.val = i.val + 1 := by
        simp [Fin.val_mk]
      have hsu_val : (⟨↑i + 1, (by omega : ↑i + 1 < p + 1 + q)⟩ : Fin (p + 1 + q)).succ.val = i.val + 2 := by
        simp [Fin.val_succ, Fin.val_mk]
      split_ifs <;> try omega
      all_goals simp only [] at *
      · congr 2;
      · exfalso; rename_i h_sa h_not
        exact h_not (Fin.succAbove_lt_succAbove_iff.mp (by convert h_sa using 2))
      · exfalso; rename_i h_sa h_orig
        exact h_sa (Fin.succAbove_lt_succAbove_iff.mpr (by convert h_orig using 2))

/-- **Key inversion-count identity** (additive form, avoiding ℕ subtraction):
`invCount(insertLeftStep ν j) + j = invCount(ν) + insertLeftIndex(ν, j)`.

Proof sketch: split the invCount sum for the new shuffle at the insertion
index `t`. The term at `t` contributes `t - j`
(by `insertLeftStep_invCount_term_at`). Each remaining step `r ≠ t` bijects
with a step of `ν` having the same contribution
(by `insertLeftStep_invCount_term_skip`). -/
private lemma invCount_insertLeftStep_add {p q : ℕ}
    (ν : Shuffle p q) (j : Fin (p + 2)) :
    (insertLeftStep ν j).invCount + j.val =
    ν.invCount + (insertLeftIndex ν j).val := by
  set μ := insertLeftStep ν j
  have hge : j.val ≤ (insertLeftIndex ν j).val := insertLeftIndex_ge ν j
  have hle : (insertLeftIndex ν j).val ≤ j.val + q := insertLeftIndex_le ν j
  -- Key: rewrite p+1+q as (p+q)+1 to use Fin.sum_univ_succAbove
  -- This is valid because p + 1 + q = (p + q) + 1 definitionally in Lean's kernel?
  -- No — but we can cast via finCongr.
  -- The insertion index as a Fin ((p+q)+1), if in range
  -- Since t ≤ j + q ≤ (p+1) + q = p + 1 + q, and p + 1 + q = (p + q) + 1,
  -- we have t ≤ (p+q) + 1. But we need t < (p+q) + 1, i.e., t ≤ p + q.
  -- When t = (p+q)+1, the insertion is at the very end.
  -- Actually, Fin.sum_univ_succAbove splits Fin (n+1) at ANY element of Fin (n+1),
  -- so we just need t < p + 1 + q. This might not hold when t = p+q+1 = p+1+q.
  -- Use Finset approach instead: extract element from univ, biject rest.
  simp only [invCount]
  -- Use Finset.sum_erase_add to extract one element
  by_cases ht_in : (insertLeftIndex ν j).val < p + 1 + q
  · -- Main case: t is a valid step index
    set t : Fin (p + 1 + q) := ⟨(insertLeftIndex ν j).val, ht_in⟩
    -- Extract term at t: ∑ = f(t) + (∑ over univ \ {t})
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ t)]
    -- f(t) = t - j by insertLeftStep_invCount_term_at
    rw [insertLeftStep_invCount_term_at ν j ht_in]
    -- Biject remaining terms with invCount(ν) via skip map
    have hskip := insertLeftStep_invCount_term_skip ν j
    suffices h : ∑ x ∈ Finset.univ.erase t,
        (if (μ.1 x.castSucc).1 < (μ.1 x.succ).1 then (μ.1 x.castSucc).2.val else 0) =
      ∑ r : Fin (p + q),
        (if (ν.1 r.castSucc).1 < (ν.1 r.succ).1 then (ν.1 r.castSucc).2.val else 0) by omega
    -- φ(i) = if i.val < t then ⟨i, _⟩ else ⟨i+1, _⟩
    let φ : Fin (p + q) → Fin (p + 1 + q) :=
      fun i => if h : i.val < (insertLeftIndex ν j).val
        then ⟨i.val, by omega⟩ else ⟨i.val + 1, by omega⟩
    apply (Finset.sum_nbij φ _ _ _ _).symm
    · -- maps into erase t
      intro i _; simp only [Finset.mem_erase, Finset.mem_univ, and_true, φ]
      intro heq
      have : (if h : i.val < (insertLeftIndex ν j).val then (⟨i.val, by omega⟩ : Fin (p+1+q))
        else ⟨i.val + 1, by omega⟩).val = t.val := congr_arg Fin.val heq
      have ht_val : t.val = (insertLeftIndex ν j).val := rfl
      split_ifs at this with h <;> simp at this <;> omega
    · -- injective
      intro a _ b _ hab
      have : (φ a).val = (φ b).val := congr_arg Fin.val hab
      simp only [φ] at this
      ext
      split_ifs at this with ha hb <;> simp at this <;> omega
    · -- surjective onto erase t
      intro r hr
      simp [Finset.mem_erase, Finset.mem_univ, and_true] at hr
      have hr_ne : r.val ≠ (insertLeftIndex ν j).val := fun h => hr (Fin.ext h)
      by_cases hrlt : r.val < (insertLeftIndex ν j).val
      · exact ⟨⟨r.val, by omega⟩, Finset.mem_coe.mpr (Finset.mem_univ _), by
          show φ ⟨r.val, by omega⟩ = r
          simp only [φ, hrlt, dite_true];⟩
      · exact ⟨⟨r.val - 1, by omega⟩, Finset.mem_coe.mpr (Finset.mem_univ _), by
          show φ ⟨r.val - 1, by omega⟩ = r
          simp only [φ]; split_ifs with h; · exfalso; omega
          · exact Fin.ext (by simp; omega)⟩
    · -- pointwise equality: fν(i) = fμ(φ(i))
      intro i _; exact (hskip i).symm
  · -- Boundary case: t = p + 1 + q (insertion at the very end, j = p+1)
    have hfmu : (if (μ.1 (Fin.castSucc ⟨p + q, by omega⟩)).1 < (μ.1 (Fin.succ ⟨p + q, by omega⟩)).1
      then (μ.1 (Fin.castSucc ⟨p + q, by omega⟩)).2.val else 0) = q := by
      have ht_eq : (insertLeftIndex ν j).val = p + 1 + q := by omega
      simp only [μ, insertLeftStep, insertLeftStepFun, OrderHom.coe_mk]
      split_ifs with h1 h2 h3 h4 h5 h6 <;> simp_all [fin_val_castSucc, Fin.val_succ] <;> try omega
      -- Remaining: "before" branch for castSucc, "at" branch for succ
      have hlast : ν.1 ⟨p + q, by omega⟩ = (Fin.last p, Fin.last q) := by
        have : (⟨p + q, (by omega : p + q < p + q + 1)⟩ : Fin (p + q + 1)) = Fin.last (p + q) :=
          Fin.ext (by simp [Fin.last])
        rw [this]; exact Shuffle.apply_last ν
      simp only [hlast, Fin.last]
      · exfalso; simp at h2; omega
      · have heq : (⟨p + q, (by omega : p + q < p + q + 1)⟩ : Fin (p + q + 1)) = Fin.last (p + q) :=
          Fin.ext (by simp [Fin.last])
        have h := Shuffle.apply_last ν; rw [← heq] at h
        show (ν.1 ⟨p + q, _⟩).2.val = q
        rw [show (ν.1 ⟨p + q, _⟩).2 = (Fin.last q) from congr_arg Prod.snd h]
        simp [Fin.last]
      · exfalso
        have heq : (⟨p + q, (by omega : p + q < p + q + 1)⟩ : Fin (p + q + 1)) = Fin.last (p + q) :=
          Fin.ext (by simp [Fin.last])
        have hlast' := Shuffle.apply_last ν; rw [← heq] at hlast'
        simp only [hlast', Fin.last] at h5
        have : j.succAbove ⟨p, by omega⟩ < j := by
          rw [Fin.succAbove_lt_iff_castSucc_lt]; simp [Fin.lt_def]; omega
        exact not_le.mpr this h5
    set s : Fin (p + 1 + q) := ⟨p + q, by omega⟩
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ s), hfmu]
    have hskip := insertLeftStep_invCount_term_skip ν j
    suffices h : ∑ x ∈ Finset.univ.erase s,
        (if (μ.1 x.castSucc).1 < (μ.1 x.succ).1 then (μ.1 x.castSucc).2.val else 0) =
      ∑ r : Fin (p + q),
        (if (ν.1 r.castSucc).1 < (ν.1 r.succ).1 then (ν.1 r.castSucc).2.val else 0) by omega
    let φ : Fin (p + q) → Fin (p + 1 + q) :=
      fun i => if h : i.val < (insertLeftIndex ν j).val
        then ⟨i.val, by omega⟩ else ⟨i.val + 1, by omega⟩
    apply (Finset.sum_nbij φ _ _ _ _).symm
    · -- maps into erase s
      intro i _; simp only [Finset.mem_erase, Finset.mem_univ, and_true, φ]
      intro heq
      have : (if h : i.val < (insertLeftIndex ν j).val then (⟨i.val, by omega⟩ : Fin (p+1+q))
        else ⟨i.val + 1, by omega⟩).val = s.val := congr_arg Fin.val heq
      have hs_val : s.val = p + q := rfl
      split_ifs at this with h <;> simp at this <;> omega
    · -- injective
      intro a _ b _ hab
      have : (φ a).val = (φ b).val := congr_arg Fin.val hab
      simp only [φ] at this
      ext
      split_ifs at this with ha hb <;> simp at this <;> omega
    · -- surjective onto erase s
      intro r hr
      simp [Finset.mem_erase, Finset.mem_univ, and_true] at hr
      have hr_ne : r.val ≠ p + q := fun h => hr (Fin.ext h)
      by_cases hrlt : r.val < (insertLeftIndex ν j).val
      · exact ⟨⟨r.val, by omega⟩, Finset.mem_coe.mpr (Finset.mem_univ _), by
          show φ ⟨r.val, by omega⟩ = r
          simp only [φ, hrlt, dite_true]⟩
      · exact ⟨⟨r.val - 1, by omega⟩, Finset.mem_coe.mpr (Finset.mem_univ _), by
          show φ ⟨r.val - 1, by omega⟩ = r
          simp only [φ]; split_ifs with h; · exfalso; omega
          · exact Fin.ext (by simp; omega)⟩
    · -- pointwise equality
      intro i _; exact (hskip i).symm

/-- Sign relation for left insertion:
`(insertLeftStep ν j).sign * (-1)^(insertLeftIndex ν j) = (-1)^j * ν.sign`.

Derived from `invCount_insertLeftStep_add` via exponent arithmetic:
the identity `invCount(μ) + j = invCount(ν) + t` gives
`(-1)^(invCount(μ) + j) = (-1)^(invCount(ν) + t)`, hence
`sign(μ) * (-1)^j = sign(ν) * (-1)^t`, and multiplying both sides
by `(-1)^(j+t)` (using `(-1)^(2k) = 1`) yields the result. -/
lemma sign_insertLeftStep {p q : ℕ}
    (ν : Shuffle p q) (j : Fin (p + 2)) :
    (insertLeftStep ν j).sign * (-1 : ℤ) ^ (insertLeftIndex ν j).val =
    (-1 : ℤ) ^ j.val * ν.sign := by
  simp only [sign, ← pow_add]
  have h := invCount_insertLeftStep_add ν j
  have hge := insertLeftIndex_ge ν j
  rw [show (insertLeftStep ν j).invCount + (insertLeftIndex ν j).val =
    (j.val + ν.invCount) + 2 * ((insertLeftIndex ν j).val - j.val) from by omega]
  rw [pow_add, pow_mul, neg_one_sq, one_pow, mul_one]



/-- Right insertion index equals left insertion index on the swapped shuffle. -/
private lemma insertRightIndex_eq_swap {p q : ℕ}
    (ν : Shuffle p q) (k : Fin (q + 2)) :
    (insertRightIndex ν k).val = (insertLeftIndex (ν.swap) k).val := by
  simp only [insertRightIndex, insertLeftIndex]
  have : (Finset.univ.filter fun r : Fin (q + p + 1) =>
      ((ν.swap).1 r).1.val < k.val) =
    (Finset.univ.filter fun r : Fin (p + q + 1) =>
      (ν.1 r).2.val < k.val).map (Fin.castOrderIso (by omega)).toEquiv.toEmbedding := by
    ext x; simp [Finset.mem_filter, swap, Fin.castOrderIso]
  rw [this, Finset.card_map]


/-- Right insertion is left insertion on the swapped shuffle. -/
private lemma insertRightStep_eq_swap {p q : ℕ}
    (ν : Shuffle p q) (k : Fin (q + 2)) :
    (insertRightStep ν k).swap = insertLeftStep (ν.swap) k := by
  have hidx := insertRightIndex_eq_swap ν k
  apply Subtype.ext; ext r
  all_goals {
    simp only [swap, insertRightStep, insertLeftStep, insertRightStepFun, insertLeftStepFun,
      OrderHom.coe_mk, Fin.castOrderIso, Prod.swap]
    -- The Fin.cast on r preserves .val, so both dite conditions key on r.val vs t
    -- where t = insertRightIndex = insertLeftIndex (by hidx)
    have hcast : (Fin.cast (by omega : q + 1 + p + 1 = p + (q + 1) + 1) r).val = r.val := by
      simp [Fin.cast]
    set t := (insertRightIndex ν k).val with ht_def
    set s := (insertLeftIndex (ν.swap) k).val with hs_def
    have hts : t = s := hidx
    simp only [swap, insertRightStep, insertLeftStep, insertRightStepFun, insertLeftStepFun,
      OrderHom.coe_mk, Fin.castOrderIso, Prod.swap, insertRightIndex, insertLeftIndex] at *
    split_ifs <;> simp_all [Fin.cast, Fin.val_mk] <;> try rfl <;> try omega
    all_goals (try (congr 1; ext; simp [Fin.cast]; omega))
    · rename_i h1 h2
      simp [Fin.cast] at h1 h2
      exfalso; linarith [ht_def]
    all_goals (rename_i h1 h2 h3; simp [Fin.cast] at h1 h2 h3; exfalso; try ( linarith [ht_def]))
    all_goals (exfalso; try omega)
  }


/-- Sign relation for right insertion:
`(insertRightStep ν k).sign * (-1)^(insertRightIndex ν k) =
 (-1)^p * (-1)^k * ν.sign`. -/
lemma sign_insertRightStep {p q : ℕ}
    (ν : Shuffle p q) (k : Fin (q + 2)) :
    (insertRightStep ν k).sign * (-1 : ℤ) ^ (insertRightIndex ν k).val =
    (-1 : ℤ) ^ p * ((-1 : ℤ) ^ k.val * ν.sign) := by
  have h1 := sign_eq_negOnePow_mul_swap_sign (insertRightStep ν k)
  have h2 := insertRightStep_eq_swap ν k
  have h3 := insertRightIndex_eq_swap ν k
  have h4 := sign_insertLeftStep (ν.swap) k
  have h5 := sign_eq_negOnePow_mul_swap_sign ν
  rw [h1, h2, h3, h5]
  -- LHS: (-1)^(p*(q+1)) * sign * (-1)^idx
  -- RHS: (-1)^p * ((-1)^k * ((-1)^(p*q) * swap_sign))
  -- Use h4: sign * (-1)^idx = (-1)^k * swap_sign
  -- Then LHS = (-1)^(p*(q+1)) * (-1)^k * swap_sign
  -- RHS = (-1)^(p + p*q) * (-1)^k * swap_sign, and p*(q+1) = p + p*q
  calc (-1 : ℤ) ^ (p * (q + 1)) *
      (insertLeftStep (ν.swap) k).sign * (-1) ^ (insertLeftIndex (ν.swap) k).val
      = (-1) ^ (p * (q + 1)) *
        ((insertLeftStep (ν.swap) k).sign * (-1) ^ (insertLeftIndex (ν.swap) k).val) := by ring
    _ = (-1) ^ (p * (q + 1)) * ((-1) ^ k.val * (ν.swap).sign) := by rw [h4]
    _ = (-1) ^ p * ((-1) ^ k.val * ((-1) ^ (p * q) * (ν.swap).sign)) := by
        rw [show p * (q + 1) = p * q + p from by ring, pow_add]; ring

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
  by_contra h_contra
  generalize_proofs at *;
  unfold Shuffle.isDiagonalVertex at h_contra
  generalize_proofs at *;
  split_ifs at h_contra ; simp_all +decide [ Shuffle.isLeftStep ];
  cases h : ( ν.insertLeftIndex j : ℕ ) <;> simp_all +decide [ Fin.castSucc, Fin.succ ];
  · aesop;
  · unfold Shuffle.insertLeftStep at * ; simp_all +decide [ Fin.castSucc, Fin.succ ] ;
    unfold Shuffle.insertLeftStepFun at * ; simp_all +decide [ Fin.castSucc, Fin.succ ] ;
    cases h_contra <;> simp_all +decide [ Fin.succAbove ];
    · split_ifs at * <;> simp_all +decide [ Fin.lt_iff_val_lt_val, Fin.le_iff_val_le_val ];
      · rename_i k hk₁ hk₂ hk₃ hk₄ hk₅ hk₆
        generalize_proofs at *; (
        have := insertLeftIndex_iff ν j ⟨ hk₄ + 1, by linarith ⟩ ; simp_all +decide [ Fin.castSucc, Fin.succ ] ;);
      · grind;
      · grind;
      · linarith! [ ν.1.monotone ( show ⟨ ‹_›, by linarith ⟩ ≤ ⟨ ‹_› + 1, by linarith ⟩ from Nat.le_succ _ ) ];
    · split_ifs at * <;> simp_all +decide [ Fin.le_iff_val_le_val, Fin.lt_iff_val_lt_val ] ; omega;
      · linarith! [ Fin.is_lt j ] ;
      · linarith! [ ν.1.monotone ( show ⟨ ‹_›, by linarith ⟩ ≤ ⟨ ‹_› + 1, by linarith ⟩ from Nat.le_succ _ ) ] ;
      · have := insertLeftIndex_iff ν j ⟨ ‹_›, by omega ⟩ ; simp_all +decide [ Fin.castSucc, Fin.succ ] ;
        linarith! [ Fin.is_lt j ] ;

/-- Right insertion always produces a non-diagonal vertex: the two steps
adjacent to the inserted vertex are both right steps (RR pattern). -/
lemma insertRightStep_not_diagonal {p q : ℕ}
    (ν : Shuffle (p + 1) q) (k : Fin (q + 2)) :
    ¬isDiagonalVertex (insertRightStep ν k)
      ((insertRightIndex ν k).cast (by omega)) := by
  unfold Shuffle.isDiagonalVertex; simp +decide [ Shuffle.insertRightStep ] ;
  unfold Shuffle.isLeftStep; intros; simp_all +decide [ Shuffle.insertRightStepFun ] ;
  split_ifs at * <;> simp_all +decide [ Fin.ext_iff, Fin.val_add, Nat.mod_eq_of_lt ];
  all_goals erw [ Fin.lt_iff_val_lt_val ] at *; simp_all +decide [ Fin.val_add, Nat.mod_eq_of_lt ] ;
  any_goals omega;
  · constructor <;> intro h <;> have := ν.1.monotone ( show ⟨ ( ν.insertRightIndex k : ℕ ) - 1, by omega ⟩ ≤ ⟨ ( ν.insertRightIndex k : ℕ ), by omega ⟩ from Nat.sub_le _ _ ) <;> simp_all +decide [ Fin.le_iff_val_le_val ] ;
    · have := insertRightIndex_iff ν k ⟨ ( ν.insertRightIndex k : ℕ ) - 1, by omega ⟩ ; simp_all +decide [ Fin.ext_iff, Fin.val_add, Nat.mod_eq_of_lt ] ;
      have := coordSum_eq ν ⟨ ( ν.insertRightIndex k : ℕ ) - 1, by omega ⟩ ; have := coordSum_eq ν ⟨ ( ν.insertRightIndex k : ℕ ), by omega ⟩ ; simp_all +decide [ Fin.ext_iff, Fin.val_add, Nat.mod_eq_of_lt ] ; omega;
    · have := coordSum_eq ν ⟨ ( ν.insertRightIndex k : ℕ ), by omega ⟩ ; simp_all +decide [ Fin.add_def, Nat.mod_eq_of_lt ] ;
      have := ( insertRightIndex_iff ν k ⟨ ( ν.insertRightIndex k : ℕ ), by omega ⟩ ) ; simp_all +decide [ Fin.lt_iff_val_lt_val ] ;
      omega;
  · exact absurd ‹_› ( not_le_of_gt ( Nat.pred_lt ( ne_bot_of_gt ‹_› ) ) )

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
  simp_all only [Subtype.exists]
  obtain ⟨val, property⟩ := μ

  unfold isDiagonalVertex at hr
  split_ifs at hr with h₁ h₂
  · -- Interior case: 0 < r and r < bound. hr says NOT diagonal, so LL or RR.
    push_neg at hr
    -- hr : (isLeftStep ... ∧ ¬isLeftStep ...) ∨ (¬isLeftStep ... ∧ isLeftStep ...) → False
    -- i.e., both steps same direction. Case split on isLeftStep at r-1.
    by_cases hL : isLeftStep ⟨val, property⟩ ⟨↑r - 1, by omega⟩
    · -- LL case: both steps are left steps → left insertion
      left
      refine ⟨(val ⟨r, by omega⟩).1, ?_⟩
      -- Sub-shuffle ν: skip position r, undo succAbove j on fst
      -- For i < r: fst < j, so succAbove j was identity → ν(i).1 = μ(i).1
      -- For i ≥ r: fst ≥ j, so succAbove j added 1 → ν(i).1 = μ(i+1).1 - 1
      let j := (val ⟨r, by omega⟩).1
      let νOH : Fin (p + (q + 1) + 1) →o (Index p × Index (q + 1)) :=
        ⟨fun i =>
          if h : i.val < r.val then
            (⟨(val ⟨i.val, by omega⟩).1.val, by sorry⟩, (val ⟨i.val, by omega⟩).2)
          else
            (⟨(val ⟨i.val + 1, by omega⟩).1.val - 1, by sorry⟩,
             (val ⟨i.val + 1, by omega⟩).2), by
          sorry⟩
      have νInj : Function.Injective νOH := by
        intro a b hab
        simp only [νOH, OrderHom.coe_mk] at hab
        split_ifs at hab with ha hb hb
        · -- a < r, b < r: both map to val directly, use property
          have heq : val ⟨a.val, by omega⟩ = val ⟨b.val, by omega⟩ :=
            Prod.ext (Fin.ext (by simp [Prod.ext_iff, Fin.ext_iff] at hab; exact hab.1))
                     (Fin.ext (by simp [Prod.ext_iff, Fin.ext_iff] at hab; exact hab.2))
          exact Fin.ext (by have := property heq; simp [Fin.ext_iff] at this; exact this)
        · -- a < r, b ≥ r: val(a).1 ≤ val(r-1).1 < val(r).1 ≤ val(b+1).1
          -- so val(a).1 < val(b+1).1 - 1 is impossible given hab says they're equal
          exfalso
          simp [Prod.ext_iff, Fin.ext_iff] at hab
          have hLfst : (val ⟨r.val - 1, by omega⟩).1.val < (val ⟨r.val, by omega⟩).1.val := by
            have := hL; unfold isLeftStep at this; dsimp at this
            have hrm1 : r.val - 1 + 1 = r.val := Nat.succ_pred_eq_of_pos h₁
            rwa [show (⟨r.val - 1 + 1, by omega⟩ : Fin _) = ⟨r.val, by omega⟩
              from Fin.ext hrm1] at this
          have hmon_a : val ⟨a.val, by omega⟩ ≤ val ⟨r.val - 1, by omega⟩ :=
            val.monotone (Fin.mk_le_mk.mpr (by omega))
          have hmon_rb : val ⟨r.val, by omega⟩ ≤ val ⟨b.val + 1, by omega⟩ :=
            val.monotone (Fin.mk_le_mk.mpr (by omega))
          simp only [Prod.le_def, Fin.le_def] at hmon_a hmon_rb
          sorry
        · -- a ≥ r, b < r: symmetric contradiction
          sorry
        · -- a ≥ r, b ≥ r: both map to val(·+1), use property
          sorry
      sorry
    · sorry -- RR case: both steps are right steps → right insertion
  · sorry -- r = last (boundary)
  · -- r = 0 boundary case
    have hr0 : r.val = 0 := by omega
    by_cases hL : isLeftStep ⟨val, property⟩ ⟨0, by omega⟩
    · -- first step is left → left insertion at j = 0
      left; refine ⟨0, ?_⟩
      -- ν is the "tail": ν(i) = (μ(i+1).1 - 1, μ(i+1).2)
      -- First, the first step being left means μ(0).1 = 0 and μ(1).1 = 1
      -- so μ(i).1 ≥ 1 for i ≥ 1, making the subtraction safe.
      have hcs0 : (val ⟨0, by omega⟩).1.val + (val ⟨0, by omega⟩).2.val = 0 :=
        coordSum_eq ⟨val, property⟩ ⟨0, by omega⟩
      have hval0_1 : (val ⟨0, by omega⟩).1.val = 0 := by omega
      have hval0_2 : (val ⟨0, by omega⟩).2.val = 0 := by omega
      have hfst_pos : ∀ (i : Fin (p + (q + 1) + 1)), 1 ≤ (val ⟨i.val + 1, by omega⟩).1.val := by
        intro i
        have hL' : (val ⟨0, by omega⟩).1.val < (val ⟨1, by omega⟩).1.val := hL
        have hmon : val ⟨1, by omega⟩ ≤ val ⟨i.val + 1, by omega⟩ :=
          val.monotone (by simp [Fin.le_def])
        simp only [Prod.le_def, Fin.le_def] at hmon; omega
      -- Build the sub-shuffle: ν(i) = (μ(i+1).1 - 1, μ(i+1).2)
      let νOH : Fin (p + (q + 1) + 1) →o (Index p × Index (q + 1)) :=
        ⟨fun i => (⟨(val ⟨i.val + 1, by omega⟩).1.val - 1, by omega⟩,
                   (val ⟨i.val + 1, by omega⟩).2), by
          intro a b hab
          simp only [Prod.le_def, Fin.le_def]
          have hmab : val ⟨a.val + 1, by omega⟩ ≤ val ⟨b.val + 1, by omega⟩ :=
            val.monotone (Fin.mk_le_mk.mpr (by omega))
          simp only [Prod.le_def, Fin.le_def] at hmab
          constructor <;> omega⟩
      have νInj : Function.Injective νOH := by
        intro a b hab
        simp only [νOH, OrderHom.coe_mk, Prod.mk.injEq, Fin.ext_iff] at hab
        have ha := hfst_pos a; have hb := hfst_pos b
        have heq : val ⟨a.val + 1, by omega⟩ = val ⟨b.val + 1, by omega⟩ :=
          Prod.ext (Fin.ext (by omega)) (Fin.ext (by omega))
        exact Fin.ext (by have := property heq; simp [Fin.ext_iff] at this; omega)
      let ν : Shuffle p (q + 1) := ⟨νOH, νInj⟩
      refine ⟨νOH, νInj, ?eq_insert, ?idx_eq⟩
      case eq_insert =>
        -- insertLeftIndex ν 0 = 0 since all fst coords of ν are ≥ 0.
        have ht0 : (insertLeftIndex ⟨νOH, νInj⟩ 0).val = 0 := by
          simp only [insertLeftIndex, Fin.val_zero]
          apply Finset.card_eq_zero.mpr
          rw [Finset.filter_eq_empty_iff]
          intro x _
          simp only [νOH, OrderHom.coe_mk, Fin.val_mk]
          omega
        apply Subtype.ext; apply OrderHom.ext; funext i
        change val i = insertLeftStepFun ⟨νOH, νInj⟩ 0 i
        unfold insertLeftStepFun
        -- First branch i < t is impossible since t = 0
        rw [dif_neg (by omega : ¬(i.val < (insertLeftIndex ⟨νOH, νInj⟩ 0).val))]
        by_cases hi : i.val = 0
        · -- i = 0: second branch gives (0, 0), matching val 0 = (0, 0)
          rw [dif_pos (by omega)]
          have hi0 : i = ⟨0, by omega⟩ := Fin.ext hi
          simp only [hi0, Fin.val_zero, Nat.sub_zero]
          exact Prod.ext (Fin.ext hval0_1) (Fin.ext hval0_2)
        · -- i > 0: succAbove 0 (fst-1) = fst since fst ≥ 1, snd matches directly
          rw [dif_neg (by omega)]
          simp only [νOH, OrderHom.coe_mk]
          have hfp := hfst_pos ⟨i.val - 1, by omega⟩
          have him1v : i.val - 1 + 1 = i.val := by omega
          -- Collapse ⟨i.val - 1 + 1, ...⟩ to i via congrArg val
          have hval_eq : val ⟨i.val - 1 + 1, by omega⟩ = val i :=
            congrArg val (Fin.ext him1v)
          simp only [hval_eq]
          -- Now: val i = (succAbove 0 ⟨fst-1⟩, snd)
          -- succAbove 0 is Fin.succ (since nothing is < 0), so result is ⟨fst-1+1⟩ = fst
          refine Prod.ext (Fin.ext ?_) rfl
          simp only [Fin.succAbove, Fin.lt_def, Fin.val_zero]
          split
          · -- ⟨fst-1⟩ < 0 is impossible
            rename_i hlt; simp [fin_val_castSucc] at hlt
          · -- succAbove gives succ: ⟨fst-1+1⟩ = fst
            simp only [Fin.val_succ, Fin.val_mk]
            -- hfp gives (val i).1.val ≥ 1 after collapsing ⟨i-1+1⟩ = i
            simp only [hval_eq] at hfp; omega
      case idx_eq =>
        simp only [insertLeftIndex, hr0]
        apply Finset.card_eq_zero.mpr
        rw [Finset.filter_eq_empty_iff]
        intro x _
        simp only [νOH, OrderHom.coe_mk, Fin.val_mk, Fin.val_zero]
        omega
    · sorry -- first step is right

/- The images of `insertLeftStep` and `insertRightStep` are disjoint:
no `(p+1,q+1)`-shuffle with a given vertex index can arise from both
a left insertion and a right insertion. -/
noncomputable section AristotleLemmas

/-
At the insertion index `t`, `insertRightStep` does not have a left step (i.e., it has a right step).
-/
open HomologyLean.SingularHomology in
lemma insertRightStep_not_isLeftStep_at {p q : ℕ}
    (ν : Shuffle p q) (k : Fin (q + 2))
    (ht : (insertRightIndex ν k).val < p + q + 1) :
    ¬ isLeftStep (insertRightStep ν k) ⟨(insertRightIndex ν k).val, ht⟩ := by
      unfold isLeftStep;
      simp +decide [ Fin.castSucc, Fin.succ, Shuffle.insertRightStep ] at *;
      unfold insertRightStepFun; simp +decide [ * ] ;
      have := coordSum_eq ν ⟨ ( ν.insertRightIndex k : ℕ ), by omega ⟩ ; simp_all +decide [ Fin.val_add, Nat.add_mod, Nat.mod_eq_of_lt ] ;
      have := insertRightIndex_ge ν k; simp_all +decide [ Fin.le_def, Nat.le_sub_iff_add_le ] ;
      linarith [ show ( ν.1 ⟨ ( ν.insertRightIndex k : ℕ ), ht ⟩ |>.2 : ℕ ) ≥ k from by
                  have := insertRightIndex_iff ν k ⟨ ( ν.insertRightIndex k : ℕ ), ht ⟩ ; aesop; ]

end AristotleLemmas
/-- The images of `insertLeftStep` and `insertRightStep` are disjoint:
no `(p+1,q+1)`-shuffle with a given vertex index can arise from both
a left insertion and a right insertion. -/
lemma insertLeft_insertRight_disjoint {p q : ℕ}
    (j : Fin (p + 2)) (ν₁ : Shuffle p (q + 1))
    (k : Fin (q + 2)) (ν₂ : Shuffle (p + 1) q)
    (hμ : insertLeftStep ν₁ j = insertRightStep ν₂ k)
    (hr : (insertLeftIndex ν₁ j).val = (insertRightIndex ν₂ k).val) :
    False := by
  by_cases ht : (ν₁.insertLeftIndex j).val < p + 1 + (q + 1);
  · have := insertLeftStep_isLeftStep_at ν₁ j ht; have := insertRightStep_not_isLeftStep_at ν₂ k ( by linarith ) ; simp_all +decide [ isLeftStep ] ;
  · have h_last : (ν₁.insertLeftIndex j).val = p + 1 + (q + 1) ∧ (ν₂.insertRightIndex k).val = p + 1 + (q + 1) := by
      exact ⟨ by linarith [ Fin.is_lt ( ν₁.insertLeftIndex j ) ], by linarith [ Fin.is_lt ( ν₂.insertRightIndex k ) ] ⟩;
    have h_last : j = Fin.last (p + 1) ∧ k = Fin.last (q + 1) := by
      have h_last : j.val = p + 1 ∧ k.val = q + 1 := by
        have h_last : (ν₁.insertLeftIndex j).val ≤ j.val + (q + 1) ∧ (ν₂.insertRightIndex k).val ≤ (p + 1) + k.val := by
          exact ⟨ insertLeftIndex_le ν₁ j, insertRightIndex_le ν₂ k ⟩;
        constructor <;> linarith [ Fin.is_lt j, Fin.is_lt k ];
      exact ⟨ Fin.ext h_last.1, Fin.ext h_last.2 ⟩;
    have := hμ; replace := congr_arg ( fun f => f.1.1 ⟨ ( p + 1 + ( q + 1 ) - 1 ), by omega ⟩ ) this; simp +decide [ h_last ] at this;
    unfold insertLeftStep insertRightStep at this; simp +decide [ h_last ] at this;
    unfold insertLeftStepFun insertRightStepFun at this; simp +decide [ h_last ] at this;
    have := Shuffle.apply_last ν₁; have := Shuffle.apply_last ν₂; simp_all +decide [ add_comm, add_left_comm, add_assoc ] ;
    simp_all +decide [ add_comm, add_left_comm, add_assoc, Fin.last ]


/-- Left insertion produces a left-type vertex: the step at (or just before)
the inserted vertex is a left step.  Here `isLeftType` checks `isLeftStep`
at index `min r.val ((p+1)+(q+1)-1)`. -/
lemma insertLeftStep_isLeftType {p q : ℕ}
    (ν : Shuffle p (q + 1)) (j : Fin (p + 2)) :
    isLeftStep (insertLeftStep ν j)
      ⟨min (insertLeftIndex ν j).val ((p + 1) + (q + 1) - 1), by omega⟩ := by
  cases min_cases ( ν.insertLeftIndex j : ℕ ) ( p + 1 + ( q + 1 ) - 1 ) <;> simp_all +decide [ Shuffle.isLeftStep ];
  · have := insertLeftStep_isLeftStep_at ν j ( by omega ) ; aesop;
  · -- Since the first component of the last element is (insertLeftIndex ν j).val, which is j.val + (q + 1), and the second component is 0, the pair (j, 0) is indeed the last element.
    have h_last : (insertLeftIndex ν j).val = j.val + (q + 1) := by
      have h_last : (insertLeftIndex ν j).val ≤ j.val + (q + 1) := by
        apply_rules [ insertLeftIndex_le ]
      generalize_proofs at *; (
      linarith [ Fin.is_lt j ])
    generalize_proofs at *;
    norm_num [ show ( ( ν.insertLeftStep j ) : Fin ( p + 1 + ( q + 1 ) + 1 ) → Index ( p + 1 ) × Index ( q + 1 ) ) = insertLeftStepFun ν j from rfl, insertLeftStepFun ] at *;
    split_ifs <;> simp_all +decide [ Fin.succAbove ];
    · grind;
    · split_ifs <;> norm_num [ Fin.lt_iff_val_lt_val ] at * <;> omega;
    · omega

/-- Right insertion produces a non-left-type vertex: the step at (or just before)
the inserted vertex is a right step, not a left step. -/
lemma insertRightStep_not_isLeftType {p q : ℕ}
    (ν : Shuffle (p + 1) q) (k : Fin (q + 2)) :
    ¬isLeftStep (insertRightStep ν k)
      ⟨min (insertRightIndex ν k).val ((p + 1) + (q + 1) - 1), by omega⟩ := by
  intro h_left_step
  generalize_proofs at *;
  unfold isLeftStep at h_left_step;
  simp +decide [ *, insertRightStep ] at h_left_step ⊢;
  unfold insertRightStepFun at h_left_step; simp +decide [ *, Fin.ext_iff ] at h_left_step ⊢;
  split_ifs at h_left_step <;> try linarith [ Fin.is_lt ( ν.insertRightIndex k ) ] ;
  any_goals omega;
  · have := ν.1.monotone ( show ⟨ Min.min ( ν.insertRightIndex k : ℕ ) ( p + 1 + q ), by omega ⟩ ≤ ⟨ p + 1 + q, by omega ⟩ from Nat.min_le_right _ _ ) ; simp_all +decide [ Fin.le_iff_val_le_val ] ;
    have h_last : ν.1 ⟨p + 1 + q, by omega⟩ = (Fin.last (p + 1), Fin.last q) := by
      exact Shuffle.apply_last ν
    generalize_proofs at *; simp_all +decide [ Fin.le_iff_val_le_val ] ;
    simp_all +decide [ Fin.le_def, min_eq_right ( by linarith : p + 1 + q ≤ ( ν.insertRightIndex k : ℕ ) ) ];
    exact h_left_step.not_ge ( Nat.le_of_lt_succ <| by simp +arith +decide [ *, Fin.is_lt ] );
  · cases min_cases ( ν.insertRightIndex k : ℕ ) ( p + 1 + q ) <;> simp_all +decide [ Fin.lt_iff_val_lt_val ];
    have := insertRightIndex_iff ν k ⟨ ( ν.insertRightIndex k : ℕ ), by omega ⟩ ; simp_all +decide [ Fin.ext_iff ] ;
    have := coordSum_eq ν ⟨ ( ν.insertRightIndex k : ℕ ), by omega ⟩ ; simp_all +decide [ Fin.ext_iff ] ; omega;


/-- Extract the two facts from `isDiagonalVertex`: `0 < r` and `r < (p+1)+(q+1)`. -/
private lemma isDiagonalVertex_bounds {p q : ℕ} {μ : Shuffle (p + 1) (q + 1)}
    {r : Index (p + 1 + (q + 1))} (hr : isDiagonalVertex μ r) :
    0 < r.val ∧ r.val < (p + 1) + (q + 1) := by
  unfold isDiagonalVertex at hr
  split_ifs at hr with h₁ h₂ <;> exact ⟨‹_›, ‹_›⟩

/-- At a diagonal vertex with a left step at `r-1`, the shuffle step from
`r-1` to `r` increments fst, giving `μ(r).1 ≥ 1`. -/
private lemma diagonal_left_fst_pos {p q : ℕ} {μ : Shuffle (p + 1) (q + 1)}
    {r : Index (p + 1 + (q + 1))} (hr : isDiagonalVertex μ r)
    (hL : isLeftStep μ ⟨r.val - 1, by have := (isDiagonalVertex_bounds hr).2; omega⟩) :
    0 < (μ.1 r).1.val := by
  have ⟨h₁, h₂⟩ := isDiagonalVertex_bounds hr
  have hstep := shuffle_step μ ⟨r.val - 1, by omega⟩
  have hcs : (⟨r.val - 1, by omega⟩ : Fin ((p + 1) + (q + 1))).castSucc =
      (⟨r.val - 1, by omega⟩ : Index ((p + 1) + (q + 1))) :=
    Fin.ext (by simp [Fin.castSucc])
  have hsu : (⟨r.val - 1, by omega⟩ : Fin ((p + 1) + (q + 1))).succ = r :=
    Fin.ext (by simp [Fin.succ]; omega)
  rw [hcs, hsu] at hstep
  unfold isLeftStep at hL; rw [hcs, hsu] at hL
  rcases hstep with ⟨h1, _⟩ | ⟨h1, _⟩
  · omega
  · omega

/-- At a diagonal vertex with a right step at `r-1`, the shuffle step from
`r-1` to `r` increments snd, giving `μ(r).2 ≥ 1`. -/
private lemma diagonal_right_snd_pos {p q : ℕ} {μ : Shuffle (p + 1) (q + 1)}
    {r : Index (p + 1 + (q + 1))} (hr : isDiagonalVertex μ r)
    (hR : ¬isLeftStep μ ⟨r.val - 1, by have := (isDiagonalVertex_bounds hr).2; omega⟩) :
    0 < (μ.1 r).2.val := by
  have ⟨h₁, h₂⟩ := isDiagonalVertex_bounds hr
  have hstep := shuffle_step μ ⟨r.val - 1, by omega⟩
  have hcs : (⟨r.val - 1, by omega⟩ : Fin ((p + 1) + (q + 1))).castSucc =
      (⟨r.val - 1, by omega⟩ : Index ((p + 1) + (q + 1))) :=
    Fin.ext (by simp [Fin.castSucc])
  have hsu : (⟨r.val - 1, by omega⟩ : Fin ((p + 1) + (q + 1))).succ = r :=
    Fin.ext (by simp [Fin.succ]; omega)
  rw [hcs, hsu] at hstep
  unfold isLeftStep at hR; rw [hcs, hsu] at hR
  rcases hstep with ⟨h1, _⟩ | ⟨_, h2⟩
  · omega
  · omega

/-- The underlying function for `swapDiagonalSteps`: agrees with `μ` everywhere
except at vertex `r`, where the step type is swapped.
- LR diagonal (left then right): `μ(r)` becomes `(μ(r).1 - 1, μ(r).2 + 1)`
- RL diagonal (right then left): `μ(r)` becomes `(μ(r).1 + 1, μ(r).2 - 1)` -/
private def swapDiagonalSteps_fun {p q : ℕ} (μ : Shuffle (p + 1) (q + 1))
    (r : Index (p + 1 + (q + 1))) (hr : isDiagonalVertex μ r) :
    Index ((p + 1) + (q + 1)) → Index (p + 1) × Index (q + 1) :=
  fun i =>
    if i = r then
      have ⟨h₁, h₂⟩ := isDiagonalVertex_bounds hr
      have hsum := coordSum_eq μ r
      if hL : isLeftStep μ ⟨r.val - 1, by omega⟩ then
        -- LR case: fst decrements, snd increments
        -- fst ≥ 1 (step r-1 incremented fst) so fst - 1 is valid
        have hfst_pos := diagonal_left_fst_pos hr hL
        -- snd < q+1 because step r is right (snd increments at r),
        -- so μ(r+1).2 > μ(r).2 and μ(r+1).2 ≤ q+1
        have hsnd_lt : (μ.1 r).2.val < q + 1 := by
          -- Step r is right (not left) in LR diagonal, so snd increments at r
          unfold isDiagonalVertex at hr; simp [h₁, h₂] at hr
          have hnotL : ¬isLeftStep μ ⟨r.val, h₂⟩ := by tauto
          have hstep := shuffle_step μ ⟨r.val, h₂⟩
          have hcs : (⟨r.val, h₂⟩ : Fin ((p + 1) + (q + 1))).castSucc = r :=
            Fin.ext (by simp [Fin.castSucc])
          rw [hcs] at hstep
          unfold isLeftStep at hnotL; rw [hcs] at hnotL
          have hsucc_snd := (μ.1 (⟨r.val, h₂⟩ : Fin ((p + 1) + (q + 1))).succ).2.isLt
          rcases hstep with ⟨h1, _⟩ | ⟨_, h2⟩
          · exfalso; exact hnotL (by omega)
          · omega
        (⟨(μ.1 r).1.val - 1, by omega⟩,
         ⟨(μ.1 r).2.val + 1, by omega⟩)
      else
        -- RL case: fst increments, snd decrements
        -- snd ≥ 1 (step r-1 incremented snd) so snd - 1 is valid
        have hsnd_pos := diagonal_right_snd_pos hr (by exact hL)
        -- fst < p+1 because step r is left (fst increments at r),
        -- so μ(r+1).1 > μ(r).1 and μ(r+1).1 ≤ p+1
        have hfst_lt : (μ.1 r).1.val < p + 1 := by
          -- Step r is left in RL diagonal, so fst increments at r
          unfold isDiagonalVertex at hr; simp [h₁, h₂] at hr
          have hisL : isLeftStep μ ⟨r.val, h₂⟩ := by tauto
          have hstep := shuffle_step μ ⟨r.val, h₂⟩
          have hcs : (⟨r.val, h₂⟩ : Fin ((p + 1) + (q + 1))).castSucc = r :=
            Fin.ext (by simp [Fin.castSucc])
          rw [hcs] at hstep
          unfold isLeftStep at hisL; rw [hcs] at hisL
          have hsucc_fst := (μ.1 (⟨r.val, h₂⟩ : Fin ((p + 1) + (q + 1))).succ).1.isLt
          rcases hstep with ⟨h1, _⟩ | ⟨h1, _⟩
          · omega
          · exfalso; exact absurd (by omega : (μ.1 r).1.val < _) (by omega)
        (⟨(μ.1 r).1.val + 1, by omega⟩,
         ⟨(μ.1 r).2.val - 1, by omega⟩)
    else
      μ.1 i

/-- `swapDiagonalSteps_fun` preserves the coordinate sum: fst + snd = i for all i.
At `i ≠ r` this is `coordSum_eq μ`. At `i = r` the ±1 adjustments cancel. -/
private lemma swapDiagonalSteps_fun_coordSum {p q : ℕ}
    (μ : Shuffle (p + 1) (q + 1)) (r : Index (p + 1 + (q + 1)))
    (hr : isDiagonalVertex μ r) (i : Index ((p + 1) + (q + 1))) :
    (swapDiagonalSteps_fun μ r hr i).1.val +
      (swapDiagonalSteps_fun μ r hr i).2.val = i.val := by
  unfold HomologyLean.SingularHomology.Shuffle.swapDiagonalSteps_fun;
  split_ifs <;> simp_all +decide [ coordSum_eq ];
  rename_i hrcn;
  -- By definition of `swapDiagonalSteps_fun`, we know that the sum of the components is preserved.
  by_cases hL : μ.isLeftStep ⟨r.val - 1, by
    grind⟩
  all_goals generalize_proofs at *;
  · simp_all +decide [ Nat.sub_add_cancel, Nat.add_sub_of_le, Nat.le_of_lt_succ ];
    rename_i h₁ h₂ h₃ h₄ h₅ h₆;
    rcases h₁ with ⟨ h₁, h₂ ⟩ ; simp +decide [ h₁, h₂ ] at *;
    linarith [ Nat.sub_add_cancel ( show 1 ≤ ( μ.1 r |>.1 : ℕ ) from by linarith [ diagonal_left_fst_pos hr hL ] ), coordSum_eq μ r ];
  · simp_all +decide [ Fin.ext_iff ];
    rename_i h₁ h₂ h₃ h₄ h₅ h₆ h₇ h₈;
    have := coordSum_eq μ r; simp_all +decide [ Fin.ext_iff ] ;
    rcases h₃ with ⟨ h₃, h₄ ⟩ ; simp_all +decide [ Fin.ext_iff ] ;
    linarith [ Nat.sub_add_cancel ( show 1 ≤ ( μ.1 r |>.2 : ℕ ) from Nat.pos_of_ne_zero fun h => by have := diagonal_right_snd_pos hr h₂; aesop ), h₇ h₃ h₄ h₂ ]

/- `swapDiagonalSteps_fun` is monotone in the product order. Only the pairs
`(r-1, r)` and `(r, r+1)` need checking — the two adjacent steps swap type
(LR↔RL) but both remain valid (one coordinate +1, the other unchanged). -/
noncomputable section AristotleLemmas

open HomologyLean.SingularHomology

private lemma swapDiagonalSteps_fun_local_bounds {p q : ℕ}
    (μ : Shuffle (p + 1) (q + 1)) (r : Index (p + 1 + (q + 1)))
    (hr : isDiagonalVertex μ r) :
    μ.1 ⟨r.val - 1, by have := isDiagonalVertex_bounds hr; omega⟩ ≤ swapDiagonalSteps_fun μ r hr r ∧
    swapDiagonalSteps_fun μ r hr r ≤ μ.1 ⟨r.val + 1, by have := isDiagonalVertex_bounds hr; omega⟩ := by
      -- By definition of swapDiagonalSteps_fun, we need to consider the two cases for the diagonal vertex.
      by_cases hL : isLeftStep μ ⟨r.val - 1, by have := (isDiagonalVertex_bounds hr).2; omega⟩
      all_goals generalize_proofs at *;
      · -- By definition of swapDiagonalSteps_fun, when isLeftStep is true, the function returns (μ(r-1).fst, μ(r-1).snd + 1).
        have h_swap : μ.swapDiagonalSteps_fun r hr r = (⟨(μ.1 r).1.val - 1, by
          exact Nat.lt_succ_of_le ( Nat.sub_le_of_le_add <| by linarith [ Fin.is_lt ( μ.1 r |>.1 ) ] )⟩, ⟨(μ.1 r).2.val + 1, by
          simp +zetaDelta at *;
          unfold isDiagonalVertex at hr
          generalize_proofs at *;
          have hnotL : ¬isLeftStep μ ⟨r.val, by
            assumption⟩ := by
            grind +ring
          generalize_proofs at *;
          have hstep := shuffle_step μ ⟨r.val, by
            assumption⟩
          generalize_proofs at *;
          unfold isLeftStep at hnotL; simp_all +decide [ Fin.castSucc, Fin.succ ] ; omega;⟩) := by
          unfold HomologyLean.SingularHomology.Shuffle.swapDiagonalSteps_fun; aesop;
        generalize_proofs at *;
        -- By definition of swapDiagonalSteps_fun, we know that μ(r) is equal to (μ(r-1).fst + 1, μ(r-1).snd).
        have h_mu_r : μ.1 r = (⟨(μ.1 ⟨r.val - 1, by
          exact?⟩).1.val + 1, by
          exact Nat.lt_succ_of_le ( Nat.le_trans ( Nat.succ_le_of_lt hL ) ( Nat.le_of_lt_succ ( by simp only [Fin.succ_mk,
            Nat.succ_eq_add_one, Fin.is_lt] ) ) ) ⟩,
            ⟨(μ.1 ⟨r.val - 1, by
          exact?⟩).2.val, by
          grind⟩) := by
          all_goals generalize_proofs at *;
          have h_step : μ.1 (Fin.succ ⟨r.val - 1, by
            exact?⟩) = (⟨(μ.1 ⟨r.val - 1, by
            exact?⟩).1.val + 1, by
            exact?⟩, ⟨(μ.1 ⟨r.val - 1, by
            exact?⟩).2.val, by
            linarith
            skip⟩) := by
            have := shuffle_step μ ⟨r.val - 1, by
              exact?⟩
            generalize_proofs at *;
            rcases this with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> simp_all +decide [ isLeftStep ] ; omega
            skip
          generalize_proofs at *;
          convert h_step using 1
          generalize_proofs at *; (
          congr! 1
          generalize_proofs at *; (
          exact Eq.symm ( Fin.ext <| Nat.succ_pred_eq_of_pos <| Nat.pos_of_ne_zero <| by rintro h; have := isDiagonalVertex_bounds hr; aesop )))
        generalize_proofs at *;
        have h_mu_r_next : μ.1 ⟨r.val + 1, by
          exact?⟩ = (⟨(μ.1 r).1.val, by
          exact?⟩, ⟨(μ.1 r).2.val + 1, by
          exact?⟩) := by
          have h_mu_r_next : ¬isLeftStep μ ⟨r.val, by
            exact Nat.lt_of_succ_lt_succ ‹_›
            skip⟩ := by
            unfold isDiagonalVertex at hr; simp +decide [ hL ] at hr; tauto;
          generalize_proofs at *;
          have := shuffle_step μ ⟨r.val, by
            linarith [ Fin.is_lt r ]⟩
          generalize_proofs at *;
          simp_all +decide [ isLeftStep ];
          ext <;> simp_all +decide [ Fin.ext_iff, Prod.ext_iff ] <;> omega
          skip
        generalize_proofs at *;
        simp_all +decide [ Prod.le_def, Fin.le_def ];
      · -- Since μ(r-1) is a right step, we have (μ.1 r).2 = (μ.1 r-1).2 + 1.
        have h_right_step : (μ.1 r).2.val = (μ.1 ⟨r.val - 1, by
          exact?⟩).2.val + 1 := by
          have h_right_step : (μ.1 ⟨r.val - 1, by
            exact?⟩).1.val = (μ.1 r).1.val := by
            rcases r with ⟨ _ | r, hr ⟩ <;> norm_num at *;
            exact Classical.not_not.1 fun h => hL <| by exact lt_of_le_of_ne ( by exact μ.1.monotone ( Nat.le_succ _ ) |> And.left ) <| Ne.symm <| by aesop;
          generalize_proofs at *;
          have := coordSum_eq μ ⟨r.val - 1, by
            exact?⟩
          generalize_proofs at *;
          have := coordSum_eq μ r
          generalize_proofs at *;
          have := coordSum_eq μ ⟨r.val + 1, by
            linarith [ Fin.is_lt r ]⟩
          generalize_proofs at *;
          rcases r with ⟨ _ | r, hr ⟩ <;> simp_all +arith +decide
          generalize_proofs at *;
          · unfold isDiagonalVertex at hr; simp_all +decide ;
          · linarith! [ shuffle_step μ ⟨ r, by linarith ⟩ ]
        generalize_proofs at *;
        have h_left_step : (μ.1 ⟨r.val + 1, by
          grind⟩).1.val = (μ.1 r).1.val + 1 := by
          have := shuffle_step μ ⟨ r.val, by
            linarith [ Fin.is_lt r ] ⟩
          generalize_proofs at *;
          unfold isDiagonalVertex at hr; simp_all +decide [ isLeftStep ] ; omega;
        generalize_proofs at *;
        -- By definition of `swapDiagonalSteps_fun`, we need to consider the two cases for the diagonal vertex. Since `hL` is false, we have `¬isLeftStep μ ⟨r.val - 1, by sorry⟩`.
        have h_swap : swapDiagonalSteps_fun μ r hr r = (⟨(μ.1 r).1.val + 1, by
          grind⟩, ⟨(μ.1 r).2.val - 1, by
          grind⟩) := by
          -- By definition of swapDiagonalSteps_fun, when i = r and hL is false, we have:
          simp [swapDiagonalSteps_fun, hL];
          generalize_proofs at *;
          -- `grind` fails: the goal is a stuck `match` on a conjunction proof term
          -- that `grind` can't reduce. `split` evaluates the match, then both sides
          -- have equal `val`s so `Fin.ext rfl` closes each component.
          split; exact Prod.ext (Fin.ext rfl) (Fin.ext rfl)
        generalize_proofs at *;
        constructor <;> simp_all +decide [ Prod.le_def ];
        · exact Nat.le_succ_of_le ( μ.1.monotone ( Nat.pred_le _ ) |> And.left );
        · constructor
          · simp only [Fin.le_iff_val_le_val]; omega
          -- `by omega` alone fails: omega doesn't reduce `Fin.le` to `val ≤ val`,
          -- so we `simp [Fin.le_def]` first to expose the ℕ comparison.
          · exact μ.1.monotone (show _ ≤ _ by simp [Fin.le_def]; omega) |>.2

end AristotleLemmas

private lemma swapDiagonalSteps_fun_monotone {p q : ℕ}
    (μ : Shuffle (p + 1) (q + 1)) (r : Index (p + 1 + (q + 1)))
    (hr : isDiagonalVertex μ r) :
    Monotone (swapDiagonalSteps_fun μ r hr) := by
  -- Let's unfold the definition of `swapDiagonalSteps_fun`.
  unfold swapDiagonalSteps_fun;
  intro i j hij; by_cases hi : i = r <;> by_cases hj : j = r <;> simp +decide [ hi, hj ] at hij ⊢;
  · have h_swap_diag : swapDiagonalSteps_fun μ r hr r ≤ μ.1 j := by
      have h_swap_diag : swapDiagonalSteps_fun μ r hr r ≤ μ.1 ⟨r.val + 1, by
        grind⟩ := by
        exact swapDiagonalSteps_fun_local_bounds μ r hr |>.2
      generalize_proofs at *;
      refine' le_trans h_swap_diag _;
      exact μ.1.monotone ( Nat.succ_le_of_lt ( hij.lt_of_ne' hj ) );
    unfold swapDiagonalSteps_fun at h_swap_diag; simp_all +decide [ Fin.ext_iff ] ;
  · have := swapDiagonalSteps_fun_local_bounds μ r hr;
    convert this.1.trans' _ using 1;
    · unfold HomologyLean.SingularHomology.Shuffle.swapDiagonalSteps_fun; aesop;
    · exact μ.1.monotone ( Nat.le_pred_of_lt ( hij.lt_of_ne hi ) );
  · exact μ.1.monotone hij

/-- `swapDiagonalSteps_fun` is injective.  Follows from monotonicity +
coordinate-sum preservation (same argument as for `insertLeftStep`). -/
private lemma swapDiagonalSteps_fun_injective {p q : ℕ}
    (μ : Shuffle (p + 1) (q + 1)) (r : Index (p + 1 + (q + 1)))
    (hr : isDiagonalVertex μ r) :
    Function.Injective (swapDiagonalSteps_fun μ r hr) := by
  intros i j hij; have := swapDiagonalSteps_fun_coordSum μ r hr i; have := swapDiagonalSteps_fun_coordSum μ r hr j; aesop;


/-- The sign-reversing involution on diagonal terms.  Given a `(p+1, q+1)`-shuffle
`μ` and a diagonal vertex `r`, swap the steps adjacent to `r` (replacing an LR
corner with RL or vice versa).  This produces a new shuffle `μ'` such that:
- `μ' ∘ δ_r = μ ∘ δ_r` (same underlying map after vertex removal)
- `μ'.sign = -μ.sign` (opposite sign, from the inversion count change) -/
def swapDiagonalSteps {p q : ℕ} (μ : Shuffle (p + 1) (q + 1))
    (r : Index (p + 1 + (q + 1))) (hr : isDiagonalVertex μ r) :
    Shuffle (p + 1) (q + 1) :=
  ⟨⟨swapDiagonalSteps_fun μ r hr, swapDiagonalSteps_fun_monotone μ r hr⟩,
   swapDiagonalSteps_fun_injective μ r hr⟩

/- The swap involution preserves the diagonal vertex property. -/
noncomputable section AristotleLemmas

/-
For any index `i` different from the diagonal vertex `r`, the shuffle map `swapDiagonalSteps` has the same value as the original shuffle `μ`. This follows directly from the definition of `swapDiagonalSteps_fun`, which uses an `if i = r` condition.
-/
open HomologyLean.SingularHomology

lemma swapDiagonalSteps_apply_ne {p q : ℕ} (μ : Shuffle (p + 1) (q + 1))
    (r : Index (p + 1 + (q + 1))) (hr : isDiagonalVertex μ r)
    (i : Index (p + 1 + (q + 1))) (hi : i ≠ r) :
    (swapDiagonalSteps μ r hr).1 i = μ.1 i := by
      -- Since $i \neq r$, the else part of the definition of `swapDiagonalSteps_fun` applies.
      simp [swapDiagonalSteps, hi];
      unfold HomologyLean.SingularHomology.Shuffle.swapDiagonalSteps_fun; aesop;

/-
If the step entering the diagonal vertex `r` is a Left step, then `swapDiagonalSteps` modifies the value at `r` by decrementing the first coordinate and incrementing the second. This corresponds to the `then` branch of `swapDiagonalSteps_fun`.
-/
open HomologyLean.SingularHomology

lemma swapDiagonalSteps_apply_r_of_left {p q : ℕ} (μ : Shuffle (p + 1) (q + 1))
    (r : Index (p + 1 + (q + 1))) (hr : isDiagonalVertex μ r)
    (hL : isLeftStep μ ⟨r.val - 1, by have := (isDiagonalVertex_bounds hr).2; omega⟩) :
    (swapDiagonalSteps μ r hr).1 r =
      (⟨(μ.1 r).1.val - 1, by
        exact Nat.lt_succ_of_le ( Nat.sub_le_of_le_add <| by linarith [ Fin.is_lt ( μ.1 r |>.1 ) ] )⟩, ⟨(μ.1 r).2.val + 1, by
        -- Since the second component of `μ r` is in `Fin (q + 1)`, its value is between 0 and q.
        have h_snd_range : (μ.1 r).2.val < q + 1 := by
          have h_snd_lt : (μ.1 r).2.val < q + 1 := by
            have h_not_left : ¬isLeftStep μ ⟨r.val, (isDiagonalVertex_bounds hr).2⟩ := by
              unfold isDiagonalVertex at hr; simp [hL] at hr; tauto;
            have h_step := shuffle_step μ ⟨r.val, (isDiagonalVertex_bounds hr).2⟩
            generalize_proofs at *;
            unfold isLeftStep at h_not_left; simp_all +decide [ Fin.castSucc, Fin.succ ] ; omega;
          generalize_proofs at *;
          exact h_snd_lt.trans_le ( Nat.le_refl _ ) |> lt_of_lt_of_le <| Nat.le_refl _;
        linarith [h_snd_range]⟩) := by
        exact if_pos rfl |> fun h => h.trans ( by aesop )

/-
If the step entering the diagonal vertex `r` is a Right step (not Left), then `swapDiagonalSteps` modifies the value at `r` by incrementing the first coordinate and decrementing the second. This corresponds to the `else` branch of `swapDiagonalSteps_fun`.
-/
open HomologyLean.SingularHomology

lemma swapDiagonalSteps_apply_r_of_right {p q : ℕ} (μ : Shuffle (p + 1) (q + 1))
    (r : Index (p + 1 + (q + 1))) (hr : isDiagonalVertex μ r)
    (hR : ¬ isLeftStep μ ⟨r.val - 1, by have := (isDiagonalVertex_bounds hr).2; omega⟩) :
    (swapDiagonalSteps μ r hr).1 r =
      (⟨(μ.1 r).1.val + 1, by
        -- By definition of `isDiagonalVertex`, we know that `isLeftStep μ ⟨r.val, h₂⟩` is false.
        unfold isDiagonalVertex at hr; simp_all +decide [ Fin.ext_iff ];
        split_ifs at hr ; simp_all +decide [ isLeftStep ];
        grind⟩, ⟨(μ.1 r).2.val - 1, by
        exact Nat.lt_succ_of_le ( Nat.sub_le_of_le_add <| by linarith [ Fin.is_lt ( μ.1 r |>.2 ) ] )⟩) := by
        unfold HomologyLean.SingularHomology.Shuffle.swapDiagonalSteps
        generalize_proofs at *;
        unfold HomologyLean.SingularHomology.Shuffle.swapDiagonalSteps_fun; aesop;

/-
The step entering the diagonal vertex `r` (index `r-1`) flips its type (Left ↔ Right) under `swapDiagonalSteps`.
Proof sketch:
1. Let `i = r-1`. We compare `(μ'.1 i).1` and `(μ'.1 (i+1)).1`.
2. `μ'.1 i = μ.1 i` since `i ≠ r` (as `r > 0`).
3. `μ'.1 (i+1) = μ'.1 r`.
4. If `isLeftStep μ i` is true (Left step):
   - `(μ.1 i).1 + 1 = (μ.1 r).1`.
   - `(μ'.1 r).1 = (μ.1 r).1 - 1` (by `swapDiagonalSteps_apply_r_of_left`).
   - So `(μ'.1 r).1 = (μ.1 i).1`.
   - Thus `isLeftStep μ' i` is false.
5. If `isLeftStep μ i` is false (Right step):
   - `(μ.1 i).1 = (μ.1 r).1`.
   - `(μ'.1 r).1 = (μ.1 r).1 + 1` (by `swapDiagonalSteps_apply_r_of_right`).
   - So `(μ'.1 i).1 < (μ'.1 r).1`.
   - Thus `isLeftStep μ' i` is true.
-/
open HomologyLean.SingularHomology

lemma swapDiagonalSteps_flip_prev {p q : ℕ} (μ : Shuffle (p + 1) (q + 1))
    (r : Index (p + 1 + (q + 1))) (hr : isDiagonalVertex μ r) :
    isLeftStep (swapDiagonalSteps μ r hr) ⟨r.val - 1, by have := (isDiagonalVertex_bounds hr).2; omega⟩ ↔
    ¬ isLeftStep μ ⟨r.val - 1, by have := (isDiagonalVertex_bounds hr).2; omega⟩ := by
      unfold isLeftStep
      generalize_proofs at *;
      by_cases hL : isLeftStep μ ⟨ r.val - 1, by have := ( isDiagonalVertex_bounds hr ).2; omega ⟩ <;> simp_all +decide [ swapDiagonalSteps_apply_ne ];
      · rcases r with ⟨ _ | r, hr ⟩ <;> simp_all +decide [ isLeftStep ];
        · exact?;
        · rw [ swapDiagonalSteps_apply_r_of_left ] <;> norm_num [ hL ];
          · constructor <;> intro h <;> contrapose! h;
            · convert Nat.le_refl _ using 1;
              rotate_left;
              exact ( μ.1 ⟨ r + 1, by linarith ⟩ |>.1 : ℕ ) - 1
              (generalize_proofs at *; (simp_all +decide [ Fin.le_def, Nat.le_sub_one_of_lt ] ) ;);
              rw [ swapDiagonalSteps_apply_ne ] <;> norm_num [ h ];
              have := shuffle_step μ ⟨ r, by linarith ⟩ ; aesop;
            · exact hL
              skip;
          · exact hL;
      · rcases r with ⟨ _ | r, hr ⟩ <;> simp_all +decide [ Nat.succ_eq_add_one ];
        · unfold isDiagonalVertex at hr; simp_all +decide [ Nat.succ_eq_add_one ] ;
          grind +ring;
        · -- Since `hL` states that `isLeftStep μ ⟨r, by omega⟩` is false, we have `(μ.1 ⟨r, by omega⟩).1 = (μ.1 ⟨r + 1, by omega⟩).1`.
          have h_eq : (μ.1 ⟨r, by omega⟩).1 = (μ.1 ⟨r + 1, by omega⟩).1 := by
            -- Since `hL` states that `isLeftStep μ ⟨r, by omega⟩` is false, we have `(μ.1 ⟨r, by omega⟩).1 = (μ.1 ⟨r + 1, by omega⟩).1` by definition of `isLeftStep`.
            simp [HomologyLean.SingularHomology.Shuffle.isLeftStep] at hL ⊢
            generalize_proofs at *; (
            exact le_antisymm ( by simpa using μ.1.monotone ( show ⟨ r, by omega ⟩ ≤ ⟨ r + 1, by omega ⟩ from Nat.le_succ _ ) |> And.left ) hL
            skip)
          generalize_proofs at *; (
          rw [ swapDiagonalSteps_apply_ne, swapDiagonalSteps_apply_r_of_right ] <;> simp_all +decide [ Fin.le_def ];
          exact Nat.lt_succ_self _)

/-
The step leaving the diagonal vertex `r` (index `r`) flips its type (Left ↔ Right) under `swapDiagonalSteps`.
Proof sketch:
1. Let `i = r`. We compare `isLeftStep μ' i` with `isLeftStep μ i`.
2. `μ'.1 (i+1) = μ.1 (i+1)` since `i+1 ≠ r`.
3. `μ'.1 i` is given by `swapDiagonalSteps_apply_r_of_left` or `_right`.
4. If `isLeftStep μ (r-1)` is true (Left incoming):
   - `μ` has Left at `r-1`. Since `r` is diagonal, `μ` must have Right at `r`.
   - So `isLeftStep μ r` is false.
   - We want to show `isLeftStep μ' r` is true.
   - `μ'.1 r = (μ.1 r).1 - 1`.
   - `μ.1 (r+1) = (μ.1 r).1` (since step `r` is Right).
   - So `(μ'.1 r).1 < (μ'.1 (r+1)).1` becomes `(μ.1 r).1 - 1 < (μ.1 r).1`, which is true.
5. If `isLeftStep μ (r-1)` is false (Right incoming):
   - `μ` has Right at `r-1`. Since `r` is diagonal, `μ` must have Left at `r`.
   - So `isLeftStep μ r` is true.
   - We want to show `isLeftStep μ' r` is false.
   - `μ'.1 r = (μ.1 r).1 + 1`.
   - `μ.1 (r+1) = (μ.1 r).1 + 1` (since step `r` is Left).
   - So `(μ'.1 r).1 < (μ'.1 (r+1)).1` becomes `(μ.1 r).1 + 1 < (μ.1 r).1 + 1`, which is false.
-/
open HomologyLean.SingularHomology

lemma swapDiagonalSteps_flip_curr {p q : ℕ} (μ : Shuffle (p + 1) (q + 1))
    (r : Index (p + 1 + (q + 1))) (hr : isDiagonalVertex μ r) :
    isLeftStep (swapDiagonalSteps μ r hr) ⟨r.val, by have := (isDiagonalVertex_bounds hr).2; omega⟩ ↔
    ¬ isLeftStep μ ⟨r.val, by have := (isDiagonalVertex_bounds hr).2; omega⟩ := by
      unfold HomologyLean.SingularHomology.Shuffle.isLeftStep
      generalize_proofs at *;
      by_cases h : isLeftStep μ ⟨r.val - 1, by
        exact lt_of_le_of_lt ( Nat.pred_le _ ) ‹_›⟩
      all_goals generalize_proofs at *;
      · have h_step : (μ.1 (Fin.succ ⟨r.val, by
          assumption⟩)).1.val = (μ.1 ⟨r.val, by
          grind⟩).1.val := by
          have := shuffle_step μ ⟨r.val, by
            assumption⟩
          generalize_proofs at *;
          unfold isDiagonalVertex at hr; simp_all +decide [ Fin.ext_iff, Fin.val_add, Fin.val_one, Fin.val_zero ] ;
          unfold Shuffle.isLeftStep at hr; simp_all +decide [ Fin.ext_iff, Fin.val_add, Fin.val_one, Fin.val_zero ] ;
          grind
        generalize_proofs at *;
        have := swapDiagonalSteps_apply_r_of_left μ r hr h; simp_all +decide [ Fin.castSucc, Fin.succ ] ;
        convert Nat.sub_lt ( diagonal_left_fst_pos hr h ) zero_lt_one using 1
        generalize_proofs at *;
        convert h_step using 1
        generalize_proofs at *; (
        exact congr_arg Fin.val ( swapDiagonalSteps_apply_ne μ r hr ⟨ r.val + 1, by omega ⟩ ( by simp +decide [ Fin.ext_iff ] ) |> congr_arg Prod.fst ) |> Eq.trans <| rfl
        skip);
      · simp_all +decide [ Fin.castSucc, Fin.succ ];
        rw [ show ( μ.swapDiagonalSteps r hr : HomologyLean.SingularHomology.Index ( p + 1 + ( q + 1 ) ) →o HomologyLean.SingularHomology.Index ( p + 1 ) × HomologyLean.SingularHomology.Index ( q + 1 ) ) r = ( ⟨ ( μ.1 r ).1.val + 1, by
              unfold HomologyLean.SingularHomology.Shuffle.isDiagonalVertex at hr; simp_all +decide [ Fin.castSucc, Fin.succ ] ;
              have := μ.1 r |>.1.isLt; have := μ.1 r |>.2.isLt; simp_all +arith +decide [ HomologyLean.SingularHomology.Shuffle.isLeftStep ] ;
              grind ⟩, ⟨ ( μ.1 r ).2.val - 1, by
              exact Nat.lt_succ_of_le ( Nat.sub_le_of_le_add <| by linarith [ Fin.is_lt ( μ.1 r |>.2 ) ] ) ⟩ ) from ?_ ]
        all_goals generalize_proofs at *;
        · rw [ show ( μ.swapDiagonalSteps r hr : HomologyLean.SingularHomology.Index ( p + 1 + ( q + 1 ) ) →o HomologyLean.SingularHomology.Index ( p + 1 ) × HomologyLean.SingularHomology.Index ( q + 1 ) ) ⟨ r.val + 1, by linarith ⟩ = μ.1 ⟨ r.val + 1, by linarith ⟩ from ?_ ];
          · rw [ Fin.lt_iff_val_lt_val, Fin.le_iff_val_le_val ] ; simp +arith +decide [ * ];
            constructor <;> intro <;> norm_cast at * <;> simp_all +decide [ Nat.succ_le_iff ];
            · unfold isDiagonalVertex at hr; simp_all +decide [ Nat.succ_le_iff ] ;
              exact le_of_not_gt fun h => h.not_ge <| by have := shuffle_step μ ⟨ r, by linarith ⟩ ; unfold isLeftStep at hr; aesop;
            · unfold isDiagonalVertex at hr; simp_all +decide [ Nat.succ_le_iff ] ;
              exact absurd ‹_› ( not_le_of_gt hr.2 );
          · exact swapDiagonalSteps_apply_ne _ _ _ _ ( ne_of_gt ( Nat.lt_succ_self _ ) );
        · exact?

end AristotleLemmas

lemma swapDiagonalSteps_vertex {p q : ℕ}
    (μ : Shuffle (p + 1) (q + 1)) (r : Index (p + 1 + (q + 1)))
    (hr : isDiagonalVertex μ r) :
    isDiagonalVertex (swapDiagonalSteps μ r hr) r := by
  unfold isDiagonalVertex at *; simp_all +decide [ isLeftStep ] ;
  split_ifs at hr ; simp_all +decide [ isLeftStep ] ;
  -- Apply the lemmas swapDiagonalSteps_flip_prev and swapDiagonalSteps_flip_curr to show that the step types are different.
  have h_diff : ¬isLeftStep (swapDiagonalSteps μ r ‹_›) ⟨r.val - 1, by have := (isDiagonalVertex_bounds ‹_›).2; omega⟩ ∧ isLeftStep (swapDiagonalSteps μ r ‹_›) ⟨r.val, by have := (isDiagonalVertex_bounds ‹_›).2; omega⟩ ∨ isLeftStep (swapDiagonalSteps μ r ‹_›) ⟨r.val - 1, by have := (isDiagonalVertex_bounds ‹_›).2; omega⟩ ∧ ¬isLeftStep (swapDiagonalSteps μ r ‹_›) ⟨r.val, by have := (isDiagonalVertex_bounds ‹_›).2; omega⟩ := by
    have := swapDiagonalSteps_flip_prev μ r ‹_›; have := swapDiagonalSteps_flip_curr μ r ‹_›; simp_all +decide [ isLeftStep ] ;
  generalize_proofs at *; (
  cases h_diff <;> simp_all +decide [ isLeftStep ])


/- The swap is an involution. -/
noncomputable section AristotleLemmas

/-
The `swapDiagonalSteps` map agrees with the original shuffle at all indices other than `r`.
-/
open HomologyLean.SingularHomology

lemma swapDiagonalSteps_apply_ne_r {p q : ℕ}
    (μ : Shuffle (p + 1) (q + 1)) (r : Index (p + 1 + (q + 1)))
    (hr : isDiagonalVertex μ r) (i : Index (p + 1 + (q + 1))) (h : i ≠ r) :
    (swapDiagonalSteps μ r hr).1 i = μ.1 i := by
      unfold HomologyLean.SingularHomology.Shuffle.swapDiagonalSteps;
      unfold HomologyLean.SingularHomology.Shuffle.swapDiagonalSteps_fun; aesop;

/-
The value of the swapped shuffle at the diagonal vertex `r` is given by decrementing/incrementing coordinates based on the step type.
-/
open HomologyLean.SingularHomology

lemma swapDiagonalSteps_val_r {p q : ℕ}
    (μ : Shuffle (p + 1) (q + 1)) (r : Index (p + 1 + (q + 1)))
    (hr : isDiagonalVertex μ r)
    (rm1 : Fin ((p + 1) + (q + 1)))
    (h_rm1 : rm1.val = r.val - 1) :
    (swapDiagonalSteps μ r hr).1 r =
      if h : isLeftStep μ rm1 then
        (⟨(μ.1 r).1.val - 1, by
          grind⟩, ⟨(μ.1 r).2.val + 1, by
          have h_snd_lt : ¬isLeftStep μ ⟨r.val, by have := (isDiagonalVertex_bounds hr).2; omega⟩ := by
            have h_snd_lt : ¬isLeftStep μ ⟨r.val, by have := (isDiagonalVertex_bounds hr).2; omega⟩ := by
              have := hr
              unfold isDiagonalVertex at this
              have h_snd_lt : isLeftStep μ ⟨r.val - 1, by have := (isDiagonalVertex_bounds hr).2; omega⟩ := by
                convert h using 1
                generalize_proofs at *; (
                exact Fin.ext ( by aesop ) ;)
              generalize_proofs at *; (
              split_ifs at this ; tauto;)
            (generalize_proofs at *; (
            exact h_snd_lt))
          generalize_proofs at *; (
          have hstep := shuffle_step μ ⟨r.val, by have := (isDiagonalVertex_bounds hr).2; omega⟩
          generalize_proofs at *; (
          unfold isLeftStep at h_snd_lt; simp_all +decide [ Fin.castSucc, Fin.succ ] ; omega;))⟩)
      else
        (⟨(μ.1 r).1.val + 1, by
          convert Nat.lt_succ_of_le ( Fin.is_le _ ) using 1;
          convert rfl;
          convert Fin.val_cast_of_lt _;
          · infer_instance;
          · contrapose! h;
            unfold isDiagonalVertex at hr; simp_all +decide [ isLeftStep ] ;
            rw [ show rm1.castSucc = ⟨ r.val - 1, by omega ⟩ from ?_, show rm1.succ = r from ?_ ];
            · grind;
            · exact Fin.ext ( by simp +decide [ h_rm1, Nat.sub_add_cancel ( show 1 ≤ ( r : ℕ ) from Nat.pos_of_ne_zero ( by aesop_cat ) ) ] );
            · exact Fin.ext h_rm1⟩, ⟨(μ.1 r).2.val - 1, by
          exact Nat.lt_succ_of_le ( Nat.sub_le_of_le_add <| by linarith [ Fin.is_lt ( μ.1 r |>.2 ) ] )⟩) := by
          -- By definition of swapDiagonalSteps, applying it twice returns the original shuffle.
          simp [swapDiagonalSteps, swapDiagonalSteps_fun] at *; (
          have h_if_eq : (isLeftStep μ ⟨r.val - 1, by have := (isDiagonalVertex_bounds hr).2; omega⟩) = (isLeftStep μ rm1) := by
            exact congr_arg _ ( Fin.ext <| by simp +decide [ h_rm1 ] )
          generalize_proofs at *; (
          split_ifs <;> aesop ( simp_config := { singlePass := true } ) ;))

/-
The `swapDiagonalSteps` involution toggles the type (Left/Right) of the step immediately preceding the diagonal vertex `r`.
-/
open HomologyLean.SingularHomology

lemma swapDiagonalSteps_isLeftStep_toggle {p q : ℕ}
    (μ : Shuffle (p + 1) (q + 1)) (r : Index (p + 1 + (q + 1)))
    (hr : isDiagonalVertex μ r) :
    let rm1 : Fin ((p + 1) + (q + 1)) := ⟨r.val - 1, by
      unfold isDiagonalVertex at hr
      split_ifs at hr
      omega⟩
    isLeftStep (swapDiagonalSteps μ r hr) rm1 ↔ ¬ isLeftStep μ rm1 := by
      have hswap := swapDiagonalSteps_val_r μ r hr ⟨r.val - 1, by omega⟩ rfl
      generalize_proofs at *;
      split_ifs at hswap <;> simp_all +decide [ Shuffle.isLeftStep ];
      · convert iff_of_false ?_ ?_ using 1
        all_goals generalize_proofs at *;
        · rw [ swapDiagonalSteps_apply_ne_r ] <;> norm_num [ * ];
          · rcases r with ⟨ _ | r, hr ⟩ <;> norm_num at *;
            · simp_all +decide [ Shuffle.apply_zero ];
            · simp_all +decide [ Fin.ext_iff, Fin.val_add, Fin.val_one, Fin.val_zero, Nat.mod_eq_of_lt ];
              exact Nat.sub_le_of_le_add <| by linarith! [ show ( μ.1 ⟨ r + 1, by linarith ⟩ |>.1 : ℕ ) ≤ ( μ.1 ⟨ r, by linarith ⟩ |>.1 : ℕ ) + 1 from by
                                                            have := shuffle_step μ ⟨ r, by linarith ⟩ ; aesop; ] ;
          · exact ne_of_lt ( Nat.pred_lt ( ne_bot_of_gt ( isDiagonalVertex_bounds hr |>.1 ) ) );
        · cases r ; aesop
          skip;
      · rw [ swapDiagonalSteps_apply_ne_r μ r hr ⟨ r.val - 1, by omega ⟩ ( by
          rcases r with ⟨ _ | r, hr ⟩ <;> norm_num at *;
          unfold Shuffle.isDiagonalVertex at hr ; aesop ( simp_config := { decide := true } ) ; ) ]
        generalize_proofs at *;
        rcases r with ⟨ _ | r, hr ⟩ <;> simp_all +decide [ Nat.succ_eq_add_one ];
        · exact?;
        · unfold Shuffle.isLeftStep at * ; simp_all +decide [ Fin.ext_iff, Fin.val_add ];
          exact Nat.lt_succ_of_le ( by exact le_trans ( by aesop ) ( μ.1.monotone ( Nat.le_succ _ ) |>.1 ) )

end AristotleLemmas

lemma swapDiagonalSteps_involutive {p q : ℕ}
    (μ : Shuffle (p + 1) (q + 1)) (r : Index (p + 1 + (q + 1)))
    (hr : isDiagonalVertex μ r) :
    swapDiagonalSteps (swapDiagonalSteps μ r hr) r
      (swapDiagonalSteps_vertex μ r hr) = μ := by
  refine' ( ExistsUnique.unique _ _ _ );
  use fun x => x.1 = μ.1;
  · use μ; aesop;
  · -- By definition of swapDiagonalSteps, we know that applying it twice returns the original shuffle.
    have h_swap : ∀ i : Index ((p + 1) + (q + 1)), (swapDiagonalSteps (swapDiagonalSteps μ r hr) r (swapDiagonalSteps_vertex μ r hr)).1 i = μ.1 i := by
      intro i; by_cases hi : i = r <;> simp +decide [ hi, swapDiagonalSteps_apply_ne_r ] ;
      let rm1 : Fin ((p + 1) + (q + 1)) := ⟨r.val - 1, by
        have := isDiagonalVertex_bounds hr
        omega⟩
      have h₁ := swapDiagonalSteps_val_r μ r hr rm1 rfl
      have h₂ := swapDiagonalSteps_val_r (swapDiagonalSteps μ r hr) r (swapDiagonalSteps_vertex μ r hr) rm1 rfl
      have htoggle : isLeftStep (swapDiagonalSteps μ r hr) rm1 ↔ ¬ isLeftStep μ rm1 := by
        simpa [rm1] using swapDiagonalSteps_isLeftStep_toggle μ r hr
      by_cases hL : isLeftStep μ rm1
      · have hS : ¬ isLeftStep (swapDiagonalSteps μ r hr) rm1 := by
          exact fun hs => (htoggle.mp hs) hL
        rw [h₂]
        simp [rm1, hL, hS, h₁]
        exact Prod.ext (Fin.ext <| Nat.sub_add_cancel <| Nat.pos_of_ne_zero <| by
          have := diagonal_left_fst_pos hr (by simpa [rm1] using hL)
          aesop) rfl
      · have hS : isLeftStep (swapDiagonalSteps μ r hr) rm1 := by
          exact htoggle.mpr hL
        rw [h₂]
        simp [rm1, hL, hS, h₁]
        exact Prod.ext rfl (Fin.ext <| Nat.sub_add_cancel <| Nat.pos_of_ne_zero <| by
          have := diagonal_right_snd_pos hr (by simpa [rm1] using hL)
          aesop)
    aesop;
  · rfl

/-- The swap preserves the underlying OrderHom when composed with any OrderHom
that avoids the diagonal vertex. -/
lemma swapDiagonalSteps_same_map {p q n : ℕ}
    (μ : Shuffle (p + 1) (q + 1)) (r : Index (p + 1 + (q + 1)))
    (hr : isDiagonalVertex μ r) (φ : Fin n →o Index (p + 1 + (q + 1)))
    (hφ : ∀ k, φ k ≠ r) :
    (swapDiagonalSteps μ r hr).1.comp φ = μ.1.comp φ := by
  have h_swap_fun : ∀ i : Fin n, swapDiagonalSteps_fun μ r hr (φ i) = μ.1 (φ i) := by
    intro i; unfold swapDiagonalSteps_fun; aesop;
  ext i; simp [h_swap_fun];
  · exact congr_arg Fin.val ( congr_arg Prod.fst ( h_swap_fun i ) );
  · exact congr_arg Fin.val ( congr_arg Prod.snd ( h_swap_fun i ) )


/-- The swap negates the signed coefficient. -/
lemma swapDiagonalSteps_neg_sign {p q : ℕ}
    (μ : Shuffle (p + 1) (q + 1)) (r : Index (p + 1 + (q + 1)))
    (hr : isDiagonalVertex μ r) :
    (swapDiagonalSteps μ r hr).sign  =
    -(μ.sign) := by
  sorry

/-- The swap involution is never the identity: swapping two steps of different
type always produces a distinct shuffle. -/
lemma swapDiagonalSteps_ne {p q : ℕ}
    (μ : Shuffle (p + 1) (q + 1)) (r : Index (p + 1 + (q + 1)))
    (hr : isDiagonalVertex μ r) :
    swapDiagonalSteps μ r hr ≠ μ := by
  apply mt (congrArg Shuffle.sign)
  rw [swapDiagonalSteps_neg_sign]
  simpa [Shuffle.sign] using
    (CharZero.neg_eq_self_iff (R := ℤ) (a := (-1 : ℤ) ^ μ.invCount)).not.2
      (pow_ne_zero _ (show (-1 : ℤ) ≠ 0 by decide))



end Shuffle

end HomologyLean.SingularHomology
