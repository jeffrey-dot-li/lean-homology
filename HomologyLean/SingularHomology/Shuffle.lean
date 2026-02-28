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

end Shuffle

end HomologyLean.SingularHomology
