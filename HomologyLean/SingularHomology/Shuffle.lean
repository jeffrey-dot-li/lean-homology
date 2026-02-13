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
  -- First: `OrderHom` between finite types is finite, by injecting into plain functions.
  have : Finite (Index (p + q) →o (Index p × Index q)) := by
    classical
    -- codomain is finite because it's a function type on fintypes
    refine Finite.of_injective (fun f : Index (p + q) →o (Index p × Index q) => f.toFun) ?_
    intro f g h
    ext x
    repeat simp at h; simp [h]
  -- Then `Shuffle p q` is a subtype of that finite type, hence finite; turn it into a `Fintype`.
  exact Fintype.ofFinite (Shuffle p q)

-- TODO: Actually show order is Nat.choose (p + q) p
/-- The **number of inversions** of a shuffle.

We view a shuffle `μ : Shuffle p q` as a monotone injective map
`Index (p+q) → Index p × Index q`, i.e. a monotone lattice path from `(0,0)` to `(p,q)`.

For a valid lattice path shuffle, each of the `(p+q)` steps increments exactly one coordinate.
An inversion is a pair consisting of a `q`-step occurring before a `p`-step; equivalently,
\(k = \sum\) (current `q`-coordinate) over all `p`-steps. -/
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
  -- Transport the domain `Index (q+p)` to `Index (p+q)` along commutativity of addition.
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
      -- `Prod.swap` is an involution, so swapping both sides recovers the original equality.
      simpa using congrArg Prod.swap hab
    have : e a = e b := μ.2 hab'
    exact e.injective this

@[simp]
theorem swap_swap {p q : ℕ} (μ : Shuffle p q) : swap (swap μ) = μ := by
  classical
  -- equality of subtypes reduces to equality of the underlying order homs
  apply Subtype.ext
  ext x
  repeat simp [swap]

/-- Swapping coordinates gives an equivalence `Shuffle p q ≃ Shuffle q p`. -/
def swapEquiv (p q : ℕ) : Shuffle p q ≃ Shuffle q p where
  toFun := swap
  invFun := swap
  left_inv μ := by simp
  right_inv μ := by simp

/-- Swapping a `(p,q)`-shuffle changes the sign by the Koszul factor `(-1)^(p*q)`. -/
theorem sign_eq_negOnePow_mul_swap_sign {p q : ℕ} (u : Shuffle p q) :
    u.sign = (-1 : ℤ) ^ (p * q) * (u.swap).sign := by
  sorry

end Shuffle

end HomologyLean.SingularHomology
