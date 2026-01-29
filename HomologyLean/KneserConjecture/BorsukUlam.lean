/-
Copyright (c) 2025 Sebastian Kumar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Kumar
-/

import Mathlib.Topology.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Topology.MetricSpace.HausdorffDistance
import Mathlib.Analysis.Normed.Lp.PiLp

/-!
# Borsuk-Ulam Theorem

This file contains the Borsuk-Ulam theorem and related definitions about spheres
and antipodal points.

## Main Definitions

* `Sphere n`: The n-dimensional sphere in ℝⁿ⁺¹
* `Antipodal x y`: Two points on the sphere are antipodal if y = -x
* `HasAntipodalPair F`: A set F contains an antipodal pair
* `antipode x`: The antipodal point of x on the sphere

## Main Results

* `borsuk_ulam`: Any continuous map from Sⁿ to ℝⁿ sends some pair of antipodal points
  to the same point
* `borsuk_covering`: If Sⁿ is covered by n + 1 closed sets, at least one contains
  an antipodal pair

## References

* Borsuk, K. "Drei Sätze über die n-dimensionale euklidische Sphäre",
  Fundamenta Mathematicae 20 (1933), 177-190.
-/

noncomputable section

namespace Borsuk

/-- The n-dimensional sphere in ℝⁿ⁺¹ -/
def Sphere (n : ℕ) : Set (EuclideanSpace ℝ (Fin (n + 1))) :=
  Metric.sphere 0 1

/-- Two points on the sphere are antipodal if one is the negation of the other -/
def Antipodal {n : ℕ} (x y : Sphere n) : Prop :=
  y.1 = -x.1

/-- A set contains an antipodal pair if there exists x such that both x and -x are in the set -/
def HasAntipodalPair {n : ℕ} (F : Set (Sphere n)) : Prop :=
  ∃ x : Sphere n, x ∈ F ∧ ∃ y : Sphere n, y ∈ F ∧ Antipodal x y

/-- The antipodal point of x on the sphere -/
def antipode {n : ℕ} (x : Sphere n) : Sphere n :=
  ⟨-x.1, by
    simp only [Sphere, Metric.mem_sphere, dist_zero_right, norm_neg]
    have hx := x.2
    simp only [Sphere, Metric.mem_sphere, dist_zero_right] at hx
    exact hx⟩

/-- **Borsuk-Ulam Theorem**: Any continuous map from Sⁿ to ℝⁿ sends some pair of
antipodal points to the same point. -/
theorem borsuk_ulam {n : ℕ} (f : Sphere n → EuclideanSpace ℝ (Fin n))
    (hf : Continuous f) :
    ∃ x : Sphere n, f x = f (antipode x) := by
  sorry

/-- **Borsuk's Theorem (Covering Version)**: If the n-sphere Sⁿ is covered by n + 1 closed sets,
then at least one of the sets contains a pair of antipodal points.

This is equivalent to the Borsuk-Ulam theorem and is the key topological input for
Lovász's proof of Kneser's conjecture. -/
theorem borsuk_covering {n : ℕ} (F : Fin (n + 1) → Set (Sphere n))
    (hClosed : ∀ i, IsClosed (F i))
    (hCover : ∀ x : Sphere n, ∃ i, x ∈ F i) :
    ∃ i, HasAntipodalPair (F i) := by
  -- Define f : Sⁿ → ℝⁿ by f(x)ᵢ = infDist x (F i) for i < n
  let f : Sphere n → EuclideanSpace ℝ (Fin n) := fun x =>
    WithLp.toLp 2 (fun i => Metric.infDist x (F i.castSucc))
  -- f is continuous
  have hf : Continuous f := by
    apply (PiLp.continuous_toLp 2 (fun _ : Fin n => ℝ)).comp
    exact continuous_pi fun i => Metric.continuous_infDist_pt _
  -- By Borsuk-Ulam, there exists x such that f(x) = f(antipode x)
  obtain ⟨x, hx⟩ := borsuk_ulam f hf
  -- So infDist x (F i) = infDist (antipode x) (F i) for all i < n
  have h_eq : ∀ i : Fin n, Metric.infDist x (F i.castSucc) =
      Metric.infDist (antipode x) (F i.castSucc) := by
    intro i
    have := congrArg (WithLp.ofLp) hx
    exact congrFun this i
  -- Case analysis: either x ∈ F i for some i < n, or x ∈ F n
  by_cases h : ∃ i : Fin n, x ∈ F i.castSucc
  · -- Case 1: x ∈ F i for some i < n
    obtain ⟨i, hxi⟩ := h
    use i.castSucc
    refine ⟨x, hxi, antipode x, ?_, rfl⟩
    -- Since x ∈ F i, infDist x (F i) = 0
    have hne : (F i.castSucc).Nonempty := Set.nonempty_of_mem hxi
    have h_dist_x : Metric.infDist x (F i.castSucc) = 0 :=
      (IsClosed.mem_iff_infDist_zero (hClosed i.castSucc) hne).mp hxi
    -- So infDist (antipode x) (F i) = 0
    have h_dist_ax : Metric.infDist (antipode x) (F i.castSucc) = 0 := h_eq i ▸ h_dist_x
    -- Hence antipode x ∈ F i (since F i is closed and nonempty)
    exact (IsClosed.mem_iff_infDist_zero (hClosed i.castSucc) hne).mpr h_dist_ax
  · -- Case 2: x ∉ F i for all i < n, so x ∈ F n
    push_neg at h
    use Fin.last n
    -- Since the sets cover, x must be in F n
    have hxn : x ∈ F (Fin.last n) := by
      obtain ⟨j, hj⟩ := hCover x
      by_cases hj' : j = Fin.last n
      · exact hj' ▸ hj
      · have : j.val < n := Nat.lt_of_le_of_ne (Nat.lt_succ_iff.mp j.isLt) (Fin.val_ne_of_ne hj')
        exact absurd hj (h ⟨j.val, this⟩)
    refine ⟨x, hxn, antipode x, ?_, rfl⟩
    -- We need to show antipode x ∈ F n
    -- First show antipode x ∉ F i for all i < n
    have h_ax : ∀ i : Fin n, antipode x ∉ F i.castSucc := by
      intro i hax
      -- If antipode x ∈ F i, then infDist (antipode x) (F i) = 0
      have hne : (F i.castSucc).Nonempty := Set.nonempty_of_mem hax
      have h_dist_ax : Metric.infDist (antipode x) (F i.castSucc) = 0 :=
        (IsClosed.mem_iff_infDist_zero (hClosed i.castSucc) hne).mp hax
      -- So infDist x (F i) = 0
      have h_dist_x : Metric.infDist x (F i.castSucc) = 0 := (h_eq i).symm ▸ h_dist_ax
      -- Hence x ∈ F i, contradiction
      exact h i ((IsClosed.mem_iff_infDist_zero (hClosed i.castSucc) hne).mpr h_dist_x)
    -- By covering, antipode x must be in F n
    obtain ⟨j, hj⟩ := hCover (antipode x)
    by_cases hj' : j = Fin.last n
    · exact hj' ▸ hj
    · have : j.val < n := Nat.lt_of_le_of_ne (Nat.lt_succ_iff.mp j.isLt) (Fin.val_ne_of_ne hj')
      exact absurd hj (h_ax ⟨j.val, this⟩)

end Borsuk
