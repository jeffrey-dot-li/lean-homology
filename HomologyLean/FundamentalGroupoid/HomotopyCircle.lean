/-
Copyright (c) 2025 Sebastian Kumar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Kumar
-/

import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import Mathlib.AlgebraicTopology.FundamentalGroupoid.FundamentalGroup
import Mathlib.AlgebraicTopology.FundamentalGroupoid.SimplyConnected
import Mathlib.Topology.Homotopy.Lifting
import Mathlib.Topology.Connected.PathConnected
import Mathlib.Data.Complex.Exponential
import HomologyLean.FundamentalGroupoid.Basic

/-!
# Fundamental Group of the Circle

This file proves that the fundamental group of the circle is isomorphic to the integers,
following Hatcher's Theorem 1.7.

## Main Results

* `windingNumber`: The winding number of a loop in the circle as an integer
* `windingNumberMonoidHom`: The winding number as a group homomorphism π₁(S¹) → ℤ
* `fundamentalGroupCircleEquivInt`: The isomorphism π₁(S¹) ≃* ℤ
* `fundamentalGroup_circle_eq_int`: Main theorem stating π₁(S¹) ≅ ℤ

## Implementation Strategy

The proof uses the covering map `Circle.exp : ℝ → Circle` defined by `t ↦ exp(t * I)`.
Key steps:
1. Define winding number by lifting loops to ℝ and measuring endpoint displacement
2. Show winding number is well-defined on homotopy classes (monodromy theorem)
3. Prove it's a group homomorphism
4. Construct the standard generator loop with winding number 1 (surjectivity)
5. Use simple connectivity of ℝ to prove injectivity
-/

noncomputable section

open scoped unitInterval
open ContinuousMap FundamentalGroupoid Path

namespace Circle

/-- Helper lemma: the lift of a loop at 1 in the circle ends at an integer multiple of 2π. -/
lemma liftPath_loop_endpoint_eq_int_mul_two_pi (γ : Path (1 : Circle) 1) :
    ∃ n : ℤ, Circle.isCoveringMap_exp.liftPath γ.toContinuousMap 0
      (γ.source.trans Circle.exp_zero.symm) 1 = n * (2 * Real.pi) := by
  let h_basepoint := γ.source.trans Circle.exp_zero.symm
  set lift := Circle.isCoveringMap_exp.liftPath γ.toContinuousMap 0 h_basepoint
  have h_lift : Circle.exp ∘ lift = γ.toContinuousMap :=
    Circle.isCoveringMap_exp.liftPath_lifts _ _ _
  have h_endpoint : Circle.exp (lift 1) = 1 := by
    have := congr_fun h_lift 1
    simp only [Function.comp_apply] at this
    rw [this]
    exact γ.target
  rw [Circle.exp_eq_one] at h_endpoint
  exact h_endpoint

/-- The winding number of a loop in the circle at basepoint 1.
    This is defined by lifting the loop to ℝ via the covering map Circle.exp
    and measuring how many times the lift "winds around" (in units of 2π). -/
def windingNumber (γ : Path (1 : Circle) 1) : ℤ :=
  (liftPath_loop_endpoint_eq_int_mul_two_pi γ).choose

/-- The winding number is constant on homotopy classes. -/
theorem windingNumber_eq_of_homotopic {γ₁ γ₂ : Path (1 : Circle) 1}
    (h : γ₁.Homotopic γ₂) : windingNumber γ₁ = windingNumber γ₂ := by
  unfold windingNumber
  let h₁ := γ₁.source.trans Circle.exp_zero.symm
  let h₂ := γ₂.source.trans Circle.exp_zero.symm
  set lift₁ := Circle.isCoveringMap_exp.liftPath γ₁.toContinuousMap 0 h₁
  set lift₂ := Circle.isCoveringMap_exp.liftPath γ₂.toContinuousMap 0 h₂
  have endpoint_eq : lift₁ 1 = lift₂ 1 :=
    Circle.isCoveringMap_exp.liftPath_apply_one_eq_of_homotopicRel h 0 h₁ h₂
  -- Since the endpoints are equal and both are integer multiples of 2π, the integers must be equal
  have eq₁ := (liftPath_loop_endpoint_eq_int_mul_two_pi γ₁).choose_spec
  have eq₂ := (liftPath_loop_endpoint_eq_int_mul_two_pi γ₂).choose_spec
  -- Now eq₁ and eq₂ both say possibly different things equal different multiples of 2π
  have : ((liftPath_loop_endpoint_eq_int_mul_two_pi γ₁).choose : ℝ) * (2 * Real.pi) =
      (liftPath_loop_endpoint_eq_int_mul_two_pi γ₂).choose * (2 * Real.pi) := by
    calc ((liftPath_loop_endpoint_eq_int_mul_two_pi γ₁).choose : ℝ) * (2 * Real.pi)
        = lift₁ 1 := eq₁.symm
      _ = lift₂ 1 := endpoint_eq
      _ = (liftPath_loop_endpoint_eq_int_mul_two_pi γ₂).choose * (2 * Real.pi) := eq₂
  -- Cancel 2π (which is nonzero)
  have pi_ne_zero : (2 : ℝ) * Real.pi ≠ 0 := by
    apply mul_ne_zero
    · norm_num
    · exact Real.pi_ne_zero
  exact Int.cast_injective (mul_right_cancel₀ pi_ne_zero this)

/-- Step 1: The standard loop that wraps n times around the circle.
    For positive n, wraps counterclockwise; for negative n, wraps clockwise. -/
def standardLoop_pow (n : ℤ) : Path (1 : Circle) 1 where
  toFun := fun t => Circle.exp (2 * Real.pi * n * t)
  continuous_toFun := Circle.exp.continuous.comp (continuous_const.mul continuous_subtype_val)
  source' := by simp [Circle.exp_zero]
  target' := by
    simp only [Set.Icc.coe_one, mul_one]
    exact Circle.exp_two_pi_mul_int n

/-- Step 2a: The winding number of standardLoop_pow n is n. -/
lemma windingNumber_standardLoop_pow (n : ℤ) : windingNumber (standardLoop_pow n) = n := by
  unfold windingNumber
  -- The lift of standardLoop_pow n starting at 0 is t ↦ 2π * n * t
  let candidate : C(I, ℝ) := ⟨fun t => 2 * Real.pi * n * t, by continuity⟩
  have h_candidate_is_lift : candidate =
      Circle.isCoveringMap_exp.liftPath (standardLoop_pow n).toContinuousMap 0
        ((standardLoop_pow n).source.trans Circle.exp_zero.symm) := by
    rw [Circle.isCoveringMap_exp.eq_liftPath_iff']
    refine ⟨?_, ?_⟩
    · ext t
      simp [candidate, standardLoop_pow, Circle.coe_exp]
    · simp [candidate]
  -- Therefore the endpoint of the lift is 2π * n
  have h_endpoint : Circle.isCoveringMap_exp.liftPath (standardLoop_pow n).toContinuousMap 0
      ((standardLoop_pow n).source.trans Circle.exp_zero.symm) 1 = 2 * Real.pi * n := by
    rw [← h_candidate_is_lift]
    simp only [candidate, ContinuousMap.coe_mk, Set.Icc.coe_one, mul_one]
  -- This equals n * (2 * π), so the extracted integer is n
  have choose_spec := (liftPath_loop_endpoint_eq_int_mul_two_pi (standardLoop_pow n)).choose_spec
  have : ((liftPath_loop_endpoint_eq_int_mul_two_pi (standardLoop_pow n)).choose : ℝ) *
      (2 * Real.pi) = n * (2 * Real.pi) := by
    rw [← choose_spec, h_endpoint]
    ring
  have pi_ne_zero : (2 : ℝ) * Real.pi ≠ 0 := by
    apply mul_ne_zero <;> [norm_num; exact Real.pi_ne_zero]
  exact Int.cast_injective (mul_right_cancel₀ pi_ne_zero this)

/-- Step 2b: Every path is homotopic to the standard loop with the same winding number. -/
theorem homotopic_standardLoop_of_windingNumber (γ : Path (1 : Circle) 1) :
    γ.Homotopic (standardLoop_pow (windingNumber γ)) := by
  sorry
open scoped Real
open scoped Circle
/-- Step 3: Composing standard loops with winding numbers n and m is homotopic
    to the standard loop with winding number n + m. -/
theorem standardLoop_pow_trans (n m : ℤ) :
    (standardLoop_pow n).trans (standardLoop_pow m) |>.Homotopic (standardLoop_pow (n + m)) := by
      -- Define the two “winding-number as a function of t”
      -- functions A (piecewise) and B (straight).
  let A : I → ℝ := fun t =>
    if (t : ℝ) ≤ (1 / 2 : ℝ) then
      (2 : ℝ) * (n : ℝ) * (t : ℝ)
    else
      (n : ℝ) + (m : ℝ) * ((2 : ℝ) * (t : ℝ) - 1)
  let B : I → ℝ := fun t =>
    (n + m : ℤ) * (t : ℝ)  -- coerces to ℝ
--
  refine ⟨{
    toFun := fun ⟨s, t⟩ =>
      exp (2 * Real.pi * (((1 : ℝ) - (s : ℝ)) * A t + (s : ℝ) * B t))
    continuous_toFun := by
      -- First show A is continuous
      have hA : Continuous A := by
        refine Continuous.if_le
          (continuous_const.mul continuous_subtype_val)
          (continuous_const.add (continuous_const.mul
            ((continuous_const.mul continuous_subtype_val).sub continuous_const)))
          continuous_subtype_val continuous_const ?_
        intro t ht
        rw [ht]
        norm_num
        ring
      -- Show B is continuous
      have hB : Continuous B := continuous_const.mul continuous_subtype_val
      -- Now show the full homotopy is continuous
      apply Circle.exp.continuous.comp
      refine Continuous.mul continuous_const ?_
      refine Continuous.add ?_ ?_
      · refine Continuous.mul ?_ (hA.comp continuous_snd)
        exact continuous_const.sub (continuous_induced_dom.comp continuous_fst)
      · refine Continuous.mul ?_ (hB.comp continuous_snd)
        exact continuous_induced_dom.comp continuous_fst
    map_zero_left := by
      intro t
      simp only [Set.Icc.coe_zero, zero_mul, coe_toContinuousMap, Path.trans_apply,
        standardLoop_pow, Circle.ext_iff]
      split_ifs with h
      · -- t ≤ 1/2: both sides simplify to exp(2πn * (2t))
        simp only [Circle.coe_exp]
        congr 1
        simp only [A, h, ↓reduceIte]
        ring_nf
      · -- t > 1/2: exp(2π*(n + m*(2t-1))) = exp(2πm*(2t-1)) via periodicity
        simp only [Circle.coe_exp, add_zero, one_mul, sub_zero, A, h, ↓reduceIte]
        rw [show (2 * Real.pi * (↑n + ↑m * (2 * ↑t - 1))) =
          2 * Real.pi * ↑n + 2 * Real.pi * ↑m * (2 * ↑t - 1) by ring]
        rw [Complex.ofReal_add, add_mul, Complex.exp_add]
        simp
        -- Same as simp [rules]; exact h
        simpa [mul_assoc, mul_left_comm, mul_comm] using
          (Complex.exp_int_mul_two_pi_mul_I n)
    map_one_left := by
      intro t
      simp only [Set.Icc.coe_one, sub_self, zero_mul, one_mul, zero_add]
      simp [standardLoop_pow, B]
      ring_nf
    prop' := by
      intro s t ht
      simp only [coe_toContinuousMap]
      rcases ht with ht | ht
      · -- t = 0: both sides give 1
        rw [ht, ((standardLoop_pow n).trans (standardLoop_pow m)).source]
        simp only [coe_mk, A, B]
        simp
      · -- t = 1: both sides give 1
        rw [Set.mem_singleton_iff] at ht
        rw [ht, ((standardLoop_pow n).trans (standardLoop_pow m)).target]
        have h : ¬ (1 : ℝ) ≤ (2 : ℝ)⁻¹ := by
          nlinarith
--
        simp? [A, B, h]
        ring_nf
        have h_alg : (π: ℝ) * ↑n * 2 + (π: ℝ) * ↑m * 2 = 2 * (π: ℝ) * (n + m) := by ring
        rw [h_alg]
        simpa [mul_assoc, mul_left_comm, mul_comm] using
          (Circle.exp_int_mul_two_pi (n + m))
  }⟩

/-- The winding number of a concatenated path is the sum of the individual winding numbers. -/
theorem windingNumber_mul (γ₁ γ₂ : Path (1 : Circle) 1) :
    windingNumber (γ₁.trans γ₂) = windingNumber γ₁ + windingNumber γ₂ := by
  set n₁ := windingNumber γ₁
  set n₂ := windingNumber γ₂
  -- Step 3: γ₁.trans γ₂ ~ standardLoop_pow n₁ .trans standardLoop_pow n₂
  have h1 : γ₁.Homotopic (standardLoop_pow n₁) := homotopic_standardLoop_of_windingNumber γ₁
  have h2 : γ₂.Homotopic (standardLoop_pow n₂) := homotopic_standardLoop_of_windingNumber γ₂
  have h_trans : (γ₁.trans γ₂).Homotopic ((standardLoop_pow n₁).trans (standardLoop_pow n₂)) :=
    h1.hcomp h2
  -- Step 4: standardLoop_pow n₁ .trans standardLoop_pow n₂ ~ standardLoop_pow (n₁ + n₂)
  have h_standard : ((standardLoop_pow n₁).trans (standardLoop_pow n₂)).Homotopic
      (standardLoop_pow (n₁ + n₂)) := standardLoop_pow_trans n₁ n₂
  -- Step 5: By transitivity and well-definedness
  have h_final : (γ₁.trans γ₂).Homotopic (standardLoop_pow (n₁ + n₂)) :=
    h_trans.trans h_standard
  calc windingNumber (γ₁.trans γ₂)
      = windingNumber (standardLoop_pow (n₁ + n₂)) := windingNumber_eq_of_homotopic h_final
    _ = n₁ + n₂ := windingNumber_standardLoop_pow (n₁ + n₂)

/-- The winding number as a group homomorphism. -/
def windingNumberMonoidHom : FundamentalGroup Circle 1 →* ℤ := by
  sorry

/-- The winding number descends to a well-defined map on the fundamental group. -/
abbrev windingNumberHom : FundamentalGroup Circle 1 → ℤ := windingNumberMonoidHom

/-- The standard loop that wraps once around the circle counterclockwise.
    Defined as t ↦ exp(2πt). -/
def standardLoop : Path (1 : Circle) 1 where
  toFun := fun t => Circle.exp (2 * Real.pi * t)
  continuous_toFun := Circle.exp.continuous.comp (continuous_const.mul continuous_subtype_val)
  source' := by simp [Circle.exp_zero]
  target' := by simp [Circle.exp_two_pi]

/-- The standard loop has winding number 1. -/
lemma windingNumber_standardLoop : windingNumber standardLoop = 1 := by
  unfold windingNumber standardLoop
  -- The lift of the standard loop starting at 0 should be t ↦ 2πt
  -- So it ends at 2π = 1 * 2π
  sorry

/-- The winding number homomorphism is surjective. -/
theorem windingNumberHom_surjective : Function.Surjective windingNumberHom := by
  sorry

/-- The real line is simply connected. -/
instance : SimplyConnectedSpace ℝ := by
  sorry

/-- The winding number homomorphism is injective.
    Uses the fact that ℝ is simply connected. -/
theorem windingNumberHom_injective : Function.Injective windingNumberHom := by
  sorry

/-- The fundamental group of the circle is isomorphic to the integers. -/
noncomputable def fundamentalGroupCircleEquivInt : FundamentalGroup Circle 1 ≃* ℤ :=
  MulEquiv.ofBijective windingNumberMonoidHom
    ⟨windingNumberHom_injective, windingNumberHom_surjective⟩

/-- Main theorem: The fundamental group of the circle is isomorphic to the integers.
    This is Theorem 1.7 from Hatcher's Algebraic Topology. -/
theorem fundamentalGroup_circle_eq_int :
    Nonempty (FundamentalGroup Circle 1 ≃* ℤ) :=
  ⟨fundamentalGroupCircleEquivInt⟩

end Circle

end
