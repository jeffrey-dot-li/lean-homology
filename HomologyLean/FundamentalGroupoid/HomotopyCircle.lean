/-
Copyright (c) 2025 Sebastian Kumar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors:Sebastian Kumar
-/

import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import Mathlib.AlgebraicTopology.FundamentalGroupoid.FundamentalGroup
import Mathlib.AlgebraicTopology.FundamentalGroupoid.SimplyConnected
import Mathlib.Topology.Homotopy.Lifting
import Mathlib.Topology.Connected.PathConnected
import Mathlib.Analysis.Convex.Contractible
import Mathlib.Algebra.Group.TypeTags.Basic
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

open scoped Real
open scoped Circle

/-- Step 2b: Every path is homotopic to the standard loop with the same winding number. -/
theorem homotopic_standardLoop_of_windingNumber (γ : Path (1 : Circle) 1) :
    γ.Homotopic (standardLoop_pow (windingNumber γ)) := by
  set n := windingNumber γ
  let h_basepoint := γ.source.trans Circle.exp_zero.symm
  let h_basepoint' := (standardLoop_pow n).source.trans Circle.exp_zero.symm
  -- Step 1: Lift both paths to ℝ
  set lift_γ := Circle.isCoveringMap_exp.liftPath γ.toContinuousMap 0 h_basepoint
  set lift_std := Circle.isCoveringMap_exp.liftPath
    (standardLoop_pow n).toContinuousMap 0 h_basepoint'
  -- Step 2: Show the endpoints are the same in ℝ
  have endpoint_eq : lift_γ 1 = lift_std 1 := by
    -- Both endpoints are n * (2π) by definition of winding number
    have h_γ : lift_γ 1 = n * (2 * Real.pi) := by
      -- By definition, n = windingNumber γ = choose from the existence proof
      -- and choose_spec says the lift endpoint equals choose * (2π)
      exact (liftPath_loop_endpoint_eq_int_mul_two_pi γ).choose_spec
    have h_std : lift_std 1 = n * (2 * Real.pi) := by
      -- We proved windingNumber (standardLoop_pow n) = n
      -- So the lift of standardLoop_pow n also ends at n * (2π)
      have h_endpoint := (liftPath_loop_endpoint_eq_int_mul_two_pi (standardLoop_pow n)).choose_spec
      have h_winding := windingNumber_standardLoop_pow n
      -- Convert: windingNumber is defined as choose, so choose = n
      have : (liftPath_loop_endpoint_eq_int_mul_two_pi (standardLoop_pow n)).choose = n := by
        exact h_winding
      rw [this] at h_endpoint
      exact h_endpoint
    rw [h_γ, h_std]
  -- Step 3: Show the lifts agree at 0
  have start_eq : lift_γ 0 = lift_std 0 := by
    rw [Circle.isCoveringMap_exp.liftPath_zero, Circle.isCoveringMap_exp.liftPath_zero]
  -- Step 4: Since ℝ is simply connected and the lifts have the same endpoints,
  -- they are homotopic rel {0,1} in ℝ
  have lifts_homotopic : lift_γ.HomotopicRel lift_std {0, 1} := by
    -- Extract h_γ and h_std from Step 2
    have h_γ : lift_γ 1 = n * (2 * Real.pi) := by
      exact (liftPath_loop_endpoint_eq_int_mul_two_pi γ).choose_spec
    have h_std : lift_std 1 = n * (2 * Real.pi) := by
      have h_endpoint := (liftPath_loop_endpoint_eq_int_mul_two_pi (standardLoop_pow n)).choose_spec
      have : (liftPath_loop_endpoint_eq_int_mul_two_pi (standardLoop_pow n)).choose = n :=
        windingNumber_standardLoop_pow n
      rw [this] at h_endpoint
      exact h_endpoint
    -- Convert the continuous maps to paths in ℝ
    let path_γ : Path (0 : ℝ) (n * (2 * Real.pi)) := {
      toFun := lift_γ
      continuous_toFun := lift_γ.continuous
      source' := start_eq ▸ Circle.isCoveringMap_exp.liftPath_zero _ _ _
      target' := h_γ
    }
    let path_std : Path (0 : ℝ) (n * (2 * Real.pi)) := {
      toFun := lift_std
      continuous_toFun := lift_std.continuous
      source' := Circle.isCoveringMap_exp.liftPath_zero _ _ _
      target' := h_std
    }
    -- Use simply connected ℝ to show paths are homotopic
    -- ℝ is contractible (RealTopologicalVectorSpace.contractibleSpace)
    -- and contractible spaces are simply connected (SimplyConnectedSpace.ofContractible)
    have : path_γ.Homotopic path_std := SimplyConnectedSpace.paths_homotopic path_γ path_std
    -- Path.Homotopic is Nonempty (Path.Homotopy) which is HomotopicRel {0,1}
    exact this
  -- Step 5: Use IsCoveringMap.homotopicRel_iff_comp to project the homotopy to S¹
  -- This says: lifts are homotopic rel S ↔ projections are homotopic rel S
  have : (Circle.exp.comp lift_γ).HomotopicRel (Circle.exp.comp lift_std) {0, 1} := by
    apply (Circle.isCoveringMap_exp.homotopicRel_iff_comp ?_).mp lifts_homotopic
    use 0
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, true_or, start_eq, and_self]
  -- Step 6: The compositions are exactly γ and standardLoop_pow n
  have γ_eq : Circle.exp.comp lift_γ = γ.toContinuousMap := by
    -- liftPath_lifts says: Circle.exp ∘ lift_γ = γ.toContinuousMap
    have h := Circle.isCoveringMap_exp.liftPath_lifts γ.toContinuousMap 0 h_basepoint
    -- Convert function composition to ContinuousMap.comp
    ext t
    simp only [ContinuousMap.comp_apply]
    rw [← h]
    rfl
--
  have std_eq : Circle.exp.comp lift_std = (standardLoop_pow n).toContinuousMap := by
    -- liftPath_lifts says: Circle.exp ∘ lift_std = (standardLoop_pow n).toContinuousMap
    have h := Circle.isCoveringMap_exp.liftPath_lifts
      (standardLoop_pow n).toContinuousMap 0 h_basepoint'
    -- Convert function composition to ContinuousMap.comp
    ext t
    simp only [ContinuousMap.comp_apply]
    rw [← h]
    rfl
--
  -- Conclude: HomotopicRel {0,1} for paths is exactly Path.Homotopic
  -- this : (exp.comp lift_γ).HomotopicRel (exp.comp lift_std) {0, 1}
  -- After substituting the equalities, this becomes Path.Homotopic
  rwa [γ_eq, std_eq] at this

/-- If two paths have the same winding number, they are homotopic.
    Both are homotopic to the standard loop with that winding number. -/
theorem homotopic_of_windingNumber_eq {γ₁ γ₂ : Path (1 : Circle) 1}
    (h : windingNumber γ₁ = windingNumber γ₂) : γ₁.Homotopic γ₂ := by
  -- Both γ₁ and γ₂ are homotopic to standardLoop_pow n
  have h₁ : γ₁.Homotopic (standardLoop_pow (windingNumber γ₁)) :=
    homotopic_standardLoop_of_windingNumber γ₁
  have h₂ : γ₂.Homotopic (standardLoop_pow (windingNumber γ₂)) :=
    homotopic_standardLoop_of_windingNumber γ₂
  -- Since windingNumber γ₁ = windingNumber γ₂, they're both homotopic to the same loop
  rw [h] at h₁
  -- Use transitivity: γ₁ ~ standardLoop_pow n ~ γ₂
  exact h₁.trans h₂.symm

/-- Two paths are homotopic if and only if they have the same winding number. -/
theorem homotopic_iff_windingNumber_eq {γ₁ γ₂ : Path (1 : Circle) 1} :
    γ₁.Homotopic γ₂ ↔ windingNumber γ₁ = windingNumber γ₂ := by
  constructor
  · exact windingNumber_eq_of_homotopic
  · exact homotopic_of_windingNumber_eq

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
open scoped Multiplicative
/-- The winding number as a group homomorphism. -/
def windingNumberMonoidHom : Additive (FundamentalGroup Circle 1) →+ ℤ where
  toFun p := Multiplicative.ofAdd (windingNumber (Quotient.out p))
  map_zero' := by
    -- rw [ofAdd_eq_one]
    -- rw [Quotient.out]
    -- rw [Quot.out]
    sorry
  map_add' := fun x y => by
    -- Need: ofAdd (windingNumber (Quotient.out (x * y))) =
    --       ofAdd (windingNumber (Quotient.out x)) * ofAdd (windingNumber (Quotient.out y))
    -- In Multiplicative, multiplication is addition, so this is:
    -- ofAdd (windingNumber (Quotient.out (x * y))) = ofAdd (windingNumber (Quotient.out x) + windingNumber (Quotient.out y))
    simp only [← ofAdd_add]
    congr 1

    sorry

/-- The winding number descends to a well-defined map on the fundamental group. -/
abbrev windingNumberHom : FundamentalGroup Circle 1 → ℤ :=
  Multiplicative.toAdd ∘ windingNumberMonoidHom


/-- The winding number homomorphism is surjective. -/
theorem windingNumberHom_surjective : Function.Surjective windingNumberHom := by
  intro n
  -- The preimage of n is the homotopy class of standardLoop_pow n
  use FundamentalGroupoid.fromPath' (standardLoop_pow n)
  -- Show windingNumberHom applied to this equals n
  unfold windingNumberHom windingNumberMonoidHom
  simp only [Function.comp_apply, toAdd_ofAdd, MonoidHom.coe_mk, OneHom.coe_mk]
  -- Now need: windingNumber (Quotient.out (fromPath' (standardLoop_pow n))) = n
  -- Quotient.out gives a representative homotopic to the original
  have h_out_homotopic : (Quotient.out
      (FundamentalGroupoid.fromPath' (standardLoop_pow n))).Homotopic
      (standardLoop_pow n) := by
    -- fromPath' is Quotient.mk _, and out gives a representative in the same equivalence class
    have : ⟦Quotient.out (FundamentalGroupoid.fromPath' (standardLoop_pow n))⟧ =
        FundamentalGroupoid.fromPath' (standardLoop_pow n) := Quotient.out_eq _
    rw [FundamentalGroupoid.fromPath'] at this
    simp only at this
    exact Quotient.exact this
  calc windingNumber (Quotient.out (FundamentalGroupoid.fromPath' (standardLoop_pow n)))
      = windingNumber (standardLoop_pow n) := windingNumber_eq_of_homotopic h_out_homotopic
    _ = n := windingNumber_standardLoop_pow n

/-- The winding number homomorphism is injective.
    Uses the fact that ℝ is simply connected. -/
theorem windingNumberHom_injective : Function.Injective windingNumberHom := by
  rw[Function.Injective]
  intro a b
  unfold windingNumberHom windingNumberMonoidHom
  intro h
  simp only [AddMonoidHom.coe_mk, ZeroHom.coe_mk, Function.comp_apply, toAdd_ofAdd,
    ← homotopic_iff_windingNumber_eq] at h
  -- h : (Quotient.out a).Homotopic (Quotient.out b)
  -- Need to show a = b in the quotient
  -- Use Quotient.sound to show quotients of equivalent elements are equal
  calc a = ⟦Quotient.out a⟧ := (Quotient.out_eq a).symm
    _ = ⟦Quotient.out b⟧ := Quotient.sound h
    _ = b := Quotient.out_eq b
/-- The fundamental group of the circle is isomorphic to the integers. -/
noncomputable def fundamentalGroupCircleEquivInt : Additive (FundamentalGroup Circle 1) ≃+ ℤ :=
  AddEquiv.ofBijective windingNumberMonoidHom
    ⟨windingNumberHom_injective, windingNumberHom_surjective⟩

/-- Main theorem: The fundamental group of the circle is isomorphic to the integers.
    This is Theorem 1.7 from Hatcher's Algebraic Topology. -/
theorem fundamentalGroup_circle_eq_int :
    Nonempty (Additive (FundamentalGroup Circle 1) ≃+ ℤ) :=
  ⟨fundamentalGroupCircleEquivInt⟩

end Circle

end
