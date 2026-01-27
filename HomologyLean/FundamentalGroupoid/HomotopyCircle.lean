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
  sorry

/-- The winding number of a loop in the circle at basepoint 1.
    This is defined by lifting the loop to ℝ via the covering map Circle.exp
    and measuring how many times the lift "winds around" (in units of 2π). -/
def windingNumber (γ : Path (1 : Circle) 1) : ℤ := by
  sorry

/-- The winding number is constant on homotopy classes. -/
theorem windingNumber_eq_of_homotopic {γ₁ γ₂ : Path (1 : Circle) 1}
    (h : γ₁.Homotopic γ₂) : windingNumber γ₁ = windingNumber γ₂ := by
  sorry

/-- The winding number of a concatenated path is the sum of the individual winding numbers. -/
theorem windingNumber_mul (γ₁ γ₂ : Path (1 : Circle) 1) :
    windingNumber (γ₁.trans γ₂) = windingNumber γ₁ + windingNumber γ₂ := by
  sorry

/-- The winding number as a group homomorphism. -/
def windingNumberMonoidHom : FundamentalGroup Circle 1 →* ℤ := by
  sorry

/-- The winding number descends to a well-defined map on the fundamental group. -/
abbrev windingNumberHom : FundamentalGroup Circle 1 → ℤ := windingNumberMonoidHom

/-- The standard loop that wraps once around the circle counterclockwise.
    Defined as t ↦ exp(2πt * I). -/
def standardLoop : Path (1 : Circle) 1 := by
  sorry

/-- The standard loop has winding number 1. -/
lemma windingNumber_standardLoop : windingNumber standardLoop = 1 := by
  sorry

/-- For any integer n, construct a loop with winding number n. -/
def standardLoop_pow (n : ℤ) : Path (1 : Circle) 1 := by
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
