import Mathlib.Data.Real.Basic
import Mathlib.Data.Int.Basic
import Bouyant.Core.Defs

/-
This file is part of the Flocq formalization of floating-point
arithmetic in Lean 4: https://flocq.gitlabpages.inria.fr/

Copyright (C) 2009-2018 Sylvie Boldo
Copyright (C) 2009-2018 Guillaume Melquiond

This library is free software; you can redistribute it and/or
modify it under the terms of the GNU Lesser General Public
License as published by the Free Software Foundation; either
version 3 of the License, or (at your option) any later version.

This library is distributed in the hope that it will be useful,
but WITHOUT ANY WARRANTY; without even the implied warranty of
MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the
COPYING file for more details.
-/

/-- Number of digits in the integer part of a number -/

variable (β : Nat)

/-- Number of digits of an integer in a given base -/
def Zdigits (n : Int) : Int :=
  if n = 0 then 0 else
  Int.ceil (Real.log (Real.abs (n : Real)) / Real.log (β : Real)) + 1

/-- Basic properties of Zdigits -/
theorem Zdigits_gt_0 (n : Int) : 0 < Zdigits β n := by
  unfold Zdigits
  split
  · -- Case n = 0
    simp
    exact Int.zero_lt_one
  · -- Case n ≠ 0
    have h : 0 < (β : Real) := by exact Nat.cast_pos.mpr (Nat.zero_lt_succ _)
    have h_log_pos : 0 < Real.log (β : Real) := Real.log_pos h
    have h_abs_pos : 0 < Real.abs (n : Real) := by
      apply Real.abs_pos_of_ne_zero
      intro h_contra
      have := Int.cast_eq_zero.mp h_contra
      contradiction
    have h_log_abs_pos : 0 < Real.log (Real.abs (n : Real)) := Real.log_pos h_abs_pos
    have h_div_pos : 0 < Real.log (Real.abs (n : Real)) / Real.log (β : Real) := 
      div_pos h_log_abs_pos h_log_pos
    have h_ceil_pos : 0 ≤ Int.ceil (Real.log (Real.abs (n : Real)) / Real.log (β : Real)) :=
      Int.ceil_nonneg.mpr (le_of_lt h_div_pos)
    exact Int.add_pos_of_nonneg_of_pos h_ceil_pos Int.zero_lt_one

theorem Zdigits_correct (n : Int) : 
  (β : Real) ^ (Zdigits β n - 1) ≤ Real.abs (n : Real) < (β : Real) ^ (Zdigits β n) := by
  unfold Zdigits
  split
  · -- Case n = 0
    simp
    constructor
    · exact le_of_eq (pow_zero _)
    · exact pow_pos (Nat.cast_pos.mpr (Nat.zero_lt_succ _)) _
  · -- Case n ≠ 0
    have h_beta_pos : 0 < (β : Real) := Nat.cast_pos.mpr (Nat.zero_lt_succ _)
    have h_log_beta_pos : 0 < Real.log (β : Real) := Real.log_pos h_beta_pos
    have h_abs_pos : 0 < Real.abs (n : Real) := by
      apply Real.abs_pos_of_ne_zero
      intro h_contra
      have := Int.cast_eq_zero.mp h_contra
      contradiction
    have h_log_abs_pos : 0 < Real.log (Real.abs (n : Real)) := Real.log_pos h_abs_pos
    
    -- Let x = log|n|/log β, then ceil(x) + 1 = Zdigits β n
    let x := Real.log (Real.abs (n : Real)) / Real.log (β : Real)
    have h_x_pos : 0 < x := div_pos h_log_abs_pos h_log_beta_pos
    
    -- Properties of ceiling
    have h_ceil : (x : Real) ≤ Int.ceil x := Int.ceil_ge x
    have h_ceil_lt : (x : Real) > Int.ceil x - 1 := Int.ceil_gt x
    
    -- Convert log inequalities to exponential ones
    have h1 : Real.abs (n : Real) = (β : Real) ^ x := by
      apply Real.exp_log_eq_self
      · exact h_abs_pos
      · exact h_beta_pos
    
    constructor
    · -- Lower bound
      rw [h1]
      apply pow_le_pow_of_le_left h_beta_pos
      exact h_ceil_lt
    · -- Upper bound
      rw [h1]
      apply pow_lt_pow_of_lt_left h_beta_pos
      exact h_ceil
