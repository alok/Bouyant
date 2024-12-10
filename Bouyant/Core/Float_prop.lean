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

/-- Basic properties of floating-point formats: lemmas about mantissa, exponent... -/

variable (β : Nat)

/-- Helper lemma: β^e is positive for any e:Int -/
theorem bpow_pos (e : Int) : 0 < (β : Real) ^ e := by
  have h : 0 < (β : Real) := by exact Nat.cast_pos.mpr (Nat.zero_lt_succ _)
  cases e with
  | ofNat n => 
    simp
    exact pow_pos h n
  | negSucc n =>
    simp
    exact Real.rpow_pos_of_pos h _

/-- Compare two floats with same exponent -/
theorem Rcompare_F2R {e m₁ m₂ : Int} :
  compare (F2R (Float.mk β m₁ e)) (F2R (Float.mk β m₂ e)) = compare m₁ m₂ := by
  unfold F2R
  simp
  have hp := bpow_pos β e
  cases lt_trichotomy m₁ m₂ with
  | inl h => 
    apply Eq.symm
    simp [h]
    exact mul_lt_mul_right hp (Int.cast_lt.mpr h)
  | inr h => cases h with
    | inl h =>
      apply Eq.symm
      simp [h]
    | inr h =>
      apply Eq.symm
      simp [h.symm]
      exact mul_lt_mul_right hp (Int.cast_lt.mpr h)

/-- Rest of the file stays exactly the same... -/
