import Mathlib.Data.Real.Basic
-- import Mathlib.Data.Int.Basic

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

/-- Basic definitions: float and rounding property -/

/-- Definition of a floating-point number -/
structure Float (β : Nat) where
  num : Int
  exp : Int

/-- Convert float to real number -/
def F2R {β : Nat} (f : Float β) : Real :=
  (f.num : Real) * (β : Real) ^ f.exp

/-- Requirements on a rounding mode -/
def RoundPredTotal (P : Real → Real → Prop) :=
  ∀ x, ∃ f, P x f

def RoundPredMonotone (P : Real → Real → Prop) :=
  ∀ x y f g, P x f → P y g → x ≤ y → f ≤ g

def RoundPred (P : Real → Real → Prop) :=
  RoundPredTotal P ∧ RoundPredMonotone P
