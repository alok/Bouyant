import Mathlib.Data.Real.Basic
import Mathlib.Data.Int.Basic
import Bouyant.Core.Defs
import Bouyant.Core.Float_prop
import Bouyant.Core.Digits

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

/-- Generic format for floating-point numbers -/

variable (β : Nat)

/-- A floating-point format is a property of real numbers -/
def Format := Real → Prop

/-- A format is valid if it contains at least one number -/
def Valid_format (format : Format) :=
  ∃ x, format x

/-- A format is canonical if it contains no two equal numbers -/
def Canonical_format (format : Format) :=
  ∀ x y, format x → format y → x = y → x = y

/-- A format is satisfactory if it contains canonical representatives -/
def Satisfies_any (format : Format) :=
  ∀ x, ∃ y, format y ∧ y = x

/-- A format is stable by scaling by powers of β -/
def Scaled_format (format : Format) :=
  ∀ x e, format x → format (x * (β : Real) ^ e)

/-- A format is stable by absolute value -/
def Abs_format (format : Format) :=
  ∀ x, format x → format (Real.abs x)

/-- A format contains zero -/
def Contains_zero (format : Format) :=
  format 0

/-- A format contains all integers -/
def Contains_integers (format : Format) :=
  ∀ n : Int, format (n : Real)

/-- A satisfactory format is valid -/
theorem satisfies_valid (format : Format) :
  Satisfies_any format → Valid_format format := by
  intro h
  have ⟨y, hy⟩ := h 0
  exact ⟨y, hy.1⟩

/-- A satisfactory format is canonical -/
theorem satisfies_canonical (format : Format) :
  Satisfies_any format → Canonical_format format := by
  intro h x y fx fy eq
  have ⟨z, hz⟩ := h x
  have ⟨w, hw⟩ := h y
  rw [hz.2, hw.2, eq]

/-- A scaled format containing zero contains all powers of β -/
theorem scaled_contains_bpow (format : Format) :
  Scaled_format format → Contains_zero format →
  ∀ e : Int, format ((β : Real) ^ e) := by
  intros hs hz e
  have h1 : (β : Real) ^ e = 0 * (β : Real) ^ e := by simp
  rw [←h1]
  exact hs 0 e hz

/-- A format containing integers and stable by scaling contains all powers of β -/
theorem integers_scaled_contains_bpow (format : Format) :
  Contains_integers format → Scaled_format format →
  ∀ e : Int, format ((β : Real) ^ e) := by
  intros hi hs e
  have h1 : (β : Real) ^ e = 1 * (β : Real) ^ e := by simp
  rw [←h1]
  exact hs 1 e (hi 1)

