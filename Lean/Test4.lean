/-
SPDX-License-Identifier: MIT
Copyright (c) 2026 Santhosh Shyamsundar, Santosh Prabhu Shenbagamoorthy — Studio TYTO
-/

import Mathlib.Data.Complex.Basic
import Mathlib.Data.Matrix.RowCol
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.LinearAlgebra.Matrix.PosDef

open scoped Matrix ComplexOrder BigOperators

variable {n : ℕ}

theorem test_single (i k : Fin n) (hneq : k ≠ i) : (Pi.single i (1:ℂ) : Fin n → ℂ) k = 0 := by
  exact Pi.single_eq_of_ne (f := fun _ => ℂ) hneq (1:ℂ)

theorem test_single_same (i : Fin n) : (Pi.single i (1:ℂ) : Fin n → ℂ) i = 1 := by
  exact Pi.single_eq_same (f := fun _ => ℂ) i (1:ℂ)
