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

theorem test_single (i k : Fin n) (hneq : k ≠ i) : Pi.single (f := fun _ => ℂ) i (1:ℂ) k = 0 := by
  exact Pi.single_eq_of_ne (f := fun _ => ℂ) hneq

theorem test_single2 (i k : Fin n) (hneq : k ≠ i) : Pi.single (f := fun _ => ℂ) i (1:ℂ) k = 0 := by
  exact @Pi.single_eq_of_ne' _ (fun _ => ℂ) _ _ i (1:ℂ) k hneq.symm
