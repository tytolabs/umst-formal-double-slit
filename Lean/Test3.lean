SPDX-FileCopyrightText: 2026 Santosh Prabhu Shenbagamoorthy and Santhosh Shyamsundar
SPDX-License-Identifier: MIT
import Mathlib.Data.Complex.Basic

example : { re := 0, im := 0 } = (0 : ℂ) := by rfl
example : { re := 0, im := 0 } = (0 : ℂ) := by simp [Complex.ext_iff]
