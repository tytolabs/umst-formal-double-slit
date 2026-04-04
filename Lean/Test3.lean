import Mathlib.Data.Complex.Basic

example : { re := 0, im := 0 } = (0 : ℂ) := by rfl
example : { re := 0, im := 0 } = (0 : ℂ) := by simp [Complex.ext_iff]
