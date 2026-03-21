/-
SPDX-License-Identifier: MIT
Copyright (c) 2026 Santhosh Shyamsundar, Santosh Prabhu Shenbagamoorthy — Studio TYTO
-/

import Mathlib

open scoped Matrix ComplexOrder BigOperators
open Matrix Complex

variable {n : ℕ} (hn : 0 < n)
local notation "ℂⁿ" => Fin n → ℂ

theorem trace_sum_s (S : Finset (Fin n)) (s : Fin n → ℂ) : Complex.re (∑ i in S, s i) = ∑ i in S, (s i).re := by
  induction S using Finset.induction
  case empty => simp
  case insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha]
    simp [ih]

theorem erase_sum (s : Fin n → ℝ) (i : Fin n) : s i + ∑ j in Finset.univ.erase i, s j = ∑ j : Fin n, s j := by
  exact Finset.add_sum_erase (Finset.univ : Finset (Fin n)) (fun j => s j) (Finset.mem_univ i)

theorem single_dot (M : Matrix (Fin n) (Fin n) ℂ) (i : Fin n) :
  dotProduct (star (Pi.single i (1 : ℂ))) (M *ᵥ Pi.single i (1 : ℂ)) = M i i := by
  dsimp [dotProduct, mulVec]
  have inner (j : Fin n) : (∑ k : Fin n, M j k * (Pi.single i (1:ℂ) k)) = M j i := by
    rw [Finset.sum_eq_single i]
    · simp
    · intro k _ hneq
      have hz : Pi.single i (1:ℂ) k = 0 := Pi.single_eq_of_ne' hneq
      simp [hz]
    · simp
  simp_rw [inner]
  rw [Finset.sum_eq_single i]
  · simp
  · intro j _ hneq
    have hz : star (Pi.single i (1:ℂ) j) = 0 := by
      have hzz : Pi.single i (1:ℂ) j = 0 := Pi.single_eq_of_ne' hneq
      rw [hzz]
      exact star_zero ℂ
    simp [hz]
  · simp
