/-
SPDX-License-Identifier: MIT
Copyright (c) 2026 Santhosh Shyamsundar, Santosh Prabhu Shenbagamoorthy — Studio TYTO
-/

import MeasurementCost
import Mathlib.Order.GaloisConnection
import Mathlib.Data.Real.Basic

/-!
# EpistemicGalois — Landauer adjunction between Information and Energy

This module establishes a formal **Galois connection** (adjunction) between
information acquisition and thermodynamic cost.

Given a fixed environment temperature `T > 0`:
1. **Left Adjoint (L)**: Maps an information requirement `I` (bits) to the 
   minimum energy required `L(I) = I * k_B * T * ln(2)`.
2. **Right Adjoint (R)**: Maps an energy budget `E` (Joules) to the maximum 
   information acquirable `R(E) = E / (k_B * T * ln(2))`.

The Galois connection theorem states:
   `L(I) ≤ E ↔ I ≤ R(E)`

This perfectly mirrors the adjunction in `GaloisGate.lean` but bridges 
epistemic (observational) requirements with physical (thermodynamic) resources.
-/

namespace UMST.DoubleSlit

open Real UMST.Quantum

-- ============================================================
-- Section 1: The Landauer Adjoints
-- ============================================================

/-- Minimum energy (Joules) required to acquire `I` bits of information 
    at temperature `T`. (Left adjoint) -/
noncomputable def requiredEnergy (T I : ℝ) : ℝ :=
  I * landauerBitEnergy T

/-- Maximum information (bits) acquirable with an energy budget `E`
    at temperature `T`. (Right adjoint) -/
noncomputable def acquirableInfo (T E : ℝ) : ℝ :=
  E / landauerBitEnergy T

-- ============================================================
-- Section 2: Properties of the Adjoints
-- ============================================================

/-- The required energy is monotone with respect to information. -/
theorem requiredEnergy_mono (T : ℝ) (hT : 0 ≤ T) {I₁ I₂ : ℝ} (h : I₁ ≤ I₂) :
    requiredEnergy T I₁ ≤ requiredEnergy T I₂ := by
  unfold requiredEnergy
  exact mul_le_mul_of_nonneg_right h (landauerBitEnergy_nonneg hT)

/-- The acquirable info is monotone with respect to energy budget. -/
theorem acquirableInfo_mono (T : ℝ) (hT : 0 < T) {E₁ E₂ : ℝ} (h : E₁ ≤ E₂) :
    acquirableInfo T E₁ ≤ acquirableInfo T E₂ := by
  unfold acquirableInfo
  have hpos : 0 < landauerBitEnergy T := landauerBitEnergy_pos hT
  exact div_le_div_of_nonneg_right h (le_of_lt hpos)

-- ============================================================
-- Section 3: The Galois Connection
-- ============================================================

/-- The Landauer Galois connection: For a strict positive temperature, 
    the minimum required energy to get `I` bits is ≤ the budget `E` 
    if and only if `I` is ≤ the maximum acquirable info with budget `E`. -/
theorem landauer_galois_connection (T : ℝ) (hT : 0 < T) (I E : ℝ) :
    requiredEnergy T I ≤ E ↔ I ≤ acquirableInfo T E := by
  unfold requiredEnergy acquirableInfo
  have hpos : 0 < landauerBitEnergy T := landauerBitEnergy_pos hT
  constructor
  · intro h
    exact (le_div_iff₀ hpos).mpr h
  · intro h
    exact (le_div_iff₀ hpos).mp h

/-- Round-trip: requiredEnergy (acquirableInfo E) = E -/
theorem requiredEnergy_acquirableInfo (T E : ℝ) (hT : 0 < T) :
    requiredEnergy T (acquirableInfo T E) = E := by
  unfold requiredEnergy acquirableInfo
  have hpos : 0 < landauerBitEnergy T := landauerBitEnergy_pos hT
  exact div_mul_cancel₀ E (ne_of_gt hpos)

/-- Round-trip: acquirableInfo (requiredEnergy I) = I -/
theorem acquirableInfo_requiredEnergy (T I : ℝ) (hT : 0 < T) :
    acquirableInfo T (requiredEnergy T I) = I := by
  unfold requiredEnergy acquirableInfo
  have hpos : 0 < landauerBitEnergy T := landauerBitEnergy_pos hT
  exact mul_div_cancel_right₀ I (ne_of_gt hpos)

-- ============================================================
-- Section 4: Physical Link (Bounding Real Measurements)
-- ============================================================

/-- An epistemic probe fits within the energy budget IF AND ONLY IF 
    its acquired information fits within the acquirable info bound. -/
theorem probe_budget_iff_info_bound (p : PathProbe) (ρ : DensityMatrix hnQubit) 
    (T E : ℝ) (hT : 0 < T) :
    measurementCost p ρ T ≤ E ↔ epistemicMIBits p ρ ≤ acquirableInfo T E := by
  have h_cost : measurementCost p ρ T = requiredEnergy T (epistemicMIBits p ρ) := rfl
  rw [h_cost]
  exact landauer_galois_connection T hT (epistemicMIBits p ρ) E

end UMST.DoubleSlit
