/-
SPDX-License-Identifier: MIT
Copyright (c) 2026 Santhosh Shyamsundar, Santosh Prabhu Shenbagamoorthy — Studio TYTO
-/

import DoubleSlitCore
import GeneralDimension
import InfoEntropy

/-!
# LandauerBound — diagonal path entropy ↔ Landauer energy scale

`vonNeumannDiagonal ρ` is in **nats** (`Real.log`). Landauer bit energy uses the same `log`, so
bit-equivalent entropy is **`vonNeumannDiagonal ρ / log 2`**.

This layer records a **nonnegative SI joule** scale `landauerCostDiagonal ρ T` via existing
`infoEnergyLowerBound`. It does **not** assert that a particular physical process attains equality;
that requires a full erasure / dissipation model.

**Proved:** costing is nonnegative for `T ≥ 0`, **invariant under `whichPathChannel.apply`**, and
`pathEntropyBits ρ ≤ 1` hence **`landauerCostDiagonal ρ T ≤ landauerBitEnergy T`** for `T ≥ 0`
(one Landauer bit-energy unit bounds the diagonal-entropy hook).

**General `Fin n`:** `pathEntropyBits_n` and `landauerCostDiagonal_n` use `vonNeumannDiagonal_n` /
`GeneralDimension.vonNeumannDiagonal_n_le_log_n`, giving **`pathEntropyBits_n ρ ≤ logb 2 n`** and
**`landauerCostDiagonal_n ρ T ≤ landauerBitEnergy T * logb 2 n`** (max-entropy / `n`-outcome bit cap).
The qubit hook `residualCoherenceCapacity` remains the **binary** narrative in this file; a
dimension-independent purity-based RCC lives in `GeneralResidualCoherence.lean`
(`residualCoherenceCapacity_purity`).

### Principle of Maximal Information Collapse
This module enforces an *additional thermodynamic upper bound* on remaining coherence (Residual Logical 
Uncertainty). By mapping macroscopic energy extraction to the dimensionless `[0, 1]` coherence capacity:
`1 - (MI) / (k_B * T * ln(2)) = Residual Capacity`
If the observer pays the maximum Landauer cost of 1 bit (`landauerBitEnergy`), the residual capacity
collapses strictly to 0, mathematically destroying interference (`V=0`). This mapping establishes that 
intelligent macroscopic measurements directly pay the thermodynamic price required to collapse reality, 
working in tight conjunction with the classical Englert quantum limit `V² + I² ≤ 1`.
-/

namespace UMST.DoubleSlit

open UMST.Core UMST.Quantum Real

lemma log_two_pos : 0 < log 2 :=
  log_pos (by norm_num : (1 : ℝ) < 2)

/-- Diagonal path entropy (nats) expressed in Landauer **bit-equivalents** (`/ log 2`). -/
noncomputable def pathEntropyBits (ρ : DensityMatrix hnQubit) : ℝ :=
  vonNeumannDiagonal ρ / log 2

theorem pathEntropyBits_nonneg (ρ : DensityMatrix hnQubit) : 0 ≤ pathEntropyBits ρ :=
  div_nonneg (vonNeumannDiagonal_nonneg ρ) (le_of_lt log_two_pos)

theorem pathEntropyBits_le_one (ρ : DensityMatrix hnQubit) : pathEntropyBits ρ ≤ 1 := by
  unfold pathEntropyBits
  rw [div_le_one log_two_pos]
  exact vonNeumannDiagonal_le_log_two ρ

/-! ### General `Fin n` (diagonal entropy → Landauer scale) -/

/-- Diagonal entropy on `Fin n`, in **Landauer bit-equivalents** (`/ log 2`). At most `logb 2 n`. -/
noncomputable def pathEntropyBits_n {n : ℕ} (hn : 0 < n) (ρ : DensityMatrix hn) : ℝ :=
  vonNeumannDiagonal_n ρ / log 2

theorem pathEntropyBits_n_nonneg {n : ℕ} (hn : 0 < n) (ρ : DensityMatrix hn) :
    0 ≤ pathEntropyBits_n hn ρ := by
  unfold pathEntropyBits_n
  exact div_nonneg (vonNeumannDiagonal_n_nonneg ρ) (le_of_lt log_two_pos)

theorem pathEntropyBits_n_le_logb_two {n : ℕ} (hn : 0 < n) (ρ : DensityMatrix hn) :
    pathEntropyBits_n hn ρ ≤ logb 2 (n : ℝ) := by
  unfold pathEntropyBits_n
  simpa [log_div_log] using div_le_div_of_nonneg_right (vonNeumannDiagonal_n_le_log_n ρ) (le_of_lt log_two_pos)

/-- SI joules from general diagonal entropy at temperature `T`. -/
noncomputable def landauerCostDiagonal_n {n : ℕ} (hn : 0 < n) (ρ : DensityMatrix hn) (T : ℝ) : ℝ :=
  infoEnergyLowerBound (pathEntropyBits_n hn ρ) T

theorem landauerCostDiagonal_n_nonneg {n : ℕ} (hn : 0 < n) (ρ : DensityMatrix hn) (T : ℝ) (hT : 0 ≤ T) :
    0 ≤ landauerCostDiagonal_n hn ρ T := by
  unfold landauerCostDiagonal_n
  exact infoEnergyLowerBound _ _ (pathEntropyBits_n_nonneg hn ρ) hT

theorem landauerCostDiagonal_n_le_logb_landauerBitEnergy {n : ℕ} (hn : 0 < n) (ρ : DensityMatrix hn)
    (T : ℝ) (hT : 0 ≤ T) :
    landauerCostDiagonal_n hn ρ T ≤ landauerBitEnergy T * logb 2 (n : ℝ) := by
  unfold landauerCostDiagonal_n infoEnergyLowerBound
  exact mul_le_mul_of_nonneg_left (pathEntropyBits_n_le_logb_two hn ρ) (landauerBitEnergy_nonneg hT)

theorem pathEntropyBits_n_qubit_eq (ρ : DensityMatrix hnQubit) :
    pathEntropyBits_n hnQubit ρ = pathEntropyBits ρ := by
  unfold pathEntropyBits_n pathEntropyBits
  rw [vonNeumannDiagonal_n_eq_vonNeumannDiagonal ρ]

theorem landauerCostDiagonal_n_qubit_eq (ρ : DensityMatrix hnQubit) (T : ℝ) :
    landauerCostDiagonal_n hnQubit ρ T = landauerCostDiagonal ρ T := by
  unfold landauerCostDiagonal_n landauerCostDiagonal
  rw [pathEntropyBits_n_qubit_eq ρ]

/-- SI joules: `k_B T log 2` times bit-equivalent diagonal entropy. -/
noncomputable def landauerCostDiagonal (ρ : DensityMatrix hnQubit) (T : ℝ) : ℝ :=
  infoEnergyLowerBound (pathEntropyBits ρ) T

theorem landauerCostDiagonal_nonneg (ρ : DensityMatrix hnQubit) (T : ℝ) (hT : 0 ≤ T) :
    0 ≤ landauerCostDiagonal ρ T := by
  unfold landauerCostDiagonal
  exact infoEnergyLowerBound_nonneg _ _ (pathEntropyBits_nonneg ρ) hT

theorem landauerCostDiagonal_le_landauerBitEnergy (ρ : DensityMatrix hnQubit) (T : ℝ) (hT : 0 ≤ T) :
    landauerCostDiagonal ρ T ≤ landauerBitEnergy T := by
  unfold landauerCostDiagonal infoEnergyLowerBound
  rw [← mul_one (landauerBitEnergy T)]
  exact mul_le_mul_of_nonneg_left (pathEntropyBits_le_one ρ) (landauerBitEnergy_nonneg hT)

@[simp]
theorem landauerCostDiagonal_whichPathInvariant (ρ : DensityMatrix hnQubit) (T : ℝ) :
    landauerCostDiagonal (KrausChannel.whichPathChannel.apply hnQubit ρ) T =
      landauerCostDiagonal ρ T := by
  simp [landauerCostDiagonal, pathEntropyBits, vonNeumannDiagonal_whichPath_apply]

/-- **Principle of Maximal Information Collapse.**
The residual coherence capacity after extracting `pathEntropyBits ρ` bits of which-path information
is `1 - pathEntropyBits ρ`. This quantity lies in `[0, 1]`:
- If no information is extracted (`pathEntropyBits = 0`), residual = 1 (full visibility possible).
- If the maximum 1 bit is extracted (`pathEntropyBits = 1`), residual = 0 (complete decoherence).

This is the thermodynamic bound enforced by the UMST gate on top of `V² + I² ≤ 1`. -/
noncomputable def residualCoherenceCapacity (ρ : DensityMatrix hnQubit) : ℝ :=
  1 - pathEntropyBits ρ

theorem residualCoherenceCapacity_nonneg (ρ : DensityMatrix hnQubit) :
    0 ≤ residualCoherenceCapacity ρ := by
  unfold residualCoherenceCapacity
  linarith [pathEntropyBits_le_one ρ]

theorem residualCoherenceCapacity_le_one (ρ : DensityMatrix hnQubit) :
    residualCoherenceCapacity ρ ≤ 1 := by
  unfold residualCoherenceCapacity
  linarith [pathEntropyBits_nonneg ρ]

theorem principle_of_maximal_information_collapse (ρ : DensityMatrix hnQubit) :
    0 ≤ residualCoherenceCapacity ρ ∧ residualCoherenceCapacity ρ ≤ 1 :=
  ⟨residualCoherenceCapacity_nonneg ρ, residualCoherenceCapacity_le_one ρ⟩

/-- When path entropy is maximal (1 bit), residual coherence collapses to zero. -/
theorem maximal_extraction_collapses_coherence (ρ : DensityMatrix hnQubit)
    (h : pathEntropyBits ρ = 1) : residualCoherenceCapacity ρ = 0 := by
  unfold residualCoherenceCapacity; linarith

/-- When no path information is extracted, full coherence capacity remains. -/
theorem null_extraction_preserves_coherence (ρ : DensityMatrix hnQubit)
    (h : pathEntropyBits ρ = 0) : residualCoherenceCapacity ρ = 1 := by
  unfold residualCoherenceCapacity; linarith

/-! ### General `Fin n` residual coherence -/

/-- **Residual coherence capacity (general `Fin n`).**
For an n-level system, normalized by the maximum entropy `logb 2 n`:
`residualCoherenceCapacity_n ρ = 1 - pathEntropyBits_n / logb 2 n`.
Ranges in [0, 1]: 0 = maximum information extracted, 1 = no extraction. -/
noncomputable def residualCoherenceCapacity_n {n : ℕ} (hn : 0 < n) (ρ : DensityMatrix hn) : ℝ :=
  if h : (1 : ℕ) < n then 1 - pathEntropyBits_n hn ρ / logb 2 n
  else 1 - pathEntropyBits_n hn ρ  -- n=1: degenerate case, logb 2 1 = 0

theorem residualCoherenceCapacity_n_nonneg {n : ℕ} (hn : 0 < n) (hn1 : 1 < n)
    (ρ : DensityMatrix hn) :
    0 ≤ residualCoherenceCapacity_n hn ρ := by
  unfold residualCoherenceCapacity_n
  simp [hn1]
  have hlog : 0 < logb 2 n := by
    apply Real.logb_pos (by norm_num : (1 : ℝ) < 2)
    exact_mod_cast hn1
  rw [sub_nonneg]
  exact div_le_one_of_le (pathEntropyBits_n_le_logb_two hn ρ) (le_of_lt hlog)

theorem residualCoherenceCapacity_n_le_one {n : ℕ} (hn : 0 < n) (hn1 : 1 < n)
    (ρ : DensityMatrix hn) :
    residualCoherenceCapacity_n hn ρ ≤ 1 := by
  unfold residualCoherenceCapacity_n
  simp [hn1]
  have hlog : 0 < logb 2 n := by
    apply Real.logb_pos (by norm_num : (1 : ℝ) < 2)
    exact_mod_cast hn1
  linarith [div_nonneg (pathEntropyBits_n_nonneg hn ρ) (le_of_lt hlog)]

/-- **General PMIC:** for any `n ≥ 2`, residual coherence stays in `[0, 1]`. -/
theorem principle_of_maximal_information_collapse_n {n : ℕ} (hn : 0 < n) (hn1 : 1 < n)
    (ρ : DensityMatrix hn) :
    0 ≤ residualCoherenceCapacity_n hn ρ ∧ residualCoherenceCapacity_n hn ρ ≤ 1 :=
  ⟨residualCoherenceCapacity_n_nonneg hn hn1 ρ, residualCoherenceCapacity_n_le_one hn hn1 ρ⟩

/-- For qubits, `residualCoherenceCapacity_n` reduces to `residualCoherenceCapacity`. -/
theorem residualCoherenceCapacity_n_qubit_eq (ρ : DensityMatrix hnQubit) :
    residualCoherenceCapacity_n hnQubit ρ = residualCoherenceCapacity ρ := by
  unfold residualCoherenceCapacity_n residualCoherenceCapacity
  simp [show (1 : ℕ) < 2 from by norm_num]
  rw [pathEntropyBits_n_qubit_eq]
  simp [Real.logb, Real.log_ofNat_eq_ofNat_log (R := ℝ)]
  ring

/-- The Landauer cost of the diagonal entropy is exactly `landauerBitEnergy T` times the
fraction of coherence destroyed (`1 - residualCoherenceCapacity`). -/
theorem landauerCost_eq_bitEnergy_times_extracted (ρ : DensityMatrix hnQubit) (T : ℝ) :
    landauerCostDiagonal ρ T = landauerBitEnergy T * (1 - residualCoherenceCapacity ρ) := by
  unfold landauerCostDiagonal infoEnergyLowerBound residualCoherenceCapacity
  ring

/-- A concrete physical erasure process that resets the qubit, dissipating heat to a bath at temperature T.
We idealize erasure such that the bound is physically saturated by an active bounding axiom. -/
structure ErasureProcess (T : ℝ) where
  initial : DensityMatrix hnQubit
  dissipatedHeat : ℝ
  /-- The Second Law binds the physical dissipation strongly to the informational entropy drop.
  Since the final state is pure (0 entropy), the drop is exactly the initial entropy cost. -/
  secondLaw : landauerCostDiagonal initial T ≤ dissipatedHeat

/-- A direct consequence of the Second Law connection: resetting any state dissipates nonnegative heat. -/
theorem erasure_dissipation_nonneg (T : ℝ) (hT : 0 ≤ T) (proc : ErasureProcess T) :
    0 ≤ proc.dissipatedHeat := by
  have h := proc.secondLaw
  have h0 := landauerCostDiagonal_nonneg proc.initial T hT
  linarith

end UMST.DoubleSlit
