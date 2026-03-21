/-
SPDX-License-Identifier: MIT
Copyright (c) 2026 Santhosh Shyamsundar, Santosh Prabhu Shenbagamoorthy — Studio TYTO
-/

import UMSTCore
import MeasurementChannel
import QuantumClassicalBridge
import LandauerBound
import EpistemicSensing
import GeneralVisibility

/-!
# GateCompat — UMST `Admissible` shape vs qubit path statistics

Maps a `2 × 2` density matrix to a **minimal** `ThermodynamicState` so that the four `UMST.Core`
conjuncts can be checked. The mapping is intentionally **schematic**: Born weights sit in `density`
and `freeEnergy`; `hydration` and `strength` are fixed at `0` so the latter two conjuncts are trivial.

**Proved:** after **`whichPathChannel.apply`**, the scaffold is **unchanged** (diagonal / Born weights
invariant), hence **`Admissible` holds** between before/after (in fact reflexively on the image).

**Not yet:** physically motivated `ℝ` calibration, or nontrivial hydration/strength from QM.
-/

namespace UMST.DoubleSlit

open UMST.Core UMST.Quantum

/-- Minimal ℝ scaffold from computational-basis path weights. -/
noncomputable def thermoFromQubitPath (ρ : DensityMatrix hnQubit) : ThermodynamicState where
  density := pathWeight ρ 0
  freeEnergy := pathWeight ρ 1
  hydration := 0
  strength := 0

@[simp]
theorem thermoFromQubitPath_whichPath (ρ : DensityMatrix hnQubit) :
    thermoFromQubitPath (KrausChannel.whichPathChannel.apply hnQubit ρ) = thermoFromQubitPath ρ := by
  simp [thermoFromQubitPath, pathWeight_whichPath_apply]

theorem admissible_thermoFromQubitPath_whichPath (ρ : DensityMatrix hnQubit) :
    Admissible (thermoFromQubitPath ρ)
      (thermoFromQubitPath (KrausChannel.whichPathChannel.apply hnQubit ρ)) := by
  rw [thermoFromQubitPath_whichPath]
  exact admissibleRefl _

/-! ## Thermodynamic calibration: `freeEnergy = -T · S(ρ)` (Gap 10)

The physically motivated scaffold maps a qubit density matrix to a `ThermodynamicState` where:

- `density` = Born weight `p₀ = ρ₀₀` (total path probability for slit 0).
- `freeEnergy` = **negative Landauer cost** `- k_B T ln(2) · pathEntropyBits(ρ)`.
  This is the Helmholtz free energy interpretation: the entropy contribution `T·S` reduces
  the extractable work. The sign convention matches `F = U - TS` with internal energy `U = 0`.
- `hydration`, `strength` = 0 (schematic; no QM content).

**Proved:**
- After `whichPathChannel.apply`, diagonal entropy is invariant → **scaffold unchanged** →
  `Admissible` reflexively.
- `freeEnergy` is bounded: `|freeEnergy| ≤ landauerBitEnergy T` (one-bit cap).
-/

/-- Calibrated ℝ scaffold: `freeEnergy = -landauerCostDiagonal ρ T`. -/
noncomputable def thermoCalibratedScaffold (ρ : DensityMatrix hnQubit) (T : ℝ) :
    ThermodynamicState where
  density := pathWeight ρ 0
  freeEnergy := -landauerCostDiagonal ρ T
  hydration := 0
  strength := 0

@[simp]
theorem thermoCalibratedScaffold_whichPath (ρ : DensityMatrix hnQubit) (T : ℝ) :
    thermoCalibratedScaffold (KrausChannel.whichPathChannel.apply hnQubit ρ) T =
      thermoCalibratedScaffold ρ T := by
  simp [thermoCalibratedScaffold, pathWeight_whichPath_apply]

theorem admissible_thermoCalibratedScaffold_whichPath (ρ : DensityMatrix hnQubit) (T : ℝ) :
    Admissible (thermoCalibratedScaffold ρ T)
      (thermoCalibratedScaffold (KrausChannel.whichPathChannel.apply hnQubit ρ) T) := by
  rw [thermoCalibratedScaffold_whichPath]
  exact admissibleRefl _

/-- The calibrated free energy is nonpositive for `T ≥ 0`. -/
theorem thermoCalibratedScaffold_freeEnergy_nonpos (ρ : DensityMatrix hnQubit) (T : ℝ)
    (hT : 0 ≤ T) :
    (thermoCalibratedScaffold ρ T).freeEnergy ≤ 0 := by
  simp only [thermoCalibratedScaffold]
  linarith [landauerCostDiagonal_nonneg ρ T hT]

/-- `|freeEnergy| ≤ landauerBitEnergy T` — the free energy magnitude is bounded by the
one-bit Landauer energy scale. -/
theorem thermoCalibratedScaffold_freeEnergy_bounded (ρ : DensityMatrix hnQubit) (T : ℝ)
    (hT : 0 ≤ T) :
    |(thermoCalibratedScaffold ρ T).freeEnergy| ≤ landauerBitEnergy T := by
  simp only [thermoCalibratedScaffold]
  rw [abs_neg]
  exact abs_of_nonneg (landauerCostDiagonal_nonneg ρ T hT) ▸
    landauerCostDiagonal_le_landauerBitEnergy ρ T hT

/-! ## Physical Calibration: Hydration & Strength (Gap 10) -/

/-- Physically calibrated hydration: decoherence fraction `1 - visibility`.
This maps the irreversible loss of quantum interference to the irreversible
thermodynamic hydration process. 0 = full fringe, 1 = fully classical. -/
noncomputable def calibratedHydration (ρ : DensityMatrix hnQubit) : ℝ :=
  1 - fringeVisibility ρ

theorem calibratedHydration_nonneg (ρ : DensityMatrix hnQubit) :
    0 ≤ calibratedHydration ρ := by
  unfold calibratedHydration
  linarith [fringeVisibility_le_one ρ]

theorem calibratedHydration_le_one (ρ : DensityMatrix hnQubit) :
    calibratedHydration ρ ≤ 1 := by
  unfold calibratedHydration
  linarith [fringeVisibility_nonneg ρ]

@[simp]
theorem calibratedHydration_whichPath (ρ : DensityMatrix hnQubit) :
    calibratedHydration (KrausChannel.whichPathChannel.apply hnQubit ρ) = 1 := by
  simp [calibratedHydration, fringeVisibility_whichPath_apply]

/-- Physically calibrated strength: probe measurement fidelity (strength surrogate).
This maps the epistemic capacity of the measurement to material strength. -/
noncomputable def calibratedStrength (P : QuantumProbe) (ρ : DensityMatrix hnQubit) : ℝ :=
  ProbeStrength P ρ

theorem calibratedStrength_nonneg (P : QuantumProbe) (ρ : DensityMatrix hnQubit) :
    0 ≤ calibratedStrength P ρ :=
  ProbeStrength_nonneg P ρ

theorem calibratedStrength_le_one (P : QuantumProbe) (ρ : DensityMatrix hnQubit) :
    calibratedStrength P ρ ≤ 1 :=
  ProbeStrength_le_one P ρ

/-- Full calibrated gate state with physical content:
- `freeEnergy`: negative Landauer cost
- `hydration`: decoherence fraction `1 - fringeVisibility`
- `strength`: probe fidelity (e.g. `whichPathDistinguishability`) -/
noncomputable def thermoCalibratedPhys (P : QuantumProbe) (ρ : DensityMatrix hnQubit) (T : ℝ) :
    ThermodynamicState where
  density := pathWeight ρ 0
  freeEnergy := -landauerCostDiagonal ρ T
  hydration := calibratedHydration ρ
  strength := calibratedStrength P ρ

/-! ## General Dimension `Fin n` Extensions (Gaps 2 & 10) -/

/-- N-dimensional physical hydration metric built from the $l_1$ norm of coherence. -/
noncomputable def calibratedHydration_n {n : ℕ} (hn : 0 < n) (ρ : DensityMatrix hn) : ℝ :=
  1 - fringeVisibility_n hn ρ

/-- Full N-dimensional calibrated gate state. 
Connects diagonal Landauer bounds spanning $N$ dimensions with $N$-slit visibility for the
thermodynamic and epistemic metrics. -/
noncomputable def thermoCalibratedPhys_n {n : ℕ} (hn : 0 < n) (P : QuantumProbe) 
    (ρ : DensityMatrix hn) (T : ℝ) : ThermodynamicState where
  density := pathWeight ρ 0
  freeEnergy := -landauerCostDiagonal_n_real hn ρ T
  hydration := calibratedHydration_n hn ρ
  strength := 0 -- Placeholder for generalized probe strength.

/-- For the canonical measuring probe, the calibrated physical state satisfies the standard
`Admissible` thermodynamic conditions across the path measurement channel. -/
theorem admissible_thermoCalibratedPhys_whichPath (ρ : DensityMatrix hnQubit) (T : ℝ) :
    Admissible (thermoCalibratedPhys whichPathProbe ρ T)
      (thermoCalibratedPhys whichPathProbe (KrausChannel.whichPathChannel.apply hnQubit ρ) T) := by
  constructor
  · -- MassCond
    simp [MassCond, thermoCalibratedPhys, δMass, pathWeight_whichPath_apply, sub_self, abs_zero]
  constructor
  · -- DissipCond
    simp [DissipCond, thermoCalibratedPhys, landauerCostDiagonal_whichPathInvariant, le_refl]
  constructor
  · -- HydratCond: old.hydration ≤ new.hydration
    simp [HydratCond, thermoCalibratedPhys, calibratedHydration_whichPath]
    exact calibratedHydration_le_one ρ
  · -- StrengthCond: old.strength ≤ new.strength
    simp [StrengthCond, thermoCalibratedPhys, calibratedStrength, whichPathProbe_strength_invariant]

end UMST.DoubleSlit
