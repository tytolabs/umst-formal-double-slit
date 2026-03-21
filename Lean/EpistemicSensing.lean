/-
SPDX-License-Identifier: MIT
Copyright (c) 2026 Santhosh Shyamsundar, Santosh Prabhu Shenbagamoorthy — Studio TYTO
-/

import DoubleSlit

/-!
# EpistemicSensing — interface layer for probe selection

This module adds a **formal interface** for epistemic probe policies over the existing path-qubit
stack.

- `QuantumProbe`: probe map + scalar strength surrogate in `[0,1]`.
- `whichPathProbe`: canonical probe induced by Lüders which-path measurement.
- `IsMaxMIProbeAt`: pointwise "max-strength" witness over a probe set.
- `LandauerCostFromProbeStrength`: SI energy hook for a chosen probe strength.

This is a structural step toward the full epistemic-sensing plan; it does **not** yet encode
trajectory MI estimation, PPO, or a concrete dissipation model.
-/

namespace UMST.DoubleSlit

open UMST.Core UMST.Quantum

/-- A probe policy on the path qubit with a scalar strength surrogate in `[0,1]`. -/
structure QuantumProbe where
  apply : DensityMatrix hnQubit → DensityMatrix hnQubit
  strength : DensityMatrix hnQubit → ℝ
  strength_bounds : ∀ ρ, 0 ≤ strength ρ ∧ strength ρ ≤ 1

/-- Strength of a probe at a given state (coarse MI surrogate). -/
noncomputable def ProbeStrength (P : QuantumProbe) (ρ : DensityMatrix hnQubit) : ℝ :=
  P.strength ρ

theorem ProbeStrength_nonneg (P : QuantumProbe) (ρ : DensityMatrix hnQubit) :
    0 ≤ ProbeStrength P ρ :=
  (P.strength_bounds ρ).1

theorem ProbeStrength_le_one (P : QuantumProbe) (ρ : DensityMatrix hnQubit) :
    ProbeStrength P ρ ≤ 1 :=
  (P.strength_bounds ρ).2

/-- Canonical which-path probe: apply Lüders channel, use `whichPathDistinguishability` as strength. -/
noncomputable def whichPathProbe : QuantumProbe where
  apply := KrausChannel.whichPathChannel.apply hnQubit
  strength := whichPathDistinguishability
  strength_bounds := fun ρ => ⟨whichPathDistinguishability_nonneg ρ, whichPathDistinguishability_le_one ρ⟩

@[simp]
theorem whichPathProbe_apply (ρ : DensityMatrix hnQubit) :
    whichPathProbe.apply ρ = KrausChannel.whichPathChannel.apply hnQubit ρ :=
  rfl

@[simp]
theorem whichPathProbe_strength (ρ : DensityMatrix hnQubit) :
    ProbeStrength whichPathProbe ρ = whichPathDistinguishability ρ :=
  rfl

/-- Pointwise maximal-strength witness over a probe set at a state `ρ`. -/
def IsMaxMIProbeAt (probes : Set QuantumProbe) (ρ : DensityMatrix hnQubit) (P : QuantumProbe) : Prop :=
  P ∈ probes ∧ ∀ Q, Q ∈ probes → ProbeStrength Q ρ ≤ ProbeStrength P ρ

/-- Trivial maximality: the only probe in a singleton set is maximal at every state. -/
theorem whichPathProbe_isMax_on_singleton (ρ : DensityMatrix hnQubit) :
    IsMaxMIProbeAt ({whichPathProbe} : Set QuantumProbe) ρ whichPathProbe := by
  constructor
  · simp
  · intro Q hQ
    simpa [Set.mem_singleton_iff.mp hQ]

/-- Probe strength is invariant under applying `whichPathProbe` itself. -/
theorem whichPathProbe_strength_invariant (ρ : DensityMatrix hnQubit) :
    ProbeStrength whichPathProbe (whichPathProbe.apply ρ) = ProbeStrength whichPathProbe ρ := by
  simpa [whichPathProbe_apply, whichPathProbe_strength] using
    whichPathDistinguishability_whichPath_apply ρ

/-- MI surrogate attached to which-path probing: diagonal path entropy (nats). -/
noncomputable def whichPathMI (ρ : DensityMatrix hnQubit) : ℝ :=
  vonNeumannDiagonal ρ

theorem whichPathMI_nonneg (ρ : DensityMatrix hnQubit) : 0 ≤ whichPathMI ρ :=
  vonNeumannDiagonal_nonneg ρ

theorem whichPathMI_le_log_two (ρ : DensityMatrix hnQubit) : whichPathMI ρ ≤ Real.log 2 :=
  vonNeumannDiagonal_le_log_two ρ

@[simp]
theorem whichPathMI_whichPath_apply (ρ : DensityMatrix hnQubit) :
    whichPathMI (whichPathProbe.apply ρ) = whichPathMI ρ := by
  simpa [whichPathMI, whichPathProbe_apply] using vonNeumannDiagonal_whichPath_apply ρ

/-- Null probe: identity channel with zero epistemic strength extraction. -/
noncomputable def nullProbe : QuantumProbe where
  apply := (KrausChannel.identity 2).apply hnQubit
  strength := fun _ => 0
  strength_bounds := fun _ => ⟨le_rfl, by norm_num⟩

@[simp]
theorem nullProbe_strength (ρ : DensityMatrix hnQubit) :
    ProbeStrength nullProbe ρ = 0 :=
  rfl

@[simp]
theorem nullProbe_apply (ρ : DensityMatrix hnQubit) :
    nullProbe.apply ρ = ρ := by
  apply DensityMat.ext
  simpa [nullProbe, KrausChannel.apply] using
    KrausChannel.identity_map 2 ρ.carrier

/-- Pointwise dominance: `P` extracts at least as much probe strength as `Q` at state `ρ`. -/
def ProbeDominatesAt (P Q : QuantumProbe) (ρ : DensityMatrix hnQubit) : Prop :=
  ProbeStrength Q ρ ≤ ProbeStrength P ρ

/-- Global dominance across all path-qubit states. -/
def ProbeDominates (P Q : QuantumProbe) : Prop :=
  ∀ ρ, ProbeDominatesAt P Q ρ

theorem whichPathProbe_dominates_nullProbe : ProbeDominates whichPathProbe nullProbe := by
  intro ρ
  simp [ProbeDominatesAt, nullProbe_strength, ProbeStrength_nonneg]

/-- Null probe preserves interference exactly (identity channel). -/
theorem interference_preserved_nullProbe (ρ : DensityMatrix hnQubit) :
    fringeVisibility (nullProbe.apply ρ) = fringeVisibility ρ := by
  simp [nullProbe_apply]

/-- Which-path probe collapses fringes (`V = 0`). -/
theorem collapse_on_whichPathProbe (ρ : DensityMatrix hnQubit) :
    fringeVisibility (whichPathProbe.apply ρ) = 0 := by
  simpa [whichPathProbe_apply] using fringeVisibility_whichPath_apply ρ

/-- `whichPathProbe` is maximal on the two-probe set `{nullProbe, whichPathProbe}`. -/
theorem whichPathProbe_isMax_on_null_pair (ρ : DensityMatrix hnQubit) :
    IsMaxMIProbeAt ({nullProbe, whichPathProbe} : Set QuantumProbe) ρ whichPathProbe := by
  constructor
  · simp
  · intro Q hQ
    rcases Set.mem_insert_iff.mp hQ with h | h
    · subst h
      simp [nullProbe_strength, ProbeStrength_nonneg]
    · simpa [Set.mem_singleton_iff.mp h]

/-- Maximal probe index in a finite probe family at state `ρ`. -/
def IsMaxProbeIndexAt {ι : Type*} (family : ι → QuantumProbe) (ρ : DensityMatrix hnQubit)
    (i : ι) : Prop :=
  ∀ j, ProbeStrength (family j) ρ ≤ ProbeStrength (family i) ρ

theorem exists_maxProbeIndexAt {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (family : ι → QuantumProbe) (ρ : DensityMatrix hnQubit) :
    ∃ i, IsMaxProbeIndexAt family ρ i := by
  obtain ⟨i, hi, hmax⟩ :=
    (Finset.univ : Finset ι).exists_max_image (fun j => ProbeStrength (family j) ρ)
      (Finset.univ_nonempty)
  refine ⟨i, ?_⟩
  intro j
  exact hmax j (Finset.mem_univ j)

/-- Noncomputable argmax choice from a finite probe family. -/
noncomputable def argmaxProbeIndexAt {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (family : ι → QuantumProbe) (ρ : DensityMatrix hnQubit) : ι :=
  Classical.choose (exists_maxProbeIndexAt family ρ)

theorem argmaxProbeIndexAt_spec {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (family : ι → QuantumProbe) (ρ : DensityMatrix hnQubit) :
    IsMaxProbeIndexAt family ρ (argmaxProbeIndexAt family ρ) :=
  Classical.choose_spec (exists_maxProbeIndexAt family ρ)

/-- Two-probe family: index `0` is `nullProbe`, index `1` is `whichPathProbe`. -/
noncomputable def nullWhichFamily : Fin 2 → QuantumProbe
  | 0 => nullProbe
  | 1 => whichPathProbe

@[simp]
theorem nullWhichFamily_zero : nullWhichFamily 0 = nullProbe :=
  rfl

@[simp]
theorem nullWhichFamily_one : nullWhichFamily 1 = whichPathProbe :=
  rfl

/-- If distinguishability is strictly positive, argmax on `{nullProbe, whichPathProbe}`
chooses `whichPathProbe` (index `1`). -/
theorem argmax_nullWhichFamily_eq_which_of_pos (ρ : DensityMatrix hnQubit)
    (hpos : 0 < whichPathDistinguishability ρ) :
    argmaxProbeIndexAt nullWhichFamily ρ = 1 := by
  have hmax := argmaxProbeIndexAt_spec nullWhichFamily ρ
  let i := argmaxProbeIndexAt nullWhichFamily ρ
  have h1 : ProbeStrength (nullWhichFamily 1) ρ ≤ ProbeStrength (nullWhichFamily i) ρ := hmax 1
  cases i using Fin.cases with
  | zero =>
      have hle : whichPathDistinguishability ρ ≤ 0 := by
        simpa [nullWhichFamily, nullProbe_strength, whichPathProbe_strength] using h1
      exact (not_le_of_gt hpos hle).elim
  | succ i =>
      -- `Fin 2` has only `1` as successor case.
      fin_cases i
      simp [i]

/-- SI Landauer hook from any probe strength surrogate. -/
noncomputable def LandauerCostFromProbeStrength (P : QuantumProbe) (ρ : DensityMatrix hnQubit)
    (T : ℝ) : ℝ :=
  infoEnergyLowerBound (ProbeStrength P ρ) T

theorem LandauerCostFromProbeStrength_nonneg (P : QuantumProbe) (ρ : DensityMatrix hnQubit)
    (T : ℝ) (hT : 0 ≤ T) :
    0 ≤ LandauerCostFromProbeStrength P ρ T := by
  unfold LandauerCostFromProbeStrength
  exact infoEnergyLowerBound_nonneg _ _ (ProbeStrength_nonneg P ρ) hT

theorem LandauerCostFromProbeStrength_le_landauerBitEnergy (P : QuantumProbe)
    (ρ : DensityMatrix hnQubit) (T : ℝ) (hT : 0 ≤ T) :
    LandauerCostFromProbeStrength P ρ T ≤ landauerBitEnergy T := by
  unfold LandauerCostFromProbeStrength infoEnergyLowerBound
  rw [← mul_one (landauerBitEnergy T)]
  exact mul_le_mul_of_nonneg_left (ProbeStrength_le_one P ρ) (landauerBitEnergy_nonneg hT)

theorem LandauerCostFromProbeStrength_nullProbe (ρ : DensityMatrix hnQubit) (T : ℝ) :
    LandauerCostFromProbeStrength nullProbe ρ T = 0 := by
  simp [LandauerCostFromProbeStrength, nullProbe_strength, infoEnergyLowerBound]

theorem LandauerCostFromProbeStrength_mono (P Q : QuantumProbe) (ρ : DensityMatrix hnQubit)
    (T : ℝ) (hT : 0 ≤ T) (hPQ : ProbeStrength Q ρ ≤ ProbeStrength P ρ) :
    LandauerCostFromProbeStrength Q ρ T ≤ LandauerCostFromProbeStrength P ρ T := by
  unfold LandauerCostFromProbeStrength infoEnergyLowerBound
  exact mul_le_mul_of_nonneg_left hPQ (landauerBitEnergy_nonneg hT)

/-- Bridge to existing `MeasurementUpdate` instance: which-path update is info-monotone. -/
theorem measurementUpdateWhichPath_info_monotone (ρ : DensityMatrix hnQubit) :
    (measurementUpdateWhichPath ρ).oldState.I ≤ (measurementUpdateWhichPath ρ).newState.I :=
  (measurementUpdateWhichPath ρ).hInfoMonotone

/-- Bridge to existing `MeasurementUpdate` instance: which-path update drops visibility. -/
theorem measurementUpdateWhichPath_visibility_drop (ρ : DensityMatrix hnQubit) :
    (measurementUpdateWhichPath ρ).newState.V ≤ (measurementUpdateWhichPath ρ).oldState.V :=
  (measurementUpdateWhichPath ρ).hVisibilityDrop

end UMST.DoubleSlit
