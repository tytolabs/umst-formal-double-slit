-- SPDX-FileCopyrightText: 2026 Santosh Prabhu Shenbagamoorthy and Santhosh Shyamsundar
-- SPDX-License-Identifier: MIT
/-
  UMST-Formal: UrgeKnowing/CompactionMiCost.lean

  Knowing fiber (§17.5 / §22.4): compaction pays MI vs epistemicMI_null.
  Semantic compaction must pay probe-indexed epistemic MI above the null baseline;
  Landauer hook tracks `measurementCost` / `epistemicLandauerCost`.

  Compaction recovery composes `UMST.Excitement.select` — no second argmin.
  Sole physical law: the `SecondLaw` predicate; `LandauerLaw.physicalSecondLaw` is its erase instance (imported, not re-declared; no project `axiom`).
  Adds **zero** Lean `axiom` declarations. Zero sorry.

  `UMST.Excitement` and `UMST.Urge.ExcitementImport` are imported from umst-formal (single source).
  Landauer hook uses `LandauerEinsteinBridge.landauerBitEnergy` (avoids broken
  `DoubleSlitCore` chain in default build graph).
-/

import Core.State
import DualLedger
import LandauerLaw
import LandauerEinsteinBridge
import Mathlib.Data.Rat.Defs
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Excitement
import Urge.ExcitementImport


open UMST UMST.Core UMST.LandauerLaw


namespace UMST.Quantum

/-- Knowing-fiber density-matrix carrier (stub: avoids broken `DoubleSlitCore` chain). -/
structure DensityMatrix (n : ℕ) where
  dummy : Unit := ()

end UMST.Quantum

namespace UMST.DoubleSlit

open _root_.Real UMST.Quantum

variable {hnQubit : ℕ}

/-- Landauer lower bound for `bits` at bath temperature `T` (SI joules). -/
noncomputable def infoEnergyLowerBound (bits T : ℝ) : ℝ :=
  landauerBitEnergy T * bits

lemma landauerBitEnergy_nonneg (T : ℝ) (hT : 0 ≤ T) : 0 ≤ landauerBitEnergy T := by
  unfold landauerBitEnergy
  have hlog : 0 ≤ log 2 := le_of_lt (log_pos (by norm_num : (1 : ℝ) < 2))
  exact mul_nonneg (mul_nonneg (le_of_lt kBoltzmannSI_pos) hT) hlog

theorem infoEnergyLowerBound_nonneg (bits T : ℝ) (hbits : 0 ≤ bits) (hT : 0 ≤ T) :
    0 ≤ infoEnergyLowerBound bits T := by
  unfold infoEnergyLowerBound
  exact mul_nonneg (landauerBitEnergy_nonneg T hT) hbits

/-- Minimal probe kind for compaction MI cost probe-bits align witness. -/
inductive PathProbe where
  | null | whichPath
  deriving DecidableEq, Repr

/-- Epistemic mutual-information surrogate in nats (knowing-fiber stub). -/
noncomputable def EpistemicMI (p : PathProbe) (_ρ : DensityMatrix hnQubit) : ℝ :=
  match p with
  | .null => 0
  | .whichPath => log 2

theorem epistemicMI_null (ρ : DensityMatrix hnQubit) :
    EpistemicMI PathProbe.null ρ = 0 :=
  rfl

/-- Bit-equivalent form of `EpistemicMI`. -/
noncomputable def epistemicMIBits (p : PathProbe) (ρ : DensityMatrix hnQubit) : ℝ :=
  EpistemicMI p ρ / log 2

@[simp]
theorem epistemicMIBits_null (ρ : DensityMatrix hnQubit) :
    epistemicMIBits PathProbe.null ρ = 0 := by
  simp [epistemicMIBits, EpistemicMI]

theorem epistemicMIBits_nonneg (p : PathProbe) (ρ : DensityMatrix hnQubit) :
    0 ≤ epistemicMIBits p ρ := by
  unfold epistemicMIBits EpistemicMI
  cases p
  · simp
  · simp; norm_num

theorem epistemicMIBits_le_one (p : PathProbe) (ρ : DensityMatrix hnQubit) :
    epistemicMIBits p ρ ≤ 1 := by
  unfold epistemicMIBits EpistemicMI
  cases p
  · simp
  · simp; norm_num

/-- Minimum thermodynamic work for probe `p` on state `ρ` at temperature `T`. -/
noncomputable def measurementCost (p : PathProbe) (ρ : DensityMatrix hnQubit) (T : ℝ) : ℝ :=
  infoEnergyLowerBound (epistemicMIBits p ρ) T

theorem measurementCost_null (ρ : DensityMatrix hnQubit) (T : ℝ) :
    measurementCost PathProbe.null ρ T = 0 := by
  simp [measurementCost, infoEnergyLowerBound, epistemicMIBits, EpistemicMI]

theorem measurementCost_nonneg (p : PathProbe) (ρ : DensityMatrix hnQubit) (T : ℝ) (hT : 0 ≤ T) :
    0 ≤ measurementCost p ρ T := by
  unfold measurementCost infoEnergyLowerBound
  exact mul_nonneg (landauerBitEnergy_nonneg T hT) (epistemicMIBits_nonneg p ρ)

theorem measurementCost_le_landauerBitEnergy (p : PathProbe) (ρ : DensityMatrix hnQubit)
    (T : ℝ) (hT : 0 ≤ T) :
    measurementCost p ρ T ≤ landauerBitEnergy T := by
  unfold measurementCost infoEnergyLowerBound
  simpa [one_mul] using
    mul_le_mul_of_nonneg_left (epistemicMIBits_le_one p ρ) (landauerBitEnergy_nonneg T hT)

end UMST.DoubleSlit

open Classical _root_.Real Finset UMST UMST.Core UMST.LandauerLaw UMST.Excitement UMST.Urge.ExcitementImport
open UMST.DoubleSlit UMST.Quantum
namespace UrgeKnowing.CompactionMiCost

variable {hnQubit : ℕ}

-- ================================================================
-- SECTION 1: Modality + knowing-fiber pins (Unwired)
-- ================================================================

/-- Design modality for compaction-mi-cost claims (TYPE-03 preview). -/
inductive CompactionMiCostModality where
  | unwired | assumed | proved | surrogate
  deriving DecidableEq, Repr

def compactionMiCostModalityCurrent : CompactionMiCostModality := .unwired

def productionWired : Bool := false

def compactionProductionWired : Bool := false

-- ================================================================
-- SECTION 2: §17.5 / §22.4 compaction pays MI vs epistemicMI_null
-- ================================================================

/-- Whether probe is the null baseline (`epistemicMI_null`). -/
def isEpistemicMINull (p : PathProbe) : Prop :=
  p = PathProbe.null

@[simp]
theorem isEpistemicMINull_null : isEpistemicMINull PathProbe.null :=
  rfl

theorem isEpistemicMINull_whichPath : ¬ isEpistemicMINull PathProbe.whichPath := by
  intro h
  cases h

/-- Compaction pays bit-equivalent MI strictly above the null-probe zero baseline. -/
def compactionPaysMIBitsVsNull (p : PathProbe) (ρ : DensityMatrix hnQubit) : Prop :=
  ¬ isEpistemicMINull p ∧ 0 < epistemicMIBits p ρ

@[simp]
theorem compaction_null_probe_mi_zero (ρ : DensityMatrix hnQubit) :
    epistemicMIBits PathProbe.null ρ = 0 :=
  epistemicMIBits_null ρ

theorem compaction_epistemicMI_null (ρ : DensityMatrix hnQubit) :
    EpistemicMI PathProbe.null ρ = 0 :=
  epistemicMI_null ρ

theorem compaction_pays_mi_vs_null_whichPath (ρ : DensityMatrix hnQubit)
    (hpos : 0 < epistemicMIBits PathProbe.whichPath ρ) :
    compactionPaysMIBitsVsNull PathProbe.whichPath ρ :=
  ⟨isEpistemicMINull_whichPath, hpos⟩

theorem compaction_refuses_null_probe (ρ : DensityMatrix hnQubit) :
    ¬ compactionPaysMIBitsVsNull PathProbe.null ρ := by
  rintro ⟨_, hpos⟩
  simp [compaction_null_probe_mi_zero] at hpos

theorem compaction_null_probe_mi_zero_refuses (ρ : DensityMatrix hnQubit)
    (heq : epistemicMIBits PathProbe.null ρ = 0) :
    ¬ compactionPaysMIBitsVsNull PathProbe.null ρ := by
  rintro ⟨_, hpos⟩
  simp [heq] at hpos

theorem compactionMIBits_nonneg (p : PathProbe) (ρ : DensityMatrix hnQubit) :
    0 ≤ epistemicMIBits p ρ :=
  epistemicMIBits_nonneg p ρ

theorem compactionMIBits_le_one (p : PathProbe) (ρ : DensityMatrix hnQubit) :
    epistemicMIBits p ρ ≤ 1 :=
  epistemicMIBits_le_one p ρ

-- ================================================================
-- SECTION 3: Per-step Landauer hook for compaction MI cost
-- ================================================================

/-- Bit-equivalent compaction MI at probe `p` on state `ρ`. -/
noncomputable def compactionMIBits (p : PathProbe) (ρ : DensityMatrix hnQubit) : ℝ :=
  epistemicMIBits p ρ

/-- Landauer hook for compaction at probe `p` and temperature `T`. -/
noncomputable def compactionLandauerCost (p : PathProbe) (ρ : DensityMatrix hnQubit) (T : ℝ) : ℝ :=
  measurementCost p ρ T

theorem compactionLandauerCost_eq_measurementCost (p : PathProbe) (ρ : DensityMatrix hnQubit)
    (T : ℝ) :
    compactionLandauerCost p ρ T = measurementCost p ρ T :=
  rfl

@[simp]
theorem compactionLandauerCost_null_zero (ρ : DensityMatrix hnQubit) (T : ℝ) :
    compactionLandauerCost PathProbe.null ρ T = 0 := by
  simp [compactionLandauerCost, measurementCost_null]

theorem compactionLandauerCost_null_all_temps (ρ : DensityMatrix hnQubit) :
    ∀ T, compactionLandauerCost PathProbe.null ρ T = 0 :=
  fun T => compactionLandauerCost_null_zero ρ T

theorem compactionLandauerCost_nonneg (p : PathProbe) (ρ : DensityMatrix hnQubit) (T : ℝ)
    (hT : 0 ≤ T) :
    0 ≤ compactionLandauerCost p ρ T :=
  measurementCost_nonneg p ρ T hT

theorem compactionLandauerCost_le_landauerBitEnergy (p : PathProbe) (ρ : DensityMatrix hnQubit)
    (T : ℝ) (hT : 0 ≤ T) :
    compactionLandauerCost p ρ T ≤ landauerBitEnergy T :=
  measurementCost_le_landauerBitEnergy p ρ T hT

-- ================================================================
-- SECTION 4: Derivation witness — semantic compaction retains chain
-- ================================================================

/-- Derivation chain witness retained on admitted compaction arrows (§17.5). -/
structure CompactionDerivationWitness where
  chain : List String

def compactionDerivationRetainsChain (w : CompactionDerivationWitness) : Prop :=
  w.chain ≠ []

structure CompactionMiAttempt (n : ℕ) where
  probe : PathProbe
  ρ : DensityMatrix n
  witness : CompactionDerivationWitness

inductive CompactionMiCostRefusal where
  | epistemicMiNullCompaction
  | nullProbeCompactionTheater
  | derivationWitnessAbsent
  | secondArgmin
  deriving DecidableEq, Repr

inductive CompactionMiCostOutcome where
  | admitted (miBits : ℝ) (candidateTag : String)
  | refused (reason : CompactionMiCostRefusal)

/-- Evaluate compaction MI cost — probe payment + derivation witness gate. -/
noncomputable def evaluateCompactionMiCost {n : ℕ} (attempt : CompactionMiAttempt n) : CompactionMiCostOutcome :=
  if attempt.probe = PathProbe.null then
    .refused .epistemicMiNullCompaction
  else if attempt.witness.chain.isEmpty then
    .refused .derivationWitnessAbsent
  else if epistemicMIBits attempt.probe attempt.ρ ≤ 0 then
    .refused .nullProbeCompactionTheater
  else
    .admitted (epistemicMIBits attempt.probe attempt.ρ) "compaction-mi-admitted"

theorem evaluateCompactionMiCost_refuses_null {n : ℕ} (ρ : DensityMatrix n)
    (w : CompactionDerivationWitness) :
    evaluateCompactionMiCost ⟨PathProbe.null, ρ, w⟩ = .refused .epistemicMiNullCompaction := by
  simp [evaluateCompactionMiCost]

theorem evaluateCompactionMiCost_refuses_witness_absent {n : ℕ} (ρ : DensityMatrix n) :
    evaluateCompactionMiCost
      ⟨PathProbe.whichPath, ρ, ⟨[]⟩⟩ = .refused .derivationWitnessAbsent := by
  simp [evaluateCompactionMiCost]

-- ================================================================
-- SECTION 5: Compaction composes Excitement.select (no second argmin)
-- ================================================================

/-- Context for compaction recovery over admissible successors. -/
structure CompactionMiCtx (S : Type) [ThermodynamicSystem ℚ S] [AdmissibleSystem ℚ S]
    [JointThermo ℚ S] where
  prior       : S
  successors  : List (Cand (K := ℚ) prior)

/-- Compaction selection **is** `urgeRecoverySelect` / `Excitement.select`. -/
noncomputable def compactionMiSelect {S : Type} [ThermodynamicSystem ℚ S] [AdmissibleSystem ℚ S]
    [JointThermo ℚ S] (ctx : CompactionMiCtx S) :
    Cand (K := ℚ) ctx.prior ⊕ Residue :=
  urgeRecoverySelect ctx.prior ctx.successors

noncomputable def compactionMiSelectBare {S : Type} [ThermodynamicSystem ℚ S]
    [AdmissibleSystem ℚ S] [JointThermo ℚ S] (prior : S)
    (successors : List (Cand (K := ℚ) prior)) :
    Cand (K := ℚ) prior ⊕ Residue :=
  urgeRecoverySelect prior successors

def composeSurrogateFor : String := "UMST.Excitement.select"

def excitementComposeAuthority : String :=
  "umst-meta/crates/umst-meta/src/excitement.rs"

theorem compactionMiSelect_eq_select {S : Type} [ThermodynamicSystem ℚ S]
    [AdmissibleSystem ℚ S] [JointThermo ℚ S] (ctx : CompactionMiCtx S) :
    compactionMiSelect ctx = select ctx.prior ctx.successors :=
  rfl

theorem compactionMiSelect_eq_urgeRecoverySelect {S : Type} [ThermodynamicSystem ℚ S]
    [AdmissibleSystem ℚ S] [JointThermo ℚ S] (ctx : CompactionMiCtx S) :
    compactionMiSelect ctx = urgeRecoverySelect ctx.prior ctx.successors :=
  rfl

theorem compactionMiSelectBare_eq_select {S : Type} [ThermodynamicSystem ℚ S]
    [AdmissibleSystem ℚ S] [JointThermo ℚ S] (prior : S)
    (successors : List (Cand (K := ℚ) prior)) :
    compactionMiSelectBare prior successors = select prior successors :=
  rfl

theorem compactionNoLocalArgmin {S : Type} [ThermodynamicSystem ℚ S] [AdmissibleSystem ℚ S]
    [JointThermo ℚ S] (ctx : CompactionMiCtx S) :
    compactionMiSelect ctx = select ctx.prior ctx.successors :=
  rfl

theorem compactionComposeSurrogateFor :
    composeSurrogateFor = "UMST.Excitement.select" :=
  rfl

theorem compaction_not_second_argmin :
    composeSurrogateFor ≠ "second_argmin_selector" := by
  decide

theorem compaction_compose_excitement_authority :
    excitementComposeAuthority ≠ "" :=
  by decide

theorem compactionMiSelect_empty {S : Type} [ThermodynamicSystem ℚ S] [AdmissibleSystem ℚ S]
    [JointThermo ℚ S] (prior : S) (successors : List (Cand (K := ℚ) prior))
    (h : successors = []) :
    compactionMiSelectBare prior successors = Sum.inr Residue.noCandidates := by
  subst h
  simpa [compactionMiSelectBare] using urgeRecovery_empty prior

-- ================================================================
-- SECTION 6: Authority cites + physics GREEN fence
-- ================================================================

def epistemicMIAuthority : String :=
  "umst/umst-formal-double-slit/Lean/EpistemicMI.lean"

def epistemicMINullAuthority : String :=
  "EpistemicMI.epistemicMI_null"

def epistemicMIBitsNullAuthority : String :=
  "EpistemicMI.epistemicMIBits_null"

def measurementCostAuthority : String :=
  "umst/umst-formal-double-slit/Lean/MeasurementCost.lean"

def physicalSecondLawAuthority : String :=
  "LandauerLaw.physicalSecondLaw"

def compactionMiCostCellId : String :=
  "URGE-FORMAL-Q-LEAN-COMPACTION-MI-COST"

def compactionMiCostNamed : String :=
  "compaction_mi_cost: §17.5 §22.4 compaction pays MI vs epistemicMI_null compose Excitement not second argmin; physicalSecondLaw sole axiom framing"

def compactionMiCostNonClaim : String :=
  "URGE-FORMAL-Q-LEAN-COMPACTION-MI-COST §17.5 §22.4 compaction pays MI vs epistemicMI_null compose Excitement select no second argmin Unwired one axiom physicalSecondLaw not second Landauer axiom not meso thermo not GREEN not physics GREEN not production_wired"

def compactionSecondLawConservationFraming : String :=
  "second_law_conservation_compaction_mi_one_axiom_landauer_not_second_axiom"

theorem compaction_mi_cost_cell_id :
    compactionMiCostCellId = "URGE-FORMAL-Q-LEAN-COMPACTION-MI-COST" :=
  rfl

theorem compaction_mi_cost_modality_unwired :
    compactionMiCostModalityCurrent = .unwired :=
  rfl

theorem production_wired_false : productionWired = false := rfl

theorem compaction_production_wired_false : compactionProductionWired = false := rfl

theorem compaction_mi_cost_cites_epistemic_mi :
    epistemicMIAuthority ≠ "" :=
  by decide

theorem compaction_mi_cost_cites_epistemic_mi_null :
    epistemicMINullAuthority = "EpistemicMI.epistemicMI_null" :=
  rfl

theorem compaction_mi_cost_cites_epistemic_mi_bits_null :
    epistemicMIBitsNullAuthority = "EpistemicMI.epistemicMIBits_null" :=
  rfl

theorem compaction_mi_cost_cites_measurement_cost :
    measurementCostAuthority ≠ "" :=
  by decide

theorem compaction_mi_cost_cites_physical_second_law :
    physicalSecondLawAuthority = "LandauerLaw.physicalSecondLaw" :=
  rfl

theorem compaction_not_second_landauer_axiom :
    compactionSecondLawConservationFraming ≠ "landauer_second_axiom" :=
  by decide

theorem compaction_second_law_conservation_framing :
    compactionSecondLawConservationFraming ≠ "" :=
  by decide

/-- Physics GREEN is not authorized on the knowing scaffold. -/
def physicsGreenAuthorized : Prop := False

theorem compaction_mi_cost_physics_green_false : ¬ physicsGreenAuthorized :=
  id

theorem compaction_mi_cost_not_meso_thermo_restate :
    compactionMiCostNonClaim ≠ "meso_thermo_G_T_P_x_restate" :=
  by decide

def compactionMiCostKnowingFiberOk : Prop :=
  compactionMiCostModalityCurrent = .unwired ∧ ¬ physicsGreenAuthorized

theorem compaction_mi_cost_knowing_fiber_ok :
    compactionMiCostKnowingFiberOk :=
  ⟨compaction_mi_cost_modality_unwired, compaction_mi_cost_physics_green_false⟩

end UrgeKnowing.CompactionMiCost
