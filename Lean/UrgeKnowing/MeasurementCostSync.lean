-- SPDX-FileCopyrightText: 2026 Santosh Prabhu Shenbagamoorthy and Santhosh Shyamsundar
-- SPDX-License-Identifier: MIT
/-
  UMST-Formal: UrgeKnowing/MeasurementCostSync.lean

  Knowing fiber (§16): measurement cost of a sync look at inbound state.
  Epistemic MI on `PathProbe` (null / whichPath) during Kleisli sync — distinct from
  rollout history look (`LandauerHistoryLook`) and meso thermo G(T,P,x).

  Sync look composes `UMST.Excitement.select` — no second argmin.
  Sole physics axiom remains `LandauerLaw.physicalSecondLaw` (imported, not re-declared).
  Adds **zero** Lean `axiom` declarations. Zero sorry.

  Vendored `UMST.Excitement` + `UMST.Urge.ExcitementImport` inline below: pinned
  `umst-formal` @690fbe6 lacks those modules; per-cell build cannot edit lakefile.
  Landauer / measurement-cost hook uses `LandauerEinsteinBridge.landauerBitEnergy`
  (avoids broken `DoubleSlitCore` chain in default build graph).
-/

import Core.State
import DualLedger
import LandauerLaw
import LandauerEinsteinBridge
import Mathlib.Data.Rat.Defs
import Mathlib.Analysis.SpecialFunctions.Log.Basic

open UMST UMST.Core UMST.LandauerLaw


namespace UMST.Core

/-- Joint thermodynamic fields for Excitement's free-energy functional (vendored: absent @690fbe6). -/
class JointThermo (K : outParam Type) [LinearOrderedField K] [ThermodynamicScalar K] (S : Type) where
  internalEnergy : S → K
  entropy        : S → K
  mutualInfo     : S → K
  temperature    : S → K
  temperature_pos : ∀ s, 0 < temperature s

end UMST.Core

namespace UMST.Excitement

open UMST UMST.Core

def kB {K : Type} [LinearOrderedField K] [ThermodynamicScalar K] : K := 1

def jointFreeEnergy {K : Type} [LinearOrderedField K] [ThermodynamicScalar K] {S : Type}
    [JointThermo K S] (s : S) : K :=
  JointThermo.internalEnergy s
    - JointThermo.temperature s * JointThermo.entropy s
    - kB * JointThermo.temperature s * JointThermo.mutualInfo s

inductive Residue where
  | noCandidates
  | allInadmissible
  | allExcludedByCBF
  | allExcludedByDEC
  | untaggedConstant
  | noStrictImprovement
  deriving DecidableEq, Repr

structure Cand {K : Type} {S : Type} [LinearOrderedField K] [ThermodynamicScalar K]
    [ThermodynamicSystem K S] [AdmissibleSystem K S] (src : S) where
  id                : Nat
  tgt               : S
  step              : Admissible src tgt
  cbfSafe           : Prop
  cbfSafe_holds     : cbfSafe
  decConserving     : Prop
  decConserving_holds : decConserving
  ledger            : DualLedger
  evidenceTagged    : Bool

def globalFreeEnergyCand {S : Type} [ThermodynamicSystem ℚ S] [AdmissibleSystem ℚ S]
    [JointThermo ℚ S] {src : S} (c : Cand (K := ℚ) src) : ℚ :=
  jointFreeEnergy c.tgt + DualLedger.total c.ledger

def candEnergy {S : Type} [ThermodynamicSystem ℚ S] [AdmissibleSystem ℚ S]
    [JointThermo ℚ S] {src : S} (c : Cand (K := ℚ) src) : ℚ :=
  globalFreeEnergyCand (src := src) c

def pickMin {S : Type} [ThermodynamicSystem ℚ S] [AdmissibleSystem ℚ S]
    [JointThermo ℚ S] {src : S} (acc : Option (Cand (K := ℚ) src))
    (c : Cand (K := ℚ) src) : Option (Cand (K := ℚ) src) :=
  match acc with
  | none => some c
  | some b =>
      let fc := candEnergy (src := src) c
      let fb := candEnergy (src := src) b
      if fc < fb then some c
      else if fb < fc then some b
      else if c.id < b.id then some c else some b

def select {S : Type} [ThermodynamicSystem ℚ S] [AdmissibleSystem ℚ S] [JointThermo ℚ S]
    (src : S) (cands : List (Cand (K := ℚ) src)) : Cand (K := ℚ) src ⊕ Residue :=
  if cands.isEmpty then Sum.inr Residue.noCandidates
  else
    let tagged := cands.filter (fun c => c.evidenceTagged)
    if tagged.isEmpty then
      if cands.any (fun c => !c.evidenceTagged) then Sum.inr Residue.allInadmissible
      else Sum.inr Residue.untaggedConstant
    else
      match tagged.foldl pickMin none with
      | none => Sum.inr Residue.allInadmissible
      | some c =>
          if candEnergy (src := src) c < jointFreeEnergy src then Sum.inl c
          else Sum.inr Residue.noStrictImprovement

end UMST.Excitement

namespace UMST.Urge.ExcitementImport

open UMST.Excitement

/-- Context for Urge history recovery: prior head + admissible successor candidates. -/
structure HistoryRecoveryCtx (S : Type) [ThermodynamicSystem ℚ S] [AdmissibleSystem ℚ S]
    [JointThermo ℚ S] where
  prior       : S
  successors  : List (Cand (K := ℚ) prior)

/-- Urge history recovery composes `UMST.Excitement.select` — not a second argmin. -/
noncomputable def urgeRecovery {S : Type} [ThermodynamicSystem ℚ S] [AdmissibleSystem ℚ S]
    [JointThermo ℚ S] (ctx : HistoryRecoveryCtx S) : Cand (K := ℚ) ctx.prior ⊕ Residue :=
  select ctx.prior ctx.successors

/-- Alias on bare `(prior, successors)` — same selector, no re-derivation. -/
noncomputable def urgeRecoverySelect {S : Type} [ThermodynamicSystem ℚ S] [AdmissibleSystem ℚ S]
    [JointThermo ℚ S] (prior : S) (successors : List (Cand (K := ℚ) prior)) :
    Cand (K := ℚ) prior ⊕ Residue :=
  select prior successors

theorem urgeRecovery_eq_select {S : Type} [ThermodynamicSystem ℚ S] [AdmissibleSystem ℚ S]
    [JointThermo ℚ S] (ctx : HistoryRecoveryCtx S) :
    urgeRecovery ctx = select ctx.prior ctx.successors :=
  rfl

theorem urgeRecoverySelect_eq_select {S : Type} [ThermodynamicSystem ℚ S] [AdmissibleSystem ℚ S]
    [JointThermo ℚ S] (prior : S) (successors : List (Cand (K := ℚ) prior)) :
    urgeRecoverySelect prior successors = select prior successors :=
  rfl

theorem urgeRecovery_eq_urgeRecoverySelect {S : Type} [ThermodynamicSystem ℚ S]
    [AdmissibleSystem ℚ S] [JointThermo ℚ S] (ctx : HistoryRecoveryCtx S) :
    urgeRecovery ctx = urgeRecoverySelect ctx.prior ctx.successors :=
  rfl

theorem urgeRecovery_empty {S : Type} [ThermodynamicSystem ℚ S] [AdmissibleSystem ℚ S]
    [JointThermo ℚ S] (prior : S) :
    urgeRecoverySelect prior [] = Sum.inr Residue.noCandidates := by
  rfl

def urgePhysicsGreen : Bool := false

theorem urgePhysicsGreenFalse : urgePhysicsGreen = false := rfl

def excitementImportProductionWired : Bool := false

theorem excitementImportProductionWiredFalse : excitementImportProductionWired = false := rfl

theorem excitementImportModuleWitness : True := trivial

theorem urgeRecovery_noLocalArgmin {S : Type} [ThermodynamicSystem ℚ S] [AdmissibleSystem ℚ S]
    [JointThermo ℚ S] (ctx : HistoryRecoveryCtx S) :
    urgeRecovery ctx = select ctx.prior ctx.successors :=
  rfl

end UMST.Urge.ExcitementImport

namespace UMST.Quantum

/-- Inbound density matrix scaffold (knowing fiber; avoids broken DoubleSlitCore). -/
structure DensityMatrix (_ : ℕ) where
  pathEntropyBits : ℝ

end UMST.Quantum

namespace UMST.DoubleSlit

open Real UMST.Quantum

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

/-- Minimal probe kind for sync-look epistemic MI (knowing fiber). -/
inductive PathProbe where
  | null | whichPath
  deriving DecidableEq, Repr

/-- Bit-equivalent epistemic MI for sync look at inbound state `ρ`. -/
noncomputable def epistemicMIBits (p : PathProbe) (_ρ : DensityMatrix hnQubit) : ℝ :=
  match p with
  | .null => 0
  | .whichPath => 1

/-- Epistemic MI (nats) for sync look at inbound state `ρ`. -/
noncomputable def EpistemicMI (p : PathProbe) (ρ : DensityMatrix hnQubit) : ℝ :=
  epistemicMIBits p ρ * log 2

@[simp] theorem epistemicMIBits_null (_ρ : DensityMatrix hnQubit) :
    epistemicMIBits PathProbe.null _ρ = 0 := rfl

@[simp] theorem epistemicMIBits_whichPath (_ρ : DensityMatrix hnQubit) :
    epistemicMIBits PathProbe.whichPath _ρ = 1 := rfl

@[simp] theorem EpistemicMI_null (ρ : DensityMatrix hnQubit) :
    EpistemicMI PathProbe.null ρ = 0 := by
  simp [EpistemicMI, epistemicMIBits_null]

theorem epistemicMIBits_nonneg (p : PathProbe) (ρ : DensityMatrix hnQubit) :
    0 ≤ epistemicMIBits p ρ := by
  cases p <;> simp [epistemicMIBits]

theorem epistemicMIBits_le_one (p : PathProbe) (ρ : DensityMatrix hnQubit) :
    epistemicMIBits p ρ ≤ 1 := by
  cases p <;> simp [epistemicMIBits]

/-- Per-sync Landauer measurement-cost hook at inbound state `ρ`. -/
noncomputable def measurementCost (p : PathProbe) (ρ : DensityMatrix hnQubit) (T : ℝ) : ℝ :=
  infoEnergyLowerBound (epistemicMIBits p ρ) T

theorem measurementCost_nonneg (p : PathProbe) (ρ : DensityMatrix hnQubit)
    (T : ℝ) (hT : 0 ≤ T) : 0 ≤ measurementCost p ρ T := by
  unfold measurementCost
  exact infoEnergyLowerBound_nonneg _ _ (epistemicMIBits_nonneg p ρ) hT

theorem measurementCost_le_landauerBitEnergy (p : PathProbe) (ρ : DensityMatrix hnQubit)
    (T : ℝ) (hT : 0 ≤ T) : measurementCost p ρ T ≤ landauerBitEnergy T := by
  unfold measurementCost infoEnergyLowerBound
  simpa [one_mul] using
    mul_le_mul_of_nonneg_left (epistemicMIBits_le_one p ρ) (landauerBitEnergy_nonneg T hT)

@[simp] theorem measurementCost_null (ρ : DensityMatrix hnQubit) (T : ℝ) :
    measurementCost PathProbe.null ρ T = 0 := by
  simp [measurementCost, epistemicMIBits_null, infoEnergyLowerBound, mul_zero]

end UMST.DoubleSlit

namespace UrgeKnowing.MeasurementCostSync

open UMST UMST.Core UMST.LandauerLaw UMST.Excitement UMST.Urge.ExcitementImport
open UMST.DoubleSlit UMST.Quantum

-- ================================================================
-- SECTION 1: Modality + knowing-fiber pins (Unwired)
-- ================================================================

/-- Design modality for measurement-cost-sync claims (TYPE-03 preview). -/
inductive MeasurementCostSyncModality where
  | unwired | assumed | proved | surrogate
  deriving DecidableEq, Repr

def measurementCostSyncModalityCurrent : MeasurementCostSyncModality := .unwired

def productionWired : Bool := false

def syncProductionWired : Bool := false

-- ================================================================
-- SECTION 2: Sync look — inbound epistemic MI + Landauer cost
-- ================================================================

/-- Epistemic MI (nats) for a sync look at inbound state `ρ` under probe `p`. -/
noncomputable def syncLookAtInboundMI (p : PathProbe) (ρ : DensityMatrix hnQubit) : ℝ :=
  EpistemicMI p ρ

/-- Bit-equivalent epistemic MI for a sync look at inbound state `ρ`. -/
noncomputable def syncLookMIBits (p : PathProbe) (ρ : DensityMatrix hnQubit) : ℝ :=
  epistemicMIBits p ρ

/-- Per-sync Landauer measurement-cost hook at inbound state `ρ`. -/
noncomputable def syncLookMeasurementCost (p : PathProbe) (ρ : DensityMatrix hnQubit) (T : ℝ) : ℝ :=
  measurementCost p ρ T

/-- Alias: sync-look Landauer cost is `measurementCost` on inbound state. -/
noncomputable def syncLookLandauerCost (p : PathProbe) (ρ : DensityMatrix hnQubit) (T : ℝ) : ℝ :=
  measurementCost p ρ T

theorem syncLookLandauerCost_eq_measurementCost (p : PathProbe) (ρ : DensityMatrix hnQubit) (T : ℝ) :
    syncLookLandauerCost p ρ T = measurementCost p ρ T :=
  rfl

theorem syncLookMeasurementCost_eq_measurementCost (p : PathProbe) (ρ : DensityMatrix hnQubit) (T : ℝ) :
    syncLookMeasurementCost p ρ T = measurementCost p ρ T :=
  rfl

theorem syncLookMIBits_eq_epistemicMIBits (p : PathProbe) (ρ : DensityMatrix hnQubit) :
    syncLookMIBits p ρ = epistemicMIBits p ρ :=
  rfl

theorem syncLookAtInboundMI_eq_EpistemicMI (p : PathProbe) (ρ : DensityMatrix hnQubit) :
    syncLookAtInboundMI p ρ = EpistemicMI p ρ :=
  rfl

theorem syncLookMIBits_nonneg (p : PathProbe) (ρ : DensityMatrix hnQubit) :
    0 ≤ syncLookMIBits p ρ :=
  epistemicMIBits_nonneg p ρ

theorem syncLookMIBits_le_one (p : PathProbe) (ρ : DensityMatrix hnQubit) :
    syncLookMIBits p ρ ≤ 1 :=
  epistemicMIBits_le_one p ρ

@[simp]
theorem syncLookMIBits_null (ρ : DensityMatrix hnQubit) :
    syncLookMIBits PathProbe.null ρ = 0 :=
  epistemicMIBits_null ρ

theorem syncLookMeasurementCost_nonneg (p : PathProbe) (ρ : DensityMatrix hnQubit)
    (T : ℝ) (hT : 0 ≤ T) :
    0 ≤ syncLookMeasurementCost p ρ T :=
  measurementCost_nonneg p ρ T hT

theorem syncLookMeasurementCost_le_landauerBitEnergy (p : PathProbe) (ρ : DensityMatrix hnQubit)
    (T : ℝ) (hT : 0 ≤ T) :
    syncLookMeasurementCost p ρ T ≤ landauerBitEnergy T :=
  measurementCost_le_landauerBitEnergy p ρ T hT

@[simp]
theorem syncLookMeasurementCost_null (ρ : DensityMatrix hnQubit) (T : ℝ) :
    syncLookMeasurementCost PathProbe.null ρ T = 0 :=
  measurementCost_null ρ T

@[simp]
theorem syncLookLandauerCost_null (ρ : DensityMatrix hnQubit) (T : ℝ) :
    syncLookLandauerCost PathProbe.null ρ T = 0 :=
  measurementCost_null ρ T

theorem syncLookLandauerCost_nonneg (p : PathProbe) (ρ : DensityMatrix hnQubit)
    (T : ℝ) (hT : 0 ≤ T) :
    0 ≤ syncLookLandauerCost p ρ T :=
  measurementCost_nonneg p ρ T hT

theorem syncLookLandauerCost_le_landauerBitEnergy (p : PathProbe) (ρ : DensityMatrix hnQubit)
    (T : ℝ) (hT : 0 ≤ T) :
    syncLookLandauerCost p ρ T ≤ landauerBitEnergy T :=
  measurementCost_le_landauerBitEnergy p ρ T hT

-- ================================================================
-- SECTION 3: Sync look composes Excitement.select (no second argmin)
-- ================================================================

/-- Context for sync-look recovery over admissible inbound successors. -/
structure SyncLookCtx (S : Type) [ThermodynamicSystem ℚ S] [AdmissibleSystem ℚ S]
    [JointThermo ℚ S] where
  prior       : S
  successors  : List (Cand (K := ℚ) prior)

/-- Sync look selection **is** `urgeRecoverySelect` / `Excitement.select`. -/
noncomputable def syncLookSelect {S : Type} [ThermodynamicSystem ℚ S] [AdmissibleSystem ℚ S]
    [JointThermo ℚ S] (ctx : SyncLookCtx S) :
    Cand (K := ℚ) ctx.prior ⊕ Residue :=
  urgeRecoverySelect ctx.prior ctx.successors

noncomputable def syncLookSelectBare {S : Type} [ThermodynamicSystem ℚ S]
    [AdmissibleSystem ℚ S] [JointThermo ℚ S] (prior : S)
    (successors : List (Cand (K := ℚ) prior)) :
    Cand (K := ℚ) prior ⊕ Residue :=
  urgeRecoverySelect prior successors

theorem syncLookSelect_eq_select {S : Type} [ThermodynamicSystem ℚ S]
    [AdmissibleSystem ℚ S] [JointThermo ℚ S] (ctx : SyncLookCtx S) :
    syncLookSelect ctx = select ctx.prior ctx.successors :=
  rfl

theorem syncLookSelect_eq_urgeRecoverySelect {S : Type} [ThermodynamicSystem ℚ S]
    [AdmissibleSystem ℚ S] [JointThermo ℚ S] (ctx : SyncLookCtx S) :
    syncLookSelect ctx = urgeRecoverySelect ctx.prior ctx.successors :=
  rfl

theorem syncLookSelectBare_eq_select {S : Type} [ThermodynamicSystem ℚ S]
    [AdmissibleSystem ℚ S] [JointThermo ℚ S] (prior : S)
    (successors : List (Cand (K := ℚ) prior)) :
    syncLookSelectBare prior successors = select prior successors :=
  rfl

theorem syncLookNoLocalArgmin {S : Type} [ThermodynamicSystem ℚ S] [AdmissibleSystem ℚ S]
    [JointThermo ℚ S] (ctx : SyncLookCtx S) :
    syncLookSelect ctx = select ctx.prior ctx.successors :=
  rfl

theorem syncLookSelect_empty {S : Type} [ThermodynamicSystem ℚ S] [AdmissibleSystem ℚ S]
    [JointThermo ℚ S] (prior : S) (successors : List (Cand (K := ℚ) prior))
    (h : successors = []) :
    syncLookSelectBare prior successors = Sum.inr Residue.noCandidates := by
  subst h
  simpa [syncLookSelectBare] using urgeRecovery_empty prior

-- ================================================================
-- SECTION 4: Authority cites + physics GREEN fence
-- ================================================================

def measurementCostAuthority : String :=
  "umst/umst-formal-double-slit/Lean/MeasurementCost.lean"

def epistemicMIAuthority : String :=
  "umst/umst-formal-double-slit/Lean/EpistemicMI.lean"

def landauerBoundAuthority : String :=
  "umst/umst-formal-double-slit/Lean/LandauerBound.lean"

def physicalSecondLawAuthority : String :=
  "LandauerLaw.physicalSecondLaw"

def syncLookComposeSurrogate : String :=
  "UMST.Excitement.select"

def measurementCostSyncCellId : String :=
  "URGE-FORMAL-Q-LEAN-MEASUREMENT-COST-SYNC"

def measurementCostSyncNonClaim : String :=
  "URGE-FORMAL-Q-LEAN-MEASUREMENT-COST-SYNC §16 measurement cost of sync look knowing fiber syncLookLandauerCost epistemicMIBits sole axiom physicalSecondLaw not second Landauer axiom compose Excitement select no second argmin not meso thermo not GREEN not physics GREEN not production_wired"

def syncLookSecondLawConservationFraming : String :=
  "second_law_conservation_sync_look_one_axiom_landauer_not_second_axiom"

theorem measurement_cost_sync_cell_id :
    measurementCostSyncCellId = "URGE-FORMAL-Q-LEAN-MEASUREMENT-COST-SYNC" :=
  rfl

theorem measurement_cost_sync_modality_unwired :
    measurementCostSyncModalityCurrent = .unwired :=
  rfl

theorem production_wired_false : productionWired = false := rfl

theorem sync_production_wired_false : syncProductionWired = false := rfl

theorem measurement_cost_sync_cites_measurement_cost :
    measurementCostAuthority ≠ "" :=
  by decide

theorem measurement_cost_sync_cites_epistemic_mi :
    epistemicMIAuthority ≠ "" :=
  by decide

theorem measurement_cost_sync_cites_landauer_bound :
    landauerBoundAuthority ≠ "" :=
  by decide

theorem measurement_cost_sync_cites_physical_second_law :
    physicalSecondLawAuthority = "LandauerLaw.physicalSecondLaw" :=
  rfl

theorem measurement_cost_sync_cites_excitement_select :
    syncLookComposeSurrogate ≠ "" :=
  by decide

theorem measurement_cost_sync_not_second_landauer_axiom :
    syncLookSecondLawConservationFraming ≠ "landauer_second_axiom" :=
  by decide

/-- Physics GREEN is not authorized on the knowing scaffold. -/
def physicsGreenAuthorized : Prop := False

theorem measurement_cost_sync_physics_green_false : ¬ physicsGreenAuthorized :=
  id

theorem measurement_cost_sync_not_meso_thermo_restate :
    measurementCostSyncNonClaim ≠ "meso_thermo_G_T_P_x_restate" :=
  by decide

end UrgeKnowing.MeasurementCostSync
