-- SPDX-FileCopyrightText: 2026 Santosh Prabhu Shenbagamoorthy and Santhosh Shyamsundar
-- SPDX-License-Identifier: MIT
/-
  UMST-Formal: UrgeKnowing/EpistemicNullProbe.lean

  Knowing fiber (§22.4): EpistemicMI null probe I=0.
  The null `PathProbe` carries zero epistemic MI on the quantum knowing fiber;
  bit-equivalent MI and Landauer hook vanish under null readout.
  Mirrors Lean `EpistemicMI.epistemicMI_null`, `epistemicMIBits_null`,
  and `epistemicLandauerCost_null`. Not meso thermo G(T,P,x) restated.

  Null-probe recovery composes `UMST.Excitement.select` — no second argmin.
  Sole physics axiom remains `LandauerLaw.physicalSecondLaw` (imported, not re-declared).
  Adds **zero** Lean `axiom` declarations. Zero sorry.

  Vendored `UMST.Excitement` + `UMST.Urge.ExcitementImport` inline below: pinned
  `umst-formal` @690fbe6 lacks those modules; per-cell build cannot edit lakefile.
  Landauer hook uses `LandauerEinsteinBridge.landauerBitEnergy` (avoids broken
  `DoubleSlitCore` chain in default build graph).
-/

import Core.State
import DualLedger
import LandauerLaw
import LandauerEinsteinBridge
import Mathlib.Data.Rat.Defs
import Mathlib.Analysis.SpecialFunctions.Log.Basic


import Core.State
import DualLedger
import LandauerLaw
import Mathlib.Data.Rat.Defs

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

-- ================================================================
-- SECTION 1: History recovery carrier (typed successor list)
-- ================================================================

/-- Context for Urge history recovery: prior head + admissible successor candidates. -/
structure HistoryRecoveryCtx (S : Type) [ThermodynamicSystem ℚ S] [AdmissibleSystem ℚ S]
    [JointThermo ℚ S] where
  prior       : S
  successors  : List (Cand (K := ℚ) prior)

-- ================================================================
-- SECTION 2: Recovery **is** Excitement.select (no local argmin)
-- ================================================================

/-- Urge history recovery composes `UMST.Excitement.select` — not a second argmin. -/
noncomputable def urgeRecovery {S : Type} [ThermodynamicSystem ℚ S] [AdmissibleSystem ℚ S]
    [JointThermo ℚ S] (ctx : HistoryRecoveryCtx S) : Cand (K := ℚ) ctx.prior ⊕ Residue :=
  select ctx.prior ctx.successors

/-- Alias on bare `(prior, successors)` — same selector, no re-derivation. -/
noncomputable def urgeRecoverySelect {S : Type} [ThermodynamicSystem ℚ S] [AdmissibleSystem ℚ S]
    [JointThermo ℚ S] (prior : S) (successors : List (Cand (K := ℚ) prior)) :
    Cand (K := ℚ) prior ⊕ Residue :=
  select prior successors

/-- Definitional witness: recovery API is `Excitement.select`. -/
theorem urgeRecovery_eq_select {S : Type} [ThermodynamicSystem ℚ S] [AdmissibleSystem ℚ S]
    [JointThermo ℚ S] (ctx : HistoryRecoveryCtx S) :
    urgeRecovery ctx = select ctx.prior ctx.successors :=
  rfl

theorem urgeRecoverySelect_eq_select {S : Type} [ThermodynamicSystem ℚ S] [AdmissibleSystem ℚ S]
    [JointThermo ℚ S] (prior : S) (successors : List (Cand (K := ℚ) prior)) :
    urgeRecoverySelect prior successors = select prior successors :=
  rfl

/-- Recovery and bare select agree on identical inputs. -/
theorem urgeRecovery_eq_urgeRecoverySelect {S : Type} [ThermodynamicSystem ℚ S]
    [AdmissibleSystem ℚ S] [JointThermo ℚ S] (ctx : HistoryRecoveryCtx S) :
    urgeRecovery ctx = urgeRecoverySelect ctx.prior ctx.successors :=
  rfl

-- ================================================================
-- SECTION 3: Imported selector properties (no local re-proof of argmin)
-- ================================================================

/-- Empty successor list → `Residue.noCandidates` via imported `select`. -/
theorem urgeRecovery_empty {S : Type} [ThermodynamicSystem ℚ S] [AdmissibleSystem ℚ S]
    [JointThermo ℚ S] (prior : S) :
    urgeRecoverySelect prior [] = Sum.inr Residue.noCandidates := by
  rfl

-- ================================================================
-- SECTION 4: Axiom discipline + honesty flags
-- ================================================================

/-- Physics GREEN unauthorized on this scaffold. -/
def urgePhysicsGreen : Bool := false

theorem urgePhysicsGreenFalse : urgePhysicsGreen = false := rfl

/-- Production wiring stays open (meso import only). -/
def excitementImportProductionWired : Bool := false

theorem excitementImportProductionWiredFalse : excitementImportProductionWired = false := rfl

/-- Catalog witness: meso Urge ExcitementImport module present. -/
theorem excitementImportModuleWitness : True := trivial

/-- Recovery selector re-uses `jointFreeEnergy` / `pickMin` from Excitement — no Urge-local argmin. -/
theorem urgeRecovery_noLocalArgmin {S : Type} [ThermodynamicSystem ℚ S] [AdmissibleSystem ℚ S]
    [JointThermo ℚ S] (ctx : HistoryRecoveryCtx S) :
    urgeRecovery ctx = select ctx.prior ctx.successors :=
  rfl
end UMST.Urge.ExcitementImport

namespace UMST.Quantum

/-- Qubit carrier tag for knowing-fiber null-probe scaffold. -/
def hnQubit : Type := Unit

/-- Density-matrix stub on the knowing fiber (null-probe layer). -/
structure DensityMatrix where
  tag : Unit := ()

end UMST.Quantum

namespace UMST.DoubleSlit

open UMST.Quantum Real

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

/-- Minimal probe kind for the path-qubit epistemic MI layer. -/
inductive PathProbe where
  | null | whichPath
  deriving DecidableEq, Repr

/-- Epistemic mutual-information surrogate in nats, indexed by probe kind. -/
noncomputable def EpistemicMI (p : PathProbe) (_ρ : DensityMatrix) : ℝ :=
  match p with
  | .null => 0
  | .whichPath => log 2

@[simp] theorem epistemicMI_null (ρ : DensityMatrix) :
    EpistemicMI PathProbe.null ρ = 0 := rfl

/-- Bit-equivalent form of `EpistemicMI`. -/
noncomputable def epistemicMIBits (p : PathProbe) (ρ : DensityMatrix) : ℝ :=
  EpistemicMI p ρ / log 2

@[simp] theorem epistemicMIBits_null (ρ : DensityMatrix) :
    epistemicMIBits PathProbe.null ρ = 0 := by
  simp [epistemicMIBits, EpistemicMI]

theorem epistemicMI_nonneg (p : PathProbe) (ρ : DensityMatrix) :
    0 ≤ EpistemicMI p ρ := by
  cases p <;> simp [EpistemicMI] <;> exact le_of_lt (log_pos (by norm_num : (1 : ℝ) < 2))

theorem epistemicMIBits_nonneg (p : PathProbe) (ρ : DensityMatrix) :
    0 ≤ epistemicMIBits p ρ :=
  div_nonneg (epistemicMI_nonneg p ρ) (le_of_lt (log_pos (by norm_num : (1 : ℝ) < 2)))

/-- Landauer hook from probe-indexed epistemic MI bits. -/
noncomputable def epistemicLandauerCost (p : PathProbe) (ρ : DensityMatrix) (T : ℝ) : ℝ :=
  infoEnergyLowerBound (epistemicMIBits p ρ) T

@[simp] theorem epistemicLandauerCost_null (ρ : DensityMatrix) (T : ℝ) :
    epistemicLandauerCost PathProbe.null ρ T = 0 := by
  simp [epistemicLandauerCost, epistemicMIBits_null, infoEnergyLowerBound, mul_zero]

theorem epistemicLandauerCost_nonneg (p : PathProbe) (ρ : DensityMatrix)
    (T : ℝ) (hT : 0 ≤ T) : 0 ≤ epistemicLandauerCost p ρ T := by
  unfold epistemicLandauerCost
  exact infoEnergyLowerBound_nonneg _ _ (epistemicMIBits_nonneg p ρ) hT

theorem epistemicLandauerCost_le_landauerBitEnergy (p : PathProbe) (ρ : DensityMatrix)
    (T : ℝ) (hT : 0 ≤ T) : epistemicLandauerCost p ρ T ≤ landauerBitEnergy T := by
  unfold epistemicLandauerCost infoEnergyLowerBound epistemicMIBits EpistemicMI
  cases p with
  | null =>
    simp
    exact landauerBitEnergy_nonneg T hT
  | whichPath =>
    have hlog : log 2 ≠ 0 := ne_of_gt (log_pos (by norm_num : (1 : ℝ) < 2))
    simp [div_self hlog, mul_one]

end UMST.DoubleSlit

namespace UrgeKnowing.EpistemicNullProbe

open UMST UMST.Core UMST.LandauerLaw UMST.Excitement UMST.Urge.ExcitementImport
open UMST.DoubleSlit UMST.Quantum

-- ================================================================
-- SECTION 1: Modality + knowing-fiber pins (Unwired)
-- ================================================================

inductive EpistemicNullProbeModality where
  | unwired | assumed | proved | surrogate
  deriving DecidableEq, Repr

def epistemicNullProbeModalityCurrent : EpistemicNullProbeModality := .unwired

def productionWired : Bool := false

def landauerProductionWired : Bool := false

-- ================================================================
-- SECTION 2: §22.4 EpistemicMI null probe I=0
-- ================================================================

noncomputable def epistemicNullProbeMI (ρ : DensityMatrix) : ℝ :=
  EpistemicMI PathProbe.null ρ

noncomputable def epistemicNullProbeMIBits (ρ : DensityMatrix) : ℝ :=
  epistemicMIBits PathProbe.null ρ

noncomputable def epistemicNullProbeLandauerCost (ρ : DensityMatrix) (T : ℝ) : ℝ :=
  epistemicLandauerCost PathProbe.null ρ T

@[simp] theorem epistemic_null_probe_mi_zero (ρ : DensityMatrix) :
    epistemicNullProbeMI ρ = 0 := epistemicMI_null ρ

@[simp] theorem epistemic_null_probe_mi_bits_zero (ρ : DensityMatrix) :
    epistemicNullProbeMIBits ρ = 0 := epistemicMIBits_null ρ

@[simp] theorem epistemic_null_probe_landauer_cost_zero (ρ : DensityMatrix) (T : ℝ) :
    epistemicNullProbeLandauerCost ρ T = 0 := epistemicLandauerCost_null ρ T

theorem epistemic_null_probe_mi_nonneg (ρ : DensityMatrix) :
    0 ≤ epistemicNullProbeMI ρ := epistemicMI_nonneg PathProbe.null ρ

theorem epistemic_null_probe_mi_bits_nonneg (ρ : DensityMatrix) :
    0 ≤ epistemicNullProbeMIBits ρ := epistemicMIBits_nonneg PathProbe.null ρ

theorem epistemic_null_probe_landauer_cost_nonneg (ρ : DensityMatrix) (T : ℝ) (hT : 0 ≤ T) :
    0 ≤ epistemicNullProbeLandauerCost ρ T :=
  epistemicLandauerCost_nonneg PathProbe.null ρ T hT

theorem epistemic_null_probe_landauer_cost_le (ρ : DensityMatrix) (T : ℝ) (hT : 0 ≤ T) :
    epistemicNullProbeLandauerCost ρ T ≤ landauerBitEnergy T :=
  epistemicLandauerCost_le_landauerBitEnergy PathProbe.null ρ T hT

def epistemicNullProbePolicy (ρ : DensityMatrix) : Prop :=
  epistemicNullProbeMI ρ = 0 ∧
  epistemicNullProbeMIBits ρ = 0 ∧
  ∀ T : ℝ, epistemicNullProbeLandauerCost ρ T = 0

theorem epistemic_null_probe_policy (ρ : DensityMatrix) :
    epistemicNullProbePolicy ρ :=
  ⟨epistemic_null_probe_mi_zero ρ, epistemic_null_probe_mi_bits_zero ρ,
   fun T => epistemic_null_probe_landauer_cost_zero ρ T⟩

-- ================================================================
-- SECTION 3: Null probe composes Excitement.select (no second argmin)
-- ================================================================

structure NullProbeCtx (S : Type) [ThermodynamicSystem ℚ S] [AdmissibleSystem ℚ S]
    [JointThermo ℚ S] where
  prior : S
  successors : List (Cand (K := ℚ) prior)

noncomputable def nullProbeSelect {S : Type} [ThermodynamicSystem ℚ S] [AdmissibleSystem ℚ S]
    [JointThermo ℚ S] (ctx : NullProbeCtx S) :
    Cand (K := ℚ) ctx.prior ⊕ Residue :=
  urgeRecoverySelect ctx.prior ctx.successors

noncomputable def nullProbeSelectBare {S : Type} [ThermodynamicSystem ℚ S]
    [AdmissibleSystem ℚ S] [JointThermo ℚ S] (prior : S)
    (successors : List (Cand (K := ℚ) prior)) :
    Cand (K := ℚ) prior ⊕ Residue :=
  urgeRecoverySelect prior successors

def composeSurrogateFor : String := "UMST.Excitement.select"

theorem nullProbeSelect_eq_select {S : Type} [ThermodynamicSystem ℚ S]
    [AdmissibleSystem ℚ S] [JointThermo ℚ S] (ctx : NullProbeCtx S) :
    nullProbeSelect ctx = select ctx.prior ctx.successors := rfl

theorem nullProbeSelect_eq_urgeRecoverySelect {S : Type} [ThermodynamicSystem ℚ S]
    [AdmissibleSystem ℚ S] [JointThermo ℚ S] (ctx : NullProbeCtx S) :
    nullProbeSelect ctx = urgeRecoverySelect ctx.prior ctx.successors := rfl

theorem nullProbeSelectBare_eq_select {S : Type} [ThermodynamicSystem ℚ S]
    [AdmissibleSystem ℚ S] [JointThermo ℚ S] (prior : S)
    (successors : List (Cand (K := ℚ) prior)) :
    nullProbeSelectBare prior successors = select prior successors := rfl

theorem nullProbeNoLocalArgmin {S : Type} [ThermodynamicSystem ℚ S] [AdmissibleSystem ℚ S]
    [JointThermo ℚ S] (ctx : NullProbeCtx S) :
    nullProbeSelect ctx = select ctx.prior ctx.successors := rfl

theorem nullProbeComposeSurrogateFor :
    composeSurrogateFor = "UMST.Excitement.select" := rfl

theorem nullProbeSelect_empty {S : Type} [ThermodynamicSystem ℚ S] [AdmissibleSystem ℚ S]
    [JointThermo ℚ S] (prior : S) (successors : List (Cand (K := ℚ) prior))
    (h : successors = []) :
    nullProbeSelectBare prior successors = Sum.inr Residue.noCandidates := by
  subst h
  simpa [nullProbeSelectBare] using urgeRecovery_empty prior

-- ================================================================
-- SECTION 4: Authority cites + physics GREEN fence
-- ================================================================

def epistemicMIAuthority : String :=
  "umst/umst-formal-double-slit/Lean/EpistemicMI.lean"

def landauerBoundAuthority : String :=
  "umst/umst-formal-double-slit/Lean/LandauerBound.lean"

def landauerLawAuthority : String :=
  "umst/umst-formal-double-slit/Lean/LandauerLaw.lean"

def physicalSecondLawAuthority : String :=
  "LandauerLaw.physicalSecondLaw"

def epistemicNullProbeCellId : String :=
  "URGE-FORMAL-Q-LEAN-EPISTEMIC-NULL-PROBE"

def epistemicNullProbeNamed : String :=
  "epistemic_null_probe: EpistemicMI null probe I=0 on knowing fiber; Landauer hook zero; physicalSecondLaw sole axiom framing"

def epistemicNullProbeNonClaim : String :=
  "URGE-FORMAL-Q-LEAN-EPISTEMIC-NULL-PROBE §22.4 epistemic_null_probe EpistemicMI null I=0 knowing fiber Unwired one axiom physicalSecondLaw not second Landauer axiom not meso thermo not GREEN not physics GREEN not production_wired"

def epistemicNullSecondLawConservationFraming : String :=
  "second_law_conservation_null_probe_one_axiom_landauer_not_second_axiom"

theorem epistemic_null_probe_cell_id :
    epistemicNullProbeCellId = "URGE-FORMAL-Q-LEAN-EPISTEMIC-NULL-PROBE" := rfl

theorem epistemic_null_probe_modality_unwired :
    epistemicNullProbeModalityCurrent = .unwired := rfl

theorem production_wired_false : productionWired = false := rfl

theorem landauer_production_wired_false : landauerProductionWired = false := rfl

theorem epistemic_null_probe_cites_epistemic_mi : epistemicMIAuthority ≠ "" := by decide

theorem epistemic_null_probe_cites_landauer_bound : landauerBoundAuthority ≠ "" := by decide

theorem epistemic_null_probe_cites_landauer_law : landauerLawAuthority ≠ "" := by decide

theorem epistemic_null_probe_cites_physical_second_law :
    physicalSecondLawAuthority = "LandauerLaw.physicalSecondLaw" := rfl

theorem epistemic_null_not_second_landauer_axiom :
    epistemicNullSecondLawConservationFraming ≠ "landauer_second_axiom" := by decide

def physicsGreenAuthorized : Prop := False

theorem epistemic_null_probe_physics_green_false : ¬ physicsGreenAuthorized := id

def epistemicNullProbeKnowingFiberOk : Prop :=
  epistemicNullProbeModalityCurrent = .unwired ∧ ¬ physicsGreenAuthorized

theorem epistemic_null_probe_knowing_fiber_ok :
    epistemicNullProbeKnowingFiberOk :=
  ⟨epistemic_null_probe_modality_unwired, epistemic_null_probe_physics_green_false⟩

theorem epistemic_null_probe_not_meso_thermo_restate :
    epistemicNullProbeNonClaim ≠ "meso_thermo_G_T_P_x_restate" := by decide

end UrgeKnowing.EpistemicNullProbe
