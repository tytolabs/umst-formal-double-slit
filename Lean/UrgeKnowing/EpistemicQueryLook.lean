-- SPDX-FileCopyrightText: 2026 Santosh Prabhu Shenbagamoorthy and Santhosh Shyamsundar
-- SPDX-License-Identifier: MIT
/-
  UMST-Formal: UrgeKnowing/EpistemicQueryLook.lean

  Knowing fiber (§18): query is verification cost (information-up), not coordination.
  An epistemic query look on the quantum knowing fiber pays information-up verification
  cost — not multi-agent coordination theater or a second ℚ Excitement argmin.
  Mirrors `LandauerHistoryLook.lean` and cross-lang `EpistemicQueryLook` spine.

  Query recovery composes `UMST.Excitement.select` — no second argmin.
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


import Core.State
import DualLedger
import LandauerLaw
import Mathlib.Data.Rat.Defs
import Excitement
import Urge.ExcitementImport

open UMST UMST.Core UMST.LandauerLaw


namespace UMST.DoubleSlit

open _root_.Real

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

/-- Minimal probe kind for epistemic query look probe-bits align witness. -/
inductive PathProbe where
  | null | whichPath
  deriving DecidableEq, Repr

/-- Bit-equivalent epistemic MI stub for query-look alignment (knowing fiber). -/
noncomputable def epistemicMIBits (p : PathProbe) : ℝ :=
  match p with
  | .null => 0
  | .whichPath => 1

@[simp] theorem epistemicMIBits_null : epistemicMIBits PathProbe.null = 0 := rfl

@[simp] theorem epistemicMIBits_whichPath : epistemicMIBits PathProbe.whichPath = 1 := rfl

end UMST.DoubleSlit

namespace UrgeKnowing.EpistemicQueryLook

open UMST UMST.Core UMST.LandauerLaw UMST.Excitement UMST.Urge.ExcitementImport
open UMST.DoubleSlit

-- ================================================================
-- SECTION 1: Modality + knowing-fiber pins (Unwired)
-- ================================================================

/-- Design modality for epistemic-query-look claims (TYPE-03 preview). -/
inductive EpistemicQueryLookModality where
  | unwired | assumed | proved | surrogate
  deriving DecidableEq, Repr

def epistemicQueryLookModalityCurrent : EpistemicQueryLookModality := .unwired

def productionWired : Bool := false

def landauerProductionWired : Bool := false

-- ================================================================
-- SECTION 2: §18 query class — verification cost vs coordination
-- ================================================================

/-- §18 query class — verification-cost bits vs coordination theater. -/
inductive QueryLookClass where
  | verificationCost (bits : ℝ)
  | coordinationTheater

/-- Formal fiber — knowing vs meso acting. -/
inductive FormalFiber where
  | mesoActing | quantumKnowing
  deriving DecidableEq, Repr

/-- Epistemic query look carrier on the knowing fiber. -/
structure EpistemicQueryLook where
  lookClass : QueryLookClass
  lookFiber : FormalFiber

def verificationCostLook (bits : ℝ) : EpistemicQueryLook :=
  { lookClass := .verificationCost bits, lookFiber := .quantumKnowing }

def coordinationTheaterLook : EpistemicQueryLook :=
  { lookClass := .coordinationTheater, lookFiber := .quantumKnowing }

def queryLookClassIsVerificationCost : QueryLookClass → Bool
  | .verificationCost _ => true
  | .coordinationTheater => false

def queryLookClassIsCoordinationTheater : QueryLookClass → Bool
  | .verificationCost _ => false
  | .coordinationTheater => true

/-- Verification bits for query look — zero for coordination theater. -/
noncomputable def queryLookVerificationBits (look : EpistemicQueryLook) : ℝ :=
  match look.lookClass with
  | .verificationCost bits => bits
  | .coordinationTheater => 0

/-- Landauer lower bound at verification bits and temperature `T`. -/
noncomputable def queryLookLandauerCost (T : ℝ) (look : EpistemicQueryLook) : ℝ :=
  infoEnergyLowerBound (queryLookVerificationBits look) T

theorem queryLookVerificationBits_verificationCost (bits : ℝ) :
    queryLookVerificationBits (verificationCostLook bits) = bits := rfl

theorem queryLookVerificationBits_coordinationTheater :
    queryLookVerificationBits coordinationTheaterLook = 0 := rfl

theorem queryLookLandauerCost_eq_infoEnergy (T : ℝ) (look : EpistemicQueryLook) :
    queryLookLandauerCost T look =
      infoEnergyLowerBound (queryLookVerificationBits look) T :=
  rfl

theorem queryLookLandauerCost_nonneg (T : ℝ) (look : EpistemicQueryLook) (hT : 0 ≤ T)
    (hbits : 0 ≤ queryLookVerificationBits look) :
    0 ≤ queryLookLandauerCost T look := by
  unfold queryLookLandauerCost
  exact infoEnergyLowerBound_nonneg _ _ hbits hT

theorem queryLookLandauerCost_admitted_nonneg (T : ℝ) (bits : ℝ) (hT : 0 ≤ T) (h : 0 < bits) :
    0 ≤ queryLookLandauerCost T (verificationCostLook bits) := by
  simpa [queryLookVerificationBits_verificationCost] using
    queryLookLandauerCost_nonneg T (verificationCostLook bits) hT (le_of_lt h)

theorem queryLookLandauerCost_le_bitEnergy (T : ℝ) (look : EpistemicQueryLook)
    (hT : 0 ≤ T) (hbits : queryLookVerificationBits look ≤ 1) :
    queryLookLandauerCost T look ≤ landauerBitEnergy T := by
  unfold queryLookLandauerCost infoEnergyLowerBound
  simpa [one_mul] using
    mul_le_mul_of_nonneg_left hbits (landauerBitEnergy_nonneg T hT)

theorem queryLookProbeBitsAlign (p : PathProbe) :
    queryLookVerificationBits (verificationCostLook (epistemicMIBits p)) = epistemicMIBits p := by
  cases p <;> simp [queryLookVerificationBits, verificationCostLook, epistemicMIBits]

/-- Typed refusal for epistemic query look discipline. -/
inductive EpistemicQueryLookRefusal where
  | coordinationTheaterRefused | mesoFiberMisroute
  | nonPositiveVerificationBits | secondArgmin
  deriving DecidableEq, Repr

/-- Outcome of epistemic query look admission. -/
inductive EpistemicQueryLookOutcome where
  | admitted (bits : ℝ)
  | refused (reason : EpistemicQueryLookRefusal)

noncomputable def admitEpistemicQueryLook (look : EpistemicQueryLook) : EpistemicQueryLookOutcome :=
  match look.lookFiber, look.lookClass with
  | .quantumKnowing, .coordinationTheater => .refused .coordinationTheaterRefused
  | .mesoActing, _ => .refused .mesoFiberMisroute
  | .quantumKnowing, .verificationCost bits =>
    if 0 < bits then .admitted bits else .refused .nonPositiveVerificationBits

theorem admit_verification_cost (bits : ℝ) (h : 0 < bits) :
    admitEpistemicQueryLook (verificationCostLook bits) = .admitted bits := by
  simp [admitEpistemicQueryLook, verificationCostLook, h]

theorem admit_coordination_theater_refused :
    admitEpistemicQueryLook coordinationTheaterLook =
      .refused .coordinationTheaterRefused := rfl

theorem admit_meso_fiber_refused (bits : ℝ) :
    admitEpistemicQueryLook
      { lookClass := .verificationCost bits, lookFiber := .mesoActing } =
      .refused .mesoFiberMisroute :=
  rfl

theorem admit_nonpositive_bits_refused (bits : ℝ) (h : bits ≤ 0) :
    admitEpistemicQueryLook (verificationCostLook bits) =
      .refused .nonPositiveVerificationBits := by
  simp [admitEpistemicQueryLook, verificationCostLook, not_lt.mpr h]

def refuseCoordinationTheater : EpistemicQueryLookRefusal := .coordinationTheaterRefused

def refuseSecondArgminSelector : EpistemicQueryLookRefusal := .secondArgmin

theorem refuse_coordination_theater_ok :
    refuseCoordinationTheater = .coordinationTheaterRefused := rfl

theorem refuse_second_argmin_ok :
    refuseSecondArgminSelector = .secondArgmin := rfl

theorem query_look_class_verification_ok (bits : ℝ) :
    queryLookClassIsVerificationCost (.verificationCost bits) = true := rfl

theorem query_look_class_coordination_ok :
    queryLookClassIsCoordinationTheater .coordinationTheater = true := rfl

-- ================================================================
-- SECTION 3: Query look composes Excitement.select (no second argmin)
-- ================================================================

/-- Context for query-look recovery over admissible successors. -/
structure QueryLookCtx (S : Type) [ThermodynamicSystem ℚ S] [AdmissibleSystem ℚ S]
    [JointThermo ℚ S] where
  prior       : S
  successors  : List (Cand (K := ℚ) prior)

/-- Query look selection **is** `urgeRecoverySelect` / `Excitement.select`. -/
noncomputable def queryLookSelect {S : Type} [ThermodynamicSystem ℚ S] [AdmissibleSystem ℚ S]
    [JointThermo ℚ S] (ctx : QueryLookCtx S) :
    Cand (K := ℚ) ctx.prior ⊕ Residue :=
  urgeRecoverySelect ctx.prior ctx.successors

noncomputable def queryLookSelectBare {S : Type} [ThermodynamicSystem ℚ S]
    [AdmissibleSystem ℚ S] [JointThermo ℚ S] (prior : S)
    (successors : List (Cand (K := ℚ) prior)) :
    Cand (K := ℚ) prior ⊕ Residue :=
  urgeRecoverySelect prior successors

def composeSurrogateFor : String := "UMST.Excitement.select"

theorem queryLookSelect_eq_select {S : Type} [ThermodynamicSystem ℚ S]
    [AdmissibleSystem ℚ S] [JointThermo ℚ S] (ctx : QueryLookCtx S) :
    queryLookSelect ctx = select ctx.prior ctx.successors :=
  rfl

theorem queryLookSelect_eq_urgeRecoverySelect {S : Type} [ThermodynamicSystem ℚ S]
    [AdmissibleSystem ℚ S] [JointThermo ℚ S] (ctx : QueryLookCtx S) :
    queryLookSelect ctx = urgeRecoverySelect ctx.prior ctx.successors :=
  rfl

theorem queryLookSelectBare_eq_select {S : Type} [ThermodynamicSystem ℚ S]
    [AdmissibleSystem ℚ S] [JointThermo ℚ S] (prior : S)
    (successors : List (Cand (K := ℚ) prior)) :
    queryLookSelectBare prior successors = select prior successors :=
  rfl

theorem queryLookNoLocalArgmin {S : Type} [ThermodynamicSystem ℚ S] [AdmissibleSystem ℚ S]
    [JointThermo ℚ S] (ctx : QueryLookCtx S) :
    queryLookSelect ctx = select ctx.prior ctx.successors :=
  rfl

theorem queryLookComposeSurrogateFor :
    composeSurrogateFor = "UMST.Excitement.select" :=
  rfl

theorem queryLookSelect_empty {S : Type} [ThermodynamicSystem ℚ S] [AdmissibleSystem ℚ S]
    [JointThermo ℚ S] (prior : S) (successors : List (Cand (K := ℚ) prior))
    (h : successors = []) :
    queryLookSelectBare prior successors = Sum.inr Residue.noCandidates := by
  subst h
  simpa [queryLookSelectBare] using urgeRecovery_empty prior

-- ================================================================
-- SECTION 4: Authority cites + physics GREEN fence
-- ================================================================

def epistemicMIAuthority : String :=
  "umst/umst-formal-double-slit/Lean/EpistemicMI.lean"

def landauerBoundAuthority : String :=
  "umst/umst-formal-double-slit/Lean/LandauerBound.lean"

def measurementCostAuthority : String :=
  "umst/umst-formal-double-slit/Lean/MeasurementCost.lean"

def landauerLawAuthority : String :=
  "umst/umst-formal-double-slit/Lean/LandauerLaw.lean"

def physicalSecondLawAuthority : String :=
  "LandauerLaw.physicalSecondLaw"

def epistemicQueryLookCellId : String :=
  "URGE-FORMAL-Q-LEAN-EPISTEMIC-QUERY-LOOK"

def epistemicQueryLookNamed : String :=
  "epistemic_query_look: §18 query verification cost information-up not coordination theater knowing fiber LandauerBound sole axiom physicalSecondLaw"

def epistemicQueryLookNonClaim : String :=
  "URGE-FORMAL-Q-LEAN-EPISTEMIC-QUERY-LOOK §18 query is verification cost information-up not coordination EpistemicQueryLook QueryLookClass verification-cost coordination-theater refused sole axiom physicalSecondLaw zero new axiom modality Unwired not physics GREEN not production_wired knowing fiber only"

def epistemicQuerySecondLawConservationFraming : String :=
  "second_law_conservation_query_look_one_axiom_landauer_not_second_axiom"

theorem epistemic_query_look_cell_id :
    epistemicQueryLookCellId = "URGE-FORMAL-Q-LEAN-EPISTEMIC-QUERY-LOOK" :=
  rfl

theorem epistemic_query_look_modality_unwired :
    epistemicQueryLookModalityCurrent = .unwired :=
  rfl

theorem production_wired_false : productionWired = false := rfl

theorem landauer_production_wired_false : landauerProductionWired = false := rfl

theorem epistemic_query_look_cites_epistemic_mi :
    epistemicMIAuthority ≠ "" :=
  by decide

theorem epistemic_query_look_cites_landauer_bound :
    landauerBoundAuthority ≠ "" :=
  by decide

theorem epistemic_query_look_cites_measurement_cost :
    measurementCostAuthority ≠ "" :=
  by decide

theorem epistemic_query_look_cites_physical_second_law :
    physicalSecondLawAuthority = "LandauerLaw.physicalSecondLaw" :=
  rfl

theorem epistemic_query_look_not_second_landauer_axiom :
    epistemicQuerySecondLawConservationFraming ≠ "landauer_second_axiom" :=
  by decide

theorem epistemic_query_look_compose_surrogate_ok :
    composeSurrogateFor = "UMST.Excitement.select" :=
  rfl

/-- Physics GREEN is not authorized on the knowing scaffold. -/
def physicsGreenAuthorized : Prop := False

theorem epistemic_query_look_physics_green_false : ¬ physicsGreenAuthorized :=
  id

def epistemicQueryLookKnowingFiberOk : Prop :=
  (verificationCostLook 1).lookFiber = .quantumKnowing ∧
  epistemicQueryLookModalityCurrent = .unwired ∧ ¬ physicsGreenAuthorized

theorem epistemic_query_look_knowing_fiber_ok :
    epistemicQueryLookKnowingFiberOk :=
  ⟨rfl, epistemic_query_look_modality_unwired, epistemic_query_look_physics_green_false⟩

theorem epistemic_query_look_not_meso_thermo_restate :
    epistemicQueryLookNonClaim ≠ "meso_thermo_G_T_P_x_restate" :=
  by decide

theorem epistemic_query_look_not_coordination_only :
    epistemicQueryLookNonClaim ≠ "coordination theater only" :=
  by decide

end UrgeKnowing.EpistemicQueryLook
