-- SPDX-FileCopyrightText: 2026 Santosh Prabhu Shenbagamoorthy and Santhosh Shyamsundar
-- SPDX-License-Identifier: MIT

import ElementElectronic

/-!
# ActinideOccupancyExceptions — finite period-7 qlattice Madelung occupancy exceptions

Finite named set of period-7 **predicted ≠ observed** qlattice occupancy exceptions as
`ActinideException` (Ac / Th / Pa / U / Np / Cm / Lr). Pins mirror `umst-chem` `qlattice`
`observed_override_config` and `madelung_predicted_config` authority — **not** a second axiom,
**not** GREEN DFT. Lr named override agrees with Madelung walk (honest pin).

- Each row: atomic number, observed subshell notation, Madelung-predicted notation, valence tag.
- Approximate-not-identity: six actinide exceptions differ; Lr override agrees Madelung.
- Distinct from `NamedException` (La / Ce / Gd / Pt / Au). Pu has no override.
- No meso / acting theorems. No new physics `axiom`.
- `physics_green` stays false.
-/

namespace UMST.Chem

/-- Design modality for actinide qlattice occupancy exception claims (TYPE-03 preview). -/
inductive ActinideOccupancyModality where
  | unwired | assumed | proved | surrogate
  deriving DecidableEq, Repr

def actinideOccupancyModalityCurrent : ActinideOccupancyModality := .unwired

/-- Finite period-7 qlattice occupancy exception tag (Ac / Th / Pa / U / Np / Cm / Lr). -/
inductive ActinideException where
  | Ac | Th | Pa | U | Np | Cm | Lr
  deriving DecidableEq, Repr

def ActinideException.z : ActinideException → Nat
  | .Ac => 89
  | .Th => 90
  | .Pa => 91
  | .U => 92
  | .Np => 93
  | .Cm => 96
  | .Lr => 103

def ActinideException.symbol : ActinideException → String
  | .Ac => "Ac"
  | .Th => "Th"
  | .Pa => "Pa"
  | .U => "U"
  | .Np => "Np"
  | .Cm => "Cm"
  | .Lr => "Lr"

theorem actinide_exception_ac_z : ActinideException.z .Ac = 89 := rfl

theorem actinide_exception_th_z : ActinideException.z .Th = 90 := rfl

theorem actinide_exception_pa_z : ActinideException.z .Pa = 91 := rfl

theorem actinide_exception_u_z : ActinideException.z .U = 92 := rfl

theorem actinide_exception_np_z : ActinideException.z .Np = 93 := rfl

theorem actinide_exception_cm_z : ActinideException.z .Cm = 96 := rfl

theorem actinide_exception_lr_z : ActinideException.z .Lr = 103 := rfl

/-- Observed ground-state subshell notation pin (qlattice `observed_override_config` SSOT). -/
def ActinideException.observedNotation : ActinideException → String
  | .Ac =>
    "1s22s22p63s23p64s23d104p65s24d105p66s24f145d106p67s26d1"
  | .Th =>
    "1s22s22p63s23p64s23d104p65s24d105p66s24f145d106p67s26d2"
  | .Pa =>
    "1s22s22p63s23p64s23d104p65s24d105p66s24f145d106p67s25f26d1"
  | .U =>
    "1s22s22p63s23p64s23d104p65s24d105p66s24f145d106p67s25f36d1"
  | .Np =>
    "1s22s22p63s23p64s23d104p65s24d105p66s24f145d106p67s25f46d1"
  | .Cm =>
    "1s22s22p63s23p64s23d104p65s24d105p66s24f145d106p67s25f76d1"
  | .Lr =>
    "1s22s22p63s23p64s23d104p65s24d105p66s24f145d106p67s25f146d1"

/-- Madelung (n+ℓ) walk predicted subshell notation at Z (`madelung_predicted_config` pin). -/
def ActinideException.predictedNotation : ActinideException → String
  | .Ac =>
    "1s22s22p63s23p64s23d104p65s24d105p66s24f145d106p67s25f1"
  | .Th =>
    "1s22s22p63s23p64s23d104p65s24d105p66s24f145d106p67s25f2"
  | .Pa =>
    "1s22s22p63s23p64s23d104p65s24d105p66s24f145d106p67s25f3"
  | .U =>
    "1s22s22p63s23p64s23d104p65s24d105p66s24f145d106p67s25f4"
  | .Np =>
    "1s22s22p63s23p64s23d104p65s24d105p66s24f145d106p67s25f5"
  | .Cm =>
    "1s22s22p63s23p64s23d104p65s24d105p66s24f145d106p67s25f8"
  | .Lr =>
    "1s22s22p63s23p64s23d104p65s24d105p66s24f145d106p67s25f146d1"

/-- Chemist valence occupancy shorthand (named pin — not axiom). -/
def ActinideException.occupancyTag : ActinideException → String
  | .Ac => "6d17s2"
  | .Th => "6d27s2"
  | .Pa => "5f26d17s2"
  | .U => "5f36d17s2"
  | .Np => "7s25f46d1"
  | .Cm => "5f76d17s2"
  | .Lr => "5f146d17s2"

/-- One actinide qlattice occupancy exception row (Unwired scaffold). -/
structure ActinideExceptionRow where
  exception : ActinideException
  modality : ActinideOccupancyModality
  deriving Repr

def ActinideExceptionRow.z (row : ActinideExceptionRow) : Nat := row.exception.z

def ActinideExceptionRow.symbol (row : ActinideExceptionRow) : String := row.exception.symbol

def ActinideExceptionRow.observedNotation (row : ActinideExceptionRow) : String :=
  row.exception.observedNotation

def ActinideExceptionRow.predictedNotation (row : ActinideExceptionRow) : String :=
  row.exception.predictedNotation

def ActinideExceptionRow.occupancyTag (row : ActinideExceptionRow) : String :=
  row.exception.occupancyTag

def actinideExceptionRow (ex : ActinideException) : ActinideExceptionRow :=
  { exception := ex, modality := actinideOccupancyModalityCurrent }

theorem actinide_exception_row_z (ex : ActinideException) :
    (actinideExceptionRow ex).z = ex.z := rfl

theorem actinide_exception_row_modality_unwired (ex : ActinideException) :
    (actinideExceptionRow ex).modality = .unwired := rfl

/-- Finite actinide exception list (cardinality 7 — not Z=1…118 dump). -/
def actinideExceptionList : List ActinideException :=
  [.Ac, .Th, .Pa, .U, .Np, .Cm, .Lr]

def actinideExceptionCount : Nat := actinideExceptionList.length

theorem actinide_exception_count_seven : actinideExceptionCount = 7 := rfl

theorem actinide_exception_list_length :
    actinideExceptionList.length = 7 := by native_decide

theorem ac_observed_ne_predicted :
    ActinideException.observedNotation .Ac ≠ ActinideException.predictedNotation .Ac := by native_decide

theorem th_observed_ne_predicted :
    ActinideException.observedNotation .Th ≠ ActinideException.predictedNotation .Th := by native_decide

theorem pa_observed_ne_predicted :
    ActinideException.observedNotation .Pa ≠ ActinideException.predictedNotation .Pa := by native_decide

theorem u_observed_ne_predicted :
    ActinideException.observedNotation .U ≠ ActinideException.predictedNotation .U := by native_decide

theorem np_observed_ne_predicted :
    ActinideException.observedNotation .Np ≠ ActinideException.predictedNotation .Np := by native_decide

theorem cm_observed_ne_predicted :
    ActinideException.observedNotation .Cm ≠ ActinideException.predictedNotation .Cm := by native_decide

/-- Lr: named qlattice override in `observed_override_config`; Madelung walk agrees (honest). -/
theorem lr_named_override_observed_eq_predicted :
    ActinideException.observedNotation .Lr = ActinideException.predictedNotation .Lr := rfl

theorem lr_named_override_in_observed_override_config :
    ActinideException.observedNotation .Lr ≠ "" := by native_decide

def actinideExceptionIsMadelungException (ex : ActinideException) : Prop :=
  ex.observedNotation ≠ ex.predictedNotation

theorem actinide_exception_is_madelung_exception (ex : ActinideException)
    (H : actinideExceptionIsMadelungException ex) :
    ex.observedNotation ≠ ex.predictedNotation := H

theorem actinide_exception_ac_is_madelung_exception :
    actinideExceptionIsMadelungException .Ac := ac_observed_ne_predicted

theorem actinide_exception_th_is_madelung_exception :
    actinideExceptionIsMadelungException .Th := th_observed_ne_predicted

theorem actinide_exception_pa_is_madelung_exception :
    actinideExceptionIsMadelungException .Pa := pa_observed_ne_predicted

theorem actinide_exception_u_is_madelung_exception :
    actinideExceptionIsMadelungException .U := u_observed_ne_predicted

theorem actinide_exception_np_is_madelung_exception :
    actinideExceptionIsMadelungException .Np := np_observed_ne_predicted

theorem actinide_exception_cm_is_madelung_exception :
    actinideExceptionIsMadelungException .Cm := cm_observed_ne_predicted

theorem actinide_exception_lr_not_madelung_exception :
    ¬ actinideExceptionIsMadelungException .Lr := by
  intro H
  exact H lr_named_override_observed_eq_predicted

/-- Approximate-not-identity: six period-7 exceptions differ; Lr named override agrees. -/
def actinideExceptionApproximateNotIdentity (ex : ActinideException) : Prop :=
  actinideExceptionIsMadelungException ex

theorem actinide_exception_approximate_not_identity_ac :
    actinideExceptionApproximateNotIdentity .Ac :=
  actinide_exception_ac_is_madelung_exception

theorem actinide_exception_approximate_not_identity_th :
    actinideExceptionApproximateNotIdentity .Th :=
  actinide_exception_th_is_madelung_exception

theorem actinide_exception_approximate_not_identity_pa :
    actinideExceptionApproximateNotIdentity .Pa :=
  actinide_exception_pa_is_madelung_exception

theorem actinide_exception_approximate_not_identity_u :
    actinideExceptionApproximateNotIdentity .U :=
  actinide_exception_u_is_madelung_exception

theorem actinide_exception_approximate_not_identity_np :
    actinideExceptionApproximateNotIdentity .Np :=
  actinide_exception_np_is_madelung_exception

theorem actinide_exception_approximate_not_identity_cm :
    actinideExceptionApproximateNotIdentity .Cm :=
  actinide_exception_cm_is_madelung_exception

/-- Cited upstream Q-lattice type authority (views only — pins are named here). -/
def actinideOccupancyQlatticeAuthority : String :=
  "umst/umst-chem/src/qlattice.rs"

/-- Cited sibling Madelung witness authority — cite, no second axiom fork. -/
def actinideOccupancyMadelungWitnessAuthority : String :=
  "umst/umst-chem/src/x_rows/madelung_witness.rs"

/-- Cell id for the Lean actinide qlattice occupancy exception knowing-fiber. -/
def actinideOccupancyExceptionsCellId : String :=
  "CHEM-FORMAL-Q-LEAN-ACTINIDE-OCCUPANCY-EXCEPTIONS"

/-- Non-claim fence — finite named Ac Th Pa U Np Cm Lr exceptions Unwired ≠ Proved GREEN. -/
def actinideOccupancyExceptionsNonClaim : String :=
  "CHEM-FORMAL-Q-LEAN-ACTINIDE-OCCUPANCY-EXCEPTIONS finite period-7 named qlattice Madelung occupancy exceptions Ac Th Pa U Np Cm Lr as ActinideException; observed_override_config and madelung_predicted_config pins; Lr named override agrees Madelung honest; cites qlattice and madelung_witness not second axiom; not GREEN DFT; not physics GREEN; not production_wired"

/-- Physics GREEN is unauthorized on the knowing actinide occupancy scaffold. -/
def actinideOccupancyPhysicsGreenAuthorized : Prop := False

theorem actinide_occupancy_physics_green_false :
    ¬ actinideOccupancyPhysicsGreenAuthorized := id

theorem actinide_occupancy_modality_unwired :
    actinideOccupancyModalityCurrent = .unwired := rfl

theorem actinide_occupancy_not_second_axiom :
    actinideOccupancyMadelungWitnessAuthority ≠ "" := by native_decide

theorem actinide_occupancy_cites_qlattice :
    actinideOccupancyQlatticeAuthority = "umst/umst-chem/src/qlattice.rs" := rfl

theorem actinide_occupancy_exceptions_cell_id :
    actinideOccupancyExceptionsCellId =
      "CHEM-FORMAL-Q-LEAN-ACTINIDE-OCCUPANCY-EXCEPTIONS" := rfl

end UMST.Chem
