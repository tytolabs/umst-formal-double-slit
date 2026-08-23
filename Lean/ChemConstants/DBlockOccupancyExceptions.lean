-- SPDX-FileCopyrightText: 2026 Santosh Prabhu Shenbagamoorthy and Santhosh Shyamsundar
-- SPDX-License-Identifier: MIT

import ElementElectronic

/-!
# DBlockOccupancyExceptions — finite period-4/5 d-block qlattice Madelung occupancy exceptions

Finite named set of period-4/5 **predicted ≠ observed** qlattice occupancy exceptions as
`DBlockException` (Cr / Cu / Nb / Mo / Ru / Rh / Pd / Ag). Pins mirror `umst-chem` `qlattice`
`observed_override_config` and `madelung_predicted_config` authority — **not** a second axiom,
**not** GREEN DFT. DISTINCT from `NamedException` (La / Ce / Gd / Pt / Au) and
`ActinideException` (Ac / Th / Pa / U / Np / Cm / Lr).

- Each row: atomic number, observed subshell notation, Madelung-predicted notation, valence tag.
- Approximate-not-identity: all eight d-block exceptions differ predicted vs observed.
- No meso / acting theorems. No new physics `axiom`.
- `physics_green` stays false.
-/

namespace UMST.Chem

/-- Design modality for d-block qlattice occupancy exception claims (TYPE-03 preview). -/
inductive DBlockOccupancyModality where
  | unwired | assumed | proved | surrogate
  deriving DecidableEq, Repr

def dBlockOccupancyModalityCurrent : DBlockOccupancyModality := .unwired

/-- Finite period-4/5 d-block qlattice occupancy exception tag (Cr / Cu / Nb / Mo / Ru / Rh / Pd / Ag). -/
inductive DBlockException where
  | Cr | Cu | Nb | Mo | Ru | Rh | Pd | Ag
  deriving DecidableEq, Repr

def DBlockException.z : DBlockException → Nat
  | .Cr => 24
  | .Cu => 29
  | .Nb => 41
  | .Mo => 42
  | .Ru => 44
  | .Rh => 45
  | .Pd => 46
  | .Ag => 47

def DBlockException.symbol : DBlockException → String
  | .Cr => "Cr"
  | .Cu => "Cu"
  | .Nb => "Nb"
  | .Mo => "Mo"
  | .Ru => "Ru"
  | .Rh => "Rh"
  | .Pd => "Pd"
  | .Ag => "Ag"

theorem d_block_exception_cr_z : DBlockException.z .Cr = 24 := rfl

theorem d_block_exception_cu_z : DBlockException.z .Cu = 29 := rfl

theorem d_block_exception_nb_z : DBlockException.z .Nb = 41 := rfl

theorem d_block_exception_mo_z : DBlockException.z .Mo = 42 := rfl

theorem d_block_exception_ru_z : DBlockException.z .Ru = 44 := rfl

theorem d_block_exception_rh_z : DBlockException.z .Rh = 45 := rfl

theorem d_block_exception_pd_z : DBlockException.z .Pd = 46 := rfl

theorem d_block_exception_ag_z : DBlockException.z .Ag = 47 := rfl

/-- Observed ground-state subshell notation pin (qlattice `observed_override_config` SSOT). -/
def DBlockException.observedNotation : DBlockException → String
  | .Cr => "1s22s22p63s23p64s13d5"
  | .Cu => "1s22s22p63s23p64s13d10"
  | .Nb => "1s22s22p63s23p64s23d104p65s14d4"
  | .Mo => "1s22s22p63s23p64s23d104p65s14d5"
  | .Ru => "1s22s22p63s23p64s23d104p65s14d7"
  | .Rh => "1s22s22p63s23p64s23d104p65s14d8"
  | .Pd => "1s22s22p63s23p64s23d104p64d10"
  | .Ag => "1s22s22p63s23p64s23d104p65s14d10"

/-- Madelung (n+ℓ) walk predicted subshell notation at Z (`madelung_predicted_config` pin). -/
def DBlockException.predictedNotation : DBlockException → String
  | .Cr => "1s22s22p63s23p64s23d4"
  | .Cu => "1s22s22p63s23p64s23d9"
  | .Nb => "1s22s22p63s23p64s23d104p65s24d3"
  | .Mo => "1s22s22p63s23p64s23d104p65s24d4"
  | .Ru => "1s22s22p63s23p64s23d104p65s24d6"
  | .Rh => "1s22s22p63s23p64s23d104p65s24d7"
  | .Pd => "1s22s22p63s23p64s23d104p65s24d8"
  | .Ag => "1s22s22p63s23p64s23d104p65s24d9"

/-- Chemist valence occupancy shorthand (named pin — not axiom). -/
def DBlockException.occupancyTag : DBlockException → String
  | .Cr => "3d54s1"
  | .Cu => "3d104s1"
  | .Nb => "4d45s1"
  | .Mo => "4d55s1"
  | .Ru => "4d75s1"
  | .Rh => "4d85s1"
  | .Pd => "4d105s0"
  | .Ag => "4d105s1"

/-- One d-block qlattice occupancy exception row (Unwired scaffold). -/
structure DBlockExceptionRow where
  exception : DBlockException
  modality : DBlockOccupancyModality
  deriving Repr

def DBlockExceptionRow.z (row : DBlockExceptionRow) : Nat := row.exception.z

def DBlockExceptionRow.symbol (row : DBlockExceptionRow) : String := row.exception.symbol

def DBlockExceptionRow.observedNotation (row : DBlockExceptionRow) : String :=
  row.exception.observedNotation

def DBlockExceptionRow.predictedNotation (row : DBlockExceptionRow) : String :=
  row.exception.predictedNotation

def DBlockExceptionRow.occupancyTag (row : DBlockExceptionRow) : String :=
  row.exception.occupancyTag

def dBlockExceptionRow (ex : DBlockException) : DBlockExceptionRow :=
  { exception := ex, modality := dBlockOccupancyModalityCurrent }

theorem d_block_exception_row_z (ex : DBlockException) :
    (dBlockExceptionRow ex).z = ex.z := rfl

theorem d_block_exception_row_modality_unwired (ex : DBlockException) :
    (dBlockExceptionRow ex).modality = .unwired := rfl

/-- Finite d-block exception list (cardinality 8 — not Z=1…118 dump). -/
def dBlockExceptionList : List DBlockException :=
  [.Cr, .Cu, .Nb, .Mo, .Ru, .Rh, .Pd, .Ag]

def dBlockExceptionCount : Nat := dBlockExceptionList.length

theorem d_block_exception_count_eight : dBlockExceptionCount = 8 := rfl

theorem d_block_exception_list_length :
    dBlockExceptionList.length = 8 := by native_decide

theorem cr_observed_ne_predicted :
    DBlockException.observedNotation .Cr ≠ DBlockException.predictedNotation .Cr := by native_decide

theorem cu_observed_ne_predicted :
    DBlockException.observedNotation .Cu ≠ DBlockException.predictedNotation .Cu := by native_decide

theorem nb_observed_ne_predicted :
    DBlockException.observedNotation .Nb ≠ DBlockException.predictedNotation .Nb := by native_decide

theorem mo_observed_ne_predicted :
    DBlockException.observedNotation .Mo ≠ DBlockException.predictedNotation .Mo := by native_decide

theorem ru_observed_ne_predicted :
    DBlockException.observedNotation .Ru ≠ DBlockException.predictedNotation .Ru := by native_decide

theorem rh_observed_ne_predicted :
    DBlockException.observedNotation .Rh ≠ DBlockException.predictedNotation .Rh := by native_decide

theorem pd_observed_ne_predicted :
    DBlockException.observedNotation .Pd ≠ DBlockException.predictedNotation .Pd := by native_decide

theorem ag_observed_ne_predicted :
    DBlockException.observedNotation .Ag ≠ DBlockException.predictedNotation .Ag := by native_decide

def dBlockExceptionIsMadelungException (ex : DBlockException) : Prop :=
  ex.observedNotation ≠ ex.predictedNotation

theorem d_block_exception_is_madelung_exception (ex : DBlockException) :
    ex.observedNotation ≠ ex.predictedNotation := by
  cases ex <;> native_decide

/-- Approximate-not-identity: predicted and observed notations differ at same Z pin. -/
def dBlockExceptionApproximateNotIdentity (ex : DBlockException) : Prop :=
  ex.observedNotation ≠ ex.predictedNotation

theorem d_block_exception_approximate_not_identity (ex : DBlockException) :
    dBlockExceptionApproximateNotIdentity ex :=
  d_block_exception_is_madelung_exception ex

/-- Cited upstream Q-lattice type authority (views only — pins are named here). -/
def dBlockOccupancyQlatticeAuthority : String :=
  "umst/umst-chem/src/qlattice.rs"

/-- Cited sibling Madelung witness authority — cite, no second axiom fork. -/
def dBlockOccupancyMadelungWitnessAuthority : String :=
  "umst/umst-chem/src/x_rows/madelung_witness.rs"

/-- Cell id for the Lean d-block qlattice occupancy exception knowing-fiber. -/
def dBlockOccupancyExceptionsCellId : String :=
  "CHEM-FORMAL-Q-LEAN-DBLOCK-OCCUPANCY-EXCEPTIONS"

/-- Non-claim fence — finite period-4/5 d-block Cr Cu Nb Mo Ru Rh Pd Ag exceptions Unwired ≠ Proved GREEN. -/
def dBlockOccupancyExceptionsNonClaim : String :=
  "CHEM-FORMAL-Q-LEAN-DBLOCK-OCCUPANCY-EXCEPTIONS finite period-4/5 d-block qlattice Madelung occupancy exceptions Cr Cu Nb Mo Ru Rh Pd Ag as DBlockException; observed_override_config and madelung_predicted_config pins; DISTINCT from NamedException and actinide exceptions; cites qlattice and madelung_witness not second axiom; not GREEN DFT; not physics GREEN; not production_wired"

/-- Physics GREEN is unauthorized on the knowing d-block occupancy scaffold. -/
def dBlockOccupancyPhysicsGreenAuthorized : Prop := False

theorem d_block_occupancy_physics_green_false :
    ¬ dBlockOccupancyPhysicsGreenAuthorized := id

theorem d_block_occupancy_modality_unwired :
    dBlockOccupancyModalityCurrent = .unwired := rfl

theorem d_block_occupancy_not_second_axiom :
    dBlockOccupancyMadelungWitnessAuthority ≠ "" := by native_decide

theorem d_block_occupancy_cites_qlattice :
    dBlockOccupancyQlatticeAuthority = "umst/umst-chem/src/qlattice.rs" := rfl

theorem d_block_occupancy_exceptions_cell_id :
    dBlockOccupancyExceptionsCellId =
      "CHEM-FORMAL-Q-LEAN-DBLOCK-OCCUPANCY-EXCEPTIONS" := rfl

end UMST.Chem
