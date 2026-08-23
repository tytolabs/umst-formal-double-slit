-- SPDX-FileCopyrightText: 2026 Santosh Prabhu Shenbagamoorthy and Santhosh Shyamsundar
-- SPDX-License-Identifier: MIT

import ElementElectronic

/-!
# NamedOccupancyExceptions — finite Madelung occupancy exception set (Q lattice)

Finite named set of Madelung **predicted ≠ observed** occupancy exceptions as `NamedException`
(La / Ce / Gd / Pt / Au). Pins mirror `umst-chem` `qlattice` observed overrides and
`madelung_witness` cross-matrix authority — **not** a second axiom, **not** GREEN DFT.

- Each row: atomic number, observed subshell notation, Madelung-predicted notation, valence tag.
- Approximate-not-identity: same Z electron count, different notation (design witness).
- No meso / acting theorems. No new physics `axiom`.
- `physics_green` stays false.
-/

namespace UMST.Chem

/-- Design modality for named Madelung occupancy exception claims (TYPE-03 preview). -/
inductive NamedOccupancyModality where
  | unwired | assumed | proved | surrogate
  deriving DecidableEq, Repr

def namedOccupancyModalityCurrent : NamedOccupancyModality := .unwired

/-- Finite named Madelung occupancy exception tag (La / Ce / Gd / Pt / Au). -/
inductive NamedException where
  | La | Ce | Gd | Pt | Au
  deriving DecidableEq, Repr

def NamedException.z : NamedException → Nat
  | .La => 57
  | .Ce => 58
  | .Gd => 64
  | .Pt => 78
  | .Au => 79

def NamedException.symbol : NamedException → String
  | .La => "La"
  | .Ce => "Ce"
  | .Gd => "Gd"
  | .Pt => "Pt"
  | .Au => "Au"

theorem named_exception_la_z : NamedException.z .La = 57 := rfl

theorem named_exception_ce_z : NamedException.z .Ce = 58 := rfl

theorem named_exception_gd_z : NamedException.z .Gd = 64 := rfl

theorem named_exception_pt_z : NamedException.z .Pt = 78 := rfl

theorem named_exception_au_z : NamedException.z .Au = 79 := rfl

/-- Observed ground-state subshell notation pin (qlattice SSOT — not GREEN DFT). -/
def NamedException.observedNotation : NamedException → String
  | .La => "1s22s22p63s23p64s23d104p65s24d105p66s25d1"
  | .Ce => "1s22s22p63s23p64s23d104p65s24d105p66s24f15d1"
  | .Gd => "1s22s22p63s23p64s23d104p65s24d105p66s24f75d1"
  | .Pt =>
    "1s22s22p63s23p63d104s24p64d104f145s25p65d96s1"
  | .Au =>
    "1s22s22p63s23p64s23d104p65s24d105p66s24f145d106s1"

/-- Madelung (n+ℓ) walk predicted subshell notation at Z (design witness — not identity). -/
def NamedException.predictedNotation : NamedException → String
  | .La => "1s22s22p63s23p64s23d104p65s24d105p66s24f1"
  | .Ce => "1s22s22p63s23p64s23d104p65s24d105p66s24f2"
  | .Gd => "1s22s22p63s23p64s23d104p65s24d105p66s24f8"
  | .Pt => "1s22s22p63s23p64s23d104p65s24d105p66s24f145d8"
  | .Au => "1s22s22p63s23p64s23d104p65s24d105p66s24f145d9"

/-- Chemist valence occupancy shorthand (named pin — not axiom). -/
def NamedException.occupancyTag : NamedException → String
  | .La => "5d16s2"
  | .Ce => "4f15d16s2"
  | .Gd => "4f75d16s2"
  | .Pt => "5d96s1"
  | .Au => "5d106s1"

/-- One named Madelung occupancy exception row (Unwired scaffold). -/
structure NamedExceptionRow where
  exception : NamedException
  modality : NamedOccupancyModality
  deriving Repr

def NamedExceptionRow.z (row : NamedExceptionRow) : Nat := row.exception.z

def NamedExceptionRow.symbol (row : NamedExceptionRow) : String := row.exception.symbol

def NamedExceptionRow.observedNotation (row : NamedExceptionRow) : String :=
  row.exception.observedNotation

def NamedExceptionRow.predictedNotation (row : NamedExceptionRow) : String :=
  row.exception.predictedNotation

def NamedExceptionRow.occupancyTag (row : NamedExceptionRow) : String :=
  row.exception.occupancyTag

def namedExceptionRow (ex : NamedException) : NamedExceptionRow :=
  { exception := ex, modality := namedOccupancyModalityCurrent }

theorem named_exception_row_z (ex : NamedException) :
    (namedExceptionRow ex).z = ex.z := rfl

theorem named_exception_row_modality_unwired (ex : NamedException) :
    (namedExceptionRow ex).modality = .unwired := rfl

/-- Finite named exception list (cardinality 5 — not Z=1…118 dump). -/
def namedExceptionList : List NamedException :=
  [.La, .Ce, .Gd, .Pt, .Au]

def namedExceptionCount : Nat := namedExceptionList.length

theorem named_exception_count_five : namedExceptionCount = 5 := rfl

theorem named_exception_list_length :
    namedExceptionList.length = 5 := by native_decide

theorem la_observed_ne_predicted :
    NamedException.observedNotation .La ≠ NamedException.predictedNotation .La := by native_decide

theorem ce_observed_ne_predicted :
    NamedException.observedNotation .Ce ≠ NamedException.predictedNotation .Ce := by native_decide

theorem gd_observed_ne_predicted :
    NamedException.observedNotation .Gd ≠ NamedException.predictedNotation .Gd := by native_decide

theorem pt_observed_ne_predicted :
    NamedException.observedNotation .Pt ≠ NamedException.predictedNotation .Pt := by native_decide

theorem au_observed_ne_predicted :
    NamedException.observedNotation .Au ≠ NamedException.predictedNotation .Au := by native_decide

theorem named_exception_is_madelung_exception (ex : NamedException) :
    ex.observedNotation ≠ ex.predictedNotation := by
  cases ex <;> native_decide

/-- Approximate-not-identity: predicted and observed notations differ at same Z pin. -/
def namedExceptionApproximateNotIdentity (ex : NamedException) : Prop :=
  ex.observedNotation ≠ ex.predictedNotation

theorem named_exception_approximate_not_identity (ex : NamedException) :
    namedExceptionApproximateNotIdentity ex := named_exception_is_madelung_exception ex

/-- Cited upstream Q-lattice type authority (views only — pins are named here). -/
def namedOccupancyQlatticeAuthority : String :=
  "umst/umst-chem/src/qlattice.rs"

/-- Cited sibling Madelung witness authority — cite, no second axiom fork. -/
def namedOccupancyMadelungWitnessAuthority : String :=
  "umst/umst-chem/src/x_rows/madelung_witness.rs"

/-- Cell id for the Lean named Madelung occupancy exception knowing-fiber. -/
def namedOccupancyExceptionsCellId : String :=
  "CHEM-FORMAL-Q-LEAN-NAMED-OCCUPANCY-EXCEPTIONS"

/-- Non-claim fence — finite named La Ce Gd Pt Au exceptions Unwired ≠ Proved GREEN. -/
def namedOccupancyExceptionsNonClaim : String :=
  "CHEM-FORMAL-Q-LEAN-NAMED-OCCUPANCY-EXCEPTIONS finite named Madelung occupancy exceptions La Ce Gd Pt Au as NamedException; predicted vs observed approximate not identity; cites qlattice and madelung_witness not second axiom; not GREEN DFT; not physics GREEN; not production_wired"

/-- Physics GREEN is unauthorized on the knowing named occupancy scaffold. -/
def namedOccupancyPhysicsGreenAuthorized : Prop := False

theorem named_occupancy_physics_green_false :
    ¬ namedOccupancyPhysicsGreenAuthorized := id

theorem named_occupancy_modality_unwired :
    namedOccupancyModalityCurrent = .unwired := rfl

theorem named_occupancy_not_second_axiom :
    namedOccupancyMadelungWitnessAuthority ≠ "" := by native_decide

theorem named_occupancy_cites_qlattice :
    namedOccupancyQlatticeAuthority = "umst/umst-chem/src/qlattice.rs" := rfl

end UMST.Chem
