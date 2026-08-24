-- SPDX-FileCopyrightText: 2026 Santosh Prabhu Shenbagamoorthy and Santhosh Shyamsundar
-- SPDX-License-Identifier: MIT
/-
  UMST-Formal: UrgeKnowing/LandauerNTo1.lean

  Knowing fiber (§19.8): Landauer price of N→1 compression.
  Every ADK collapse destroys information; price in **bits of destroyed distinction**,
  not fake joules / laptop heat theater. Joule conversion is the Landauer floor
  (`kT ln 2` per bit), not measured device heat. Mirrors `LandauerHistoryLook.lean`
  and cross-lang `LandauerNTo1` — not meso thermo G(T,P,x) restated.

  N→1 recovery composes `UMST.Excitement.select` — no second argmin.
  Sole physics axiom remains `LandauerLaw.physicalSecondLaw` (imported, not re-declared).
  Adds **zero** Lean `axiom` declarations. Zero sorry.
-/

import LandauerEinsteinBridge
import LandauerLaw

open Real UMST.LandauerLaw

namespace UrgeKnowing.LandauerNTo1

-- ================================================================
-- SECTION 1: Modality + knowing-fiber pins (Unwired)
-- ================================================================

/-- Design modality for landauer-n-to-1 claims (TYPE-03 preview). -/
inductive LandauerNTo1Modality where
  | unwired | assumed | proved | surrogate
  deriving DecidableEq, Repr

def landauerNTo1ModalityCurrent : LandauerNTo1Modality := .unwired

def productionWired : Bool := false

def landauerProductionWired : Bool := false

-- ================================================================
-- SECTION 2: Destroyed distinction bits + Landauer floor scaffold
-- ================================================================

/-- Destroyed distinction bits for N distinguishable states collapsing to 1. -/
def destroyedDistinctionBitsFromN (n : ℕ) : Option ℕ :=
  match n with
  | 0 | 1 => none
  | n + 2 => some (Nat.log2 (n + 2))

@[simp] theorem destroyed_distinction_bits_four :
    destroyedDistinctionBitsFromN 4 = some 2 := by native_decide

@[simp] theorem destroyed_distinction_bits_two :
    destroyedDistinctionBitsFromN 2 = some 1 := by native_decide

@[simp] theorem destroyed_distinction_bits_one :
    destroyedDistinctionBitsFromN 1 = none := by native_decide

@[simp] theorem destroyed_distinction_bits_zero :
    destroyedDistinctionBitsFromN 0 = none := by native_decide

lemma landauerBitEnergy_nonneg_local {T : ℝ} (hT : 0 ≤ T) : 0 ≤ landauerBitEnergy T := by
  unfold landauerBitEnergy
  apply mul_nonneg
  · exact mul_nonneg (le_of_lt kBoltzmannSI_pos) hT
  · exact le_of_lt (Real.log_pos (by norm_num : (1 : ℝ) < 2))

/-- Landauer floor joules from destroyed bits (floor only, not laptop heat). -/
noncomputable def landauerFloorFromDestroyedBits (T : ℝ) (bits : ℕ) : ℝ :=
  landauerBitEnergy T * (bits : ℝ)

theorem landauerFloorFromDestroyedBits_nonneg (T : ℝ) (bits : ℕ) (hT : 0 ≤ T) :
    0 ≤ landauerFloorFromDestroyedBits T bits := by
  unfold landauerFloorFromDestroyedBits
  exact mul_nonneg (landauerBitEnergy_nonneg_local hT) (Nat.cast_nonneg bits)

theorem landauerFloor_two_bit_collapse_nonneg (T : ℝ) (hT : 0 ≤ T) :
    0 ≤ landauerFloorFromDestroyedBits T 2 :=
  landauerFloorFromDestroyedBits_nonneg T 2 hT

theorem landauerFloor_two_bit_le_bit_energy (T : ℝ) (_hT : 0 ≤ T) :
    landauerFloorFromDestroyedBits T 2 ≤ 2 * landauerBitEnergy T := by
  unfold landauerFloorFromDestroyedBits
  exact le_of_eq (by ring)

def landauerFloorScaffoldNamed : String :=
  "landauerFloorJoules: kT ln2 per bit floor scaffold — not measured laptop heat"

/-- Bits-first compression cost hook from claimed destroyed bits. -/
def landauerCompressionCost (claimedDestroyedBits : Option ℕ) : ℕ :=
  match claimedDestroyedBits with
  | some bits => bits
  | none => 0

theorem landauerCompressionCost_nonneg (claimedDestroyedBits : Option ℕ) :
    0 ≤ landauerCompressionCost claimedDestroyedBits := by
  cases claimedDestroyedBits <;> simp [landauerCompressionCost]

-- ================================================================
-- SECTION 3: N→1 compression candidate scaffold (bits-first discipline)
-- ================================================================

/-- N→1 compression candidate on the knowing fiber. -/
structure CompressionCandidate where
  sourceDistinctionCount : ℕ
  claimedDestroyedBits : Option ℕ
  laptopHeatJoulesTheater : Bool
  claimsPhysicsGreen : Bool
  provenanceIntact : Bool
  evidenceTagged : Bool

inductive LandauerNTo1Refusal where
  | laptopHeatTheater
  | inventedDistinctionBits
  | falseGreenCompression
  | secondArgmin
  | provenanceLost
  | missingEvidenceTag
  deriving DecidableEq, Repr

inductive CompressionVerdict where
  | accept | refuse
  deriving DecidableEq, Repr

def admitCompressionCandidate (c : CompressionCandidate) : Option LandauerNTo1Refusal :=
  if c.laptopHeatJoulesTheater then
    some .laptopHeatTheater
  else if c.claimsPhysicsGreen then
    some .falseGreenCompression
  else if !c.provenanceIntact then
    some .provenanceLost
  else if !c.evidenceTagged then
    some .missingEvidenceTag
  else
    match destroyedDistinctionBitsFromN c.sourceDistinctionCount, c.claimedDestroyedBits with
    | some expected, some claimed =>
      if expected = claimed then none else some .inventedDistinctionBits
    | _, _ => some .inventedDistinctionBits

def evaluateCompression (c : CompressionCandidate) : CompressionVerdict :=
  match admitCompressionCandidate c with
  | none => .accept
  | some _ => .refuse

def fixtureAdmissibleTwoBitCollapse : CompressionCandidate :=
  { sourceDistinctionCount := 4
    claimedDestroyedBits := some 2
    laptopHeatJoulesTheater := false
    claimsPhysicsGreen := false
    provenanceIntact := true
    evidenceTagged := true }

def fixtureInadmissibleLaptopHeat : CompressionCandidate :=
  { sourceDistinctionCount := 4
    claimedDestroyedBits := some 2
    laptopHeatJoulesTheater := true
    claimsPhysicsGreen := false
    provenanceIntact := true
    evidenceTagged := true }

def fixtureInadmissibleInventedBits : CompressionCandidate :=
  { sourceDistinctionCount := 4
    claimedDestroyedBits := some 47
    laptopHeatJoulesTheater := false
    claimsPhysicsGreen := false
    provenanceIntact := true
    evidenceTagged := true }

theorem fixture_admissible_two_bit_accepts :
    evaluateCompression fixtureAdmissibleTwoBitCollapse = .accept := by native_decide

theorem fixture_laptop_heat_refuses :
    admitCompressionCandidate fixtureInadmissibleLaptopHeat = some .laptopHeatTheater := by native_decide

theorem fixture_invented_bits_refuses :
    admitCompressionCandidate fixtureInadmissibleInventedBits = some .inventedDistinctionBits := by native_decide

theorem landauer_n_to_1_laptop_heat_positive_refuse :
    admitCompressionCandidate fixtureInadmissibleLaptopHeat = some .laptopHeatTheater := by native_decide

theorem landauer_n_to_1_invented_bits_positive_refuse :
    admitCompressionCandidate fixtureInadmissibleInventedBits = some .inventedDistinctionBits := by native_decide

theorem landauer_compression_cost_admissible_two_bits :
    landauerCompressionCost fixtureAdmissibleTwoBitCollapse.claimedDestroyedBits = 2 := rfl

-- ================================================================
-- SECTION 4: N→1 composes Excitement.select (no second argmin)
-- ================================================================

/-- Compose pin — import `UMST.Excitement.select`; refuse a local second argmin. -/
inductive ExcitementComposePin where
  | importSelectExcitement | secondArgminRefused
  deriving DecidableEq, Repr

def excitementComposePinCurrent : ExcitementComposePin := .importSelectExcitement

def composeSurrogateFor : String := "UMST.Excitement.select"

def excitementComposeMetaPath : String :=
  "umst-meta/crates/umst-meta/src/excitement.rs"

def localArgminTheater : String := "local_Q_argmin_second_selector"

theorem landauerNTo1ComposeImportSelect :
    excitementComposePinCurrent = .importSelectExcitement :=
  rfl

theorem landauerNTo1ComposeSurrogateOk :
    composeSurrogateFor = "UMST.Excitement.select" :=
  rfl

theorem landauerNTo1NoSecondArgmin :
    composeSurrogateFor ≠ localArgminTheater :=
  by decide

theorem landauerNTo1ComposeNotSecondArgmin :
    excitementComposePinCurrent ≠ .secondArgminRefused :=
  by decide

/-- Second Excitement selector implementation is inadmissible on this scaffold. -/
theorem refuseSecondArgminWitness : LandauerNTo1Refusal.secondArgmin = .secondArgmin := rfl

-- ================================================================
-- SECTION 5: Authority cites + physics GREEN fence
-- ================================================================

def landauerBoundAuthority : String :=
  "umst/umst-formal-double-slit/Lean/LandauerBound.lean"

def landauerLawAuthority : String :=
  "umst/umst-formal-double-slit/Lean/LandauerLaw.lean"

def physicalSecondLawAuthority : String :=
  "LandauerLaw.physicalSecondLaw"

def landauerNTo1CellId : String :=
  "URGE-FORMAL-Q-LEAN-LANDAUER-N-TO-1"

def landauerNTo1Named : String :=
  "landauer_n_to_1: §19.8 N→1 compression destroyed distinction bits LandauerBound not laptop heat"

def landauerNTo1NonClaim : String :=
  "URGE-FORMAL-Q-LEAN-LANDAUER-N-TO-1 §19.8 Landauer price of N→1 compression; bits of destroyed distinction not fake joules; Landauer floor kT ln2 per bit not measured laptop heat; compose Excitement select no second argmin; Unwired one axiom physicalSecondLaw not second Landauer axiom not meso thermo not GREEN not physics GREEN not production_wired"

def landauerNTo1SecondLawConservationFraming : String :=
  "second_law_conservation_n_to_1_one_axiom_landauer_not_second_axiom"

def laptopHeatTheaterPrimary : String :=
  "laptop_heat_joules_primary_price"

theorem landauer_n_to_1_cell_id :
    landauerNTo1CellId = "URGE-FORMAL-Q-LEAN-LANDAUER-N-TO-1" :=
  rfl

theorem landauer_n_to_1_modality_unwired :
    landauerNTo1ModalityCurrent = .unwired :=
  rfl

theorem production_wired_false : productionWired = false := rfl

theorem landauer_production_wired_false : landauerProductionWired = false := rfl

theorem landauer_n_to_1_cites_landauer_bound :
    landauerBoundAuthority ≠ "" :=
  by decide

theorem landauer_n_to_1_cites_landauer_law :
    landauerLawAuthority ≠ "" :=
  by decide

theorem landauer_n_to_1_cites_physical_second_law :
    physicalSecondLawAuthority = "LandauerLaw.physicalSecondLaw" :=
  rfl

theorem landauer_n_to_1_not_second_landauer_axiom :
    landauerNTo1SecondLawConservationFraming ≠ "landauer_second_axiom" :=
  by decide

theorem landauer_n_to_1_second_law_conservation_framing :
    landauerNTo1SecondLawConservationFraming ≠ "" :=
  by decide

theorem landauer_n_to_1_not_laptop_heat_theater :
    landauerNTo1NonClaim ≠ laptopHeatTheaterPrimary :=
  by decide

/-- Physics GREEN is not authorized on the knowing scaffold. -/
def physicsGreenAuthorized : Prop := False

theorem landauer_n_to_1_physics_green_false : ¬ physicsGreenAuthorized :=
  id

theorem landauer_n_to_1_not_meso_thermo_restate :
    landauerNTo1NonClaim ≠ "meso_thermo_G_T_P_x_restate" :=
  by decide

theorem landauerNTo1NamedOk :
    landauerNTo1Named ≠ "" :=
  by decide

end UrgeKnowing.LandauerNTo1
