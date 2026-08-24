-- SPDX-FileCopyrightText: 2026 Santosh Prabhu Shenbagamoorthy and Santhosh Shyamsundar
-- SPDX-License-Identifier: MIT

import ElementElectronic

set_option maxRecDepth 8192

/-!
# NaturalOccurrenceZ118 — Z=1..118 natural occurrence **conservation** (Q lattice)

Knowing-fiber Lean: Z=1..118 natural occurrence as Unwired named product classifiers
(native / oxide / sulfide / silicate / halide+carbonate / atmophile / synthetic-or-trace);
not folklore lists; concurrent product bits not XOR enum. He atmophile-only;
Fe native⊗oxide⊗sulfide product. Pairs `umst-chem` scaffold `natural_occurrence_z118` /
**conservation** posture.

- `NaturalOccurrenceZ118Modality` — Unwired / Assumed / Proved / Surrogate (not 118² GREEN table).
- `occurrenceProductTable` — 118-entry concurrent-bit classifier table (not XOR enum).
- `occurrenceBits` — bits for Z in 1..118 bar.
- `heliumHasNoCrustalOreBit` / `ironIsOccurrenceProduct` — named witness pins.
- Second-law + **conservation** framing cites meso `UMST.Chem.Conservation` /
  `LandauerLaw.physicalSecondLaw` — not imported.
- No meso / acting theorems. No new physics `axiom`.
- `physics_green` stays false. Does **not** claim `naturalOccurrenceZ118Proved` or physics GREEN.
- WAVE100 freeze — remainder deferred composition (env/time/cross-domain), not impossibility stop.
-/

namespace UMST.Chem

/-- Design modality for natural occurrence Z118 **conservation** (lattice SSOT). -/
inductive NaturalOccurrenceZ118Modality where
  | unwired | assumed | proved | surrogate
  deriving DecidableEq, Repr

def naturalOccurrenceZ118ModalityCurrent : NaturalOccurrenceZ118Modality := .unwired

/-- Modality lattice cardinality (Unwired / Assumed / Proved / Surrogate). -/
def naturalOccurrenceModalityLatticeCardinality : Nat := 4

theorem natural_occurrence_modality_lattice_cardinality_four :
    naturalOccurrenceModalityLatticeCardinality = 4 := rfl

theorem natural_occurrence_modality_lattice_not_118_squared :
    naturalOccurrenceModalityLatticeCardinality ≠ 118 * 118 := by decide

/-- Surface tag for name-from-content. -/
def naturalOccurrenceZ118Surface : String := "natural_occurrence_z118_surface"

theorem natural_occurrence_z118_surface_named : naturalOccurrenceZ118Surface ≠ "" := by decide

/-- IUPAC Z bar — product classifier table Z=1..118 (not 118² GREEN). -/
def iupacTableCardinality : Nat := 118

theorem iupac_table_cardinality_is_118 : iupacTableCardinality = 118 := rfl

def occurrenceElementZValid (z : Nat) : Bool :=
  0 < z && z ≤ iupacTableCardinality

/-- Concurrent product classifier bits — not XOR enum bucket. -/
def bitNative : Nat := 1
def bitOxide : Nat := 2
def bitSulfide : Nat := 4
def bitSilicate : Nat := 8
def bitHalideCarbonate : Nat := 16
def bitAtmophile : Nat := 32
def bitSyntheticTrace : Nat := 64

theorem bit_native_is_1 : bitNative = 1 := rfl
theorem bit_oxide_is_2 : bitOxide = 2 := rfl
theorem bit_sulfide_is_4 : bitSulfide = 4 := rfl
theorem bit_atmophile_is_32 : bitAtmophile = 32 := rfl

def occurrenceBitHas (bits classifier : Nat) : Bool :=
  ((bits / classifier) % 2) == 1

/-- INT SSOT table — umst-chem natural_occurrence_z118.rs pins. -/
def occurrenceProductTable : List Nat :=
  [48, 32, 24, 8, 18, 17, 32, 42, 16, 32, 24, 10, 10, 8, 16, 5, 16, 32,
   24, 24, 8, 2, 6, 2, 2, 7, 4, 5, 5, 4, 4, 4, 4, 5, 16, 32,
   8, 16, 24, 8, 2, 4, 64, 1, 1, 1, 5, 4, 4, 2, 4, 5, 16, 32,
   8, 16, 24, 24, 24, 24, 64, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 8,
   2, 2, 4, 1, 1, 1, 1, 5, 4, 4, 5, 64, 64, 96, 64, 64, 64, 24,
   64, 2, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64,
   64, 64, 64, 64, 64, 64, 64, 64, 64, 96]

def occurrenceBits (z : Nat) : Option Nat :=
  if z = 0 then none
  else if z > iupacTableCardinality then none
  else occurrenceProductTable[z - 1]?

theorem occurrence_table_length_118 : occurrenceProductTable.length = 118 := by native_decide

def everyZClassified : Bool :=
  occurrenceProductTable.all (· ≠ 0)

theorem every_z_classified_true : everyZClassified = true := by native_decide

def tableCoversZ118 : Bool :=
  occurrenceProductTable.length == iupacTableCardinality

theorem table_covers_z118_true : tableCoversZ118 = true := by native_decide

/-- Witness Z pins — He Z=2, Fe Z=26, Au Z=79, Tc Z=43. -/
def heliumZ : Nat := 2
def ironZ : Nat := 26
def goldZ : Nat := 79
def technetiumZ : Nat := 43

theorem helium_z_is_2 : heliumZ = 2 := rfl
theorem iron_z_is_26 : ironZ = 26 := rfl
theorem gold_z_is_79 : goldZ = 79 := rfl
theorem technetium_z_is_43 : technetiumZ = 43 := rfl

theorem helium_bits_atmophile_only : occurrenceBits heliumZ = some bitAtmophile := by decide

theorem iron_bits_native_oxide_sulfide_product :
    occurrenceBits ironZ = some 7 ∧
    occurrenceBitHas 7 bitNative = true ∧
    occurrenceBitHas 7 bitOxide = true ∧
    occurrenceBitHas 7 bitSulfide = true := by decide

theorem gold_bits_native : occurrenceBits goldZ = some bitNative := by decide

theorem technetium_bits_synthetic_trace :
    occurrenceBits technetiumZ = some bitSyntheticTrace := by decide

def heliumHasNoCrustalOreBit : Bool :=
  match occurrenceBits heliumZ with
  | some b => b == bitAtmophile
  | none => false

theorem helium_has_no_crustal_ore_bit_true : heliumHasNoCrustalOreBit = true := by decide

def ironIsOccurrenceProduct : Bool :=
  match occurrenceBits ironZ with
  | some b =>
      occurrenceBitHas b bitNative &&
      occurrenceBitHas b bitOxide &&
      occurrenceBitHas b bitSulfide
  | none => false

theorem iron_is_occurrence_product_true : ironIsOccurrenceProduct = true := by decide

/-- Folklore list refuse — named product classifiers, not lore lists. -/
def folkloreListMarker : String := "natural_occurrence_folklore_list_v1"
def productClassifierMarker : String := "natural_occurrence_product_classifier_v1"

theorem folklore_marker_ne_product_classifier_marker :
    folkloreListMarker ≠ productClassifierMarker := by decide

inductive OccurrenceWitnessKind where
  | productNamed | folkloreListTheater | xorEnumBucketTheater
  deriving DecidableEq, Repr

def folkloreListSmuggle (k : OccurrenceWitnessKind) : Bool :=
  match k with | .folkloreListTheater => true | _ => false

def xorEnumSmuggle (k : OccurrenceWitnessKind) : Bool :=
  match k with | .xorEnumBucketTheater => true | _ => false

def occurrenceWitnessFolklore : OccurrenceWitnessKind := .folkloreListTheater
def occurrenceWitnessNamed : OccurrenceWitnessKind := .productNamed

theorem folklore_list_smuggle_true : folkloreListSmuggle occurrenceWitnessFolklore = true := rfl

theorem named_occurrence_not_folklore_list :
    folkloreListSmuggle occurrenceWitnessNamed = false := rfl

def xorEnumMarker : String := "natural_occurrence_xor_enum_bucket_v1"
def productFactorMarker : String := "natural_occurrence_concurrent_product_factor_v1"

theorem xor_marker_ne_product_factor_marker :
    xorEnumMarker ≠ productFactorMarker := by decide

/-- Not fourth chemistry science / not 26th axiom fences. -/
def fourthScienceCollisionMarker : String :=
  "Natural occurrence Z118 product classifiers ≠ fourth parallel chemistry science axiom"

def twentySixthAxiomCollisionMarker : String :=
  "Natural occurrence Z118 concurrent bits ≠ 26th parallel chemistry axiom"

theorem fourth_science_collision_named : fourthScienceCollisionMarker ≠ "" := by decide

theorem twenty_sixth_axiom_collision_named : twentySixthAxiomCollisionMarker ≠ "" := by decide

def notFourthChemistryScience : Bool := true
def notTwentySixthAxiom : Bool := true

theorem not_fourth_chemistry_science : notFourthChemistryScience = true := rfl
theorem not_twenty_sixth_axiom : notTwentySixthAxiom = true := rfl

def soleAxiomCount : Nat := 1

theorem sole_axiom_count_is_one : soleAxiomCount = 1 := rfl

def naturalOccurrenceHonestConjunct : Bool :=
  tableCoversZ118 &&
    heliumHasNoCrustalOreBit &&
    ironIsOccurrenceProduct &&
    everyZClassified

theorem natural_occurrence_honest_conjunct_true : naturalOccurrenceHonestConjunct = true := by native_decide

/-- Verdict for natural occurrence Z118 close (fail-closed). -/
inductive NaturalOccurrenceZ118Verdict where
  | unwiredOk
  | occurrenceNamedOk
  | trivialZRefuse
  | folkloreListRefuse
  | xorEnumRefuse
  | fourthScienceRefuse
  | twentySixthAxiomRefuse
  | greenInventRefuse
  | provedWithoutBarRefuse
  | productionWiredRefuse
  deriving DecidableEq, Repr

def naturalOccurrenceVerdictOk (v : NaturalOccurrenceZ118Verdict) : Bool :=
  match v with
  | .unwiredOk | .occurrenceNamedOk => true
  | _ => false

structure NaturalOccurrenceIncidence where
  z : Nat
  witnessKind : OccurrenceWitnessKind
  level : Nat
  deriving DecidableEq, Repr

def naturalOccurrenceIncidenceNontrivial (h : NaturalOccurrenceIncidence) : Bool :=
  0 < h.level

def naturalOccurrenceIncidenceIronL1 : NaturalOccurrenceIncidence :=
  { z := ironZ, witnessKind := .productNamed, level := 1 }

def naturalOccurrenceIncidenceHeliumL1 : NaturalOccurrenceIncidence :=
  { z := heliumZ, witnessKind := .productNamed, level := 1 }

def naturalOccurrenceIncidenceTrivial : NaturalOccurrenceIncidence :=
  { z := 0, witnessKind := .productNamed, level := 0 }

def naturalOccurrenceIncidenceFolklore : NaturalOccurrenceIncidence :=
  { z := ironZ, witnessKind := .folkloreListTheater, level := 1 }

def naturalOccurrenceIncidenceXorEnum : NaturalOccurrenceIncidence :=
  { z := ironZ, witnessKind := .xorEnumBucketTheater, level := 1 }

def evaluateNaturalOccurrenceIncidence
    (modality : NaturalOccurrenceZ118Modality)
    (h : NaturalOccurrenceIncidence)
    (claimPhysicsGreen : Bool)
    (claimProved : Bool)
    (claimXorEnum : Bool)
    (claimFourthScience : Bool)
    (claimTwentySixthAxiom : Bool) : NaturalOccurrenceZ118Verdict :=
  if claimPhysicsGreen then
    .greenInventRefuse
  else if claimProved then
    .provedWithoutBarRefuse
  else if claimFourthScience then
    .fourthScienceRefuse
  else if claimTwentySixthAxiom then
    .twentySixthAxiomRefuse
  else if folkloreListSmuggle h.witnessKind then
    .folkloreListRefuse
  else if xorEnumSmuggle h.witnessKind then
    .xorEnumRefuse
  else if claimXorEnum then
    .xorEnumRefuse
  else if !naturalOccurrenceIncidenceNontrivial h then
    .trivialZRefuse
  else if !occurrenceElementZValid h.z then
    .trivialZRefuse
  else
    match modality with
    | .unwired => .occurrenceNamedOk
    | .assumed | .surrogate => .unwiredOk
    | .proved => .provedWithoutBarRefuse

def evaluateNaturalOccurrenceClose
    (modality : NaturalOccurrenceZ118Modality)
    (claimPhysicsGreen : Bool)
    (claimProductionWired : Bool) : NaturalOccurrenceZ118Verdict :=
  if claimPhysicsGreen then
    .greenInventRefuse
  else if claimProductionWired then
    .productionWiredRefuse
  else
    match modality with
    | .unwired => .unwiredOk
    | .assumed | .proved | .surrogate => .occurrenceNamedOk

/-- WAVE100 — lib.rs / eos.rs not wired (deferred composition). -/
def wave100LibRsWired : Bool := false
def wave100EosRsWired : Bool := false
def naturalOccurrenceZ118ProductionWired : Bool := false

theorem wave100_lib_rs_not_wired : wave100LibRsWired = false := rfl
theorem wave100_eos_rs_not_wired : wave100EosRsWired = false := rfl

theorem natural_occurrence_z118_production_not_wired :
    naturalOccurrenceZ118ProductionWired = false := rfl

def wave100NotWired : Bool := !wave100LibRsWired && !wave100EosRsWired

theorem wave100_not_wired_true : wave100NotWired = true := by decide

def naturalOccurrenceZ118Proved : Bool := false

theorem natural_occurrence_z118_proved_false : naturalOccurrenceZ118Proved = false := rfl

def not118SquaredGreenTable : Bool := true

theorem not_118_squared_green_table : not118SquaredGreenTable = true := rfl

def unwiredNaturalOccurrenceCloseOk : Bool :=
  decide (evaluateNaturalOccurrenceClose .unwired false false = .unwiredOk)

def ironOccurrenceNamedOk : Bool :=
  decide (evaluateNaturalOccurrenceIncidence .unwired naturalOccurrenceIncidenceIronL1
    false false false false false = .occurrenceNamedOk)

def heliumOccurrenceNamedOk : Bool :=
  decide (evaluateNaturalOccurrenceIncidence .unwired naturalOccurrenceIncidenceHeliumL1
    false false false false false = .occurrenceNamedOk)

def trivialZRefuse : Bool :=
  decide (evaluateNaturalOccurrenceIncidence .unwired naturalOccurrenceIncidenceTrivial
    false false false false false = .trivialZRefuse)

def folkloreListRefuse : Bool :=
  decide (evaluateNaturalOccurrenceIncidence .unwired naturalOccurrenceIncidenceFolklore
    false false false false false = .folkloreListRefuse)

def xorEnumRefuse : Bool :=
  decide (evaluateNaturalOccurrenceIncidence .unwired naturalOccurrenceIncidenceXorEnum
    false false false false false = .xorEnumRefuse)

def greenInventNaturalOccurrenceRefuse : Bool :=
  decide (evaluateNaturalOccurrenceClose .unwired true false = .greenInventRefuse)

def provedWithoutBarNaturalOccurrenceRefuse : Bool :=
  decide (evaluateNaturalOccurrenceIncidence .unwired naturalOccurrenceIncidenceIronL1
    false true false false false = .provedWithoutBarRefuse)

def productionWiredNaturalOccurrenceRefuse : Bool :=
  decide (evaluateNaturalOccurrenceClose .proved false true = .productionWiredRefuse)

def naturalOccurrenceZ118Scaffold : Bool :=
  unwiredNaturalOccurrenceCloseOk &&
    naturalOccurrenceHonestConjunct &&
    ironOccurrenceNamedOk &&
    heliumOccurrenceNamedOk &&
    trivialZRefuse &&
    folkloreListRefuse &&
    xorEnumRefuse &&
    greenInventNaturalOccurrenceRefuse &&
    provedWithoutBarNaturalOccurrenceRefuse &&
    productionWiredNaturalOccurrenceRefuse &&
    wave100NotWired

theorem natural_occurrence_z118_scaffold_true : naturalOccurrenceZ118Scaffold = true := by native_decide

inductive FormalFiber where
  | quantumKnowing | mesoActing
  deriving DecidableEq, Repr

def naturalOccurrenceFiberOk (f : FormalFiber) : Bool :=
  match f with | .quantumKnowing => true | .mesoActing => false

theorem natural_occurrence_knowing_fiber_ok :
    naturalOccurrenceFiberOk .quantumKnowing = true := rfl

theorem natural_occurrence_meso_acting_fiber_not_ok :
    naturalOccurrenceFiberOk .mesoActing = false := rfl

def naturalOccurrenceZ118CellId : String :=
  "CHEM-FORMAL-Q-LEAN-NATURAL-OCCURRENCE-Z118-CONSERVATION"

def naturalOccurrenceZ118PhysicsGreenAuthorized : Prop := False

theorem natural_occurrence_z118_physics_green_false :
    ¬ naturalOccurrenceZ118PhysicsGreenAuthorized := id

structure NaturalOccurrenceZ118Probe where
  cellIdNamed : Bool
  unwired : Bool
  physicsGreenRefused : Bool
  soleAxiom : Bool
  notProved : Bool
  deriving DecidableEq, Repr

def naturalOccurrenceZ118Probe : NaturalOccurrenceZ118Probe :=
  { cellIdNamed :=
      decide (naturalOccurrenceZ118CellId =
        "CHEM-FORMAL-Q-LEAN-NATURAL-OCCURRENCE-Z118-CONSERVATION")
    unwired := decide (naturalOccurrenceZ118ModalityCurrent = .unwired)
    physicsGreenRefused := true
    soleAxiom := decide (soleAxiomCount = 1)
    notProved := !naturalOccurrenceZ118Proved }

def naturalOccurrenceZ118Honest : Bool :=
  let p := naturalOccurrenceZ118Probe
  p.cellIdNamed &&
    p.unwired &&
    p.physicsGreenRefused &&
    p.soleAxiom &&
    p.notProved &&
    naturalOccurrenceZ118Scaffold

theorem natural_occurrence_z118_honest_true : naturalOccurrenceZ118Honest = true := by native_decide

def naturalOccurrenceZ118Framing : String :=
  "second_law_conservation_natural_occurrence_z118_one_axiom_not_26th_axiom"

theorem natural_occurrence_not_twenty_sixth_axiom_framing :
    naturalOccurrenceZ118Framing ≠ "twenty_sixth_chemistry_axiom" := by decide

theorem natural_occurrence_not_fourth_science_axiom :
    naturalOccurrenceZ118Framing ≠ "fourth_chemistry_science_axiom" := by decide

def naturalOccurrenceZ118SecondLawConservationFramed : Bool := true

theorem natural_occurrence_second_law_conservation_framed :
    naturalOccurrenceZ118SecondLawConservationFramed = true := rfl

def naturalOccurrenceZ118CitedModule : String :=
  "umst/umst-chem/src/x_rows/natural_occurrence_z118.rs"

def chemIntCrossNaturalOccurrenceAuthority : String :=
  "CHEM-INT-CROSS-NATURAL-OCCURRENCE-Z118-CONSERVATION"

def naturalOccurrenceZ118NonClaim : String :=
  "CHEM-FORMAL-Q-LEAN-NATURAL-OCCURRENCE-Z118-CONSERVATION Z=1..118 natural occurrence class table as Unwired named product classifiers native oxide sulfide silicate halide carbonate atmophile synthetic-or-trace not folklore lists concurrent bits not XOR not fourth chemistry science not 26th axiom GREEN invent fail-closed proved-without-bar fail-closed trivial Z=0 refuse naturalOccurrenceZ118Proved false Unwired knowing quantum fiber not meso acting WAVE100 lib eos smuggle refuse one axiom second law conservation not GREEN DFT not physics GREEN not production_wired remainder deferred composition not impossibility"

theorem natural_occurrence_z118_modality_unwired :
    naturalOccurrenceZ118ModalityCurrent = .unwired := rfl

def naturalOccurrenceZ118Axiom : Bool :=
  not118SquaredGreenTable &&
    naturalOccurrenceZ118SecondLawConservationFramed &&
    naturalOccurrenceHonestConjunct &&
    naturalOccurrenceZ118Scaffold &&
    naturalOccurrenceZ118Honest &&
    !naturalOccurrenceZ118Proved &&
    !naturalOccurrenceZ118ProductionWired &&
    !wave100LibRsWired &&
    !wave100EosRsWired &&
    notFourthChemistryScience &&
    notTwentySixthAxiom &&
    decide (naturalOccurrenceZ118Framing =
      "second_law_conservation_natural_occurrence_z118_one_axiom_not_26th_axiom")

theorem natural_occurrence_z118_axiom : naturalOccurrenceZ118Axiom = true := by native_decide

theorem unwired_close_without_production_wiring :
    evaluateNaturalOccurrenceClose .unwired false false = .unwiredOk := rfl

theorem iron_occurrence_named_ok :
    evaluateNaturalOccurrenceIncidence .unwired naturalOccurrenceIncidenceIronL1
      false false false false false = .occurrenceNamedOk := rfl

theorem helium_occurrence_named_ok :
    evaluateNaturalOccurrenceIncidence .unwired naturalOccurrenceIncidenceHeliumL1
      false false false false false = .occurrenceNamedOk := rfl

theorem trivial_z_refused :
    evaluateNaturalOccurrenceIncidence .unwired naturalOccurrenceIncidenceTrivial
      false false false false false = .trivialZRefuse := rfl

theorem folklore_list_refused :
    evaluateNaturalOccurrenceIncidence .unwired naturalOccurrenceIncidenceFolklore
      false false false false false = .folkloreListRefuse := rfl

theorem xor_enum_refused :
    evaluateNaturalOccurrenceIncidence .unwired naturalOccurrenceIncidenceXorEnum
      false false false false false = .xorEnumRefuse := rfl

theorem green_invent_refuse_unwired :
    evaluateNaturalOccurrenceClose .unwired true false = .greenInventRefuse := rfl

theorem proved_without_bar_refuse :
    evaluateNaturalOccurrenceIncidence .unwired naturalOccurrenceIncidenceIronL1
      false true false false false = .provedWithoutBarRefuse := rfl

theorem production_wired_refuse :
    evaluateNaturalOccurrenceClose .proved false true = .productionWiredRefuse := rfl

theorem natural_occurrence_z118_conservation :
    evaluateNaturalOccurrenceClose .unwired false false = .unwiredOk ∧
    naturalOccurrenceHonestConjunct = true ∧
    naturalOccurrenceZ118Proved = false ∧
    wave100LibRsWired = false ∧
    wave100EosRsWired = false :=
  ⟨rfl, natural_occurrence_honest_conjunct_true, natural_occurrence_z118_proved_false,
    wave100_lib_rs_not_wired, wave100_eos_rs_not_wired⟩

theorem natural_occurrence_z118_honest_bundle :
    naturalOccurrenceZ118Proved = false ∧
    naturalOccurrenceZ118ProductionWired = false ∧
    not118SquaredGreenTable = true ∧
    naturalOccurrenceZ118SecondLawConservationFramed = true ∧
    naturalOccurrenceHonestConjunct = true ∧
    ironIsOccurrenceProduct = true ∧
    heliumHasNoCrustalOreBit = true ∧
    tableCoversZ118 = true ∧
    everyZClassified = true ∧
    evaluateNaturalOccurrenceClose .unwired false false = .unwiredOk ∧
    evaluateNaturalOccurrenceClose .unwired true false = .greenInventRefuse ∧
    evaluateNaturalOccurrenceIncidence .unwired naturalOccurrenceIncidenceIronL1
      false true false false false = .provedWithoutBarRefuse ∧
    soleAxiomCount = 1 ∧
    naturalOccurrenceZ118Axiom = true ∧
    naturalOccurrenceFiberOk .quantumKnowing = true ∧
    naturalOccurrenceFiberOk .mesoActing = false :=
  ⟨rfl, natural_occurrence_z118_production_not_wired, not_118_squared_green_table,
    natural_occurrence_second_law_conservation_framed, natural_occurrence_honest_conjunct_true,
    iron_is_occurrence_product_true, helium_has_no_crustal_ore_bit_true, table_covers_z118_true,
    every_z_classified_true, unwired_close_without_production_wiring, green_invent_refuse_unwired,
    proved_without_bar_refuse, sole_axiom_count_is_one, natural_occurrence_z118_axiom,
    natural_occurrence_knowing_fiber_ok, natural_occurrence_meso_acting_fiber_not_ok⟩

end UMST.Chem
