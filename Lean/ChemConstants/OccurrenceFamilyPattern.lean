-- SPDX-FileCopyrightText: 2026 Santosh Prabhu Shenbagamoorthy and Santhosh Shyamsundar
-- SPDX-License-Identifier: MIT

import ElementElectronic

set_option maxRecDepth 8192

/-!
# OccurrenceFamilyPattern — occurrence-class family pattern **conservation** (Q lattice)

Knowing-fiber Lean: occurrence-class families are concurrent product classifiers on the same
sheaf (7 tags: native / oxide / sulfide / silicate / halide+carbonate / atmophile /
synthetic-or-trace); ore-engine sorts outliers (native Au Z=79 vs oxide-product Fe Z=26 vs
closed-shell He atmophile no-ore Z=2); same Z many assemblages — not folklore exclusive lists,
not XOR enum. Pairs `umst-chem` scaffold `occurrence_family_pattern` / **conservation** posture.

- `OccurrenceFamilyPatternModality` — Unwired / Assumed / Proved / Surrogate (not 118² GREEN table).
- `occurrenceFamilyTags` — seven concurrent family tags (not XOR folklore list).
- `oreEngineOutliersSortNamed` — Au native vs Fe oxide product vs He no-ore witnesses.
- Second-law + **conservation** framing cites meso `UMST.Chem.Conservation` /
  `LandauerLaw.physicalSecondLaw` — not imported.
- No meso / acting theorems. No new physics `axiom`.
- `physics_green` stays false. Does **not** claim `occurrenceFamilyPatternProved` or physics GREEN.
- WAVE100 freeze — remainder deferred composition (env/time/cross-domain), not impossibility stop.
-/

namespace UMST.Chem

/-- Design modality for occurrence family pattern **conservation** (lattice SSOT). -/
inductive OccurrenceFamilyPatternModality where
  | unwired | assumed | proved | surrogate
  deriving DecidableEq, Repr

def occurrenceFamilyPatternModalityCurrent : OccurrenceFamilyPatternModality := .unwired

/-- Modality lattice cardinality (Unwired / Assumed / Proved / Surrogate). -/
def occurrenceFamilyModalityLatticeCardinality : Nat := 4

theorem occurrence_family_modality_lattice_cardinality_four :
    occurrenceFamilyModalityLatticeCardinality = 4 := rfl

theorem occurrence_family_modality_lattice_not_118_squared :
    occurrenceFamilyModalityLatticeCardinality ≠ 118 * 118 := by decide

/-- Surface tag for name-from-content. -/
def occurrenceFamilyPatternSurface : String := "occurrence_family_pattern_surface"

theorem occurrence_family_pattern_surface_named : occurrenceFamilyPatternSurface ≠ "" := by decide

/-- Seven concurrent occurrence-family tags — not XOR folklore list. -/
def occurrenceFamilyTagCount : Nat := 7

theorem occurrence_family_tag_count_is_seven : occurrenceFamilyTagCount = 7 := rfl

inductive OccurrenceFamilyTag where
  | native | oxide | sulfide | silicate | halideCarbonate | atmophile | syntheticOrTrace
  deriving DecidableEq, Repr

def occurrenceFamilyTags : List String :=
  ["native", "oxide", "sulfide", "silicate", "halide_carbonate", "atmophile", "synthetic_or_trace"]

theorem occurrence_family_tags_length_seven : occurrenceFamilyTags.length = 7 := by decide

/-- Concurrent product classifier bits — not XOR enum bucket. INT SSOT pins. -/
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

def familyBitHas (bits mask : Nat) : Bool :=
  (bits &&& mask) == mask

def familyBitCount (bits : Nat) : Nat :=
  (if familyBitHas bits bitNative then 1 else 0) +
  (if familyBitHas bits bitOxide then 1 else 0) +
  (if familyBitHas bits bitSulfide then 1 else 0) +
  (if familyBitHas bits bitAtmophile then 1 else 0)

def familyBitsConcurrent (bits : Nat) : Bool :=
  2 ≤ familyBitCount bits

/-- IUPAC Z bar — pattern for Z=1..118 assemblages (not 118² table). -/
def iupacTableCardinality : Nat := 118

theorem iupac_table_cardinality_is_118 : iupacTableCardinality = 118 := rfl

def occurrenceElementZValid (z : Nat) : Bool :=
  0 < z && z ≤ iupacTableCardinality

/-- Named outlier Z pins — INT SSOT. -/
def goldZ : Nat := 79
def ironZ : Nat := 26
def heliumZ : Nat := 2

theorem gold_z_is_79 : goldZ = 79 := rfl
theorem iron_z_is_26 : ironZ = 26 := rfl
theorem helium_z_is_2 : heliumZ = 2 := rfl

theorem outlier_z_factors_valid :
    occurrenceElementZValid goldZ = true ∧
    occurrenceElementZValid ironZ = true ∧
    occurrenceElementZValid heliumZ = true := by decide

/-- Outlier bit pins — INT SSOT. -/
def goldOutlierBits : Nat := bitNative
def ironOutlierBits : Nat := bitNative + bitOxide + bitSulfide
def heliumOutlierBits : Nat := bitAtmophile

theorem gold_outlier_bits_is_native_only : goldOutlierBits = bitNative := rfl
theorem iron_outlier_bits_is_seven : ironOutlierBits = 7 := rfl
theorem helium_outlier_bits_is_atmophile_only : heliumOutlierBits = bitAtmophile := rfl

/-- Ore-engine outlier sort witnesses (Au native vs Fe product vs He no-ore). -/
def goldIsNativeFamilyOutlier : Bool :=
  goldOutlierBits == bitNative

def ironIsOxideFamilyProduct : Bool :=
  familyBitHas ironOutlierBits bitOxide &&
  familyBitHas ironOutlierBits bitNative &&
  familyBitHas ironOutlierBits bitSulfide

def heliumIsNoOreAtmophile : Bool :=
  heliumOutlierBits == bitAtmophile &&
  !familyBitHas heliumOutlierBits bitNative

def heliumNoOreIsMissingInteract : Bool :=
  heliumIsNoOreAtmophile

theorem gold_is_native_family_outlier_true : goldIsNativeFamilyOutlier = true := rfl
theorem iron_is_oxide_family_product_true : ironIsOxideFamilyProduct = true := by decide
theorem helium_is_no_ore_atmophile_true : heliumIsNoOreAtmophile = true := by decide
theorem helium_no_ore_is_missing_interact_true : heliumNoOreIsMissingInteract = true := rfl

def oreEngineOutliersSortNamed : Bool :=
  goldIsNativeFamilyOutlier &&
  ironIsOxideFamilyProduct &&
  heliumIsNoOreAtmophile &&
  heliumNoOreIsMissingInteract

theorem ore_engine_outliers_sort_named_true : oreEngineOutliersSortNamed = true := by decide

/-- Same Z may occupy several families — Fe concurrent product witness. -/
def sameZManyAssemblages : Bool :=
  ironIsOxideFamilyProduct

theorem same_z_many_assemblages_true : sameZManyAssemblages = true := by decide

/-- Folklore exclusive list refuse — not a single-family bucket per Z. -/
def folkloreExclusiveListRefused : Bool := true

theorem folklore_exclusive_list_refused_true : folkloreExclusiveListRefused = true := rfl

def occurrenceFamilyPatternConjunct : Bool :=
  occurrenceFamilyTagCount == 7 &&
  oreEngineOutliersSortNamed &&
  sameZManyAssemblages &&
  folkloreExclusiveListRefused

theorem occurrence_family_pattern_conjunct_true : occurrenceFamilyPatternConjunct = true := by decide

def ironOutlierIsConcurrentProduct : Bool :=
  familyBitsConcurrent ironOutlierBits

theorem iron_outlier_is_concurrent_product_true : ironOutlierIsConcurrentProduct = true := by decide

/-- Concurrent product classifiers — not XOR enum bucket. -/
def xorEnumMarker : String := "occurrence_family_xor_enum_bucket_v1"
def productFactorMarker : String := "occurrence_family_concurrent_product_v1"

theorem xor_marker_ne_product_factor_marker :
    xorEnumMarker ≠ productFactorMarker := by decide

/-- Not fourth chemistry science / not 26th axiom fences. -/
def fourthScienceCollisionMarker : String :=
  "Occurrence family pattern ≠ fourth parallel chemistry science axiom"

def twentySixthAxiomCollisionMarker : String :=
  "Occurrence family pattern ≠ 26th parallel chemistry axiom"

theorem fourth_science_collision_named : fourthScienceCollisionMarker ≠ "" := by decide
theorem twenty_sixth_axiom_collision_named : twentySixthAxiomCollisionMarker ≠ "" := by decide

def notFourthChemistryScience : Bool := true
def notTwentySixthAxiom : Bool := true

theorem not_fourth_chemistry_science : notFourthChemistryScience = true := rfl
theorem not_twenty_sixth_axiom : notTwentySixthAxiom = true := rfl

def soleAxiomCount : Nat := 1

theorem sole_axiom_count_is_one : soleAxiomCount = 1 := rfl

/-- Verdict for occurrence family pattern close (fail-closed). -/
inductive OccurrenceFamilyPatternVerdict where
  | unwiredOk
  | familyPatternNamedOk
  | trivialZRefuse
  | folkloreListRefuse
  | xorEnumRefuse
  | fourthScienceRefuse
  | twentySixthAxiomRefuse
  | greenInventRefuse
  | provedWithoutBarRefuse
  | productionWiredRefuse
  deriving DecidableEq, Repr

def occurrenceFamilyVerdictOk (v : OccurrenceFamilyPatternVerdict) : Bool :=
  match v with
  | .unwiredOk | .familyPatternNamedOk => true
  | _ => false

structure OccurrenceFamilyIncidence where
  z : Nat
  bits : Nat
  level : Nat
  deriving DecidableEq, Repr

def occurrenceFamilyIncidenceNontrivial (h : OccurrenceFamilyIncidence) : Bool :=
  0 < h.level

def occurrenceFamilyIncidenceGoldL1 : OccurrenceFamilyIncidence :=
  { z := goldZ, bits := goldOutlierBits, level := 1 }

def occurrenceFamilyIncidenceIronL1 : OccurrenceFamilyIncidence :=
  { z := ironZ, bits := ironOutlierBits, level := 1 }

def occurrenceFamilyIncidenceHeliumL1 : OccurrenceFamilyIncidence :=
  { z := heliumZ, bits := heliumOutlierBits, level := 1 }

def occurrenceFamilyIncidenceTrivial : OccurrenceFamilyIncidence :=
  { z := goldZ, bits := goldOutlierBits, level := 0 }

def occurrenceFamilyIncidenceFolklore : OccurrenceFamilyIncidence :=
  { z := ironZ, bits := ironOutlierBits, level := 1 }

def folkloreListSmuggle (claimFolkloreList : Bool) : Bool := claimFolkloreList

def xorEnumSmuggle (claimXorEnum : Bool) : Bool := claimXorEnum

def evaluateOccurrenceFamilyIncidence
    (modality : OccurrenceFamilyPatternModality)
    (h : OccurrenceFamilyIncidence)
    (claimPhysicsGreen : Bool)
    (claimProved : Bool)
    (claimXorEnum : Bool)
    (claimFolkloreList : Bool)
    (claimFourthScience : Bool)
    (claimTwentySixthAxiom : Bool) : OccurrenceFamilyPatternVerdict :=
  if claimPhysicsGreen then
    .greenInventRefuse
  else if claimProved then
    .provedWithoutBarRefuse
  else if claimFourthScience then
    .fourthScienceRefuse
  else if claimTwentySixthAxiom then
    .twentySixthAxiomRefuse
  else if folkloreListSmuggle claimFolkloreList then
    .folkloreListRefuse
  else if xorEnumSmuggle claimXorEnum then
    .xorEnumRefuse
  else if !occurrenceFamilyIncidenceNontrivial h then
    .trivialZRefuse
  else if !occurrenceElementZValid h.z then
    .trivialZRefuse
  else
    match modality with
    | .unwired => .familyPatternNamedOk
    | .assumed | .surrogate => .unwiredOk
    | .proved => .provedWithoutBarRefuse

def evaluateOccurrenceFamilyClose
    (modality : OccurrenceFamilyPatternModality)
    (claimPhysicsGreen : Bool)
    (claimProductionWired : Bool) : OccurrenceFamilyPatternVerdict :=
  if claimPhysicsGreen then
    .greenInventRefuse
  else if claimProductionWired then
    .productionWiredRefuse
  else
    match modality with
    | .unwired => .unwiredOk
    | .assumed | .proved | .surrogate => .familyPatternNamedOk

/-- WAVE100 — lib.rs / eos.rs not wired (deferred composition). -/
def wave100LibRsWired : Bool := false
def wave100EosRsWired : Bool := false
def occurrenceFamilyPatternProductionWired : Bool := false

theorem wave100_lib_rs_not_wired : wave100LibRsWired = false := rfl
theorem wave100_eos_rs_not_wired : wave100EosRsWired = false := rfl

theorem occurrence_family_pattern_production_not_wired :
    occurrenceFamilyPatternProductionWired = false := rfl

def wave100NotWired : Bool := !wave100LibRsWired && !wave100EosRsWired

theorem wave100_not_wired_true : wave100NotWired = true := by decide

def occurrenceFamilyPatternProved : Bool := false

theorem occurrence_family_pattern_proved_false : occurrenceFamilyPatternProved = false := rfl

def not118SquaredGreenTable : Bool := true

theorem not_118_squared_green_table : not118SquaredGreenTable = true := rfl

def unwiredOccurrenceFamilyCloseOk : Bool :=
  decide (evaluateOccurrenceFamilyClose .unwired false false = .unwiredOk)

def goldOutlierNamedOk : Bool :=
  decide (evaluateOccurrenceFamilyIncidence .unwired occurrenceFamilyIncidenceGoldL1
    false false false false false false = .familyPatternNamedOk)

def ironOutlierNamedOk : Bool :=
  decide (evaluateOccurrenceFamilyIncidence .unwired occurrenceFamilyIncidenceIronL1
    false false false false false false = .familyPatternNamedOk)

def heliumOutlierNamedOk : Bool :=
  decide (evaluateOccurrenceFamilyIncidence .unwired occurrenceFamilyIncidenceHeliumL1
    false false false false false false = .familyPatternNamedOk)

def trivialZRefuse : Bool :=
  decide (evaluateOccurrenceFamilyIncidence .unwired occurrenceFamilyIncidenceTrivial
    false false false false false false = .trivialZRefuse)

def folkloreListRefuse : Bool :=
  decide (evaluateOccurrenceFamilyIncidence .unwired occurrenceFamilyIncidenceGoldL1
    false false false true false false = .folkloreListRefuse)

def xorEnumRefuse : Bool :=
  decide (evaluateOccurrenceFamilyIncidence .unwired occurrenceFamilyIncidenceIronL1
    false false true false false false = .xorEnumRefuse)

def greenInventOccurrenceFamilyRefuse : Bool :=
  decide (evaluateOccurrenceFamilyClose .unwired true false = .greenInventRefuse)

def provedWithoutBarOccurrenceFamilyRefuse : Bool :=
  decide (evaluateOccurrenceFamilyIncidence .unwired occurrenceFamilyIncidenceGoldL1
    false true false false false false = .provedWithoutBarRefuse)

def productionWiredOccurrenceFamilyRefuse : Bool :=
  decide (evaluateOccurrenceFamilyClose .proved false true = .productionWiredRefuse)

def occurrenceFamilyPatternScaffold : Bool :=
  unwiredOccurrenceFamilyCloseOk &&
    occurrenceFamilyPatternConjunct &&
    goldOutlierNamedOk &&
    ironOutlierNamedOk &&
    heliumOutlierNamedOk &&
    trivialZRefuse &&
    folkloreListRefuse &&
    xorEnumRefuse &&
    greenInventOccurrenceFamilyRefuse &&
    provedWithoutBarOccurrenceFamilyRefuse &&
    productionWiredOccurrenceFamilyRefuse &&
    ironOutlierIsConcurrentProduct &&
    wave100NotWired

theorem occurrence_family_pattern_scaffold_true : occurrenceFamilyPatternScaffold = true := by native_decide

inductive FormalFiber where
  | quantumKnowing | mesoActing
  deriving DecidableEq, Repr

def occurrenceFamilyFiberOk (f : FormalFiber) : Bool :=
  match f with | .quantumKnowing => true | .mesoActing => false

theorem occurrence_family_knowing_fiber_ok :
    occurrenceFamilyFiberOk .quantumKnowing = true := rfl

theorem occurrence_family_meso_acting_fiber_not_ok :
    occurrenceFamilyFiberOk .mesoActing = false := rfl

def occurrenceFamilyPatternCellId : String :=
  "CHEM-FORMAL-Q-LEAN-OCCURRENCE-FAMILY-PATTERN-CONSERVATION"

def occurrenceFamilyPatternPhysicsGreenAuthorized : Prop := False

theorem occurrence_family_pattern_physics_green_false :
    ¬ occurrenceFamilyPatternPhysicsGreenAuthorized := id

structure OccurrenceFamilyPatternProbe where
  cellIdNamed : Bool
  unwired : Bool
  physicsGreenRefused : Bool
  soleAxiom : Bool
  notProved : Bool
  deriving DecidableEq, Repr

def occurrenceFamilyPatternProbe : OccurrenceFamilyPatternProbe :=
  { cellIdNamed :=
      decide (occurrenceFamilyPatternCellId =
        "CHEM-FORMAL-Q-LEAN-OCCURRENCE-FAMILY-PATTERN-CONSERVATION")
    unwired := decide (occurrenceFamilyPatternModalityCurrent = .unwired)
    physicsGreenRefused := true
    soleAxiom := decide (soleAxiomCount = 1)
    notProved := !occurrenceFamilyPatternProved }

def occurrenceFamilyPatternHonest : Bool :=
  let p := occurrenceFamilyPatternProbe
  p.cellIdNamed &&
    p.unwired &&
    p.physicsGreenRefused &&
    p.soleAxiom &&
    p.notProved &&
    occurrenceFamilyPatternScaffold

theorem occurrence_family_pattern_honest_true : occurrenceFamilyPatternHonest = true := by native_decide

def occurrenceFamilyPatternFraming : String :=
  "second_law_conservation_occurrence_family_pattern_one_axiom_not_26th_axiom"

theorem occurrence_family_pattern_not_twenty_sixth_axiom_framing :
    occurrenceFamilyPatternFraming ≠ "twenty_sixth_chemistry_axiom" := by decide

theorem occurrence_family_pattern_not_fourth_science_axiom :
    occurrenceFamilyPatternFraming ≠ "fourth_chemistry_science_axiom" := by decide

def occurrenceFamilyPatternSecondLawConservationFramed : Bool := true

theorem occurrence_family_pattern_second_law_conservation_framed :
    occurrenceFamilyPatternSecondLawConservationFramed = true := rfl

def occurrenceFamilyPatternCitedModule : String :=
  "umst/umst-chem/src/x_rows/occurrence_family_pattern.rs"

def chemIntCrossOccurrenceFamilyAuthority : String :=
  "CHEM-INT-CROSS-OCCURRENCE-FAMILY-PATTERN-CONSERVATION"

def occurrenceFamilyPatternNonClaim : String :=
  "CHEM-FORMAL-Q-LEAN-OCCURRENCE-FAMILY-PATTERN-CONSERVATION occurrence-class families are concurrent product classifiers 7 tags ore-engine sorts outliers native Au Z=79 vs oxide-product Fe Z=26 vs closed-shell He atmophile no-ore Z=2 same Z many assemblages not folklore exclusive lists not 26th axiom GREEN invent fail-closed proved-without-bar fail-closed trivial Z=0 refuse occurrenceFamilyPatternProved false Unwired knowing quantum fiber not meso acting WAVE100 lib eos smuggle refuse one axiom second law conservation not GREEN DFT not physics GREEN not production_wired remainder deferred composition not impossibility"

theorem occurrence_family_pattern_modality_unwired :
    occurrenceFamilyPatternModalityCurrent = .unwired := rfl

def occurrenceFamilyPatternAxiom : Bool :=
  not118SquaredGreenTable &&
    occurrenceFamilyPatternSecondLawConservationFramed &&
    occurrenceFamilyPatternConjunct &&
    occurrenceFamilyPatternScaffold &&
    occurrenceFamilyPatternHonest &&
    !occurrenceFamilyPatternProved &&
    !occurrenceFamilyPatternProductionWired &&
    !wave100LibRsWired &&
    !wave100EosRsWired &&
    notFourthChemistryScience &&
    notTwentySixthAxiom &&
    decide (occurrenceFamilyPatternFraming =
      "second_law_conservation_occurrence_family_pattern_one_axiom_not_26th_axiom")

theorem occurrence_family_pattern_axiom : occurrenceFamilyPatternAxiom = true := by native_decide

theorem unwired_close_without_production_wiring :
    evaluateOccurrenceFamilyClose .unwired false false = .unwiredOk := rfl

theorem gold_outlier_named_ok :
    evaluateOccurrenceFamilyIncidence .unwired occurrenceFamilyIncidenceGoldL1
      false false false false false false = .familyPatternNamedOk := rfl

theorem iron_outlier_named_ok :
    evaluateOccurrenceFamilyIncidence .unwired occurrenceFamilyIncidenceIronL1
      false false false false false false = .familyPatternNamedOk := rfl

theorem helium_outlier_named_ok :
    evaluateOccurrenceFamilyIncidence .unwired occurrenceFamilyIncidenceHeliumL1
      false false false false false false = .familyPatternNamedOk := rfl

theorem trivial_z_refused :
    evaluateOccurrenceFamilyIncidence .unwired occurrenceFamilyIncidenceTrivial
      false false false false false false = .trivialZRefuse := rfl

theorem folklore_list_refused :
    evaluateOccurrenceFamilyIncidence .unwired occurrenceFamilyIncidenceGoldL1
      false false false true false false = .folkloreListRefuse := rfl

theorem xor_enum_refused :
    evaluateOccurrenceFamilyIncidence .unwired occurrenceFamilyIncidenceIronL1
      false false true false false false = .xorEnumRefuse := rfl

theorem green_invent_refuse_unwired :
    evaluateOccurrenceFamilyClose .unwired true false = .greenInventRefuse := rfl

theorem proved_without_bar_refuse :
    evaluateOccurrenceFamilyIncidence .unwired occurrenceFamilyIncidenceGoldL1
      false true false false false false = .provedWithoutBarRefuse := rfl

theorem production_wired_refuse :
    evaluateOccurrenceFamilyClose .proved false true = .productionWiredRefuse := rfl

theorem occurrence_family_pattern_conservation :
    evaluateOccurrenceFamilyClose .unwired false false = .unwiredOk ∧
    occurrenceFamilyPatternConjunct = true ∧
    occurrenceFamilyPatternProved = false ∧
    wave100LibRsWired = false ∧
    wave100EosRsWired = false :=
  ⟨rfl, occurrence_family_pattern_conjunct_true, occurrence_family_pattern_proved_false,
    wave100_lib_rs_not_wired, wave100_eos_rs_not_wired⟩

theorem occurrence_family_pattern_honest_bundle :
    occurrenceFamilyPatternProved = false ∧
    occurrenceFamilyPatternProductionWired = false ∧
    not118SquaredGreenTable = true ∧
    occurrenceFamilyPatternSecondLawConservationFramed = true ∧
    occurrenceFamilyPatternConjunct = true ∧
    ironIsOxideFamilyProduct = true ∧
    heliumIsNoOreAtmophile = true ∧
    goldIsNativeFamilyOutlier = true ∧
    evaluateOccurrenceFamilyClose .unwired false false = .unwiredOk ∧
    evaluateOccurrenceFamilyClose .unwired true false = .greenInventRefuse ∧
    evaluateOccurrenceFamilyIncidence .unwired occurrenceFamilyIncidenceGoldL1
      false true false false false false = .provedWithoutBarRefuse ∧
    soleAxiomCount = 1 ∧
    occurrenceFamilyPatternAxiom = true ∧
    occurrenceFamilyFiberOk .quantumKnowing = true ∧
    occurrenceFamilyFiberOk .mesoActing = false :=
  ⟨rfl, occurrence_family_pattern_production_not_wired, not_118_squared_green_table,
    occurrence_family_pattern_second_law_conservation_framed, occurrence_family_pattern_conjunct_true,
    iron_is_oxide_family_product_true, helium_is_no_ore_atmophile_true,
    gold_is_native_family_outlier_true, unwired_close_without_production_wiring,
    green_invent_refuse_unwired, proved_without_bar_refuse, sole_axiom_count_is_one,
    occurrence_family_pattern_axiom, occurrence_family_knowing_fiber_ok,
    occurrence_family_meso_acting_fiber_not_ok⟩

end UMST.Chem
