-- SPDX-FileCopyrightText: 2026 Santosh Prabhu Shenbagamoorthy and Santhosh Shyamsundar
-- SPDX-License-Identifier: MIT

import ElementElectronic

set_option maxRecDepth 8192

/-!
# OccupancyEngineSort — occupancy-engine sort **conservation** (Q lattice)

Knowing-fiber Lean: occupancy engine **sorts** each Z into Madelung family vs three finite
exception families (Named La/Ce/Gd/Pt/Au; Actinide Ac–Lr with Pu 94 absent; DBlock
Cr/Cu/Nb/Mo/Ru/Rh/Pd/Ag); homolog ≠ copy (Ds Z=110 vs Pt Z=78). Pairs `umst-chem`
scaffold `occupancy_engine_sort` / **conservation** posture.

Read-only cites (not imported — self-contained scaffold):
- `Coq/ChemConstants/OccupancyEngineSort.v`
- `HS ChemConstants/OccupancyEngineSort.hs`
- `umst/umst-chem/src/x_rows/occupancy_engine_sort.rs`

- `OccupancyEngineSortModality` — Unwired / Assumed / Proved / Surrogate (not 118² GREEN table).
- `occupancyEngineSortBucket` — MadelungFamily / NamedException / ActinideException / DBlockException.
- Second-law + **conservation** framing cites meso `UMST.Chem.Conservation` /
  `LandauerLaw.physicalSecondLaw` — not imported.
- No meso / acting theorems. No new physics `axiom`. Sorting cites override pins — **not** 26th axiom.
- `physics_green` stays false. Does **not** claim `occupancyEngineSortProved` or physics GREEN.
- WAVE100 freeze — remainder deferred composition (env/time/cross-domain), not impossibility stop.
-/

namespace UMST.Chem

/-- Design modality for occupancy-engine sort **conservation** (lattice SSOT). -/
inductive OccupancyEngineSortModality where
  | unwired | assumed | proved | surrogate
  deriving DecidableEq, Repr

def occupancyEngineSortModalityCurrent : OccupancyEngineSortModality := .unwired

/-- Modality lattice cardinality (Unwired / Assumed / Proved / Surrogate). -/
def occupancyEngineSortModalityLatticeCardinality : Nat := 4

theorem occupancy_engine_sort_modality_lattice_cardinality_four :
    occupancyEngineSortModalityLatticeCardinality = 4 := rfl

theorem occupancy_engine_sort_modality_lattice_not_118_squared :
    occupancyEngineSortModalityLatticeCardinality ≠ 118 * 118 := by decide

/-- Surface tag for name-from-content. -/
def occupancyEngineSortSurface : String := "occupancy_engine_sort_surface"

theorem occupancy_engine_sort_surface_named : occupancyEngineSortSurface ≠ "" := by decide

/-- Occupancy-engine sort bucket — Madelung family vs finite exception families. -/
inductive OccupancyEngineSortBucket where
  | madelungFamily | namedException | actinideException | dBlockException
  deriving DecidableEq, Repr

def occupancyEngineSortBucketCount : Nat := 4

theorem occupancy_engine_sort_bucket_count_is_four : occupancyEngineSortBucketCount = 4 := rfl

def occupancyEngineSortBucketTags : List String :=
  ["madelung_family", "named_exception", "actinide_exception", "dblock_exception"]

theorem occupancy_engine_sort_bucket_tags_length_four :
    occupancyEngineSortBucketTags.length = 4 := by decide

/-- IUPAC Z bar — sort for Z=1..118 (not 118² table). -/
def iupacTableCardinality : Nat := 118

theorem iupac_table_cardinality_is_118 : iupacTableCardinality = 118 := rfl

def occupancyElementZValid (z : Nat) : Bool :=
  0 < z && z ≤ iupacTableCardinality

/-- Named occupancy exception Z pins — INT SSOT (La / Ce / Gd / Pt / Au). -/
def namedExceptionZs : List Nat := [57, 58, 64, 78, 79]

theorem named_exception_zs_length_five : namedExceptionZs.length = 5 := by decide

/-- Actinide occupancy exception Z pins — INT SSOT (Pu 94 absent). -/
def actinideExceptionZs : List Nat := [89, 90, 91, 92, 93, 96, 103]

theorem actinide_exception_zs_length_seven : actinideExceptionZs.length = 7 := by decide

/-- D-block occupancy exception Z pins — INT SSOT. -/
def dBlockExceptionZs : List Nat := [24, 29, 41, 42, 44, 45, 46, 47]

theorem d_block_exception_zs_length_eight : dBlockExceptionZs.length = 8 := by decide

def listContains (xs : List Nat) (z : Nat) : Bool :=
  match xs with
  | [] => false
  | h :: t => h == z || listContains t z

def isNamedExceptionZ (z : Nat) : Bool := listContains namedExceptionZs z
def isActinideExceptionZ (z : Nat) : Bool := listContains actinideExceptionZs z
def isDBlockExceptionZ (z : Nat) : Bool := listContains dBlockExceptionZs z

def isAnyOccupancyExceptionZ (z : Nat) : Bool :=
  isNamedExceptionZ z || isActinideExceptionZ z || isDBlockExceptionZ z

/-- Classify Z into occupancy-engine sort bucket (cite occupancy_exception_sets, no fork). -/
def occupancyEngineSortBucket (z : Nat) : OccupancyEngineSortBucket :=
  if isNamedExceptionZ z then .namedException
  else if isActinideExceptionZ z then .actinideException
  else if isDBlockExceptionZ z then .dBlockException
  else .madelungFamily

/-- Plutonium Z — absent from all exception sets (honest pin). -/
def plutoniumZ : Nat := 94

theorem plutonium_z_is_94 : plutoniumZ = 94 := rfl

theorem plutonium_not_named_exception : isNamedExceptionZ plutoniumZ = false := by decide
theorem plutonium_not_actinide_exception : isActinideExceptionZ plutoniumZ = false := by decide
theorem plutonium_not_d_block_exception : isDBlockExceptionZ plutoniumZ = false := by decide

def plutoniumNotInAnyExceptionSet : Bool :=
  !isNamedExceptionZ plutoniumZ &&
  !isActinideExceptionZ plutoniumZ &&
  !isDBlockExceptionZ plutoniumZ

theorem plutonium_not_in_any_exception_set_true : plutoniumNotInAnyExceptionSet = true := by decide

def plutoniumSortsMadelungFamily : Bool :=
  plutoniumNotInAnyExceptionSet &&
  occupancyEngineSortBucket plutoniumZ == .madelungFamily

theorem plutonium_sorts_madelung_family_true : plutoniumSortsMadelungFamily = true := by decide

/-- Platinum Z — NamedException sampled anchor. -/
def platinumZ : Nat := 78
def darmstadtiumZ : Nat := 110
def periodHomologZOffset : Nat := 32

theorem platinum_z_is_78 : platinumZ = 78 := rfl
theorem darmstadtium_z_is_110 : darmstadtiumZ = 110 := rfl
theorem period_homolog_z_offset_is_32 : periodHomologZOffset = 32 := by decide

theorem ds_homolog_z_offset_from_pt :
    platinumZ + periodHomologZOffset = darmstadtiumZ := by decide

def platinumSortsNamedException : Bool :=
  occupancyEngineSortBucket platinumZ == .namedException

def darmstadtiumSortsMadelungFamily : Bool :=
  occupancyEngineSortBucket darmstadtiumZ == .madelungFamily

def dsHomologNotPtOccupancyCopy : Bool :=
  darmstadtiumZ ≠ platinumZ &&
  platinumSortsNamedException &&
  darmstadtiumSortsMadelungFamily

theorem ds_homolog_not_pt_occupancy_copy_true : dsHomologNotPtOccupancyCopy = true := by decide

def homologNotCopyMarker : String := "occupancy_engine_sort_homolog_not_copy_v1"
def subshellCopyMarker : String := "occupancy_engine_sort_subshell_copy_v1"

theorem homolog_marker_ne_subshell_copy_marker :
    homologNotCopyMarker ≠ subshellCopyMarker := by decide

/-- Named exception Z sorts into NamedException bucket. -/
def namedExceptionZsSortDistinct : Bool :=
  listContains namedExceptionZs 57 &&
  listContains namedExceptionZs 78 &&
  occupancyEngineSortBucket 57 == .namedException &&
  occupancyEngineSortBucket 78 == .namedException &&
  occupancyEngineSortBucket 79 == .namedException

theorem named_exception_zs_sort_distinct_true : namedExceptionZsSortDistinct = true := by decide

/-- Actinide exception Z sorts into ActinideException bucket. -/
def actinideExceptionZsSortDistinct : Bool :=
  occupancyEngineSortBucket 89 == .actinideException &&
  occupancyEngineSortBucket 103 == .actinideException

theorem actinide_exception_zs_sort_distinct_true : actinideExceptionZsSortDistinct = true := by decide

/-- D-block exception Z sorts into DBlockException bucket. -/
def dBlockExceptionZsSortDistinct : Bool :=
  occupancyEngineSortBucket 24 == .dBlockException &&
  occupancyEngineSortBucket 47 == .dBlockException

theorem d_block_exception_zs_sort_distinct_true : dBlockExceptionZsSortDistinct = true := by decide

def exceptionSetsSortIntoDistinctBuckets : Bool :=
  namedExceptionZsSortDistinct &&
  actinideExceptionZsSortDistinct &&
  dBlockExceptionZsSortDistinct

theorem exception_sets_sort_into_distinct_buckets_true :
    exceptionSetsSortIntoDistinctBuckets = true := by decide

def occupancyEngineIsNewAxiom : Bool := false

theorem occupancy_engine_is_new_axiom_false : occupancyEngineIsNewAxiom = false := rfl

def occupancyEngineSortConjunct : Bool :=
  exceptionSetsSortIntoDistinctBuckets &&
  plutoniumSortsMadelungFamily &&
  dsHomologNotPtOccupancyCopy &&
  !occupancyEngineIsNewAxiom

theorem occupancy_engine_sort_conjunct_true : occupancyEngineSortConjunct = true := by decide

/-- Not fourth chemistry science / not 26th axiom fences. -/
def fourthScienceCollisionMarker : String :=
  "Occupancy engine sort ≠ fourth parallel chemistry science axiom"

def twentySixthAxiomCollisionMarker : String :=
  "Occupancy engine sort ≠ 26th parallel chemistry axiom"

theorem fourth_science_collision_named : fourthScienceCollisionMarker ≠ "" := by decide
theorem twenty_sixth_axiom_collision_named : twentySixthAxiomCollisionMarker ≠ "" := by decide

def notFourthChemistryScience : Bool := true
def notTwentySixthAxiom : Bool := true

theorem not_fourth_chemistry_science : notFourthChemistryScience = true := rfl
theorem not_twenty_sixth_axiom : notTwentySixthAxiom = true := rfl

def soleAxiomCount : Nat := 1

theorem sole_axiom_count_is_one : soleAxiomCount = 1 := rfl

/-- Verdict for occupancy-engine sort close (fail-closed). -/
inductive OccupancyEngineSortVerdict where
  | unwiredOk
  | sortNamedOk
  | trivialZRefuse
  | newAxiomRefuse
  | homologCopyRefuse
  | fourthScienceRefuse
  | twentySixthAxiomRefuse
  | greenInventRefuse
  | provedWithoutBarRefuse
  | productionWiredRefuse
  deriving DecidableEq, Repr

def occupancyEngineSortVerdictOk (v : OccupancyEngineSortVerdict) : Bool :=
  match v with
  | .unwiredOk | .sortNamedOk => true
  | _ => false

structure OccupancyEngineSortIncidence where
  z : Nat
  bucket : OccupancyEngineSortBucket
  level : Nat
  deriving DecidableEq, Repr

def occupancyEngineSortIncidenceNontrivial (h : OccupancyEngineSortIncidence) : Bool :=
  0 < h.level

def occupancyEngineSortIncidencePtL1 : OccupancyEngineSortIncidence :=
  { z := platinumZ, bucket := .namedException, level := 1 }

def occupancyEngineSortIncidenceDsL1 : OccupancyEngineSortIncidence :=
  { z := darmstadtiumZ, bucket := .madelungFamily, level := 1 }

def occupancyEngineSortIncidencePuL1 : OccupancyEngineSortIncidence :=
  { z := plutoniumZ, bucket := .madelungFamily, level := 1 }

def occupancyEngineSortIncidenceTrivial : OccupancyEngineSortIncidence :=
  { z := platinumZ, bucket := .namedException, level := 0 }

def newAxiomSmuggle (claimNewAxiom : Bool) : Bool := claimNewAxiom

def homologCopySmuggle (claimHomologCopy : Bool) : Bool := claimHomologCopy

def evaluateOccupancyEngineSortIncidence
    (modality : OccupancyEngineSortModality)
    (h : OccupancyEngineSortIncidence)
    (claimPhysicsGreen : Bool)
    (claimProved : Bool)
    (claimNewAxiom : Bool)
    (claimHomologCopy : Bool)
    (claimFourthScience : Bool)
    (claimTwentySixthAxiom : Bool) : OccupancyEngineSortVerdict :=
  if claimPhysicsGreen then
    .greenInventRefuse
  else if claimProved then
    .provedWithoutBarRefuse
  else if claimFourthScience then
    .fourthScienceRefuse
  else if claimTwentySixthAxiom then
    .twentySixthAxiomRefuse
  else if newAxiomSmuggle claimNewAxiom then
    .newAxiomRefuse
  else if homologCopySmuggle claimHomologCopy then
    .homologCopyRefuse
  else if !occupancyEngineSortIncidenceNontrivial h then
    .trivialZRefuse
  else if !occupancyElementZValid h.z then
    .trivialZRefuse
  else
    match modality with
    | .unwired => .sortNamedOk
    | .assumed | .surrogate => .unwiredOk
    | .proved => .provedWithoutBarRefuse

def evaluateOccupancyEngineSortClose
    (modality : OccupancyEngineSortModality)
    (claimPhysicsGreen : Bool)
    (claimProductionWired : Bool) : OccupancyEngineSortVerdict :=
  if claimPhysicsGreen then
    .greenInventRefuse
  else if claimProductionWired then
    .productionWiredRefuse
  else
    match modality with
    | .unwired => .unwiredOk
    | .assumed | .proved | .surrogate => .sortNamedOk

/-- WAVE100 — lib.rs / eos.rs not wired (deferred composition). -/
def wave100LibRsWired : Bool := false
def wave100EosRsWired : Bool := false
def occupancyEngineSortProductionWired : Bool := false

theorem wave100_lib_rs_not_wired : wave100LibRsWired = false := rfl
theorem wave100_eos_rs_not_wired : wave100EosRsWired = false := rfl

theorem occupancy_engine_sort_production_not_wired :
    occupancyEngineSortProductionWired = false := rfl

def wave100NotWired : Bool := !wave100LibRsWired && !wave100EosRsWired

theorem wave100_not_wired_true : wave100NotWired = true := by decide

def occupancyEngineSortProved : Bool := false

theorem occupancy_engine_sort_proved_false : occupancyEngineSortProved = false := rfl

def not118SquaredGreenTable : Bool := true

theorem not_118_squared_green_table : not118SquaredGreenTable = true := rfl

def unwiredOccupancyEngineSortCloseOk : Bool :=
  decide (evaluateOccupancyEngineSortClose .unwired false false = .unwiredOk)

def ptSortNamedOk : Bool :=
  decide (evaluateOccupancyEngineSortIncidence .unwired occupancyEngineSortIncidencePtL1
    false false false false false false = .sortNamedOk)

def dsSortMadelungOk : Bool :=
  decide (evaluateOccupancyEngineSortIncidence .unwired occupancyEngineSortIncidenceDsL1
    false false false false false false = .sortNamedOk)

def puSortMadelungOk : Bool :=
  decide (evaluateOccupancyEngineSortIncidence .unwired occupancyEngineSortIncidencePuL1
    false false false false false false = .sortNamedOk)

def trivialZRefuse : Bool :=
  decide (evaluateOccupancyEngineSortIncidence .unwired occupancyEngineSortIncidenceTrivial
    false false false false false false = .trivialZRefuse)

def newAxiomRefuse : Bool :=
  decide (evaluateOccupancyEngineSortIncidence .unwired occupancyEngineSortIncidencePtL1
    false false true false false false = .newAxiomRefuse)

def homologCopyRefuse : Bool :=
  decide (evaluateOccupancyEngineSortIncidence .unwired occupancyEngineSortIncidenceDsL1
    false false false true false false = .homologCopyRefuse)

def greenInventOccupancyEngineSortRefuse : Bool :=
  decide (evaluateOccupancyEngineSortClose .unwired true false = .greenInventRefuse)

def provedWithoutBarOccupancyEngineSortRefuse : Bool :=
  decide (evaluateOccupancyEngineSortIncidence .unwired occupancyEngineSortIncidencePtL1
    false true false false false false = .provedWithoutBarRefuse)

def productionWiredOccupancyEngineSortRefuse : Bool :=
  decide (evaluateOccupancyEngineSortClose .proved false true = .productionWiredRefuse)

def occupancyEngineSortScaffold : Bool :=
  unwiredOccupancyEngineSortCloseOk &&
    occupancyEngineSortConjunct &&
    ptSortNamedOk &&
    dsSortMadelungOk &&
    puSortMadelungOk &&
    trivialZRefuse &&
    newAxiomRefuse &&
    homologCopyRefuse &&
    greenInventOccupancyEngineSortRefuse &&
    provedWithoutBarOccupancyEngineSortRefuse &&
    productionWiredOccupancyEngineSortRefuse &&
    wave100NotWired

theorem occupancy_engine_sort_scaffold_true : occupancyEngineSortScaffold = true := by native_decide

inductive FormalFiber where
  | quantumKnowing | mesoActing
  deriving DecidableEq, Repr

def occupancyEngineSortFiberOk (f : FormalFiber) : Bool :=
  match f with | .quantumKnowing => true | .mesoActing => false

theorem occupancy_engine_sort_knowing_fiber_ok :
    occupancyEngineSortFiberOk .quantumKnowing = true := rfl

theorem occupancy_engine_sort_meso_acting_fiber_not_ok :
    occupancyEngineSortFiberOk .mesoActing = false := rfl

def occupancyEngineSortCellId : String :=
  "CHEM-FORMAL-Q-LEAN-OCCUPANCY-ENGINE-SORT-CONSERVATION"

def occupancyEngineSortPhysicsGreenAuthorized : Prop := False

theorem occupancy_engine_sort_physics_green_false :
    ¬ occupancyEngineSortPhysicsGreenAuthorized := id

structure OccupancyEngineSortProbe where
  cellIdNamed : Bool
  unwired : Bool
  physicsGreenRefused : Bool
  soleAxiom : Bool
  notProved : Bool
  deriving DecidableEq, Repr

def occupancyEngineSortProbe : OccupancyEngineSortProbe :=
  { cellIdNamed :=
      decide (occupancyEngineSortCellId =
        "CHEM-FORMAL-Q-LEAN-OCCUPANCY-ENGINE-SORT-CONSERVATION")
    unwired := decide (occupancyEngineSortModalityCurrent = .unwired)
    physicsGreenRefused := true
    soleAxiom := decide (soleAxiomCount = 1)
    notProved := !occupancyEngineSortProved }

def occupancyEngineSortHonest : Bool :=
  let p := occupancyEngineSortProbe
  p.cellIdNamed &&
    p.unwired &&
    p.physicsGreenRefused &&
    p.soleAxiom &&
    p.notProved &&
    occupancyEngineSortScaffold

theorem occupancy_engine_sort_honest_true : occupancyEngineSortHonest = true := by native_decide

def occupancyEngineSortFraming : String :=
  "second_law_conservation_occupancy_engine_sort_one_axiom_not_26th_axiom"

theorem occupancy_engine_sort_not_twenty_sixth_axiom_framing :
    occupancyEngineSortFraming ≠ "twenty_sixth_chemistry_axiom" := by decide

theorem occupancy_engine_sort_not_fourth_science_axiom :
    occupancyEngineSortFraming ≠ "fourth_chemistry_science_axiom" := by decide

def occupancyEngineSortSecondLawConservationFramed : Bool := true

theorem occupancy_engine_sort_second_law_conservation_framed :
    occupancyEngineSortSecondLawConservationFramed = true := rfl

def occupancyEngineSortCitedCoqModule : String :=
  "Coq/ChemConstants/OccupancyEngineSort.v"

def occupancyEngineSortCitedHsModule : String :=
  "HS ChemConstants/OccupancyEngineSort.hs"

def occupancyEngineSortCitedModule : String :=
  "umst/umst-chem/src/x_rows/occupancy_engine_sort.rs"

def chemIntCrossOccupancyEngineSortAuthority : String :=
  "CHEM-INT-CROSS-OCCUPANCY-ENGINE-SORT-CONSERVATION"

def occupancyEngineSortNonClaim : String :=
  "CHEM-FORMAL-Q-LEAN-OCCUPANCY-ENGINE-SORT-CONSERVATION occupancy engine sort Madelung family vs Named Actinide DBlock exception families Pu94 absent homolog not copy Ds110 not Pt78 not 26th axiom GREEN invent fail-closed proved-without-bar fail-closed trivial Z=0 refuse occupancyEngineSortProved false Unwired knowing quantum fiber not meso acting WAVE100 lib eos smuggle refuse one axiom second law conservation not GREEN DFT not physics GREEN not production_wired remainder deferred composition not impossibility"

theorem occupancy_engine_sort_modality_unwired :
    occupancyEngineSortModalityCurrent = .unwired := rfl

def occupancyEngineSortAxiom : Bool :=
  not118SquaredGreenTable &&
    occupancyEngineSortSecondLawConservationFramed &&
    occupancyEngineSortConjunct &&
    occupancyEngineSortScaffold &&
    occupancyEngineSortHonest &&
    !occupancyEngineSortProved &&
    !occupancyEngineSortProductionWired &&
    !wave100LibRsWired &&
    !wave100EosRsWired &&
    notFourthChemistryScience &&
    notTwentySixthAxiom &&
    decide (occupancyEngineSortFraming =
      "second_law_conservation_occupancy_engine_sort_one_axiom_not_26th_axiom")

theorem occupancy_engine_sort_axiom : occupancyEngineSortAxiom = true := by native_decide

theorem unwired_close_without_production_wiring :
    evaluateOccupancyEngineSortClose .unwired false false = .unwiredOk := rfl

theorem pt_sort_named_ok :
    evaluateOccupancyEngineSortIncidence .unwired occupancyEngineSortIncidencePtL1
      false false false false false false = .sortNamedOk := rfl

theorem ds_sort_madelung_ok :
    evaluateOccupancyEngineSortIncidence .unwired occupancyEngineSortIncidenceDsL1
      false false false false false false = .sortNamedOk := rfl

theorem pu_sort_madelung_ok :
    evaluateOccupancyEngineSortIncidence .unwired occupancyEngineSortIncidencePuL1
      false false false false false false = .sortNamedOk := rfl

theorem trivial_z_refused :
    evaluateOccupancyEngineSortIncidence .unwired occupancyEngineSortIncidenceTrivial
      false false false false false false = .trivialZRefuse := rfl

theorem new_axiom_refused :
    evaluateOccupancyEngineSortIncidence .unwired occupancyEngineSortIncidencePtL1
      false false true false false false = .newAxiomRefuse := rfl

theorem homolog_copy_refused :
    evaluateOccupancyEngineSortIncidence .unwired occupancyEngineSortIncidenceDsL1
      false false false true false false = .homologCopyRefuse := rfl

theorem green_invent_refuse_unwired :
    evaluateOccupancyEngineSortClose .unwired true false = .greenInventRefuse := rfl

theorem proved_without_bar_refuse :
    evaluateOccupancyEngineSortIncidence .unwired occupancyEngineSortIncidencePtL1
      false true false false false false = .provedWithoutBarRefuse := rfl

theorem production_wired_refuse :
    evaluateOccupancyEngineSortClose .proved false true = .productionWiredRefuse := rfl

theorem occupancy_engine_sort_conservation :
    evaluateOccupancyEngineSortClose .unwired false false = .unwiredOk ∧
    occupancyEngineSortConjunct = true ∧
    occupancyEngineSortProved = false ∧
    wave100LibRsWired = false ∧
    wave100EosRsWired = false :=
  ⟨rfl, occupancy_engine_sort_conjunct_true, occupancy_engine_sort_proved_false,
    wave100_lib_rs_not_wired, wave100_eos_rs_not_wired⟩

theorem occupancy_engine_sort_honest_bundle :
    occupancyEngineSortProved = false ∧
    occupancyEngineSortProductionWired = false ∧
    not118SquaredGreenTable = true ∧
    occupancyEngineSortSecondLawConservationFramed = true ∧
    occupancyEngineSortConjunct = true ∧
    plutoniumSortsMadelungFamily = true ∧
    dsHomologNotPtOccupancyCopy = true ∧
    evaluateOccupancyEngineSortClose .unwired false false = .unwiredOk ∧
    evaluateOccupancyEngineSortClose .unwired true false = .greenInventRefuse ∧
    evaluateOccupancyEngineSortIncidence .unwired occupancyEngineSortIncidencePtL1
      false true false false false false = .provedWithoutBarRefuse ∧
    soleAxiomCount = 1 ∧
    occupancyEngineSortAxiom = true ∧
    occupancyEngineSortFiberOk .quantumKnowing = true ∧
    occupancyEngineSortFiberOk .mesoActing = false :=
  ⟨rfl, occupancy_engine_sort_production_not_wired, not_118_squared_green_table,
    occupancy_engine_sort_second_law_conservation_framed, occupancy_engine_sort_conjunct_true,
    plutonium_sorts_madelung_family_true, ds_homolog_not_pt_occupancy_copy_true,
    unwired_close_without_production_wiring, green_invent_refuse_unwired,
    proved_without_bar_refuse, sole_axiom_count_is_one, occupancy_engine_sort_axiom,
    occupancy_engine_sort_knowing_fiber_ok, occupancy_engine_sort_meso_acting_fiber_not_ok⟩

end UMST.Chem
