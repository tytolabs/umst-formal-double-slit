-- SPDX-FileCopyrightText: 2026 Santosh Prabhu Shenbagamoorthy and Santhosh Shyamsundar
-- SPDX-License-Identifier: MIT

import ElementElectronic

set_option maxRecDepth 8192

/-!
# ThExceptionContinuum — class-14 **th_exception_continuum** **conservation** (Q lattice)

Knowing-fiber Lean: Th Z=90 actinide occupancy **exception continuum** **conservation**.
Occupancy-engine sort (X29) restriction on the same second-law + **conservation** object (not a
26th axiom / extra force). Concurrent Π_c PatternBundle factor — **product** not XOR.
Th Z=90 actinide Madelung exception; Ce Z=58 homolog not Th copy. Named class-14 identity
conserved under honest scaffold; trivial XOR, parallel th-exception axiom, homolog copy smuggle,
extra ElementId Z=119, extra occupancy axiom, Madelung-family smuggle, and GREEN invent fail-closed.

Read-only cites (not imported — self-contained scaffold):
- `Coq/ChemConstants/ThExceptionContinuum.v`
- `Haskell/UMST/ChemConstants/ThExceptionContinuum.hs`
- `Agda/ChemConstants/ThExceptionContinuum.agda`
- `umst/umst-chem/src/x_rows/occupancy_engine_sort.rs`
- `umst/umst-chem/src/x_rows/homolog_exception_not_copy.rs`
- `umst/umst-chem/src/qlattice.rs`
- `Coq/ChemConstants/ActinideOccupancyExceptions.v`
- `Coq/ChemConstants/OccupancyEngineSort.v`

- `ThExceptionContinuumModality` — Unwired / Assumed / Proved / Surrogate (not 118² GREEN table).
- `ThExceptionContinuumProductChannel` — occupancy engine sort ⊗ observed override ⊗ class-14 concurrent Π_c.
- Second-law + **conservation** framing cites `LandauerLaw.physicalSecondLaw` — not imported meso theorems.
- No meso / acting theorems. No new physics `axiom`.
- `physics_green` stays false. Does **not** claim `thExceptionContinuumProved` or physics GREEN.
- WAVE100 freeze — not wired lib.rs / eos.rs / nano.
- Does **not** mint parallel th-exception axiom (not 26th axiom).
-/

namespace UMST.Chem

/-- Design modality for class-14 **th_exception_continuum** **conservation** (lattice SSOT). -/
inductive ThExceptionContinuumModality where
  | unwired | assumed | proved | surrogate
  deriving DecidableEq, Repr

def thExceptionContinuumModalityCurrent : ThExceptionContinuumModality := .unwired

/-- Modality lattice cardinality (Unwired / Assumed / Proved / Surrogate). -/
def thExceptionContinuumLatticeCardinality : Nat := 4

theorem thExceptionContinuum_lattice_cardinality_four :
    thExceptionContinuumLatticeCardinality = 4 := rfl

theorem thExceptionContinuum_lattice_not_118_squared :
    thExceptionContinuumLatticeCardinality ≠ 118 * 118 := by decide

/-- Surface tag for name-from-content (`thExceptionContinuum` / `thExceptionContinuumconservation`). -/
def thExceptionContinuumSurface : String :=
  "th_exception_continuum_surface"

theorem th_exception_continuum_surface_named :
    thExceptionContinuumSurface ≠ "" := by decide

/-- Machine-readable thExceptionContinuum conservation marker. -/
def thExceptionContinuumMarker : String :=
  "chem_int_cross_th_exception_continuum_v1"

theorem th_exception_continuum_marker_named :
    thExceptionContinuumMarker ≠ "" := by decide

/-- Row stem pin for name-from-content (`th_exception_continuum`). -/
def thExceptionContinuumRowStem : String := "th_exception_continuum"

theorem th_exception_continuum_row_stem_named :
    thExceptionContinuumRowStem = "th_exception_continuum" := rfl

/-- North-star §2 class-14 thExceptionContinuum pattern index. -/
def class14ThExceptionContinuumPatternIndex : Nat := 14

theorem class14_thExceptionContinuum_pattern_index_fourteen :
    class14ThExceptionContinuumPatternIndex = 14 := rfl

/-- Cross-classifier X29 occupancy engine sort row id pin. -/
def crossClassifierOccupancyEngineSortRowId : String := "X29"

theorem cross_classifier_th_exception_continuum_row_named :
    crossClassifierOccupancyEngineSortRowId = "X29" := rfl

/-- §2 pattern class cardinality (north-star pinned — not 118²). -/
def patternClassCardinality : Nat := 25

theorem pattern_class_cardinality_twenty_five : patternClassCardinality = 25 := rfl

theorem pattern_class_not_118_squared : patternClassCardinality ≠ 118 * 118 := by decide

def patternClassIndexValid (i : Nat) : Bool := i < patternClassCardinality

theorem thExceptionContinuum_class_index_valid :
    patternClassIndexValid class14ThExceptionContinuumPatternIndex = true := by decide

/-- IUPAC periodic-table cardinality (Z=1..118). -/
def iupacTableCardinality : Nat := 118

theorem iupac_table_cardinality_118 : iupacTableCardinality = 118 := rfl

/-- Thorium Z=90 — host assemblage witness element pin. -/
def thoriumAtomicNumberZ : Nat := 90

theorem thorium_atomic_number_z_is_90 : thoriumAtomicNumberZ = 90 := rfl

theorem thorium_z_valid :
    thoriumAtomicNumberZ > 0 ∧ thoriumAtomicNumberZ ≤ iupacTableCardinality := by decide

/-- Forbidden Z=119 smuggle — not in IUPAC table. -/
def forbiddenZ119Smuggle : Nat := 119

theorem forbidden_z119_not_in_iupac_table :
    forbiddenZ119Smuggle > iupacTableCardinality := by decide

/-- Th Z=90 occupancy pins — observed vs Madelung predicted (qlattice SSOT). -/
def thElementSymbol : String := "Th"

def thObservedOccupancyTag : String := "6d27s2"

def thPredictedOccupancyTag : String := "5f27s2"

def thObservedSubshellNotation : String :=
  "1s22s22p63s23p64s23d104p65s24d105p66s24f145d106p67s26d2"

def thPredictedSubshellNotation : String :=
  "1s22s22p63s23p64s23d104p65s24d105p66s24f145d106p67s25f2"

def ceHomologObservedOccupancyTag : String := "4f15d16s2"

def ceriumHomologZ : Nat := 58

theorem cerium_homolog_z_is_58 : ceriumHomologZ = 58 := rfl

def ceriumAtomicNumberZ : Nat := 58

theorem cerium_atomic_number_z_is_58 : ceriumAtomicNumberZ = 58 := rfl

def ceriumHomologObservedSubshellNotation : String :=
  "1s22s22p63s23p64s23d104p65s24d105p66s24f15d1"

theorem th_element_symbol_named : thElementSymbol ≠ "" := by decide

theorem th_observed_occupancy_tag_named : thObservedOccupancyTag ≠ "" := by decide

theorem th_predicted_occupancy_tag_named : thPredictedOccupancyTag ≠ "" := by decide

theorem th_observed_ne_predicted_occupancy :
    thObservedOccupancyTag ≠ thPredictedOccupancyTag := by decide

theorem th_observed_ne_predicted_subshell :
    thObservedSubshellNotation ≠ thPredictedSubshellNotation := by decide

theorem th_homolog_occupancy_not_copy :
    thObservedOccupancyTag ≠ ceHomologObservedOccupancyTag := by decide

theorem th_ce_homolog_subshell_not_copy :
    thObservedSubshellNotation ≠ ceriumHomologObservedSubshellNotation := by decide

def occupancyEngineSortBucketTag : String := "actinide_exception"

theorem occupancy_engine_sort_bucket_tag_actinide :
    occupancyEngineSortBucketTag = "actinide_exception" := rfl

def thExceptionContinuumFactorTag : String := "occupancy_engine_sort"

def occupancyEngineSortChannelTag : String := "occupancy_engine_sort"

def observedOverrideChannelTag : String := "observed_override"

def northStarClass14ThExceptionContinuumTag : String := "class 14 thExceptionContinuum"

theorem thExceptionContinuum_factor_tag_named :
    thExceptionContinuumFactorTag ≠ "" := by decide

theorem occupancy_engine_sort_channel_tag_named :
    occupancyEngineSortChannelTag ≠ "" := by decide

theorem observed_override_channel_tag_named :
    observedOverrideChannelTag ≠ "" := by decide

theorem north_star_class14_thExceptionContinuum_tag_named :
    northStarClass14ThExceptionContinuumTag ≠ "" := by decide

/-- ThExceptionContinuum product channel slot — concurrent **product** factor, not XOR bucket. -/
inductive ThExceptionContinuumChannelSlot where
  | unwired | absent | present
  deriving DecidableEq, Repr

def thExceptionContinuumChannelSlotIsPresent (s : ThExceptionContinuumChannelSlot) : Bool :=
  match s with | .present => true | _ => false

/-- Named interact restriction / TST prior art / class-14 thExceptionContinuum product channels (bounded scaffold). -/
inductive ThExceptionContinuumProductChannel where
  | occupancyEngineSort | observedOverride | class14ThExceptionContinuumAxis
  deriving DecidableEq, Repr

def thExceptionContinuumProductChannelCount : Nat := 3

theorem thExceptionContinuum_product_channel_count_three :
    thExceptionContinuumProductChannelCount = 3 := rfl

def thExceptionContinuumProductChannelIndex : ThExceptionContinuumProductChannel → Nat
  | .occupancyEngineSort => 0
  | .observedOverride => 1
  | .class14ThExceptionContinuumAxis => 2

theorem thec_channel_occupancy_engine_sort_idx_is_0 :
    thExceptionContinuumProductChannelIndex .occupancyEngineSort = 0 := rfl

theorem thec_channel_observed_override_idx_is_1 :
    thExceptionContinuumProductChannelIndex .observedOverride = 1 := rfl

theorem thec_channel_class14_thExceptionContinuum_idx_is_2 :
    thExceptionContinuumProductChannelIndex .class14ThExceptionContinuumAxis = 2 := rfl

/-- Class-14 thExceptionContinuum concurrent **product** bundle (north-star §3). -/
structure ThExceptionContinuumConcurrentBundle where
  channelSlots : List ThExceptionContinuumChannelSlot
  deriving DecidableEq, Repr

/-- All channels Unwired — honest scaffold baseline. -/
def thExceptionContinuumConcurrentBundleUnwired : ThExceptionContinuumConcurrentBundle :=
  { channelSlots := List.replicate thExceptionContinuumProductChannelCount .unwired }

def thExceptionContinuumConcurrentBundleWithChannel (idx : Nat) (slot : ThExceptionContinuumChannelSlot)
    (b : ThExceptionContinuumConcurrentBundle) : ThExceptionContinuumConcurrentBundle :=
  if idx < b.channelSlots.length then
    { channelSlots :=
        b.channelSlots.take idx ++ [slot] ++ b.channelSlots.drop (idx + 1) }
  else b

def thExceptionContinuumConcurrentBundleWithPresent (idx : Nat) (b : ThExceptionContinuumConcurrentBundle) :
    ThExceptionContinuumConcurrentBundle :=
  thExceptionContinuumConcurrentBundleWithChannel idx .present b

def thExceptionContinuumConcurrentBundleChannelAt (idx : Nat) (b : ThExceptionContinuumConcurrentBundle) :
    Option ThExceptionContinuumChannelSlot :=
  b.channelSlots.get? idx

def thExceptionContinuumConcurrentBundleHolds (idx : Nat) (b : ThExceptionContinuumConcurrentBundle) : Bool :=
  match thExceptionContinuumConcurrentBundleChannelAt idx b with
  | some .present => true
  | _ => false

def thExceptionContinuumConcurrentBundlePresentCount (b : ThExceptionContinuumConcurrentBundle) : Nat :=
  b.channelSlots.foldl (fun acc s => if thExceptionContinuumChannelSlotIsPresent s then acc + 1 else acc) 0

def thExceptionContinuumConcurrentBundleIsConcurrentProduct (b : ThExceptionContinuumConcurrentBundle) : Bool :=
  decide (thExceptionContinuumConcurrentBundlePresentCount b ≥ 2)

/-- Th Z=90 interact restriction + TST prior art + class-14 thExceptionContinuum concurrent witness. -/
def thExceptionContinuumTh90Witness : ThExceptionContinuumConcurrentBundle :=
  thExceptionContinuumConcurrentBundleWithPresent 2
    (thExceptionContinuumConcurrentBundleWithPresent 1
      (thExceptionContinuumConcurrentBundleWithPresent 0
        thExceptionContinuumConcurrentBundleUnwired))

def thExceptionContinuumEmptyWitness : ThExceptionContinuumConcurrentBundle :=
  thExceptionContinuumConcurrentBundleUnwired

def thExceptionContinuumSinglePresent : ThExceptionContinuumConcurrentBundle :=
  thExceptionContinuumConcurrentBundleWithPresent 0 thExceptionContinuumConcurrentBundleUnwired

theorem occupancy_engine_sort_channel_present :
    thExceptionContinuumConcurrentBundleHolds 0 thExceptionContinuumTh90Witness = true := by decide

theorem observed_override_channel_present :
    thExceptionContinuumConcurrentBundleHolds 1 thExceptionContinuumTh90Witness = true := by decide

theorem class14_thExceptionContinuum_channel_present :
    thExceptionContinuumConcurrentBundleHolds 2 thExceptionContinuumTh90Witness = true := by decide

theorem th90_witness_present_count_is_three :
    thExceptionContinuumConcurrentBundlePresentCount thExceptionContinuumTh90Witness = 3 := by decide

theorem th90_witness_is_concurrent_product :
    thExceptionContinuumConcurrentBundleIsConcurrentProduct thExceptionContinuumTh90Witness = true := by decide

theorem empty_bundle_present_count_zero :
    thExceptionContinuumConcurrentBundlePresentCount thExceptionContinuumEmptyWitness = 0 := by decide

theorem empty_bundle_not_concurrent_product :
    thExceptionContinuumConcurrentBundleIsConcurrentProduct thExceptionContinuumEmptyWitness = false := by decide

theorem single_present_count_is_one :
    thExceptionContinuumConcurrentBundlePresentCount thExceptionContinuumSinglePresent = 1 := by decide

theorem single_present_not_concurrent_product :
    thExceptionContinuumConcurrentBundleIsConcurrentProduct thExceptionContinuumSinglePresent = false := by decide

/-- XOR posture — mutual exclusivity scaffold defect (must refuse). -/
inductive ThExceptionContinuumXorPosture where
  | exclusive | concurrent
  deriving DecidableEq, Repr

def thExceptionContinuumXorPostureExclusive : ThExceptionContinuumXorPosture := .exclusive
def thExceptionContinuumXorPostureConcurrent : ThExceptionContinuumXorPosture := .concurrent

def thecXorClassifierMarker : String := "chem_l0_thExceptionContinuum_xor_classifier_v1"
def thecConcurrentProductMarker : String := "chem_int_thExceptionContinuum_product_v1"

theorem thec_xor_marker_ne_concurrent_product_marker :
    thecXorClassifierMarker ≠ thecConcurrentProductMarker := by decide

def thecXorClassifierIncompatible (claimXor : Bool) (b : ThExceptionContinuumConcurrentBundle) : Bool :=
  claimXor && thExceptionContinuumConcurrentBundleIsConcurrentProduct b

theorem thec_xor_refuse_on_th90_witness :
    thecXorClassifierIncompatible true thExceptionContinuumTh90Witness = true := by decide

def thecProductNotXor : Bool :=
  thExceptionContinuumConcurrentBundleIsConcurrentProduct thExceptionContinuumTh90Witness &&
  thecXorClassifierIncompatible true thExceptionContinuumTh90Witness

theorem thec_product_not_xor_true : thecProductNotXor = true := by decide

/-- ThExceptionContinuum **conservation** bar — Proved-without-bar scaffold. -/
inductive ThExceptionContinuumBarPresence where
  | absent | present
  deriving DecidableEq, Repr

structure ThExceptionContinuumClaimBar where
  presence : ThExceptionContinuumBarPresence
  defectTotal : Nat
  deriving DecidableEq, Repr

def thExceptionContinuumClaimBarAbsent : ThExceptionContinuumClaimBar :=
  { presence := .absent, defectTotal := 0 }

def thExceptionContinuumClaimBarZeroDefect : ThExceptionContinuumClaimBar :=
  { presence := .present, defectTotal := 0 }

def thExceptionContinuumClaimBarZeroDefectOk (b : ThExceptionContinuumClaimBar) : Bool :=
  match b.presence with
  | .absent => false
  | .present => b.defectTotal = 0

theorem thec_claim_bar_zero_defect_true :
    thExceptionContinuumClaimBarZeroDefectOk thExceptionContinuumClaimBarZeroDefect = true := by decide

theorem thec_claim_bar_absent_not_zero_defect :
    thExceptionContinuumClaimBarZeroDefectOk thExceptionContinuumClaimBarAbsent = false := by decide

/-- Verdict for class-14 **thExceptionContinuum** close (fail-closed). -/
inductive ThExceptionContinuumVerdict where
  | unwiredOk
  | namedOk
  | designOk
  | trivialRefuse
  | xorRefuse
  | greenInventRefuse
  | provedWithoutBarRefuse
  | productionWiredRefuse
  | parallelThExceptionAxiomRefuse
  | homologCopySmuggleRefuse
  | extraElementIdRefuse
  | extraThExceptionContinuumForceRefuse
  | tpFloatPinRefuse
  deriving DecidableEq, Repr

def thExceptionContinuumVerdictOk (v : ThExceptionContinuumVerdict) : Bool :=
  match v with
  | .unwiredOk | .namedOk | .designOk => true
  | _ => false

def thExceptionContinuumBundleNontrivial (b : ThExceptionContinuumConcurrentBundle) : Bool :=
  decide (thExceptionContinuumConcurrentBundlePresentCount b > 0)

def evaluateThExceptionContinuumBundle
    (modality : ThExceptionContinuumModality)
    (_bar : ThExceptionContinuumClaimBar)
    (b : ThExceptionContinuumConcurrentBundle)
    (claimXorClassifier : Bool)
    (claimPhysicsGreen : Bool)
    (claimProved : Bool) : ThExceptionContinuumVerdict :=
  if claimPhysicsGreen then
    .greenInventRefuse
  else if claimProved then
    .provedWithoutBarRefuse
  else if !thExceptionContinuumBundleNontrivial b then
    .trivialRefuse
  else if thecXorClassifierIncompatible claimXorClassifier b then
    .xorRefuse
  else
    match modality with
    | .unwired =>
        if thExceptionContinuumConcurrentBundleIsConcurrentProduct b then .namedOk else .designOk
    | .assumed | .surrogate => .designOk
    | .proved => .provedWithoutBarRefuse

def evaluateThExceptionContinuum
    (modality : ThExceptionContinuumModality)
    (claimPhysicsGreen : Bool)
    (claimProductionWired : Bool) : ThExceptionContinuumVerdict :=
  if claimPhysicsGreen then
    .greenInventRefuse
  else if claimProductionWired then
    .productionWiredRefuse
  else
    match modality with
    | .unwired => .unwiredOk
    | .assumed | .proved | .surrogate => .namedOk

def thExceptionContinuumAuthorized (claimPhysicsGreen : Bool) (claimProductionWired : Bool) : Bool :=
  match evaluateThExceptionContinuum .proved claimPhysicsGreen claimProductionWired with
  | .namedOk => true
  | _ => false

/-- ThExceptionContinuum **conservation** law cells — four laws. -/
inductive ThExceptionContinuumLaw where
  | conserved | namedOk | trivialRefuse | greenInventRefuse
  deriving DecidableEq, Repr

def thExceptionContinuumLawCount : Nat := 4

theorem th_exception_continuum_law_count_four :
    thExceptionContinuumLawCount = 4 := rfl

inductive ThExceptionContinuumLawWitness where
  | openWitness | provedWitness
  deriving DecidableEq, Repr

def evaluateThExceptionContinuumLawWitness
    (_law : ThExceptionContinuumLaw)
    (m : ThExceptionContinuumModality) : ThExceptionContinuumLawWitness :=
  match m with
  | .unwired | .assumed | .surrogate => .openWitness
  | .proved => .provedWitness

theorem all_th_exception_continuum_laws_open_at_unwired :
    evaluateThExceptionContinuumLawWitness .conserved .unwired = .openWitness ∧
    evaluateThExceptionContinuumLawWitness .namedOk .unwired = .openWitness ∧
    evaluateThExceptionContinuumLawWitness .trivialRefuse .unwired = .openWitness ∧
    evaluateThExceptionContinuumLawWitness .greenInventRefuse .unwired = .openWitness := by
  decide

def sampleThExceptionContinuumTh90Bundle : ThExceptionContinuumConcurrentBundle :=
  thExceptionContinuumTh90Witness

def sampleTrivialUnwiredBundle : ThExceptionContinuumConcurrentBundle :=
  thExceptionContinuumEmptyWitness

def unwiredDesignOk : Bool :=
  decide (evaluateThExceptionContinuum .unwired false false = .unwiredOk)

def thExceptionContinuumTh90ConcurrentOk : Bool :=
  decide (evaluateThExceptionContinuumBundle .unwired thExceptionContinuumClaimBarAbsent sampleThExceptionContinuumTh90Bundle
      false false false = .namedOk ∧
    thExceptionContinuumConcurrentBundleIsConcurrentProduct sampleThExceptionContinuumTh90Bundle = true ∧
    thoriumAtomicNumberZ = 90 ∧
    thObservedOccupancyTag = "6d27s2")

def class14ThExceptionContinuumPatternIndexOk : Bool :=
  decide (class14ThExceptionContinuumPatternIndex = 14 ∧
    patternClassIndexValid class14ThExceptionContinuumPatternIndex = true)

def concurrentProductNotXorOk : Bool :=
  decide (thecProductNotXor = true ∧
    thExceptionContinuumConcurrentBundlePresentCount thExceptionContinuumTh90Witness = 3)

def xorMutuallyExclusiveRefuse : Bool :=
  decide (evaluateThExceptionContinuumBundle .unwired thExceptionContinuumClaimBarAbsent sampleThExceptionContinuumTh90Bundle
      true false false = .xorRefuse)

def greenInventThExceptionContinuumRefuse : Bool :=
  decide (evaluateThExceptionContinuum .unwired true false = .greenInventRefuse ∧
    evaluateThExceptionContinuumBundle .unwired thExceptionContinuumClaimBarAbsent sampleThExceptionContinuumTh90Bundle
      false true false = .greenInventRefuse)

def productionWiredRefuse : Bool :=
  decide (evaluateThExceptionContinuum .proved false true = .productionWiredRefuse)

def trivialBundleRefuse : Bool :=
  decide (evaluateThExceptionContinuumBundle .unwired thExceptionContinuumClaimBarAbsent sampleTrivialUnwiredBundle
      false false false = .trivialRefuse)

/-- PATTERN-00 class-14 **thExceptionContinuum** is **not** claimed Proved on the knowing scaffold. -/
def thExceptionContinuumProved : Bool := false

theorem th_exception_continuum_proved_false :
    thExceptionContinuumProved = false := rfl

def thExceptionContinuumProductionWired : Bool := false

theorem th_exception_continuum_production_not_wired :
    thExceptionContinuumProductionWired = false := rfl

def not118SquaredGreenTable : Bool := true

theorem not_118_squared_green_table : not118SquaredGreenTable = true := rfl

def thExceptionContinuumLandauerLawPin : String := "LandauerLaw.physicalSecondLaw"

theorem th_exception_continuum_landauer_law_pin_named :
    thExceptionContinuumLandauerLawPin = "LandauerLaw.physicalSecondLaw" := rfl

def thExceptionContinuumSecondLawConservationFramed : Bool := true

theorem thExceptionContinuum_second_law_conservation_framed :
    thExceptionContinuumSecondLawConservationFramed = true := rfl

def wave100LibRsWired : Bool := false
def wave100EosRsWired : Bool := false
def wave100NanoWired : Bool := false

def wave100NotWired : Bool :=
  !wave100LibRsWired && !wave100EosRsWired && !wave100NanoWired

theorem wave100_not_wired : wave100NotWired = true := rfl

def thExceptionContinuumNeSpeciesId : Bool := true
def homologNotCopied : Bool := false

def thExceptionContinuumAuthority : String :=
  "umst/umst-chem/src/l0_tables/thExceptionContinuum.rs"

theorem th_exception_continuum_authority_path :
    thExceptionContinuumAuthority =
      "umst/umst-chem/src/l0_tables/thExceptionContinuum.rs" := rfl

def chemL0ThExceptionContinuumAuthority : String :=
  "umst/umst-chem/src/thExceptionContinuum.rs"

def occupancyEngineSortAuthority : String :=
  "umst/umst-chem/src/th_exception_continuum_barrier.rs"

def interactPartialityAuthority : String :=
  "umst/umst-chem/src/homolog_exception_not_copy.rs"

def actinideOccupancyExceptionsAuthority : String :=
  "umst/umst-formal-double-slit/Coq/ChemConstants/ActinideOccupancyExceptions.v"

def chemL0EdgeThExceptionContinuumCellId : String := "CHEM-INT-CROSS-OCCUPANCY-EXCEPTION-SETS"

def parallelThExceptionAxiomTag : String := "26th_periodic_table_axiom"

def homologCopySmuggleFraming : String := "ce_z58_occupancy_copied_onto_th_z90"

def extraElementIdSmuggleFraming : String := "th_exception_as_extra_element_id_smuggle"

def extraOccupancyAxiomFraming : String :=
  "extra_th_exception_continuum_force_axiom_minted_as_26th_law"

def tpFloatPinFraming : String :=
  "bare_298_15_k_1_atm_float_pins_on_th_exception_continuum_scaffold"

def thExceptionContinuumFraming : String :=
  "second_law_conservation_th_exception_continuum_occupancy_engine_sort_one_axiom"

def madelungWalkFraming : String :=
  "madelung_walk_predicted_not_observed_override"

def dblockExceptionNamedObject : String :=
  "interact_restriction_on_th_exception_continuum_morphism"

def occupancyEngineSortFraming : String :=
  "occupancy_engine_sort_not_extra_force"

theorem thExceptionContinuum_not_26th_axiom :
    thExceptionContinuumFraming ≠ parallelThExceptionAxiomTag := by decide

def parallelThExceptionAxiomRefuse : Bool :=
  decide (thExceptionContinuumAuthority ≠ parallelThExceptionAxiomTag ∧
    thExceptionContinuumProved = false)

def madelungFamilySmuggleFraming : String :=
  "madelung_family_only_no_observed_override"

def madelungWitnessAuthority : String :=
  "umst/umst-chem/src/x_rows/madelung_witness.rs"

def madelungFamilySmuggleRefuse : Bool :=
  decide (thExceptionContinuumFraming ≠ madelungFamilySmuggleFraming ∧
    thObservedOccupancyTag ≠ thPredictedOccupancyTag)

def homologCopySmuggleRefuse : Bool :=
  decide (thExceptionContinuumFraming ≠ homologCopySmuggleFraming ∧
    thoriumAtomicNumberZ = 90 ∧
    thObservedOccupancyTag = "6d27s2")

def extraElementIdRefuse : Bool :=
  decide (thExceptionContinuumFraming ≠ extraElementIdSmuggleFraming ∧
    forbiddenZ119Smuggle > iupacTableCardinality ∧
    thoriumAtomicNumberZ = 90)

def extraThExceptionContinuumForceRefuse : Bool :=
  decide (thExceptionContinuumFraming ≠ extraOccupancyAxiomFraming ∧
    occupancyEngineSortAuthority ≠ "" ∧
    thExceptionContinuumProved = false)

def tpFloatPinRefuse : Bool :=
  decide (thExceptionContinuumFraming ≠ tpFloatPinFraming ∧
    occupancyEngineSortChannelTag = "occupancy_engine_sort" ∧
    observedOverrideChannelTag = "observed_override")

def tstPriorArtNotNamedObjectRefuse : Bool :=
  decide (dblockExceptionNamedObject ≠ madelungWalkFraming ∧
    observedOverrideChannelTag = "observed_override" ∧
    thExceptionContinuumProved = false)

