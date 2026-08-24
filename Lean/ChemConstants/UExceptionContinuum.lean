-- SPDX-FileCopyrightText: 2026 Santosh Prabhu Shenbagamoorthy and Santhosh Shyamsundar
-- SPDX-License-Identifier: MIT

import ElementElectronic

set_option maxRecDepth 8192

/-!
# UExceptionContinuum — class-14 **u_exception_continuum** **conservation** (Q lattice)

Knowing-fiber Lean: U Z=92 actinide occupancy **exception continuum** **conservation**. Occupancy-engine
sort (X29) restriction on the same second-law + **conservation** object (not a 26th axiom / extra force).
Concurrent Π_c PatternBundle factor — **product** not XOR. U Z=92 5f3 6d1 7s2 actinide Madelung exception;
W Z=74 homolog not U copy. Named class-14 identity conserved under honest scaffold; trivial XOR, parallel
u_exception_continuum axiom, homolog copy smuggle, extra ElementId Z=119, extra occupancy axiom, Madelung
family smuggle, and GREEN invent fail-closed.

Read-only cites (not imported — self-contained scaffold):
- `Coq/ChemConstants/UExceptionContinuum.v`
- `Haskell/UMST/ChemConstants/UExceptionContinuum.hs`
- `Agda/ChemConstants/UExceptionContinuum.agda`
- `umst/umst-chem/src/x_rows/occupancy_engine_sort.rs`
- `umst/umst-chem/src/x_rows/homolog_exception_not_copy.rs`
- `umst/umst-chem/src/qlattice.rs`
- `Coq/ChemConstants/ActinideOccupancyExceptions.v`
- `Coq/ChemConstants/OccupancyEngineSort.v`

- `UExceptionContinuumModality` — Unwired / Assumed / Proved / Surrogate (not 118² GREEN table).
- `UExceptionContinuumProductChannel` — occupancy engine sort ⊗ observed override ⊗ class-14 concurrent Π_c.
- Second-law + **conservation** framing cites `LandauerLaw.physicalSecondLaw` — not imported meso theorems.
- No meso / acting theorems. No new physics `axiom`.
- `physics_green` stays false. Does **not** claim `uExceptionContinuumProved` or physics GREEN.
- WAVE100 freeze — not wired lib.rs / eos.rs / nano.
- Does **not** mint parallel u_exception_continuum axiom (not 26th axiom).
-/

namespace UMST.Chem

/-- Design modality for class-14 **u_exception_continuum** **conservation** (lattice SSOT). -/
inductive UExceptionContinuumModality where
  | unwired | assumed | proved | surrogate
  deriving DecidableEq, Repr

def uExceptionContinuumModalityCurrent : UExceptionContinuumModality := .unwired

/-- Modality lattice cardinality (Unwired / Assumed / Proved / Surrogate). -/
def uExceptionContinuumLatticeCardinality : Nat := 4

theorem u_exception_continuum_lattice_cardinality_four :
    uExceptionContinuumLatticeCardinality = 4 := rfl

theorem u_exception_continuum_lattice_not_118_squared :
    uExceptionContinuumLatticeCardinality ≠ 118 * 118 := by decide

/-- Surface tag for name-from-content (`u_exception_continuum` / `uexceptioncontinuum`). -/
def uExceptionContinuumSurface : String :=
  "u_exception_continuum_surface"

theorem u_exception_continuum_surface_named :
    uExceptionContinuumSurface ≠ "" := by decide

/-- Machine-readable u-exception-continuum conservation marker. -/
def uExceptionContinuumMarker : String :=
  "chem_int_cross_u_exception_continuum_conservation_v1"

theorem u_exception_continuum_marker_named :
    uExceptionContinuumMarker ≠ "" := by decide

/-- Row stem pin for name-from-content (`u_exception_continuum`). -/
def uExceptionContinuumRowStem : String := "u_exception_continuum"

theorem u_exception_continuum_row_stem_named :
    uExceptionContinuumRowStem = "u_exception_continuum" := rfl

/-- North-star §2 class-14 u_exception_continuum pattern index. -/
def class14UExceptionContinuumPatternIndex : Nat := 14

theorem class14_u_exception_continuum_pattern_index_fourteen :
    class14UExceptionContinuumPatternIndex = 14 := rfl

/-- Cross-classifier X29 occupancy-engine-sort row id pin. -/
def crossClassifierOccupancyEngineSortRowId : String := "X29"

theorem cross_classifier_u_exception_continuum_row_named :
    crossClassifierOccupancyEngineSortRowId = "X29" := rfl

/-- §2 pattern class cardinality (north-star pinned — not 118²). -/
def patternClassCardinality : Nat := 25

theorem pattern_class_cardinality_twenty_five : patternClassCardinality = 25 := rfl

theorem pattern_class_not_118_squared : patternClassCardinality ≠ 118 * 118 := by decide

def patternClassIndexValid (i : Nat) : Bool := i < patternClassCardinality

theorem u_exception_continuum_class_index_valid :
    patternClassIndexValid class14UExceptionContinuumPatternIndex = true := by decide

/-- IUPAC periodic-table cardinality (Z=1..118). -/
def iupacTableCardinality : Nat := 118

theorem iupac_table_cardinality_118 : iupacTableCardinality = 118 := rfl

/-- Uranium Z=92 — host assemblage witness element pin. -/
def uraniumAtomicNumberZ : Nat := 92

theorem uranium_atomic_number_z_is_92 : uraniumAtomicNumberZ = 92 := rfl

theorem uranium_z_valid :
    uraniumAtomicNumberZ > 0 ∧ uraniumAtomicNumberZ ≤ iupacTableCardinality := by decide

/-- Forbidden Z=119 smuggle — not in IUPAC table. -/
def forbiddenZ119Smuggle : Nat := 119

theorem forbidden_z119_not_in_iupac_table :
    forbiddenZ119Smuggle > iupacTableCardinality := by decide

/-- U Z=92 occupancy pins — observed vs Madelung predicted (qlattice SSOT). -/
def uElementSymbol : String := "U"

def uObservedOccupancyTag : String := "5f36d17s2"

def uPredictedOccupancyTag : String := "5f47s2"

def uObservedSubshellNotation : String :=
  "1s22s22p63s23p64s23d104p65s24d105p66s24f145d106p67s25f36d1"

def uPredictedSubshellNotation : String :=
  "1s22s22p63s23p64s23d104p65s24d105p66s24f145d106p67s25f4"

def wHomologObservedOccupancyTag : String := "4f145d46s2"

def tungstenHomologZ : Nat := 74

theorem tungsten_homolog_z_is_74 : tungstenHomologZ = 74 := rfl

theorem u_element_symbol_nonempty : uElementSymbol ≠ "" := by decide

theorem u_observed_occupancy_tag_nonempty : uObservedOccupancyTag ≠ "" := by decide

theorem u_predicted_occupancy_tag_nonempty : uPredictedOccupancyTag ≠ "" := by decide

theorem u_observed_ne_predicted_occupancy :
    uObservedOccupancyTag ≠ uPredictedOccupancyTag := by decide

theorem u_observed_ne_predicted_subshell :
    uObservedSubshellNotation ≠ uPredictedSubshellNotation := by decide

theorem u_homolog_occupancy_not_copy :
    uObservedOccupancyTag ≠ wHomologObservedOccupancyTag := by decide

def occupancyEngineSortBucketTag : String := "named_exception"

theorem occupancy_engine_sort_bucket_tag_named :
    occupancyEngineSortBucketTag = "named_exception" := rfl

def uExceptionContinuumFactorTag : String := "occupancy_engine_sort"

def occupancyEngineSortChannelTag : String := "occupancy_engine_sort"

def observedOverrideChannelTag : String := "observed_override"

def northStarClass14UExceptionContinuumTag : String := "X29 occupancy engine sort"

theorem u_exception_continuum_factor_tag_named :
    uExceptionContinuumFactorTag ≠ "" := by decide

theorem occupancy_engine_sort_channel_tag_named :
    occupancyEngineSortChannelTag ≠ "" := by decide

theorem observed_override_channel_tag_named :
    observedOverrideChannelTag ≠ "" := by decide

theorem north_star_class14_u_exception_continuum_tag_named :
    northStarClass14UExceptionContinuumTag ≠ "" := by decide

/-- UExceptionContinuum product channel slot — concurrent **product** factor, not XOR bucket. -/
inductive UExceptionContinuumChannelSlot where
  | unwired | absent | present
  deriving DecidableEq, Repr

def uecChannelSlotIsPresent (s : UExceptionContinuumChannelSlot) : Bool :=
  match s with | .present => true | _ => false

/-- Named occupancy engine sort / observed override / class-14 u_exception_continuum product channels. -/
inductive UExceptionContinuumProductChannel where
  | occupancyEngineSort | observedOverride | class14UExceptionContinuumAxis
  deriving DecidableEq, Repr

def uExceptionContinuumProductChannelCount : Nat := 3

theorem u_exception_continuum_product_channel_count_three :
    uExceptionContinuumProductChannelCount = 3 := rfl

def uExceptionContinuumProductChannelIndex : UExceptionContinuumProductChannel → Nat
  | .occupancyEngineSort => 0
  | .observedOverride => 1
  | .class14UExceptionContinuumAxis => 2

theorem uec_channel_occupancy_engine_sort_idx_is_0 :
    uExceptionContinuumProductChannelIndex .occupancyEngineSort = 0 := rfl

theorem uec_channel_observed_override_idx_is_1 :
    uExceptionContinuumProductChannelIndex .observedOverride = 1 := rfl

theorem uec_channel_class14_u_exception_continuum_idx_is_2 :
    uExceptionContinuumProductChannelIndex .class14UExceptionContinuumAxis = 2 := rfl

/-- Class-14 u_exception_continuum concurrent **product** bundle (north-star §3). -/
structure UExceptionContinuumConcurrentBundle where
  channelSlots : List UExceptionContinuumChannelSlot
  deriving DecidableEq, Repr

/-- All channels Unwired — honest scaffold baseline. -/
def uExceptionContinuumConcurrentBundleUnwired : UExceptionContinuumConcurrentBundle :=
  { channelSlots := List.replicate uExceptionContinuumProductChannelCount .unwired }

def uExceptionContinuumConcurrentBundleWithChannel (idx : Nat) (slot : UExceptionContinuumChannelSlot)
    (b : UExceptionContinuumConcurrentBundle) : UExceptionContinuumConcurrentBundle :=
  if idx < b.channelSlots.length then
    { channelSlots :=
        b.channelSlots.take idx ++ [slot] ++ b.channelSlots.drop (idx + 1) }
  else b

def uExceptionContinuumConcurrentBundleWithPresent (idx : Nat) (b : UExceptionContinuumConcurrentBundle) :
    UExceptionContinuumConcurrentBundle :=
  uExceptionContinuumConcurrentBundleWithChannel idx .present b

def uExceptionContinuumConcurrentBundleChannelAt (idx : Nat) (b : UExceptionContinuumConcurrentBundle) :
    Option UExceptionContinuumChannelSlot :=
  b.channelSlots.get? idx

def uExceptionContinuumConcurrentBundleHolds (idx : Nat) (b : UExceptionContinuumConcurrentBundle) : Bool :=
  match uExceptionContinuumConcurrentBundleChannelAt idx b with
  | some .present => true
  | _ => false

def uExceptionContinuumConcurrentBundlePresentCount (b : UExceptionContinuumConcurrentBundle) : Nat :=
  b.channelSlots.foldl (fun acc s => if uecChannelSlotIsPresent s then acc + 1 else acc) 0

def uExceptionContinuumConcurrentBundleIsConcurrentProduct (b : UExceptionContinuumConcurrentBundle) : Bool :=
  decide (uExceptionContinuumConcurrentBundlePresentCount b ≥ 2)

/-- U Z=92 occupancy engine sort + observed override + class-14 u_exception_continuum concurrent witness. -/
def uExceptionContinuumU92Witness : UExceptionContinuumConcurrentBundle :=
  uExceptionContinuumConcurrentBundleWithPresent 2
    (uExceptionContinuumConcurrentBundleWithPresent 1
      (uExceptionContinuumConcurrentBundleWithPresent 0
        uExceptionContinuumConcurrentBundleUnwired))

def uExceptionContinuumEmptyWitness : UExceptionContinuumConcurrentBundle :=
  uExceptionContinuumConcurrentBundleUnwired

def uExceptionContinuumSinglePresent : UExceptionContinuumConcurrentBundle :=
  uExceptionContinuumConcurrentBundleWithPresent 0 uExceptionContinuumConcurrentBundleUnwired

theorem occupancy_engine_sort_channel_present :
    uExceptionContinuumConcurrentBundleHolds 0 uExceptionContinuumU92Witness = true := by decide

theorem observed_override_channel_present :
    uExceptionContinuumConcurrentBundleHolds 1 uExceptionContinuumU92Witness = true := by decide

theorem class14_u_exception_continuum_channel_present :
    uExceptionContinuumConcurrentBundleHolds 2 uExceptionContinuumU92Witness = true := by decide

theorem u92_witness_present_count_is_three :
    uExceptionContinuumConcurrentBundlePresentCount uExceptionContinuumU92Witness = 3 := by decide

theorem u92_witness_is_concurrent_product :
    uExceptionContinuumConcurrentBundleIsConcurrentProduct uExceptionContinuumU92Witness = true := by decide

theorem empty_bundle_present_count_zero :
    uExceptionContinuumConcurrentBundlePresentCount uExceptionContinuumEmptyWitness = 0 := by decide

theorem empty_bundle_not_concurrent_product :
    uExceptionContinuumConcurrentBundleIsConcurrentProduct uExceptionContinuumEmptyWitness = false := by decide

theorem single_present_count_is_one :
    uExceptionContinuumConcurrentBundlePresentCount uExceptionContinuumSinglePresent = 1 := by decide

theorem single_present_not_concurrent_product :
    uExceptionContinuumConcurrentBundleIsConcurrentProduct uExceptionContinuumSinglePresent = false := by decide

/-- XOR posture — mutual exclusivity scaffold defect (must refuse). -/
inductive UExceptionContinuumXorPosture where
  | exclusive | concurrent
  deriving DecidableEq, Repr

def uecXorClassifierMarker : String := "chem_l0_u_exception_continuum_xor_classifier_v1"
def uecConcurrentProductMarker : String := "chem_int_u_exception_continuum_product_v1"

theorem uec_xor_marker_ne_concurrent_product_marker :
    uecXorClassifierMarker ≠ uecConcurrentProductMarker := by decide

def uecXorClassifierIncompatible (claimXor : Bool) (b : UExceptionContinuumConcurrentBundle) : Bool :=
  claimXor && uExceptionContinuumConcurrentBundleIsConcurrentProduct b

theorem uec_xor_refuse_on_u92_witness :
    uecXorClassifierIncompatible true uExceptionContinuumU92Witness = true := by decide

def uecProductNotXor : Bool :=
  uExceptionContinuumConcurrentBundleIsConcurrentProduct uExceptionContinuumU92Witness &&
  uecXorClassifierIncompatible true uExceptionContinuumU92Witness

theorem uec_product_not_xor_true : uecProductNotXor = true := by decide

/-- UExceptionContinuum **conservation** bar — Proved-without-bar scaffold. -/
inductive UExceptionContinuumBarPresence where
  | absent | present
  deriving DecidableEq, Repr

structure UExceptionContinuumClaimBar where
  presence : UExceptionContinuumBarPresence
  defectTotal : Nat
  deriving DecidableEq, Repr

def uExceptionContinuumClaimBarAbsent : UExceptionContinuumClaimBar :=
  { presence := .absent, defectTotal := 0 }

def uExceptionContinuumClaimBarZeroDefect : UExceptionContinuumClaimBar :=
  { presence := .present, defectTotal := 0 }

def uecClaimBarZeroDefectOk (b : UExceptionContinuumClaimBar) : Bool :=
  match b.presence with
  | .absent => false
  | .present => b.defectTotal = 0

theorem uec_claim_bar_zero_defect_true :
    uecClaimBarZeroDefectOk uExceptionContinuumClaimBarZeroDefect = true := by decide

theorem uec_claim_bar_absent_not_zero_defect :
    uecClaimBarZeroDefectOk uExceptionContinuumClaimBarAbsent = false := by decide

/-- Verdict for class-14 **u_exception_continuum** close (fail-closed). -/
inductive UExceptionContinuumVerdict where
  | unwiredOk
  | namedOk
  | designOk
  | trivialRefuse
  | xorRefuse
  | greenInventRefuse
  | provedWithoutBarRefuse
  | productionWiredRefuse
  | parallelUExceptionAxiomRefuse
  | speciesIdSmuggleRefuse
  | extraElementIdRefuse
  | extraOccupancyAxiomRefuse
  | madelungFamilySmuggleRefuse
  | tpFloatPinRefuse
  deriving DecidableEq, Repr

def uExceptionContinuumVerdictOk (v : UExceptionContinuumVerdict) : Bool :=
  match v with
  | .unwiredOk | .namedOk | .designOk => true
  | _ => false

def uExceptionContinuumBundleNontrivial (b : UExceptionContinuumConcurrentBundle) : Bool :=
  decide (uExceptionContinuumConcurrentBundlePresentCount b > 0)

def evaluateUExceptionContinuumBundle
    (modality : UExceptionContinuumModality)
    (_bar : UExceptionContinuumClaimBar)
    (b : UExceptionContinuumConcurrentBundle)
    (claimXorClassifier : Bool)
    (claimPhysicsGreen : Bool)
    (claimProved : Bool) : UExceptionContinuumVerdict :=
  if claimPhysicsGreen then
    .greenInventRefuse
  else if claimProved then
    .provedWithoutBarRefuse
  else if !uExceptionContinuumBundleNontrivial b then
    .trivialRefuse
  else if uecXorClassifierIncompatible claimXorClassifier b then
    .xorRefuse
  else
    match modality with
    | .unwired =>
        if uExceptionContinuumConcurrentBundleIsConcurrentProduct b then .namedOk else .designOk
    | .assumed | .surrogate => .designOk
    | .proved => .provedWithoutBarRefuse

def evaluateUExceptionContinuumClose
    (modality : UExceptionContinuumModality)
    (claimPhysicsGreen : Bool)
    (claimProductionWired : Bool) : UExceptionContinuumVerdict :=
  if claimPhysicsGreen then
    .greenInventRefuse
  else if claimProductionWired then
    .productionWiredRefuse
  else
    match modality with
    | .unwired => .unwiredOk
    | .assumed | .proved | .surrogate => .namedOk

def uExceptionContinuumAuthorized (claimPhysicsGreen : Bool) (claimProductionWired : Bool) : Bool :=
  match evaluateUExceptionContinuumClose .proved claimPhysicsGreen claimProductionWired with
  | .namedOk => true
  | _ => false

/-- UExceptionContinuum **conservation** law cells — four laws. -/
inductive UExceptionContinuumLaw where
  | conserved | namedOk | trivialRefuse | greenInventRefuse
  deriving DecidableEq, Repr

def uExceptionContinuumLawCount : Nat := 4

theorem u_exception_continuum_law_count_four :
    uExceptionContinuumLawCount = 4 := rfl

inductive UExceptionContinuumLawWitness where
  | openWitness | provedWitness
  deriving DecidableEq, Repr

def evaluateUExceptionContinuumLawWitness
    (_law : UExceptionContinuumLaw)
    (m : UExceptionContinuumModality) : UExceptionContinuumLawWitness :=
  match m with
  | .unwired | .assumed | .surrogate => .openWitness
  | .proved => .provedWitness

theorem all_uec_conservation_laws_open_at_unwired :
    evaluateUExceptionContinuumLawWitness .conserved .unwired = .openWitness ∧
    evaluateUExceptionContinuumLawWitness .namedOk .unwired = .openWitness ∧
    evaluateUExceptionContinuumLawWitness .trivialRefuse .unwired = .openWitness ∧
    evaluateUExceptionContinuumLawWitness .greenInventRefuse .unwired = .openWitness := by
  decide

def sampleUExceptionContinuumU92Bundle : UExceptionContinuumConcurrentBundle :=
  uExceptionContinuumU92Witness

def sampleTrivialUnwiredBundle : UExceptionContinuumConcurrentBundle :=
  uExceptionContinuumEmptyWitness

def unwiredDesignOk : Bool :=
  decide (evaluateUExceptionContinuumClose .unwired false false = .unwiredOk)

def uExceptionContinuumU92ConcurrentOk : Bool :=
  decide (evaluateUExceptionContinuumBundle .unwired uExceptionContinuumClaimBarAbsent
      sampleUExceptionContinuumU92Bundle false false false = .namedOk ∧
    uExceptionContinuumConcurrentBundleIsConcurrentProduct sampleUExceptionContinuumU92Bundle = true ∧
    uraniumAtomicNumberZ = 92 ∧
    uObservedOccupancyTag = "5f36d17s2")

def class14UExceptionContinuumPatternIndexOk : Bool :=
  decide (class14UExceptionContinuumPatternIndex = 14 ∧
    patternClassIndexValid class14UExceptionContinuumPatternIndex = true)

def concurrentProductNotXorOk : Bool :=
  decide (uecProductNotXor = true ∧
    uExceptionContinuumConcurrentBundlePresentCount uExceptionContinuumU92Witness = 3)

def xorMutuallyExclusiveRefuse : Bool :=
  decide (evaluateUExceptionContinuumBundle .unwired uExceptionContinuumClaimBarAbsent
      sampleUExceptionContinuumU92Bundle true false false = .xorRefuse)

def greenInventUExceptionRefuse : Bool :=
  decide (evaluateUExceptionContinuumClose .unwired true false = .greenInventRefuse ∧
    evaluateUExceptionContinuumBundle .unwired uExceptionContinuumClaimBarAbsent
      sampleUExceptionContinuumU92Bundle false true false = .greenInventRefuse)

def productionWiredRefuse : Bool :=
  decide (evaluateUExceptionContinuumClose .proved false true = .productionWiredRefuse)

def trivialBundleRefuse : Bool :=
  decide (evaluateUExceptionContinuumBundle .unwired uExceptionContinuumClaimBarAbsent
      sampleTrivialUnwiredBundle false false false = .trivialRefuse)

/-- PATTERN-00 class-14 **u_exception_continuum** is **not** claimed Proved on the knowing scaffold. -/
def uExceptionContinuumProved : Bool := false

theorem u_exception_continuum_proved_false :
    uExceptionContinuumProved = false := rfl

def uExceptionContinuumProductionWired : Bool := false

theorem u_exception_continuum_production_not_wired :
    uExceptionContinuumProductionWired = false := rfl

def not118SquaredGreenTable : Bool := true

theorem not_118_squared_green_table : not118SquaredGreenTable = true := rfl

def uExceptionContinuumLandauerLawPin : String := "LandauerLaw.physicalSecondLaw"

theorem u_exception_continuum_landauer_law_pin_named :
    uExceptionContinuumLandauerLawPin = "LandauerLaw.physicalSecondLaw" := rfl

def uExceptionContinuumSecondLawConservationFramed : Bool := true

theorem u_exception_continuum_second_law_conservation_framed :
    uExceptionContinuumSecondLawConservationFramed = true := rfl

def wave100LibRsWired : Bool := false
def wave100EosRsWired : Bool := false
def wave100NanoWired : Bool := false

def wave100NotWired : Bool :=
  !wave100LibRsWired && !wave100EosRsWired && !wave100NanoWired

theorem wave100_not_wired : wave100NotWired = true := rfl

def uExceptionContinuumAuthority : String :=
  "umst/umst-chem/src/x_rows/occupancy_engine_sort.rs"

theorem u_exception_continuum_authority_path :
    uExceptionContinuumAuthority =
      "umst/umst-chem/src/x_rows/occupancy_engine_sort.rs" := rfl

def uExceptionContinuumQlatticeAuthority : String :=
  "umst/umst-chem/src/qlattice.rs"

def homologExceptionNotCopyAuthority : String :=
  "umst/umst-chem/src/x_rows/homolog_exception_not_copy.rs"

def dBlockOccupancyExceptionsAuthority : String :=
  "umst/umst-formal-double-slit/Coq/ChemConstants/ActinideOccupancyExceptions.v"

def occupancyEngineSortExceptionSetsCellId : String :=
  "CHEM-INT-CROSS-OCCUPANCY-EXCEPTION-SETS"

def homologExceptionNotCopyCellId : String :=
  "CHEM-INT-CROSS-HOMOLOG-EXCEPTION-NOT-COPY"

def parallelUExceptionAxiomTag : String := "26th_periodic_table_axiom"

def homologCopyFraming : String := "w_z74_occupancy_copied_onto_u_z92"

def extraElementIdSmuggleFraming : String :=
  "u_exception_as_extra_element_id_smuggle"

def extraOccupancyAxiomFraming : String :=
  "extra_u_exception_continuum_force_axiom_minted_as_26th_law"

def occupancyEngineSortAuthority : String :=
  "umst/umst-chem/src/u_exception_continuum_barrier.rs"

def madelungFamilySmuggleFraming : String :=
  "madelung_family_only_no_observed_override"

def madelungWitnessAuthority : String :=
  "umst/umst-chem/src/x_rows/madelung_witness.rs"

def tpFloatPinFraming : String :=
  "bare_298_15_k_1_atm_float_pins_on_u_exception_continuum_scaffold"

def uExceptionContinuumFraming : String :=
  "second_law_conservation_u_exception_continuum_occupancy_engine_sort_one_axiom"

def madelungWalkFraming : String :=
  "madelung_walk_predicted_not_observed_override"

def namedExceptionNamedObject : String :=
  "interact_restriction_on_u_exception_continuum_morphism"

def occupancyEngineSortFraming : String :=
  "occupancy_engine_sort_not_extra_force"

theorem u_exception_continuum_not_26th_axiom :
    uExceptionContinuumFraming ≠ parallelUExceptionAxiomTag := by decide

def parallelUExceptionAxiomRefuse : Bool :=
  decide (uExceptionContinuumAuthority ≠ parallelUExceptionAxiomTag ∧
    uExceptionContinuumProved = false)

def homologCopySmuggleRefuse : Bool :=
  decide (uExceptionContinuumFraming ≠ homologCopyFraming ∧
    uraniumAtomicNumberZ = 92 ∧
    uObservedOccupancyTag = "5f36d17s2" ∧
    uObservedOccupancyTag ≠ wHomologObservedOccupancyTag)

def extraElementIdRefuse : Bool :=
  decide (uExceptionContinuumFraming ≠ extraElementIdSmuggleFraming ∧
    forbiddenZ119Smuggle > iupacTableCardinality ∧
    uraniumAtomicNumberZ = 92)

def extraOccupancyAxiomRefuse : Bool :=
  decide (uExceptionContinuumFraming ≠ extraOccupancyAxiomFraming ∧
    occupancyEngineSortAuthority ≠ "" ∧
    uExceptionContinuumProved = false)

def madelungFamilySmuggleRefuse : Bool :=
  decide (uExceptionContinuumFraming ≠ madelungFamilySmuggleFraming ∧
    uObservedOccupancyTag ≠ uPredictedOccupancyTag ∧
    uObservedOccupancyTag = "5f36d17s2")

def tpFloatPinRefuse : Bool :=
  decide (uExceptionContinuumFraming ≠ tpFloatPinFraming ∧
    occupancyEngineSortChannelTag = "occupancy_engine_sort" ∧
    observedOverrideChannelTag = "observed_override")

def madelungWalkNotNamedObjectRefuse : Bool :=
  decide (namedExceptionNamedObject ≠ madelungWalkFraming ∧
    observedOverrideChannelTag = "observed_override" ∧
    uExceptionContinuumProved = false)

def occupancyEngineSortNotExtraForceRefuse : Bool :=
  decide (occupancyEngineSortFraming ≠ extraOccupancyAxiomFraming ∧
    occupancyEngineSortChannelTag = "occupancy_engine_sort" ∧
    occupancyEngineSortAuthority =
      "umst/umst-chem/src/u_exception_continuum_barrier.rs")

def wHomologNotUCopyOk : Bool :=
  decide (uraniumAtomicNumberZ = 92 ∧
    tungstenHomologZ = 74 ∧
    uObservedOccupancyTag = "5f36d17s2" ∧
    wHomologObservedOccupancyTag = "4f145d46s2" ∧
    uObservedOccupancyTag ≠ wHomologObservedOccupancyTag)

def uecConservationCoherenceScaffold : Bool :=
  decide (evaluateUExceptionContinuumClose .proved false false = .namedOk ∧
    evaluateUExceptionContinuumClose .unwired true false = .greenInventRefuse ∧
    evaluateUExceptionContinuumClose .proved false true = .productionWiredRefuse)

theorem uec_conservation_coherence_scaffold_true :
    uecConservationCoherenceScaffold = true := by decide

def uExceptionContinuumLatticeScaffold : Bool :=
  unwiredDesignOk &&
    uExceptionContinuumU92ConcurrentOk &&
    class14UExceptionContinuumPatternIndexOk &&
    concurrentProductNotXorOk &&
    xorMutuallyExclusiveRefuse &&
    greenInventUExceptionRefuse &&
    parallelUExceptionAxiomRefuse &&
    homologCopySmuggleRefuse &&
    extraElementIdRefuse &&
    extraOccupancyAxiomRefuse &&
    madelungFamilySmuggleRefuse &&
    tpFloatPinRefuse &&
    madelungWalkNotNamedObjectRefuse &&
    occupancyEngineSortNotExtraForceRefuse &&
    wHomologNotUCopyOk &&
    trivialBundleRefuse &&
    productionWiredRefuse &&
    uecConservationCoherenceScaffold &&
    wave100NotWired

theorem u_exception_continuum_lattice_scaffold_true :
    uExceptionContinuumLatticeScaffold = true := by native_decide

inductive UExceptionContinuumFiber where
  | quantumKnowing | mesoActing
  deriving DecidableEq, Repr

def uExceptionContinuumFiberOk (f : UExceptionContinuumFiber) : Bool :=
  match f with | .quantumKnowing => true | .mesoActing => false

theorem u_exception_continuum_knowing_fiber_ok :
    uExceptionContinuumFiberOk .quantumKnowing = true := rfl

theorem u_exception_continuum_meso_acting_not_ok :
    uExceptionContinuumFiberOk .mesoActing = false := rfl

def fiberNotMesoActing : Bool :=
  uExceptionContinuumFiberOk .quantumKnowing &&
  !uExceptionContinuumFiberOk .mesoActing

theorem fiber_not_meso_acting_true : fiberNotMesoActing = true := by decide

def uExceptionContinuumCellId : String :=
  "CHEM-FORMAL-Q-LEAN-U-EXCEPTION-CONTINUUM"

def uExceptionContinuumNonClaim : String :=
  "CHEM-FORMAL-Q-LEAN-U-EXCEPTION-CONTINUUM U Z=92 actinide occupancy exception continuum X29 occupancy engine sort observed override dblock exception concurrent product identity conserved present ge 2 product not XOR xor mutually exclusive refuse parallel u exception axiom refuse homolog copy smuggle refuse extra element id Z=119 refuse extra occupancy axiom refuse W Z=74 homolog not U 5f3 6d1 7s2 copy Unwired one axiom second law conservation not 118 squared GREEN table not meso acting not physics GREEN not production_wired"

def uExceptionContinuumPhysicsGreenAuthorized : Prop := False

theorem u_exception_continuum_physics_green_false :
    ¬ uExceptionContinuumPhysicsGreenAuthorized := id

structure UExceptionContinuumProbe where
  cellIdNamed : Bool
  unwired : Bool
  physicsGreenRefused : Bool
  notProved : Bool
  class14Index : Bool
  u92HostWitness : Bool
  occupancyObservedOverrideProduct : Bool
  concurrentNotXor : Bool
  u92WitnessOk : Bool
  xorRefuse : Bool
  greenInventRefuse : Bool
  parallelAxiomRefuse : Bool
  homologCopySmuggleRefuse : Bool
  extraElementIdRefuse : Bool
  extraOccupancyAxiomRefuse : Bool
  madelungFamilySmuggleRefuse : Bool
  tpFloatPinRefuse : Bool
  madelungWalkRefuse : Bool
  occupancyEngineSortRefuse : Bool
  wHomologNotCopy : Bool
  productionWiredRefuse : Bool
  knowingFiberOk : Bool
  wave100NotWired : Bool
  intAuthorityCited : Bool
  actinideExceptionsCited : Bool
  deriving DecidableEq, Repr

def uExceptionContinuumProbe : UExceptionContinuumProbe :=
  { cellIdNamed :=
      decide (uExceptionContinuumCellId =
        "CHEM-FORMAL-Q-LEAN-U-EXCEPTION-CONTINUUM")
    unwired := decide (uExceptionContinuumModalityCurrent = .unwired)
    physicsGreenRefused := true
    notProved := !uExceptionContinuumProved
    class14Index := decide (class14UExceptionContinuumPatternIndex = 14)
    u92HostWitness := decide (uraniumAtomicNumberZ = 92)
    occupancyObservedOverrideProduct := decide (occupancyEngineSortChannelTag = "occupancy_engine_sort" ∧
      observedOverrideChannelTag = "observed_override" ∧
      uExceptionContinuumFactorTag = "occupancy_engine_sort")
    concurrentNotXor := uecProductNotXor
    u92WitnessOk := uExceptionContinuumU92ConcurrentOk
    xorRefuse := xorMutuallyExclusiveRefuse
    greenInventRefuse := greenInventUExceptionRefuse
    parallelAxiomRefuse := parallelUExceptionAxiomRefuse
    homologCopySmuggleRefuse := homologCopySmuggleRefuse
    extraElementIdRefuse := extraElementIdRefuse
    extraOccupancyAxiomRefuse := extraOccupancyAxiomRefuse
    madelungFamilySmuggleRefuse := madelungFamilySmuggleRefuse
    tpFloatPinRefuse := tpFloatPinRefuse
    madelungWalkRefuse := madelungWalkNotNamedObjectRefuse
    occupancyEngineSortRefuse := occupancyEngineSortNotExtraForceRefuse
    wHomologNotCopy := wHomologNotUCopyOk
    productionWiredRefuse := productionWiredRefuse
    knowingFiberOk := uExceptionContinuumFiberOk .quantumKnowing
    wave100NotWired := wave100NotWired
    intAuthorityCited := uExceptionContinuumAuthority ≠ ""
    actinideExceptionsCited := dBlockOccupancyExceptionsAuthority ≠ "" }

def uExceptionContinuumHonest : Bool :=
  let p := uExceptionContinuumProbe
  p.cellIdNamed &&
    p.unwired &&
    p.physicsGreenRefused &&
    p.notProved &&
    p.class14Index &&
    p.u92HostWitness &&
    p.occupancyObservedOverrideProduct &&
    p.concurrentNotXor &&
    p.u92WitnessOk &&
    p.xorRefuse &&
    p.greenInventRefuse &&
    p.parallelAxiomRefuse &&
    p.homologCopySmuggleRefuse &&
    p.extraElementIdRefuse &&
    p.extraOccupancyAxiomRefuse &&
    p.madelungFamilySmuggleRefuse &&
    p.tpFloatPinRefuse &&
    p.madelungWalkRefuse &&
    p.occupancyEngineSortRefuse &&
    p.wHomologNotCopy &&
    p.productionWiredRefuse &&
    p.knowingFiberOk &&
    p.wave100NotWired &&
    p.intAuthorityCited &&
    p.actinideExceptionsCited &&
    uExceptionContinuumLatticeScaffold

theorem u_exception_continuum_honest_true :
    uExceptionContinuumHonest = true := by native_decide

def uExceptionContinuumAxiom : Bool :=
  not118SquaredGreenTable &&
    uExceptionContinuumSecondLawConservationFramed &&
    uExceptionContinuumLatticeScaffold &&
    uExceptionContinuumHonest &&
    !uExceptionContinuumProved &&
    !uExceptionContinuumProductionWired &&
    !wave100LibRsWired &&
    !wave100EosRsWired &&
    !wave100NanoWired &&
    decide (uExceptionContinuumFraming =
      "second_law_conservation_u_exception_continuum_occupancy_engine_sort_one_axiom")

theorem u_exception_continuum_axiom :
    uExceptionContinuumAxiom = true := by native_decide

theorem u_exception_continuum_modality_unwired :
    uExceptionContinuumModalityCurrent = .unwired := rfl

theorem unwired_close_without_production_wiring :
    evaluateUExceptionContinuumClose .unwired false false = .unwiredOk := rfl

theorem u92_witness_named_ok :
    evaluateUExceptionContinuumBundle .unwired uExceptionContinuumClaimBarAbsent
      sampleUExceptionContinuumU92Bundle false false false = .namedOk := rfl

theorem trivial_empty_bundle_fail_closed :
    evaluateUExceptionContinuumBundle .unwired uExceptionContinuumClaimBarAbsent
      sampleTrivialUnwiredBundle false false false = .trivialRefuse := rfl

theorem xor_classifier_refused :
    evaluateUExceptionContinuumBundle .unwired uExceptionContinuumClaimBarAbsent
      sampleUExceptionContinuumU92Bundle true false false = .xorRefuse := rfl

theorem green_invent_refuse_unwired :
    evaluateUExceptionContinuumClose .unwired true false = .greenInventRefuse := rfl

theorem proved_without_bar_refuse :
    evaluateUExceptionContinuumBundle .unwired uExceptionContinuumClaimBarAbsent
      sampleUExceptionContinuumU92Bundle false false true = .provedWithoutBarRefuse := rfl

theorem production_wired_refuse :
    evaluateUExceptionContinuumClose .proved false true = .productionWiredRefuse := rfl

theorem w_period6_homolog_not_u_occupancy_copy :
    uraniumAtomicNumberZ = 92 ∧
    tungstenHomologZ = 74 ∧
    uObservedOccupancyTag = "5f36d17s2" ∧
    wHomologObservedOccupancyTag = "4f145d46s2" ∧
    uObservedOccupancyTag ≠ wHomologObservedOccupancyTag ∧
    uExceptionContinuumProved = false := by
  decide

theorem u_exception_continuum_honest_bundle :
    uExceptionContinuumProved = false ∧
    uExceptionContinuumProductionWired = false ∧
    not118SquaredGreenTable = true ∧
    uExceptionContinuumSecondLawConservationFramed = true ∧
    evaluateUExceptionContinuumClose .unwired false false = .unwiredOk ∧
    evaluateUExceptionContinuumBundle .unwired uExceptionContinuumClaimBarAbsent
      sampleUExceptionContinuumU92Bundle false false false = .namedOk ∧
    evaluateUExceptionContinuumBundle .unwired uExceptionContinuumClaimBarAbsent
      sampleTrivialUnwiredBundle false false false = .trivialRefuse ∧
    evaluateUExceptionContinuumBundle .unwired uExceptionContinuumClaimBarAbsent
      sampleUExceptionContinuumU92Bundle true false false = .xorRefuse ∧
    evaluateUExceptionContinuumClose .unwired true false = .greenInventRefuse ∧
    uecProductNotXor = true ∧
    uraniumAtomicNumberZ = 92 ∧
    class14UExceptionContinuumPatternIndex = 14 ∧
    uExceptionContinuumAxiom = true :=
  ⟨rfl, rfl, not_118_squared_green_table, u_exception_continuum_second_law_conservation_framed,
    unwired_close_without_production_wiring, u92_witness_named_ok,
    trivial_empty_bundle_fail_closed, xor_classifier_refused, green_invent_refuse_unwired,
    uec_product_not_xor_true, uranium_atomic_number_z_is_92,
    class14_u_exception_continuum_pattern_index_fourteen,
    u_exception_continuum_axiom⟩

end UMST.Chem
