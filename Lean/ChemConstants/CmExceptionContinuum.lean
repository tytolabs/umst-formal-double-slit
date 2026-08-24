-- SPDX-FileCopyrightText: 2026 Santosh Prabhu Shenbagamoorthy and Santhosh Shyamsundar
-- SPDX-License-Identifier: MIT

import ElementElectronic

set_option maxRecDepth 8192

/-!
# CmExceptionContinuum — class-14 **cm_exception_continuum** **conservation** (Q lattice)

Knowing-fiber Lean: Cm Z=96 actinide occupancy **exception continuum** **conservation**. Occupancy-engine
sort (X29) restriction on the same second-law + **conservation** object (not a 26th axiom / extra force).
Concurrent Π_c PatternBundle factor — **product** not XOR. Cm Z=96 5f7 6d1 7s2 actinide Madelung exception;
Gd Z=64 homolog not Cm copy. `cmExceptionContinuumProved` false. Modality Unwired.

Read-only cites (not imported — self-contained scaffold):
- `Coq/ChemConstants/CmExceptionContinuum.v`
- `Haskell/UMST/ChemConstants/CmExceptionContinuum.hs`
- `Agda/ChemConstants/CmExceptionContinuum.agda`
- `umst/umst-chem/src/x_rows/occupancy_engine_sort.rs`
- `umst/umst-chem/src/x_rows/homolog_exception_not_copy.rs`
- `umst/umst-chem/src/qlattice.rs`

- `CmExceptionContinuumModality` — Unwired / Assumed / Proved / Surrogate (not 118² GREEN table).
- `CmExceptionContinuumProductChannel` — occupancy engine sort ⊗ observed override ⊗ class-14 concurrent Π_c.
- Second-law + **conservation** framing cites `LandauerLaw.physicalSecondLaw` — not imported meso theorems.
- No meso / acting theorems. No new physics `axiom`.
- `physics_green` stays false. Does **not** claim `cmExceptionContinuumProved` or physics GREEN.
- WAVE100 freeze — not wired lib.rs / eos.rs / nano.
- Does **not** mint second cm_exception_continuum axiom (not 26th axiom).
- File stem pin (`cmexceptioncontinuum`).
-/

namespace UMST.Chem

/-- Design modality for class-14 **cm_exception_continuum** **conservation** (lattice SSOT). -/
inductive CmExceptionContinuumModality where
  | unwired | assumed | proved | surrogate
  deriving DecidableEq, Repr

def cmExceptionContinuumModalityCurrent : CmExceptionContinuumModality := .unwired

/-- Modality lattice cardinality (Unwired / Assumed / Proved / Surrogate). -/
def cmExceptionContinuumLatticeCardinality : Nat := 4

theorem cm_exception_continuum_lattice_cardinality_four :
    cmExceptionContinuumLatticeCardinality = 4 := rfl

theorem cm_exception_continuum_lattice_not_118_squared :
    cmExceptionContinuumLatticeCardinality ≠ 118 * 118 := by decide

/-- Surface tag for name-from-content (`cm_exception_continuum` / `cmexceptioncontinuum`). -/
def cmExceptionContinuumSurface : String := "cm_exception_continuum_surface"

theorem cm_exception_continuum_surface_named :
    cmExceptionContinuumSurface ≠ "" := by decide

/-- Machine-readable cm-exception-continuum conservation marker. -/
def cmExceptionContinuumMarker : String :=
  "chem_int_cross_cm_exception_continuum_conservation_v1"

theorem cm_exception_continuum_marker_named :
    cmExceptionContinuumMarker ≠ "" := by decide

/-- Row stem pin for name-from-content (`cm_exception_continuum`). -/
def cmExceptionContinuumRowStem : String := "cm_exception_continuum"

theorem cm_exception_continuum_row_stem_named :
    cmExceptionContinuumRowStem = "cm_exception_continuum" := rfl

/-- North-star §2 class-14 cm_exception_continuum pattern index. -/
def class14CmExceptionContinuumPatternIndex : Nat := 14

theorem class14_cm_exception_continuum_pattern_index_fourteen :
    class14CmExceptionContinuumPatternIndex = 14 := rfl

/-- Cross-classifier X29 row id pin. -/
def crossClassifierOccupancyEngineSortRowId : String := "X29"

theorem cross_classifier_cm_exception_continuum_row_named :
    crossClassifierOccupancyEngineSortRowId = "X29" := rfl

def patternClassCmExceptionContinuumTag : String := "occupancy_engine_sort"

def northStarClass14CmExceptionContinuumTag : String := "X29 occupancy engine sort"

theorem pattern_class_cm_exception_continuum_tag_named :
    patternClassCmExceptionContinuumTag ≠ "" := by decide

theorem north_star_class_14_cm_exception_continuum_tag_named :
    northStarClass14CmExceptionContinuumTag ≠ "" := by decide

/-- §2 pattern class cardinality (north-star pinned — not 118²). -/
def patternClassCardinality : Nat := 25

theorem pattern_class_cardinality_twenty_five : patternClassCardinality = 25 := rfl

theorem pattern_class_not_118_squared : patternClassCardinality ≠ 118 * 118 := by decide

def patternClassIndexValid (i : Nat) : Bool := i < patternClassCardinality

theorem cm_exception_continuum_class_index_valid :
    patternClassIndexValid class14CmExceptionContinuumPatternIndex = true := by decide

/-- IUPAC periodic-table cardinality (Z=1..118). -/
def iupacTableCardinality : Nat := 118

theorem iupac_table_cardinality_118 : iupacTableCardinality = 118 := rfl

/-- Curium Z=96 — host assemblage witness element pin. -/
def curiumAtomicNumberZ : Nat := 96

theorem curium_atomic_number_z_is_96 : curiumAtomicNumberZ = 96 := rfl

def curiumZValid : Bool :=
  0 < curiumAtomicNumberZ && curiumAtomicNumberZ ≤ iupacTableCardinality

theorem curium_z_valid_true : curiumZValid = true := by decide

/-- Forbidden Z=119 smuggle — not in IUPAC table. -/
def forbiddenZ119Smuggle : Nat := 119

theorem forbidden_z119_not_in_iupac_table :
    forbiddenZ119Smuggle > iupacTableCardinality := by decide

/-- Cm Z=96 occupancy pins — observed vs Madelung predicted (qlattice SSOT). -/
def cmElementSymbol : String := "Cm"

def cmObservedOccupancyTag : String := "5f76d17s2"

def cmPredictedOccupancyTag : String := "5f87s2"

def cmObservedSubshellNotation : String :=
  "1s22s22p63s23p64s23d104p65s24d105p66s24f145d106p67s25f76d1"

def cmPredictedSubshellNotation : String :=
  "1s22s22p63s23p64s23d104p65s24d105p66s24f145d106p67s25f8"

def gdHomologObservedOccupancyTag : String := "4f75d16s2"

/-- Gd Z=64 homolog — period-6 f-block contrast, not Cm occupancy copy. -/
def gadoliniumHomologZ : Nat := 64

theorem gadolinium_homolog_z_is_64 : gadoliniumHomologZ = 64 := rfl

def gadoliniumAtomicNumberZ : Nat := 64

theorem gadolinium_atomic_number_z_is_64 : gadoliniumAtomicNumberZ = 64 := rfl

def gadoliniumHomologObservedSubshellNotation : String :=
  "1s22s22p63s23p64s23d104p65s24d105p66s24f75d1"

theorem cm_element_symbol_nonempty : cmElementSymbol ≠ "" := by decide

theorem cm_observed_occupancy_tag_nonempty : cmObservedOccupancyTag ≠ "" := by decide

theorem cm_predicted_occupancy_tag_nonempty : cmPredictedOccupancyTag ≠ "" := by decide

theorem cm_observed_ne_predicted_occupancy :
    cmObservedOccupancyTag ≠ cmPredictedOccupancyTag := by decide

theorem cm_observed_ne_predicted_subshell :
    cmObservedSubshellNotation ≠ cmPredictedSubshellNotation := by decide

theorem cm_homolog_occupancy_not_copy :
    cmObservedOccupancyTag ≠ gdHomologObservedOccupancyTag := by decide

theorem gd_homolog_occupancy_tag_named :
    gdHomologObservedOccupancyTag = "4f75d16s2" := rfl

theorem cm_gd_homolog_subshell_not_copy :
    cmObservedSubshellNotation ≠ gadoliniumHomologObservedSubshellNotation := by decide

def occupancyEngineSortBucketTag : String := "actinide_exception"

theorem occupancy_engine_sort_bucket_tag_named :
    occupancyEngineSortBucketTag = "actinide_exception" := rfl

def cmExceptionContinuumFactorTag : String := "occupancy_engine_sort"

def occupancyEngineSortChannelTag : String := "occupancy_engine_sort"

def observedOverrideChannelTag : String := "observed_override"

theorem cm_exception_continuum_factor_tag_named :
    cmExceptionContinuumFactorTag ≠ "" := by decide

theorem occupancy_engine_sort_channel_tag_named :
    occupancyEngineSortChannelTag ≠ "" := by decide

theorem observed_override_channel_tag_named :
    observedOverrideChannelTag ≠ "" := by decide

/-- CmExceptionContinuum product channel slot — concurrent **product** factor, not XOR bucket. -/
inductive CmExceptionContinuumChannelSlot where
  | unwired | absent | present
  deriving DecidableEq, Repr

def cmExceptionContinuumChannelSlotIsPresent (s : CmExceptionContinuumChannelSlot) : Bool :=
  match s with | .present => true | _ => false

/-- Named occupancy engine sort / observed override / class-14 cm_exception_continuum product channels. -/
inductive CmExceptionContinuumProductChannel where
  | occupancyEngineSort | observedOverride | actinideExceptionContinuum
  deriving DecidableEq, Repr

def cmExceptionContinuumProductChannelCount : Nat := 3

theorem cm_exception_continuum_product_channel_count_three :
    cmExceptionContinuumProductChannelCount = 3 := rfl

def cmExceptionContinuumProductChannelIndex : CmExceptionContinuumProductChannel → Nat
  | .occupancyEngineSort => 0
  | .observedOverride => 1
  | .actinideExceptionContinuum => 2

theorem cmec_channel_occupancy_engine_sort_idx_is_0 :
    cmExceptionContinuumProductChannelIndex .occupancyEngineSort = 0 := rfl

theorem cmec_channel_observed_override_idx_is_1 :
    cmExceptionContinuumProductChannelIndex .observedOverride = 1 := rfl

theorem cmec_channel_actinide_exception_continuum_idx_is_2 :
    cmExceptionContinuumProductChannelIndex .actinideExceptionContinuum = 2 := rfl

/-- Class-14 cm_exception_continuum concurrent **product** bundle (north-star §3). -/
structure CmExceptionContinuumConcurrentBundle where
  channelSlots : List CmExceptionContinuumChannelSlot
  deriving DecidableEq, Repr

def cmExceptionContinuumConcurrentBundleUnwired : CmExceptionContinuumConcurrentBundle :=
  { channelSlots := List.replicate cmExceptionContinuumProductChannelCount .unwired }

def cmExceptionContinuumConcurrentBundleWithChannel (idx : Nat) (slot : CmExceptionContinuumChannelSlot)
    (b : CmExceptionContinuumConcurrentBundle) : CmExceptionContinuumConcurrentBundle :=
  if idx < b.channelSlots.length then
    { channelSlots :=
        b.channelSlots.take idx ++ [slot] ++ b.channelSlots.drop (idx + 1) }
  else b

def cmExceptionContinuumConcurrentBundleWithPresent (idx : Nat) (b : CmExceptionContinuumConcurrentBundle) :
    CmExceptionContinuumConcurrentBundle :=
  cmExceptionContinuumConcurrentBundleWithChannel idx .present b

def cmExceptionContinuumConcurrentBundleChannelAt (idx : Nat) (b : CmExceptionContinuumConcurrentBundle) :
    Option CmExceptionContinuumChannelSlot :=
  b.channelSlots.get? idx

def cmExceptionContinuumConcurrentBundleHolds (idx : Nat) (b : CmExceptionContinuumConcurrentBundle) : Bool :=
  match cmExceptionContinuumConcurrentBundleChannelAt idx b with
  | some .present => true
  | _ => false

def cmExceptionContinuumConcurrentBundlePresentCount (b : CmExceptionContinuumConcurrentBundle) : Nat :=
  b.channelSlots.foldl (fun acc s => if cmExceptionContinuumChannelSlotIsPresent s then acc + 1 else acc) 0

def cmExceptionContinuumConcurrentBundleIsConcurrentProduct (b : CmExceptionContinuumConcurrentBundle) : Bool :=
  decide (cmExceptionContinuumConcurrentBundlePresentCount b ≥ 2)

/-- Cm Z=96 occupancy engine sort + observed override + class-14 concurrent witness. -/
def cmExceptionContinuumCm96Witness : CmExceptionContinuumConcurrentBundle :=
  cmExceptionContinuumConcurrentBundleWithPresent 2
    (cmExceptionContinuumConcurrentBundleWithPresent 1
      (cmExceptionContinuumConcurrentBundleWithPresent 0
        cmExceptionContinuumConcurrentBundleUnwired))

def cmExceptionContinuumEmptyWitness : CmExceptionContinuumConcurrentBundle :=
  cmExceptionContinuumConcurrentBundleUnwired

def cmExceptionContinuumSinglePresent : CmExceptionContinuumConcurrentBundle :=
  cmExceptionContinuumConcurrentBundleWithPresent 0 cmExceptionContinuumConcurrentBundleUnwired

theorem occupancy_engine_sort_channel_present :
    cmExceptionContinuumConcurrentBundleHolds 0 cmExceptionContinuumCm96Witness = true := by decide

theorem observed_override_channel_present :
    cmExceptionContinuumConcurrentBundleHolds 1 cmExceptionContinuumCm96Witness = true := by decide

theorem class14_cm_exception_continuum_channel_present :
    cmExceptionContinuumConcurrentBundleHolds 2 cmExceptionContinuumCm96Witness = true := by decide

theorem cm96_witness_present_count_is_three :
    cmExceptionContinuumConcurrentBundlePresentCount cmExceptionContinuumCm96Witness = 3 := by decide

theorem cm96_witness_is_concurrent_product :
    cmExceptionContinuumConcurrentBundleIsConcurrentProduct cmExceptionContinuumCm96Witness = true := by decide

theorem empty_bundle_present_count_zero :
    cmExceptionContinuumConcurrentBundlePresentCount cmExceptionContinuumEmptyWitness = 0 := by decide

theorem empty_bundle_not_concurrent_product :
    cmExceptionContinuumConcurrentBundleIsConcurrentProduct cmExceptionContinuumEmptyWitness = false := by decide

theorem single_present_count_is_one :
    cmExceptionContinuumConcurrentBundlePresentCount cmExceptionContinuumSinglePresent = 1 := by decide

theorem single_present_not_concurrent_product :
    cmExceptionContinuumConcurrentBundleIsConcurrentProduct cmExceptionContinuumSinglePresent = false := by decide

/-- XOR posture — mutual exclusivity scaffold defect (must refuse). -/
inductive CmExceptionContinuumXorPosture where
  | exclusive | concurrent
  deriving DecidableEq, Repr

def cmecXorClassifierMarker : String := "chem_l0_cm_exception_continuum_xor_classifier_v1"
def cmecConcurrentProductMarker : String := "chem_int_cm_exception_continuum_product_v1"

theorem cmec_xor_marker_ne_concurrent_product_marker :
    cmecXorClassifierMarker ≠ cmecConcurrentProductMarker := by decide

def cmecXorClassifierIncompatible (claimXor : Bool) (b : CmExceptionContinuumConcurrentBundle) : Bool :=
  claimXor && cmExceptionContinuumConcurrentBundleIsConcurrentProduct b

theorem cmec_xor_refuse_on_cm96_witness :
    cmecXorClassifierIncompatible true cmExceptionContinuumCm96Witness = true := by decide

def cmecProductNotXor : Bool :=
  cmExceptionContinuumConcurrentBundleIsConcurrentProduct cmExceptionContinuumCm96Witness &&
  cmecXorClassifierIncompatible true cmExceptionContinuumCm96Witness

theorem cmec_product_not_xor_true : cmecProductNotXor = true := by decide

/-- Claim bar for proved-without-bar refuse (fail-closed). -/
inductive CmExceptionContinuumBarPresence where
  | absent | present
  deriving DecidableEq, Repr

structure CmExceptionContinuumClaimBar where
  presence : CmExceptionContinuumBarPresence
  defectTotal : Nat
  deriving DecidableEq, Repr

def cmExceptionContinuumClaimBarAbsent : CmExceptionContinuumClaimBar :=
  { presence := .absent, defectTotal := 0 }

def cmExceptionContinuumClaimBarZeroDefect : CmExceptionContinuumClaimBar :=
  { presence := .present, defectTotal := 0 }

def cmecClaimBarZeroDefect (b : CmExceptionContinuumClaimBar) : Bool :=
  match b.presence with
  | .absent => false
  | .present => b.defectTotal == 0

theorem cmec_claim_bar_zero_defect_true :
    cmecClaimBarZeroDefect cmExceptionContinuumClaimBarZeroDefect = true := by decide

theorem cmec_claim_bar_absent_not_zero_defect :
    cmecClaimBarZeroDefect cmExceptionContinuumClaimBarAbsent = false := by decide

/-- Verdict for class-14 **cm_exception_continuum** close (fail-closed). -/
inductive CmExceptionContinuumVerdict where
  | unwiredOk
  | namedOk
  | designOk
  | trivialRefuse
  | xorRefuse
  | greenInventRefuse
  | provedWithoutBarRefuse
  | productionWiredRefuse
  | parallelCmExceptionContinuumAxiomRefuse
  | speciesIdSmuggleRefuse
  | extraElementIdRefuse
  | extraCmExceptionContinuumForceRefuse
  | tpFloatPinRefuse
  deriving DecidableEq, Repr

def cmExceptionContinuumVerdictOk (v : CmExceptionContinuumVerdict) : Bool :=
  match v with
  | .unwiredOk | .namedOk | .designOk => true
  | _ => false

def cmExceptionContinuumBundleNontrivial (b : CmExceptionContinuumConcurrentBundle) : Bool :=
  decide (cmExceptionContinuumConcurrentBundlePresentCount b > 0)

def evaluateCmExceptionContinuumBundle
    (modality : CmExceptionContinuumModality)
    (b : CmExceptionContinuumConcurrentBundle)
    (_bar : CmExceptionContinuumClaimBar)
    (claimXorClassifier : Bool)
    (claimPhysicsGreen : Bool)
    (claimProved : Bool) : CmExceptionContinuumVerdict :=
  if claimPhysicsGreen then
    .greenInventRefuse
  else if claimProved then
    .provedWithoutBarRefuse
  else if !cmExceptionContinuumBundleNontrivial b then
    .trivialRefuse
  else if cmecXorClassifierIncompatible claimXorClassifier b then
    .xorRefuse
  else
    match modality with
    | .unwired =>
        if cmExceptionContinuumConcurrentBundleIsConcurrentProduct b then .namedOk else .designOk
    | .assumed | .surrogate => .designOk
    | .proved => .provedWithoutBarRefuse

def evaluateCmExceptionContinuumClose
    (modality : CmExceptionContinuumModality)
    (claimPhysicsGreen : Bool)
    (claimProductionWired : Bool) : CmExceptionContinuumVerdict :=
  if claimPhysicsGreen then
    .greenInventRefuse
  else if claimProductionWired then
    .productionWiredRefuse
  else
    match modality with
    | .unwired => .unwiredOk
    | .assumed | .proved | .surrogate => .namedOk

def cmExceptionContinuumAuthorized (claimPhysicsGreen : Bool) (claimProductionWired : Bool) : Bool :=
  match evaluateCmExceptionContinuumClose .proved claimPhysicsGreen claimProductionWired with
  | .namedOk => true
  | _ => false

/-- Conservation law witnesses — four laws, open at Unwired. -/
inductive CmExceptionContinuumConservationLaw where
  | conserved | namedOk | trivialRefuse | greenInventRefuse
  deriving DecidableEq, Repr

def cmExceptionContinuumConservationLawCount : Nat := 4

theorem cmec_conservation_law_count_is_four :
    cmExceptionContinuumConservationLawCount = 4 := rfl

inductive CmExceptionContinuumConservationLawWitness where
  | open | proved
  deriving DecidableEq, Repr

def evaluateCmecConservationLawWitness
    (_law : CmExceptionContinuumConservationLaw)
    (m : CmExceptionContinuumModality) : CmExceptionContinuumConservationLawWitness :=
  match m with
  | .unwired | .assumed | .surrogate => .open
  | .proved => .proved

def sampleCmExceptionContinuumCm96Bundle : CmExceptionContinuumConcurrentBundle :=
  cmExceptionContinuumCm96Witness

def sampleTrivialUnwiredBundle : CmExceptionContinuumConcurrentBundle :=
  cmExceptionContinuumEmptyWitness

def unwiredDesignOk : Bool :=
  decide (evaluateCmExceptionContinuumClose .unwired false false = .unwiredOk)

def cmExceptionContinuumCm96ConcurrentOk : Bool :=
  decide (evaluateCmExceptionContinuumBundle .unwired sampleCmExceptionContinuumCm96Bundle
      cmExceptionContinuumClaimBarAbsent false false false = .namedOk ∧
    cmExceptionContinuumConcurrentBundleIsConcurrentProduct sampleCmExceptionContinuumCm96Bundle = true ∧
    curiumAtomicNumberZ = 96 ∧
    cmObservedOccupancyTag = "5f76d17s2")

def class14CmExceptionContinuumPatternIndexOk : Bool :=
  decide (class14CmExceptionContinuumPatternIndex = 14 ∧
    patternClassIndexValid class14CmExceptionContinuumPatternIndex = true)

def concurrentProductNotXorOk : Bool :=
  decide (cmecProductNotXor = true ∧
    cmExceptionContinuumConcurrentBundlePresentCount cmExceptionContinuumCm96Witness = 3)

def xorMutuallyExclusiveRefuse : Bool :=
  decide (evaluateCmExceptionContinuumBundle .unwired sampleCmExceptionContinuumCm96Bundle
      cmExceptionContinuumClaimBarAbsent true false false = .xorRefuse)

def greenInventCmExceptionContinuumRefuse : Bool :=
  decide (evaluateCmExceptionContinuumClose .unwired true false = .greenInventRefuse ∧
    evaluateCmExceptionContinuumBundle .unwired sampleCmExceptionContinuumCm96Bundle
      cmExceptionContinuumClaimBarAbsent false true false = .greenInventRefuse)

def productionWiredRefuse : Bool :=
  decide (evaluateCmExceptionContinuumClose .proved false true = .productionWiredRefuse)

def trivialBundleRefuse : Bool :=
  decide (evaluateCmExceptionContinuumBundle .unwired sampleTrivialUnwiredBundle
      cmExceptionContinuumClaimBarAbsent false false false = .trivialRefuse)

def provedWithoutBarRefuse : Bool :=
  decide (evaluateCmExceptionContinuumBundle .unwired sampleCmExceptionContinuumCm96Bundle
      cmExceptionContinuumClaimBarAbsent false false true = .provedWithoutBarRefuse)

/-- PATTERN-00 class-14 **cm_exception_continuum** is **not** claimed Proved on the knowing scaffold. -/
def cmExceptionContinuumProved : Bool := false

theorem cm_exception_continuum_proved_false :
    cmExceptionContinuumProved = false := rfl

def cmExceptionContinuumProductionWired : Bool := false

theorem cm_exception_continuum_production_not_wired :
    cmExceptionContinuumProductionWired = false := rfl

def not118SquaredGreenTable : Bool := true

theorem not_118_squared_green_table : not118SquaredGreenTable = true := rfl

def cmExceptionContinuumLandauerLawPin : String := "LandauerLaw.physicalSecondLaw"

theorem cm_exception_continuum_landauer_law_pin_named :
    cmExceptionContinuumLandauerLawPin = "LandauerLaw.physicalSecondLaw" := rfl

def cmExceptionContinuumSecondLawConservationFramed : Bool := true

theorem cm_exception_continuum_second_law_conservation_framed :
    cmExceptionContinuumSecondLawConservationFramed = true := rfl

def wave100LibRsWired : Bool := false
def wave100EosRsWired : Bool := false
def wave100NanoWired : Bool := false

def wave100NotWired : Bool :=
  !wave100LibRsWired && !wave100EosRsWired && !wave100NanoWired

theorem wave100_not_wired : wave100NotWired = true := rfl

def cmExceptionContinuumAuthority : String :=
  "umst/umst-chem/src/x_rows/occupancy_engine_sort.rs"

def parallelCmExceptionAxiomTag : String := "26th_periodic_table_axiom"

def homologCopyFraming : String := "gd_z64_occupancy_copied_onto_cm_z96"

def cmExceptionContinuumFraming : String :=
  "second_law_conservation_cm_exception_continuum_occupancy_engine_sort_one_axiom"

theorem cm_exception_continuum_not_26th_axiom :
    cmExceptionContinuumFraming ≠ parallelCmExceptionAxiomTag := by decide

def parallelCmExceptionContinuumAxiomRefuse : Bool :=
  decide (cmExceptionContinuumAuthority ≠ parallelCmExceptionAxiomTag ∧
    cmExceptionContinuumProved = false)

def speciesIdSmuggleRefuse : Bool :=
  decide (cmExceptionContinuumFraming ≠ homologCopyFraming ∧
    curiumAtomicNumberZ = 96 ∧
    cmObservedOccupancyTag = "5f76d17s2")

def extraElementIdSmuggleFraming : String := "cm_exception_as_extra_element_id_smuggle"

def extraElementIdRefuse : Bool :=
  decide (cmExceptionContinuumFraming ≠ extraElementIdSmuggleFraming ∧
    forbiddenZ119Smuggle > iupacTableCardinality ∧
    curiumAtomicNumberZ = 96)

def extraOccupancyAxiomFraming : String :=
  "extra_cm_exception_continuum_force_axiom_minted_as_26th_law"

def occupancyEngineSortAuthority : String :=
  "umst/umst-chem/src/cm_exception_continuum_barrier.rs"

def extraCmExceptionContinuumForceRefuse : Bool :=
  decide (cmExceptionContinuumFraming ≠ extraOccupancyAxiomFraming ∧
    occupancyEngineSortAuthority ≠ "")

def madelungFamilySmuggleFraming : String :=
  "madelung_family_only_no_observed_override"

def madelungWitnessAuthority : String :=
  "umst/umst-chem/src/x_rows/madelung_witness.rs"

def madelungFamilySmuggleRefuse : Bool :=
  decide (cmExceptionContinuumFraming ≠ madelungFamilySmuggleFraming ∧
    cmObservedOccupancyTag ≠ cmPredictedOccupancyTag)

def tpFloatPinFraming : String :=
  "bare_298_15_k_1_atm_float_pins_on_cm_exception_continuum_scaffold"

def tpFloatPinRefuse : Bool :=
  decide (cmExceptionContinuumFraming ≠ tpFloatPinFraming ∧
    occupancyEngineSortChannelTag = "occupancy_engine_sort")

def madelungWalkFraming : String := "madelung_walk_predicted_not_observed_override"

def actinideExceptionNamedObject : String :=
  "interact_restriction_on_cm_exception_continuum_morphism"

def tstPriorArtNotNamedObject : Bool :=
  decide (actinideExceptionNamedObject ≠ madelungWalkFraming ∧
    observedOverrideChannelTag = "observed_override")

def occupancyEngineSortFraming : String := "occupancy_engine_sort_not_extra_force"

def interactRestrictionNotExtraForceRefuse : Bool :=
  decide (occupancyEngineSortFraming ≠ extraOccupancyAxiomFraming ∧
    occupancyEngineSortChannelTag = "occupancy_engine_sort")

def cmGdHomologNotCopy : Bool :=
  decide (curiumAtomicNumberZ = 96 ∧
    gadoliniumAtomicNumberZ = 64 ∧
    cmObservedOccupancyTag ≠ gdHomologObservedOccupancyTag)

def cmExceptionContinuumQlatticeAuthority : String := "umst/umst-chem/src/qlattice.rs"

def homologExceptionNotCopyAuthority : String :=
  "umst/umst-chem/src/x_rows/homolog_exception_not_copy.rs"

def dBlockOccupancyExceptionsAuthority : String :=
  "umst/umst-formal-double-slit/Coq/ChemConstants/ActinideOccupancyExceptions.v"

def occupancyEngineSortExceptionSetsCellId : String := "CHEM-INT-CROSS-OCCUPANCY-EXCEPTION-SETS"

def homologExceptionNotCopyCellId : String := "CHEM-INT-CROSS-HOMOLOG-EXCEPTION-NOT-COPY"

def cmExceptionContinuumLatticeScaffold : Bool :=
  unwiredDesignOk &&
    cmExceptionContinuumCm96ConcurrentOk &&
    class14CmExceptionContinuumPatternIndexOk &&
    concurrentProductNotXorOk &&
    xorMutuallyExclusiveRefuse &&
    greenInventCmExceptionContinuumRefuse &&
    parallelCmExceptionContinuumAxiomRefuse &&
    speciesIdSmuggleRefuse &&
    extraElementIdRefuse &&
    extraCmExceptionContinuumForceRefuse &&
    madelungFamilySmuggleRefuse &&
    tpFloatPinRefuse &&
    trivialBundleRefuse &&
    productionWiredRefuse &&
    provedWithoutBarRefuse &&
    tstPriorArtNotNamedObject &&
    interactRestrictionNotExtraForceRefuse &&
    cmGdHomologNotCopy &&
    wave100NotWired

theorem cm_exception_continuum_lattice_scaffold_true :
    cmExceptionContinuumLatticeScaffold = true := by native_decide

inductive CmExceptionContinuumFiber where
  | quantumKnowing | mesoActing
  deriving DecidableEq, Repr

def cmExceptionContinuumFiberOk (f : CmExceptionContinuumFiber) : Bool :=
  match f with | .quantumKnowing => true | .mesoActing => false

theorem cm_exception_continuum_knowing_fiber_ok :
    cmExceptionContinuumFiberOk .quantumKnowing = true := rfl

theorem cm_exception_continuum_meso_acting_not_ok :
    cmExceptionContinuumFiberOk .mesoActing = false := rfl

def cmExceptionContinuumCellId : String :=
  "CHEM-FORMAL-Q-LEAN-CM-EXCEPTION-CONTINUUM"

def cmExceptionContinuumNonClaim : String :=
  "CHEM-FORMAL-Q-LEAN-CM-EXCEPTION-CONTINUUM CmExceptionContinuumModality Unwired Assumed Proved Surrogate four-step lattice cmExceptionContinuumProved false evaluateCmExceptionContinuumBundle evaluateCmExceptionContinuumClose named Cm Z=96 actinide occupancy exception continuum X29 occupancy engine sort observed override actinide exception concurrent product identity conserved present ge 2 product not XOR xor mutually exclusive refuse parallel cm exception axiom refuse homolog copy smuggle refuse extra element id Z=119 refuse extra occupancy axiom refuse Gd Z=64 homolog not Cm 4f7 5d1 6s2 copy Unwired one axiom second law conservation not 118 squared GREEN table not meso acting not physics GREEN not production_wired"

def cmExceptionContinuumPhysicsGreenAuthorized : Prop := False

theorem cm_exception_continuum_physics_green_false :
    ¬ cmExceptionContinuumPhysicsGreenAuthorized := id

structure CmExceptionContinuumProbe where
  cellIdNamed : Bool
  unwired : Bool
  physicsGreenRefused : Bool
  notProved : Bool
  class14Index : Bool
  cm96HostWitness : Bool
  occupancyEngineSortObservedOverrideProduct : Bool
  concurrentNotXor : Bool
  cm96WitnessOk : Bool
  xorRefuse : Bool
  greenInventRefuse : Bool
  parallelAxiomRefuse : Bool
  speciesIdSmuggleRefuse : Bool
  extraElementIdRefuse : Bool
  extraCmExceptionContinuumForceRefuse : Bool
  madelungFamilySmuggleRefuse : Bool
  tpFloatPinRefuse : Bool
  productionWiredRefuse : Bool
  knowingFiberOk : Bool
  wave100NotWired : Bool
  intAuthorityCited : Bool
  gdHomologNotCopy : Bool
  deriving DecidableEq, Repr

def cmExceptionContinuumProbe : CmExceptionContinuumProbe :=
  { cellIdNamed :=
      decide (cmExceptionContinuumCellId = "CHEM-FORMAL-Q-LEAN-CM-EXCEPTION-CONTINUUM")
    unwired := decide (cmExceptionContinuumModalityCurrent = .unwired)
    physicsGreenRefused := true
    notProved := !cmExceptionContinuumProved
    class14Index := decide (class14CmExceptionContinuumPatternIndex = 14)
    cm96HostWitness := decide (curiumAtomicNumberZ = 96)
    occupancyEngineSortObservedOverrideProduct := decide (occupancyEngineSortChannelTag = "occupancy_engine_sort" ∧
      observedOverrideChannelTag = "observed_override" ∧
      cmExceptionContinuumFactorTag = "occupancy_engine_sort")
    concurrentNotXor := cmecProductNotXor
    cm96WitnessOk := cmExceptionContinuumCm96ConcurrentOk
    xorRefuse := xorMutuallyExclusiveRefuse
    greenInventRefuse := greenInventCmExceptionContinuumRefuse
    parallelAxiomRefuse := parallelCmExceptionContinuumAxiomRefuse
    speciesIdSmuggleRefuse := speciesIdSmuggleRefuse
    extraElementIdRefuse := extraElementIdRefuse
    extraCmExceptionContinuumForceRefuse := extraCmExceptionContinuumForceRefuse
    madelungFamilySmuggleRefuse := madelungFamilySmuggleRefuse
    tpFloatPinRefuse := tpFloatPinRefuse
    productionWiredRefuse := productionWiredRefuse
    knowingFiberOk := cmExceptionContinuumFiberOk .quantumKnowing
    wave100NotWired := wave100NotWired
    intAuthorityCited := cmExceptionContinuumAuthority ≠ ""
    gdHomologNotCopy := cmGdHomologNotCopy }

def cmExceptionContinuumHonest : Bool :=
  let p := cmExceptionContinuumProbe
  p.cellIdNamed &&
    p.unwired &&
    p.physicsGreenRefused &&
    p.notProved &&
    p.class14Index &&
    p.cm96HostWitness &&
    p.occupancyEngineSortObservedOverrideProduct &&
    p.concurrentNotXor &&
    p.cm96WitnessOk &&
    p.xorRefuse &&
    p.greenInventRefuse &&
    p.parallelAxiomRefuse &&
    p.speciesIdSmuggleRefuse &&
    p.extraElementIdRefuse &&
    p.extraCmExceptionContinuumForceRefuse &&
    p.madelungFamilySmuggleRefuse &&
    p.tpFloatPinRefuse &&
    p.productionWiredRefuse &&
    p.knowingFiberOk &&
    p.wave100NotWired &&
    p.intAuthorityCited &&
    p.gdHomologNotCopy &&
    cmExceptionContinuumLatticeScaffold

theorem cm_exception_continuum_honest_true :
    cmExceptionContinuumHonest = true := by native_decide

def cmExceptionContinuumAxiom : Bool :=
  not118SquaredGreenTable &&
    cmExceptionContinuumSecondLawConservationFramed &&
    cmExceptionContinuumLatticeScaffold &&
    cmExceptionContinuumHonest &&
    !cmExceptionContinuumProved &&
    !cmExceptionContinuumProductionWired &&
    !wave100LibRsWired &&
    !wave100EosRsWired &&
    !wave100NanoWired &&
    decide (cmExceptionContinuumFraming =
      "second_law_conservation_cm_exception_continuum_occupancy_engine_sort_one_axiom")

theorem cm_exception_continuum_axiom :
    cmExceptionContinuumAxiom = true := by native_decide

theorem cm_exception_continuum_modality_unwired :
    cmExceptionContinuumModalityCurrent = .unwired := rfl

theorem unwired_close_without_production_wiring :
    evaluateCmExceptionContinuumClose .unwired false false = .unwiredOk := rfl

theorem cm96_witness_named_ok :
    evaluateCmExceptionContinuumBundle .unwired sampleCmExceptionContinuumCm96Bundle
      cmExceptionContinuumClaimBarAbsent false false false = .namedOk := rfl

theorem trivial_empty_bundle_fail_closed :
    evaluateCmExceptionContinuumBundle .unwired sampleTrivialUnwiredBundle
      cmExceptionContinuumClaimBarAbsent false false false = .trivialRefuse := rfl

theorem xor_classifier_refused :
    evaluateCmExceptionContinuumBundle .unwired sampleCmExceptionContinuumCm96Bundle
      cmExceptionContinuumClaimBarAbsent true false false = .xorRefuse := rfl

theorem green_invent_refuse_unwired :
    evaluateCmExceptionContinuumClose .unwired true false = .greenInventRefuse := rfl

theorem proved_without_bar_refuse :
    evaluateCmExceptionContinuumBundle .unwired sampleCmExceptionContinuumCm96Bundle
      cmExceptionContinuumClaimBarAbsent false false true = .provedWithoutBarRefuse := rfl

theorem production_wired_refuse :
    evaluateCmExceptionContinuumClose .proved false true = .productionWiredRefuse := rfl

theorem gd_period6_homolog_not_cm_occupancy_copy :
    curiumAtomicNumberZ = 96 ∧
    gadoliniumAtomicNumberZ = 64 ∧
    cmObservedOccupancyTag = "5f76d17s2" ∧
    gdHomologObservedOccupancyTag = "4f75d16s2" ∧
    cmObservedOccupancyTag ≠ gdHomologObservedOccupancyTag ∧
    cmExceptionContinuumProved = false :=
  ⟨rfl, rfl, rfl, rfl, cm_homolog_occupancy_not_copy, cm_exception_continuum_proved_false⟩

theorem cm_exception_continuum_honest_bundle :
    cmExceptionContinuumProved = false ∧
    cmExceptionContinuumProductionWired = false ∧
    not118SquaredGreenTable = true ∧
    cmExceptionContinuumSecondLawConservationFramed = true ∧
    evaluateCmExceptionContinuumClose .unwired false false = .unwiredOk ∧
    evaluateCmExceptionContinuumBundle .unwired sampleCmExceptionContinuumCm96Bundle
      cmExceptionContinuumClaimBarAbsent false false false = .namedOk ∧
    evaluateCmExceptionContinuumBundle .unwired sampleTrivialUnwiredBundle
      cmExceptionContinuumClaimBarAbsent false false false = .trivialRefuse ∧
    evaluateCmExceptionContinuumBundle .unwired sampleCmExceptionContinuumCm96Bundle
      cmExceptionContinuumClaimBarAbsent true false false = .xorRefuse ∧
    evaluateCmExceptionContinuumClose .unwired true false = .greenInventRefuse ∧
    cmecProductNotXor = true ∧
    curiumAtomicNumberZ = 96 ∧
    class14CmExceptionContinuumPatternIndex = 14 ∧
    cmExceptionContinuumAxiom = true :=
  ⟨rfl, rfl, not_118_squared_green_table, cm_exception_continuum_second_law_conservation_framed,
    unwired_close_without_production_wiring, cm96_witness_named_ok,
    trivial_empty_bundle_fail_closed, xor_classifier_refused, green_invent_refuse_unwired,
    cmec_product_not_xor_true, curium_atomic_number_z_is_96,
    class14_cm_exception_continuum_pattern_index_fourteen, cm_exception_continuum_axiom⟩

end UMST.Chem
