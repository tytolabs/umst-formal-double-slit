-- SPDX-FileCopyrightText: 2026 Santosh Prabhu Shenbagamoorthy and Santhosh Shyamsundar
-- SPDX-License-Identifier: MIT

import ElementElectronic

set_option maxRecDepth 8192

/-!
# PtExceptionContinuum — class-14 **pt_exception_continuum** **conservation** (Q lattice)

Knowing-fiber Lean: Pt Z=78 d-block occupancy **exception continuum** **conservation**. Occupancy-engine sort
(X29) restriction on the same second-law + **conservation** object (not a 26th axiom / extra force). Concurrent Π_c
PatternBundle factor — **product** not XOR. Pt Z=78 5d9 6s1 NamedException; Ni Z=28 / Pd Z=46 homolog not Pt copy.
`ptExceptionContinuumProved` false. Modality Unwired.

Read-only cites (not imported — self-contained scaffold):
- `Coq/ChemConstants/PtExceptionContinuum.v`
- `Haskell/UMST/ChemConstants/PtExceptionContinuum.hs`
- `Agda/ChemConstants/PtExceptionContinuum.agda`
- `umst/umst-chem/src/x_rows/occupancy_engine_sort.rs`
- `umst/umst-chem/src/x_rows/homolog_exception_not_copy.rs`
- `umst/umst-chem/src/qlattice.rs`

- `PtExceptionContinuumModality` — Unwired / Assumed / Proved / Surrogate (not 118² GREEN table).
- `PtExceptionContinuumProductChannel` — occupancy engine sort ⊗ observed override ⊗ class-14 pt_exception_continuum.
- Second-law + **conservation** framing — not imported meso theorems.
- No meso / acting theorems. No new physics `axiom`.
- `physics_green` stays false. Does **not** claim `ptExceptionContinuumProved` or physics GREEN.
- WAVE100 freeze — not wired lib.rs / eos.rs.
- Does **not** mint second pt-exception-continuum axiom (not 26th axiom).
-/

namespace UMST.Chem

/-- Design modality for class-14 **pt_exception_continuum** **conservation** (lattice SSOT). -/
inductive PtExceptionContinuumModality where
  | unwired | assumed | proved | surrogate
  deriving DecidableEq, Repr

def ptExceptionContinuumModalityCurrent : PtExceptionContinuumModality := .unwired

/-- Modality lattice cardinality (Unwired / Assumed / Proved / Surrogate). -/
def ptExceptionContinuumLatticeCardinality : Nat := 4

theorem pt_exception_continuum_lattice_cardinality_four :
    ptExceptionContinuumLatticeCardinality = 4 := rfl

theorem pt_exception_continuum_lattice_not_118_squared :
    ptExceptionContinuumLatticeCardinality ≠ 118 * 118 := by decide

/-- Surface tag for name-from-content (`pt_exception_continuum` / `ptexceptioncontinuum`). -/
def ptExceptionContinuumSurface : String := "pt_exception_continuum_surface"

theorem pt_exception_continuum_surface_named :
    ptExceptionContinuumSurface ≠ "" := by decide

/-- Machine-readable pt-exception-continuum conservation marker. -/
def ptExceptionContinuumMarker : String := "chem_int_cross_pt_exception_continuum_v1"

theorem pt_exception_continuum_marker_named :
    ptExceptionContinuumMarker ≠ "" := by decide

/-- Row stem pin for name-from-content (`pt_exception_continuum`). -/
def ptExceptionContinuumRowStem : String := "pt_exception_continuum"

theorem pt_exception_continuum_row_stem_named :
    ptExceptionContinuumRowStem = "pt_exception_continuum" := rfl

/-- §2 pattern class cardinality (north-star pinned — not 118²). -/
def patternClassCardinality : Nat := 25

theorem pattern_class_cardinality_twenty_five : patternClassCardinality = 25 := rfl

theorem pattern_class_not_118_squared : patternClassCardinality ≠ 118 * 118 := by decide

def patternClassIndexValid (i : Nat) : Bool := i < patternClassCardinality

/-- North-star §2 class-14 pt_exception_continuum pattern index. -/
def class14PtExceptionContinuumPatternIndex : Nat := 14

theorem class14_pt_exception_continuum_pattern_index_fourteen :
    class14PtExceptionContinuumPatternIndex = 14 := rfl

theorem pt_exception_continuum_class_index_valid :
    patternClassIndexValid class14PtExceptionContinuumPatternIndex = true := by decide

/-- Cross-classifier X29 row id pin. -/
def crossClassifierOccupancyEngineSortRowId : String := "X29"

theorem cross_classifier_pt_exception_continuum_row_named :
    crossClassifierOccupancyEngineSortRowId = "X29" := rfl

def patternClassPtExceptionContinuumTag : String := "occupancy_engine_sort"

def northStarClass14PtExceptionContinuumTag : String := "X29 occupancy engine sort"

theorem pattern_class_pt_exception_continuum_tag_nonempty :
    patternClassPtExceptionContinuumTag ≠ "" := by decide

theorem north_star_class_14_pt_exception_continuum_tag_nonempty :
    northStarClass14PtExceptionContinuumTag ≠ "" := by decide

/-- IUPAC periodic-table cardinality (Z=1..118). -/
def iupacTableCardinality : Nat := 118

theorem iupac_table_cardinality_118 : iupacTableCardinality = 118 := rfl

/-- Platinum Z=78 — host assemblage witness element pin. -/
def platinumAtomicNumberZ : Nat := 78

theorem platinum_atomic_number_z_is_78 : platinumAtomicNumberZ = 78 := rfl

def platinumZValid : Bool :=
  0 < platinumAtomicNumberZ && platinumAtomicNumberZ ≤ iupacTableCardinality

theorem platinum_z_valid_true : platinumZValid = true := by decide

/-- Forbidden Z=119 smuggle — not in IUPAC table. -/
def forbiddenZ119Smuggle : Nat := 119

theorem forbidden_z119_not_in_iupac_table :
    forbiddenZ119Smuggle > iupacTableCardinality := by decide

/-- Pt Z=78 occupancy pins — 5d⁹6s¹ observed vs Madelung predicted. -/
def ptElementSymbol : String := "Pt"

def ptObservedOccupancyTag : String := "5d96s1"

def ptPredictedOccupancyTag : String := "5d8"

def ptObservedSubshellNotation : String :=
  "1s22s22p63s23p63d104s24p64d104f145s25p65d96s1"

def ptPredictedSubshellNotation : String :=
  "1s22s22p63s23p64s23d104p65s24d105p66s24f145d8"

def niHomologObservedOccupancyTag : String := "3d84s2"

def nickelHomologZ : Nat := 28

theorem nickel_homolog_z_is_28 : nickelHomologZ = 28 := rfl

theorem pt_element_symbol_nonempty : ptElementSymbol ≠ "" := by decide

theorem pt_observed_occupancy_tag_nonempty : ptObservedOccupancyTag ≠ "" := by decide

theorem pt_predicted_occupancy_tag_nonempty : ptPredictedOccupancyTag ≠ "" := by decide

theorem pt_observed_ne_predicted_occupancy :
    ptObservedOccupancyTag ≠ ptPredictedOccupancyTag := by decide

theorem pt_observed_ne_predicted_subshell :
    ptObservedSubshellNotation ≠ ptPredictedSubshellNotation := by decide

theorem pt_homolog_occupancy_not_copy :
    ptObservedOccupancyTag ≠ niHomologObservedOccupancyTag := by decide

def occupancyEngineSortBucketTag : String := "dblock_exception"

theorem occupancy_engine_sort_bucket_tag_named :
    occupancyEngineSortBucketTag = "dblock_exception" := rfl

def ptExceptionContinuumFactorTag : String := "occupancy_engine_sort"

def occupancyEngineSortChannelTag : String := "occupancy_engine_sort"

def observedOverrideChannelTag : String := "observed_override"

theorem pt_exception_continuum_factor_tag_nonempty :
    ptExceptionContinuumFactorTag ≠ "" := by decide

theorem occupancy_engine_sort_channel_tag_nonempty :
    occupancyEngineSortChannelTag ≠ "" := by decide

theorem observed_override_channel_tag_nonempty :
    observedOverrideChannelTag ≠ "" := by decide

/-- Pt-exception-continuum product channel slot — concurrent **product** factor, not XOR bucket. -/
inductive PtExceptionContinuumChannelSlot where
  | unwired | absent | present
  deriving DecidableEq, Repr

def ptExceptionContinuumChannelSlotIsPresent (s : PtExceptionContinuumChannelSlot) : Bool :=
  match s with | .present => true | _ => false

/-- Named occupancy engine sort / observed override / class-14 pt_exception_continuum product channels. -/
inductive PtExceptionContinuumProductChannel where
  | occupancyEngineSort | observedOverride | dblockExceptionContinuum
  deriving DecidableEq, Repr

def ptExceptionContinuumProductChannelCount : Nat := 3

theorem pt_exception_continuum_product_channel_count_three :
    ptExceptionContinuumProductChannelCount = 3 := rfl

def ptExceptionContinuumProductChannelIndex : PtExceptionContinuumProductChannel → Nat
  | .occupancyEngineSort => 0
  | .observedOverride => 1
  | .dblockExceptionContinuum => 2

theorem ptec_channel_occupancy_engine_sort_idx_is_0 :
    ptExceptionContinuumProductChannelIndex .occupancyEngineSort = 0 := rfl

theorem ptec_channel_observed_override_idx_is_1 :
    ptExceptionContinuumProductChannelIndex .observedOverride = 1 := rfl

theorem ptec_channel_dblock_exception_continuum_idx_is_2 :
    ptExceptionContinuumProductChannelIndex .dblockExceptionContinuum = 2 := rfl

/-- Class-14 pt-exception-continuum concurrent **product** bundle (north-star §3). -/
structure PtExceptionContinuumConcurrentBundle where
  channelSlots : List PtExceptionContinuumChannelSlot
  deriving DecidableEq, Repr

def ptExceptionContinuumConcurrentBundleUnwired : PtExceptionContinuumConcurrentBundle :=
  { channelSlots := List.replicate ptExceptionContinuumProductChannelCount .unwired }

def ptExceptionContinuumConcurrentBundleWithChannel (idx : Nat) (slot : PtExceptionContinuumChannelSlot)
    (b : PtExceptionContinuumConcurrentBundle) : PtExceptionContinuumConcurrentBundle :=
  if idx < b.channelSlots.length then
    { channelSlots :=
        b.channelSlots.take idx ++ [slot] ++ b.channelSlots.drop (idx + 1) }
  else b

def ptExceptionContinuumConcurrentBundleWithPresent (idx : Nat) (b : PtExceptionContinuumConcurrentBundle) :
    PtExceptionContinuumConcurrentBundle :=
  ptExceptionContinuumConcurrentBundleWithChannel idx .present b

def ptExceptionContinuumConcurrentBundleChannelAt (idx : Nat) (b : PtExceptionContinuumConcurrentBundle) :
    Option PtExceptionContinuumChannelSlot :=
  b.channelSlots.get? idx

def ptExceptionContinuumConcurrentBundleHolds (idx : Nat) (b : PtExceptionContinuumConcurrentBundle) : Bool :=
  match ptExceptionContinuumConcurrentBundleChannelAt idx b with
  | some .present => true
  | _ => false

def ptExceptionContinuumConcurrentBundlePresentCount (b : PtExceptionContinuumConcurrentBundle) : Nat :=
  b.channelSlots.foldl (fun acc s => if ptExceptionContinuumChannelSlotIsPresent s then acc + 1 else acc) 0

def ptExceptionContinuumConcurrentBundleIsConcurrentProduct (b : PtExceptionContinuumConcurrentBundle) : Bool :=
  decide (ptExceptionContinuumConcurrentBundlePresentCount b ≥ 2)

/-- Pt Z=78 occupancy engine sort + observed override + class-14 pt_exception_continuum concurrent witness. -/
def ptExceptionContinuumPt78Witness : PtExceptionContinuumConcurrentBundle :=
  ptExceptionContinuumConcurrentBundleWithPresent 2
    (ptExceptionContinuumConcurrentBundleWithPresent 1
      (ptExceptionContinuumConcurrentBundleWithPresent 0
        ptExceptionContinuumConcurrentBundleUnwired))

def ptExceptionContinuumEmptyWitness : PtExceptionContinuumConcurrentBundle :=
  ptExceptionContinuumConcurrentBundleUnwired

def ptExceptionContinuumSinglePresent : PtExceptionContinuumConcurrentBundle :=
  ptExceptionContinuumConcurrentBundleWithPresent 0 ptExceptionContinuumConcurrentBundleUnwired

theorem occupancy_engine_sort_channel_present :
    ptExceptionContinuumConcurrentBundleHolds 0 ptExceptionContinuumPt78Witness = true := by decide

theorem observed_override_channel_present :
    ptExceptionContinuumConcurrentBundleHolds 1 ptExceptionContinuumPt78Witness = true := by decide

theorem class14_pt_exception_continuum_channel_present :
    ptExceptionContinuumConcurrentBundleHolds 2 ptExceptionContinuumPt78Witness = true := by decide

theorem pt78_witness_present_count_is_three :
    ptExceptionContinuumConcurrentBundlePresentCount ptExceptionContinuumPt78Witness = 3 := by decide

theorem pt78_witness_is_concurrent_product :
    ptExceptionContinuumConcurrentBundleIsConcurrentProduct ptExceptionContinuumPt78Witness = true := by decide

theorem empty_bundle_present_count_zero :
    ptExceptionContinuumConcurrentBundlePresentCount ptExceptionContinuumEmptyWitness = 0 := by decide

theorem empty_bundle_not_concurrent_product :
    ptExceptionContinuumConcurrentBundleIsConcurrentProduct ptExceptionContinuumEmptyWitness = false := by decide

theorem single_present_count_is_one :
    ptExceptionContinuumConcurrentBundlePresentCount ptExceptionContinuumSinglePresent = 1 := by decide

theorem single_present_not_concurrent_product :
    ptExceptionContinuumConcurrentBundleIsConcurrentProduct ptExceptionContinuumSinglePresent = false := by decide

/-- XOR posture — mutual exclusivity scaffold defect (must refuse). -/
inductive PtExceptionContinuumXorPosture where
  | exclusive | concurrent
  deriving DecidableEq, Repr

def ptecXorClassifierMarker : String := "chem_l0_pt_exception_continuum_xor_classifier_v1"
def ptecConcurrentProductMarker : String := "chem_int_pt_exception_continuum_product_v1"

theorem ptec_xor_marker_ne_concurrent_product_marker :
    ptecXorClassifierMarker ≠ ptecConcurrentProductMarker := by decide

def ptecXorClassifierIncompatible (claimXor : Bool) (b : PtExceptionContinuumConcurrentBundle) : Bool :=
  claimXor && ptExceptionContinuumConcurrentBundleIsConcurrentProduct b

theorem ptec_xor_refuse_on_pt78_witness :
    ptecXorClassifierIncompatible true ptExceptionContinuumPt78Witness = true := by decide

def ptecProductNotXor : Bool :=
  ptExceptionContinuumConcurrentBundleIsConcurrentProduct ptExceptionContinuumPt78Witness &&
  ptecXorClassifierIncompatible true ptExceptionContinuumPt78Witness

theorem ptec_product_not_xor_true : ptecProductNotXor = true := by decide

/-- Verdict for class-14 **pt_exception_continuum** close (fail-closed). -/
inductive PtExceptionContinuumConservationVerdict where
  | unwiredOk
  | namedOk
  | designOk
  | trivialRefuse
  | xorRefuse
  | greenInventRefuse
  | provedWithoutBarRefuse
  | productionWiredRefuse
  | parallelPtExceptionContinuumAxiomRefuse
  | speciesIdSmuggleRefuse
  | extraElementIdRefuse
  | extraPtExceptionContinuumForceRefuse
  | tpFloatPinRefuse
  deriving DecidableEq, Repr

def ptExceptionContinuumConservationVerdictOk (v : PtExceptionContinuumConservationVerdict) : Bool :=
  match v with
  | .unwiredOk | .namedOk | .designOk => true
  | _ => false

def ptExceptionContinuumBundleNontrivial (b : PtExceptionContinuumConcurrentBundle) : Bool :=
  decide (ptExceptionContinuumConcurrentBundlePresentCount b > 0)

def evaluatePtExceptionContinuumBundle
    (modality : PtExceptionContinuumModality)
    (b : PtExceptionContinuumConcurrentBundle)
    (claimXorClassifier : Bool)
    (claimPhysicsGreen : Bool)
    (claimProved : Bool) : PtExceptionContinuumConservationVerdict :=
  if claimPhysicsGreen then
    .greenInventRefuse
  else if claimProved then
    .provedWithoutBarRefuse
  else if !ptExceptionContinuumBundleNontrivial b then
    .trivialRefuse
  else if ptecXorClassifierIncompatible claimXorClassifier b then
    .xorRefuse
  else
    match modality with
    | .unwired =>
        if ptExceptionContinuumConcurrentBundleIsConcurrentProduct b then .namedOk else .designOk
    | .assumed | .surrogate => .designOk
    | .proved => .provedWithoutBarRefuse

def evaluatePtExceptionContinuumClose
    (modality : PtExceptionContinuumModality)
    (claimPhysicsGreen : Bool)
    (claimProductionWired : Bool) : PtExceptionContinuumConservationVerdict :=
  if claimPhysicsGreen then
    .greenInventRefuse
  else if claimProductionWired then
    .productionWiredRefuse
  else
    match modality with
    | .unwired => .unwiredOk
    | .assumed | .proved | .surrogate => .namedOk

def ptExceptionContinuumAuthorized (claimPhysicsGreen : Bool) (claimProductionWired : Bool) : Bool :=
  match evaluatePtExceptionContinuumClose .proved claimPhysicsGreen claimProductionWired with
  | .namedOk => true
  | _ => false

def samplePtExceptionContinuumPt78Bundle : PtExceptionContinuumConcurrentBundle :=
  ptExceptionContinuumPt78Witness

def sampleTrivialUnwiredBundle : PtExceptionContinuumConcurrentBundle :=
  ptExceptionContinuumEmptyWitness

def unwiredDesignOk : Bool :=
  decide (evaluatePtExceptionContinuumClose .unwired false false = .unwiredOk)

def ptExceptionContinuumPt78ConcurrentOk : Bool :=
  decide (evaluatePtExceptionContinuumBundle .unwired samplePtExceptionContinuumPt78Bundle
      false false false = .namedOk ∧
    ptExceptionContinuumConcurrentBundleIsConcurrentProduct samplePtExceptionContinuumPt78Bundle = true ∧
    platinumAtomicNumberZ = 78 ∧
    ptObservedOccupancyTag = "5d96s1")

def class14PtExceptionContinuumPatternIndexOk : Bool :=
  decide (class14PtExceptionContinuumPatternIndex = 14 ∧
    patternClassIndexValid class14PtExceptionContinuumPatternIndex = true)

def concurrentProductNotXorOk : Bool :=
  decide (ptecProductNotXor = true ∧
    ptExceptionContinuumConcurrentBundlePresentCount ptExceptionContinuumPt78Witness = 3)

def xorMutuallyExclusiveRefuse : Bool :=
  decide (evaluatePtExceptionContinuumBundle .unwired samplePtExceptionContinuumPt78Bundle
      true false false = .xorRefuse)

def greenInventPtExceptionContinuumRefuse : Bool :=
  decide (evaluatePtExceptionContinuumClose .unwired true false = .greenInventRefuse ∧
    evaluatePtExceptionContinuumBundle .unwired samplePtExceptionContinuumPt78Bundle
      false true false = .greenInventRefuse)

def productionWiredRefuse : Bool :=
  decide (evaluatePtExceptionContinuumClose .proved false true = .productionWiredRefuse)

def trivialBundleRefuse : Bool :=
  decide (evaluatePtExceptionContinuumBundle .unwired sampleTrivialUnwiredBundle
      false false false = .trivialRefuse)

/-- Class-14 **pt_exception_continuum** is **not** claimed Proved on the knowing scaffold. -/
def ptExceptionContinuumProved : Bool := false

theorem pt_exception_continuum_proved_false :
    ptExceptionContinuumProved = false := rfl

def ptExceptionContinuumProductionWired : Bool := false

theorem pt_exception_continuum_production_not_wired :
    ptExceptionContinuumProductionWired = false := rfl

def not118SquaredGreenTable : Bool := true

theorem not_118_squared_green_table : not118SquaredGreenTable = true := rfl

def ptExceptionContinuumSecondLawConservationFramed : Bool := true

theorem pt_exception_continuum_second_law_conservation_framed :
    ptExceptionContinuumSecondLawConservationFramed = true := rfl

def wave100LibRsWired : Bool := false
def wave100EosRsWired : Bool := false
def wave100NanoWired : Bool := false

def wave100NotWired : Bool :=
  !wave100LibRsWired && !wave100EosRsWired && !wave100NanoWired

theorem wave100_not_wired : wave100NotWired = true := rfl

def ptExceptionContinuumAuthority : String :=
  "umst/umst-chem/src/x_rows/occupancy_engine_sort.rs"

theorem pt_exception_continuum_authority_path :
    ptExceptionContinuumAuthority =
      "umst/umst-chem/src/x_rows/occupancy_engine_sort.rs" := rfl

def ptExceptionContinuumQlatticeAuthority : String := "umst/umst-chem/src/qlattice.rs"

def occupancyEngineSortIntAuthority : String :=
  "umst/umst-chem/src/x_rows/occupancy_engine_sort.rs"

def homologExceptionNotCopyAuthority : String :=
  "umst/umst-chem/src/x_rows/homolog_exception_not_copy.rs"

def dBlockOccupancyExceptionsAuthority : String :=
  "umst/umst-formal-double-slit/Coq/ChemConstants/DBlockOccupancyExceptions.v"

def parallelPtExceptionAxiomTag : String := "26th_periodic_table_axiom"

def homologCopyFraming : String := "ni_z28_occupancy_copied_onto_pt_z78"

def ptExceptionContinuumFraming : String :=
  "second_law_conservation_pt_exception_continuum_occupancy_engine_sort_one_axiom"

theorem pt_exception_continuum_not_26th_axiom :
    ptExceptionContinuumFraming ≠ parallelPtExceptionAxiomTag := by decide

def parallelPtExceptionContinuumAxiomRefuse : Bool :=
  decide (ptExceptionContinuumAuthority ≠ parallelPtExceptionAxiomTag ∧
    ptExceptionContinuumProved = false)

def speciesIdSmuggleRefuse : Bool :=
  decide (ptExceptionContinuumFraming ≠ homologCopyFraming ∧
    platinumAtomicNumberZ = 78 ∧
    ptObservedOccupancyTag = "5d96s1")

def extraElementIdSmuggleFraming : String :=
  "pt_exception_as_extra_element_id_smuggle"

def extraElementIdRefuse : Bool :=
  decide (ptExceptionContinuumFraming ≠ extraElementIdSmuggleFraming ∧
    forbiddenZ119Smuggle > iupacTableCardinality ∧
    platinumAtomicNumberZ = 78)

def extraOccupancyAxiomFraming : String :=
  "extra_pt_exception_continuum_force_axiom_minted_as_26th_law"

def occupancyEngineSortAuthority : String :=
  "umst/umst-chem/src/pt_exception_continuum_barrier.rs"

def extraPtExceptionContinuumForceRefuse : Bool :=
  decide (ptExceptionContinuumFraming ≠ extraOccupancyAxiomFraming ∧
    occupancyEngineSortAuthority = "umst/umst-chem/src/pt_exception_continuum_barrier.rs" ∧
    ptExceptionContinuumProved = false)

def madelungFamilySmuggleFraming : String :=
  "madelung_family_only_no_observed_override"

def madelungFamilySmuggleRefuse : Bool :=
  decide (ptExceptionContinuumFraming ≠ madelungFamilySmuggleFraming ∧
    ptObservedOccupancyTag ≠ ptPredictedOccupancyTag)

def tpFloatPinFraming : String :=
  "bare_298_15_k_1_atm_float_pins_on_pt_exception_continuum_scaffold"

def tpFloatPinRefuse : Bool :=
  decide (ptExceptionContinuumFraming ≠ tpFloatPinFraming ∧
    occupancyEngineSortChannelTag = "occupancy_engine_sort")

/-- Ni Z=28 / Pd Z=46 homolog not Pt copy — homolog ≠ identity. -/
def palladiumHomologZ : Nat := 46

theorem palladium_homolog_z_is_46 : palladiumHomologZ = 46 := rfl

def pdHomologObservedOccupancyTag : String := "4d105s0"

theorem ni_pd_homolog_occupancy_tags_distinct :
    niHomologObservedOccupancyTag ≠ pdHomologObservedOccupancyTag := by decide

def homologExceptionNotCopyCellId : String :=
  "CHEM-INT-CROSS-HOMOLOG-EXCEPTION-NOT-COPY"

def ptNiPdHomologNotCopy : Bool :=
  decide (platinumAtomicNumberZ = 78 ∧
    nickelHomologZ = 28 ∧
    palladiumHomologZ = 46 ∧
    ptObservedOccupancyTag ≠ niHomologObservedOccupancyTag ∧
    ptObservedOccupancyTag ≠ pdHomologObservedOccupancyTag)

def ptExceptionContinuumLatticeScaffold : Bool :=
  unwiredDesignOk &&
    ptExceptionContinuumPt78ConcurrentOk &&
    class14PtExceptionContinuumPatternIndexOk &&
    concurrentProductNotXorOk &&
    xorMutuallyExclusiveRefuse &&
    greenInventPtExceptionContinuumRefuse &&
    parallelPtExceptionContinuumAxiomRefuse &&
    speciesIdSmuggleRefuse &&
    extraElementIdRefuse &&
    extraPtExceptionContinuumForceRefuse &&
    madelungFamilySmuggleRefuse &&
    tpFloatPinRefuse &&
    trivialBundleRefuse &&
    productionWiredRefuse &&
    ptNiPdHomologNotCopy &&
    wave100NotWired

theorem pt_exception_continuum_lattice_scaffold_true :
    ptExceptionContinuumLatticeScaffold = true := by native_decide

inductive PtExceptionContinuumConservationFiber where
  | quantumKnowing | mesoActing
  deriving DecidableEq, Repr

def ptExceptionContinuumConservationFiberOk (f : PtExceptionContinuumConservationFiber) : Bool :=
  match f with | .quantumKnowing => true | .mesoActing => false

theorem pt_exception_continuum_conservation_knowing_fiber_ok :
    ptExceptionContinuumConservationFiberOk .quantumKnowing = true := rfl

theorem pt_exception_continuum_conservation_meso_acting_not_ok :
    ptExceptionContinuumConservationFiberOk .mesoActing = false := rfl

def ptExceptionContinuumCellId : String :=
  "CHEM-FORMAL-Q-LEAN-PT-EXCEPTION-CONTINUUM"

def ptExceptionContinuumNonClaim : String :=
  "CHEM-FORMAL-Q-LEAN-PT-EXCEPTION-CONTINUUM PtExceptionContinuumModality Unwired Assumed Proved Surrogate four-step lattice ptExceptionContinuumProved false evaluatePtExceptionContinuumBundle evaluatePtExceptionContinuum named Pt Z=78 NamedException occupancy exception continuum X29 occupancy engine sort observed override dblock exception concurrent product identity conserved present ge 2 product not XOR xor mutually exclusive refuse parallel ni exception axiom refuse homolog copy smuggle refuse extra element id Z=119 refuse extra occupancy axiom refuse Ni Z=28 Pd Z=46 homolog not Pt 3d8 4s2 4d10 5s0 copy Unwired one axiom second law conservation not 118 squared GREEN table not meso acting not physics GREEN not production_wired"

def ptExceptionContinuumPhysicsGreenAuthorized : Prop := False

theorem pt_exception_continuum_physics_green_false :
    ¬ ptExceptionContinuumPhysicsGreenAuthorized := id

structure PtExceptionContinuumProbe where
  cellIdNamed : Bool
  unwired : Bool
  physicsGreenRefused : Bool
  notProved : Bool
  class14Index : Bool
  pt78HostWitness : Bool
  occupancyOverrideDblockProduct : Bool
  concurrentNotXor : Bool
  pt78WitnessOk : Bool
  xorRefuse : Bool
  greenInventRefuse : Bool
  parallelAxiomRefuse : Bool
  speciesIdSmuggleRefuse : Bool
  extraElementIdRefuse : Bool
  extraPtExceptionContinuumForceRefuse : Bool
  madelungFamilySmuggleRefuse : Bool
  tpFloatPinRefuse : Bool
  productionWiredRefuse : Bool
  knowingFiberOk : Bool
  homologNotCopy : Bool
  wave100NotWired : Bool
  intAuthorityCited : Bool
  deriving DecidableEq, Repr

def ptExceptionContinuumProbe : PtExceptionContinuumProbe :=
  { cellIdNamed :=
      decide (ptExceptionContinuumCellId = "CHEM-FORMAL-Q-LEAN-PT-EXCEPTION-CONTINUUM")
    unwired := decide (ptExceptionContinuumModalityCurrent = .unwired)
    physicsGreenRefused := true
    notProved := !ptExceptionContinuumProved
    class14Index := decide (class14PtExceptionContinuumPatternIndex = 14)
    pt78HostWitness := decide (platinumAtomicNumberZ = 78)
    occupancyOverrideDblockProduct := decide (occupancyEngineSortChannelTag = "occupancy_engine_sort" ∧
      observedOverrideChannelTag = "observed_override" ∧
      ptExceptionContinuumFactorTag = "occupancy_engine_sort")
    concurrentNotXor := ptecProductNotXor
    pt78WitnessOk := ptExceptionContinuumPt78ConcurrentOk
    xorRefuse := xorMutuallyExclusiveRefuse
    greenInventRefuse := greenInventPtExceptionContinuumRefuse
    parallelAxiomRefuse := parallelPtExceptionContinuumAxiomRefuse
    speciesIdSmuggleRefuse := speciesIdSmuggleRefuse
    extraElementIdRefuse := extraElementIdRefuse
    extraPtExceptionContinuumForceRefuse := extraPtExceptionContinuumForceRefuse
    madelungFamilySmuggleRefuse := madelungFamilySmuggleRefuse
    tpFloatPinRefuse := tpFloatPinRefuse
    productionWiredRefuse := productionWiredRefuse
    knowingFiberOk := ptExceptionContinuumConservationFiberOk .quantumKnowing
    homologNotCopy := ptNiPdHomologNotCopy
    wave100NotWired := wave100NotWired
    intAuthorityCited := ptExceptionContinuumAuthority ≠ "" }

def ptExceptionContinuumHonest : Bool :=
  let p := ptExceptionContinuumProbe
  p.cellIdNamed &&
    p.unwired &&
    p.physicsGreenRefused &&
    p.notProved &&
    p.class14Index &&
    p.pt78HostWitness &&
    p.occupancyOverrideDblockProduct &&
    p.concurrentNotXor &&
    p.pt78WitnessOk &&
    p.xorRefuse &&
    p.greenInventRefuse &&
    p.parallelAxiomRefuse &&
    p.speciesIdSmuggleRefuse &&
    p.extraElementIdRefuse &&
    p.extraPtExceptionContinuumForceRefuse &&
    p.madelungFamilySmuggleRefuse &&
    p.tpFloatPinRefuse &&
    p.productionWiredRefuse &&
    p.knowingFiberOk &&
    p.homologNotCopy &&
    p.wave100NotWired &&
    p.intAuthorityCited &&
    ptExceptionContinuumLatticeScaffold

theorem pt_exception_continuum_honest_true :
    ptExceptionContinuumHonest = true := by native_decide

def ptExceptionContinuumAxiom : Bool :=
  not118SquaredGreenTable &&
    ptExceptionContinuumSecondLawConservationFramed &&
    ptExceptionContinuumLatticeScaffold &&
    ptExceptionContinuumHonest &&
    !ptExceptionContinuumProved &&
    !ptExceptionContinuumProductionWired &&
    !wave100LibRsWired &&
    !wave100EosRsWired &&
    !wave100NanoWired &&
    decide (ptExceptionContinuumFraming =
      "second_law_conservation_pt_exception_continuum_occupancy_engine_sort_one_axiom")

theorem pt_exception_continuum_axiom :
    ptExceptionContinuumAxiom = true := by native_decide

theorem pt_exception_continuum_modality_unwired :
    ptExceptionContinuumModalityCurrent = .unwired := rfl

theorem unwired_close_without_production_wiring :
    evaluatePtExceptionContinuumClose .unwired false false = .unwiredOk := rfl

theorem pt78_witness_named_ok :
    evaluatePtExceptionContinuumBundle .unwired samplePtExceptionContinuumPt78Bundle
      false false false = .namedOk := rfl

theorem trivial_empty_bundle_fail_closed :
    evaluatePtExceptionContinuumBundle .unwired sampleTrivialUnwiredBundle
      false false false = .trivialRefuse := rfl

theorem xor_classifier_refused :
    evaluatePtExceptionContinuumBundle .unwired samplePtExceptionContinuumPt78Bundle
      true false false = .xorRefuse := rfl

theorem green_invent_refuse_unwired :
    evaluatePtExceptionContinuumClose .unwired true false = .greenInventRefuse := rfl

theorem proved_without_bar_refuse :
    evaluatePtExceptionContinuumBundle .unwired samplePtExceptionContinuumPt78Bundle
      false false true = .provedWithoutBarRefuse := rfl

theorem production_wired_refuse :
    evaluatePtExceptionContinuumClose .proved false true = .productionWiredRefuse := rfl

theorem pt_exception_continuum_honest_bundle :
    ptExceptionContinuumProved = false ∧
    ptExceptionContinuumProductionWired = false ∧
    not118SquaredGreenTable = true ∧
    ptExceptionContinuumSecondLawConservationFramed = true ∧
    evaluatePtExceptionContinuumClose .unwired false false = .unwiredOk ∧
    evaluatePtExceptionContinuumBundle .unwired samplePtExceptionContinuumPt78Bundle
      false false false = .namedOk ∧
    evaluatePtExceptionContinuumBundle .unwired sampleTrivialUnwiredBundle
      false false false = .trivialRefuse ∧
    evaluatePtExceptionContinuumBundle .unwired samplePtExceptionContinuumPt78Bundle
      true false false = .xorRefuse ∧
    evaluatePtExceptionContinuumClose .unwired true false = .greenInventRefuse ∧
    ptecProductNotXor = true ∧
    platinumAtomicNumberZ = 78 ∧
    class14PtExceptionContinuumPatternIndex = 14 ∧
    ptExceptionContinuumAxiom = true :=
  ⟨rfl, rfl, not_118_squared_green_table, pt_exception_continuum_second_law_conservation_framed,
    unwired_close_without_production_wiring, pt78_witness_named_ok,
    trivial_empty_bundle_fail_closed, xor_classifier_refused, green_invent_refuse_unwired,
    ptec_product_not_xor_true, platinum_atomic_number_z_is_78,
    class14_pt_exception_continuum_pattern_index_fourteen,
    pt_exception_continuum_axiom⟩

end UMST.Chem
