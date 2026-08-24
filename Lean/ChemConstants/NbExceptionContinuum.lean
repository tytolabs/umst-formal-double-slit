-- SPDX-FileCopyrightText: 2026 Santosh Prabhu Shenbagamoorthy and Santhosh Shyamsundar
-- SPDX-License-Identifier: MIT

import ElementElectronic

set_option maxRecDepth 8192

/-!
# NbExceptionContinuum — Nb Z=41 **exception continuum** (occupancy-engine sort)

Knowing-fiber Lean: Nb Z=41 4d⁴5s¹ **exception continuum**. D-block Madelung occupancy exception as
occupancy-engine sort on the same second-law + **conservation** object (ore ⊗ isotope ⊗ purify ⊗
G-stability ⊗ Env concurrent product — not XOR enum). Not a 26th periodic-table axiom; homolog ≠
occupancy copy (Ta Z=73 same group, distinct observed override). `nbExceptionContinuumProved` false.
Modality Unwired. WAVE100 not wired lib.rs / eos.rs.

Read-only cites (not imported — self-contained scaffold):
- `Coq/ChemConstants/NbExceptionContinuum.v`
- `umst/umst-chem/src/x_rows/occupancy_engine_sort.rs`
- `umst/umst-chem/src/x_rows/homolog_exception_not_copy.rs`
- `umst/umst-chem/src/x_rows/madelung_witness.rs`
- `Coq/ChemConstants/DBlockOccupancyExceptions.v` (read-only cite)

- `NbExceptionContinuumModality` — Unwired / Assumed / Proved / Surrogate (not 118² GREEN table).
- X29 occupancy-engine sort row pin; `dblock_exception` bucket.
- Nb Z=41 observed 4d⁴5s¹ vs Madelung predicted 5s²4d³ — occupancy-engine sort, not homolog copy.
- Second-law + **conservation** framing cites `LandauerLaw.physicalSecondLaw` — not imported meso theorems.
- No meso / acting theorems. No new physics `axiom`.
- `physics_green` stays false. Does **not** claim `nbExceptionContinuumProved` or physics GREEN.
- WAVE100 freeze — not wired lib.rs / eos.rs / nano.
- Does **not** mint second exception axiom (not 26th axiom).
-/

namespace UMST.Chem

/-- Design modality for Nb **exception continuum** (lattice SSOT). -/
inductive NbExceptionContinuumModality where
  | unwired | assumed | proved | surrogate
  deriving DecidableEq, Repr

def nbExceptionContinuumModalityCurrent : NbExceptionContinuumModality := .unwired

/-- Modality lattice cardinality (Unwired / Assumed / Proved / Surrogate). -/
def nbExceptionContinuumLatticeCardinality : Nat := 4

theorem nb_exception_continuum_lattice_cardinality_four :
    nbExceptionContinuumLatticeCardinality = 4 := rfl

theorem nb_exception_continuum_lattice_not_118_squared :
    nbExceptionContinuumLatticeCardinality ≠ 118 * 118 := by decide

/-- Surface tag for name-from-content (`nb_exception_continuum`). -/
def nbExceptionContinuumSurface : String := "nb_exception_continuum_surface"

theorem nb_exception_continuum_surface_named :
    nbExceptionContinuumSurface ≠ "" := by decide

/-- Machine-readable Nb exception continuum marker. -/
def nbExceptionContinuumMarker : String :=
  "chem_int_nb_exception_continuum_product_v1"

theorem nb_exception_continuum_marker_named :
    nbExceptionContinuumMarker ≠ "" := by decide

/-- Row stem pin for name-from-content (`nb_exception_continuum`). -/
def nbExceptionContinuumRowStem : String := "nb_exception_continuum"

theorem nb_exception_continuum_row_stem_named :
    nbExceptionContinuumRowStem = "nb_exception_continuum" := rfl

/-- X29 occupancy-engine sort row id pin. -/
def crossClassifierOccupancyEngineSortRowId : String := "X29"

theorem cross_classifier_occupancy_engine_sort_row_named :
    crossClassifierOccupancyEngineSortRowId = "X29" := rfl

/-- Occupancy-engine sort bucket tag — d-block exception. -/
def occupancyEngineSortBucketTag : String := "dblock_exception"

theorem occupancy_engine_sort_bucket_tag_named :
    occupancyEngineSortBucketTag = "dblock_exception" := rfl

/-- IUPAC periodic-table cardinality (Z=1..118). -/
def iupacTableCardinality : Nat := 118

theorem iupac_table_cardinality_118 : iupacTableCardinality = 118 := rfl

/-- Niobium Z=41 — d-block exception witness element pin. -/
def niobiumAtomicNumberZ : Nat := 41

theorem niobium_atomic_number_z_is_41 : niobiumAtomicNumberZ = 41 := rfl

/-- Tantalum Z=73 — homolog group witness (distinct observed override, not copy). -/
def tantalumHomologZ : Nat := 73

theorem tantalum_homolog_z_is_73 : tantalumHomologZ = 73 := rfl

def niobiumZValid : Bool :=
  decide (0 < niobiumAtomicNumberZ ∧ niobiumAtomicNumberZ ≤ iupacTableCardinality)

theorem niobium_z_valid_true : niobiumZValid = true := by decide

/-- Forbidden Z=119 smuggle — not in IUPAC table. -/
def forbiddenZ119Smuggle : Nat := 119

theorem forbidden_z119_not_in_iupac_table :
    forbiddenZ119Smuggle > iupacTableCardinality := by decide

/-- Nb element symbol pin. -/
def nbElementSymbol : String := "Nb"

/-- Nb observed occupancy tag — 4d⁴5s¹ (qlattice observed_override_config SSOT). -/
def nbObservedOccupancyTag : String := "4d45s1"

/-- Nb Madelung predicted occupancy tag — 5s²4d³. -/
def nbPredictedOccupancyTag : String := "5s24d3"

/-- Nb observed subshell notation. -/
def nbObservedSubshellNotation : String :=
  "1s22s22p63s23p64s23d104p65s14d4"

/-- Nb predicted subshell notation. -/
def nbPredictedSubshellNotation : String :=
  "1s22s22p63s23p64s23d104p65s24d3"

/-- Ta homolog observed occupancy tag — distinct from Nb. -/
def taHomologObservedOccupancyTag : String := "4f145d36s2"

theorem nb_element_symbol_nonempty : nbElementSymbol ≠ "" := by decide

theorem nb_observed_occupancy_tag_nonempty : nbObservedOccupancyTag ≠ "" := by decide

theorem nb_predicted_occupancy_tag_nonempty : nbPredictedOccupancyTag ≠ "" := by decide

theorem nb_observed_ne_predicted_occupancy :
    nbObservedOccupancyTag ≠ nbPredictedOccupancyTag := by decide

theorem nb_observed_ne_predicted_subshell :
    nbObservedSubshellNotation ≠ nbPredictedSubshellNotation := by decide

theorem nb_homolog_occupancy_not_copy :
    nbObservedOccupancyTag ≠ taHomologObservedOccupancyTag := by decide

def oreChannelTag : String := "ore"
def isotopeMixChannelTag : String := "isotope_mix"
def purifyRefineChannelTag : String := "purify_refine_cost"
def gStabilityChannelTag : String := "g_stability"
def envChannelTag : String := "env"

theorem ore_channel_tag_named : oreChannelTag ≠ "" := by decide
theorem isotope_mix_channel_tag_named : isotopeMixChannelTag ≠ "" := by decide
theorem purify_refine_channel_tag_named : purifyRefineChannelTag ≠ "" := by decide
theorem g_stability_channel_tag_named : gStabilityChannelTag ≠ "" := by decide
theorem env_channel_tag_named : envChannelTag ≠ "" := by decide

/-- Nb exception continuum product channel slot — concurrent **product** factor, not XOR bucket. -/
inductive NbExceptionChannelSlot where
  | unwired | absent | present
  deriving DecidableEq, Repr

def nbExceptionChannelSlotIsPresent (s : NbExceptionChannelSlot) : Bool :=
  match s with | .present => true | _ => false

/-- Named ore / isotope / purify / G-stability / env product channels (bounded scaffold). -/
inductive NbExceptionProductChannel where
  | ore | isotopeMix | purifyRefine | gStability | env
  deriving DecidableEq, Repr

def nbExceptionContinuumProductChannelCount : Nat := 5

theorem nb_exception_continuum_product_channel_count_five :
    nbExceptionContinuumProductChannelCount = 5 := rfl

def nbExceptionProductChannelIndex : NbExceptionProductChannel → Nat
  | .ore => 0
  | .isotopeMix => 1
  | .purifyRefine => 2
  | .gStability => 3
  | .env => 4

theorem nec_channel_ore_idx_is_0 :
    nbExceptionProductChannelIndex .ore = 0 := rfl

theorem nec_channel_isotope_mix_idx_is_1 :
    nbExceptionProductChannelIndex .isotopeMix = 1 := rfl

theorem nec_channel_purify_refine_idx_is_2 :
    nbExceptionProductChannelIndex .purifyRefine = 2 := rfl

theorem nec_channel_g_stability_idx_is_3 :
    nbExceptionProductChannelIndex .gStability = 3 := rfl

theorem nec_channel_env_idx_is_4 :
    nbExceptionProductChannelIndex .env = 4 := rfl

/-- Nb exception continuum concurrent **product** bundle (north-star §3). -/
structure NbExceptionConcurrentBundle where
  channelSlots : List NbExceptionChannelSlot
  deriving DecidableEq, Repr

/-- All channels Unwired — honest scaffold baseline. -/
def nbExceptionConcurrentBundleUnwired : NbExceptionConcurrentBundle :=
  { channelSlots := List.replicate nbExceptionContinuumProductChannelCount .unwired }

def nbExceptionConcurrentBundleWithChannel (idx : Nat) (slot : NbExceptionChannelSlot)
    (b : NbExceptionConcurrentBundle) : NbExceptionConcurrentBundle :=
  if idx < b.channelSlots.length then
    { channelSlots :=
        b.channelSlots.take idx ++ [slot] ++ b.channelSlots.drop (idx + 1) }
  else b

def nbExceptionConcurrentBundleWithPresent (idx : Nat) (b : NbExceptionConcurrentBundle) :
    NbExceptionConcurrentBundle :=
  nbExceptionConcurrentBundleWithChannel idx .present b

def nbExceptionConcurrentBundleChannelAt (idx : Nat) (b : NbExceptionConcurrentBundle) :
    Option NbExceptionChannelSlot :=
  b.channelSlots.get? idx

def nbExceptionConcurrentBundleHolds (idx : Nat) (b : NbExceptionConcurrentBundle) : Bool :=
  match nbExceptionConcurrentBundleChannelAt idx b with
  | some .present => true
  | _ => false

def nbExceptionConcurrentBundlePresentCount (b : NbExceptionConcurrentBundle) : Nat :=
  b.channelSlots.foldl (fun acc s => if nbExceptionChannelSlotIsPresent s then acc + 1 else acc) 0

def nbExceptionConcurrentBundleIsConcurrentProduct (b : NbExceptionConcurrentBundle) : Bool :=
  decide (nbExceptionConcurrentBundlePresentCount b ≥ 2)

/-- Nb Z=41 natural continuum witness — ore ⊗ isotope ⊗ purify ⊗ G ⊗ Env. -/
def nbExceptionContinuumNb41Witness : NbExceptionConcurrentBundle :=
  nbExceptionConcurrentBundleWithPresent 4
    (nbExceptionConcurrentBundleWithPresent 3
      (nbExceptionConcurrentBundleWithPresent 2
        (nbExceptionConcurrentBundleWithPresent 1
          (nbExceptionConcurrentBundleWithPresent 0
            nbExceptionConcurrentBundleUnwired))))

def nbExceptionContinuumEmptyWitness : NbExceptionConcurrentBundle :=
  nbExceptionConcurrentBundleUnwired

def nbExceptionContinuumSinglePresent : NbExceptionConcurrentBundle :=
  nbExceptionConcurrentBundleWithPresent 0 nbExceptionConcurrentBundleUnwired

theorem ore_channel_present :
    nbExceptionConcurrentBundleHolds 0 nbExceptionContinuumNb41Witness = true := by decide

theorem isotope_mix_channel_present :
    nbExceptionConcurrentBundleHolds 1 nbExceptionContinuumNb41Witness = true := by decide

theorem purify_refine_channel_present :
    nbExceptionConcurrentBundleHolds 2 nbExceptionContinuumNb41Witness = true := by decide

theorem g_stability_channel_present :
    nbExceptionConcurrentBundleHolds 3 nbExceptionContinuumNb41Witness = true := by decide

theorem env_channel_present :
    nbExceptionConcurrentBundleHolds 4 nbExceptionContinuumNb41Witness = true := by decide

theorem nb41_witness_present_count_is_five :
    nbExceptionConcurrentBundlePresentCount nbExceptionContinuumNb41Witness = 5 := by decide

theorem nb41_witness_is_concurrent_product :
    nbExceptionConcurrentBundleIsConcurrentProduct nbExceptionContinuumNb41Witness = true := by decide

theorem empty_bundle_present_count_zero :
    nbExceptionConcurrentBundlePresentCount nbExceptionContinuumEmptyWitness = 0 := by decide

theorem empty_bundle_not_concurrent_product :
    nbExceptionConcurrentBundleIsConcurrentProduct nbExceptionContinuumEmptyWitness = false := by decide

theorem single_present_count_is_one :
    nbExceptionConcurrentBundlePresentCount nbExceptionContinuumSinglePresent = 1 := by decide

theorem single_present_not_concurrent_product :
    nbExceptionConcurrentBundleIsConcurrentProduct nbExceptionContinuumSinglePresent = false := by decide

/-- XOR posture — mutual exclusivity scaffold defect (must refuse). -/
inductive NbExceptionXorPosture where
  | exclusive | concurrent
  deriving DecidableEq, Repr

def necXorClassifierMarker : String := "chem_l0_nb_exception_xor_classifier_v1"
def necConcurrentProductMarker : String := "chem_int_nb_exception_continuum_product_v1"

theorem nec_xor_marker_ne_concurrent_product_marker :
    necXorClassifierMarker ≠ necConcurrentProductMarker := by decide

def necXorClassifierIncompatible (claimXor : Bool) (b : NbExceptionConcurrentBundle) : Bool :=
  claimXor && nbExceptionConcurrentBundleIsConcurrentProduct b

theorem nec_xor_refuse_on_nb41_witness :
    necXorClassifierIncompatible true nbExceptionContinuumNb41Witness = true := by decide

def necProductNotXor : Bool :=
  nbExceptionConcurrentBundleIsConcurrentProduct nbExceptionContinuumNb41Witness &&
  necXorClassifierIncompatible true nbExceptionContinuumNb41Witness

theorem nec_product_not_xor_true : necProductNotXor = true := by decide

/-- Claim bar for Nb exception continuum conservation close. -/
inductive NbExceptionBarPresence where
  | absent | present
  deriving DecidableEq, Repr

structure NbExceptionClaimBar where
  barPresence : NbExceptionBarPresence
  defectTotal : Nat
  deriving DecidableEq, Repr

def nbExceptionContinuumClaimBarAbsent : NbExceptionClaimBar :=
  { barPresence := .absent, defectTotal := 0 }

def necClaimBarZeroDefect (b : NbExceptionClaimBar) : Bool :=
  match b.barPresence with
  | .absent => false
  | .present => decide (b.defectTotal = 0)

/-- Verdict for Nb **exception continuum** close (fail-closed). -/
inductive NbExceptionContinuumVerdict where
  | unwiredOk
  | namedOk
  | designOk
  | trivialRefuse
  | xorRefuse
  | greenInventRefuse
  | provedWithoutBarRefuse
  | productionWiredRefuse
  | parallelExceptionAxiomRefuse
  | homologCopyRefuse
  | extraElementIdRefuse
  | madelungFamilySmuggleRefuse
  | tpFloatPinRefuse
  deriving DecidableEq, Repr

def nbExceptionContinuumVerdictOk (v : NbExceptionContinuumVerdict) : Bool :=
  match v with
  | .unwiredOk | .namedOk | .designOk => true
  | _ => false

def nbExceptionContinuumBundleNontrivial (b : NbExceptionConcurrentBundle) : Bool :=
  decide (nbExceptionConcurrentBundlePresentCount b > 0)

def evaluateNbExceptionContinuumBundle
    (modality : NbExceptionContinuumModality)
    (b : NbExceptionConcurrentBundle)
    (claimXorClassifier : Bool)
    (claimPhysicsGreen : Bool)
    (claimProved : Bool) : NbExceptionContinuumVerdict :=
  if claimPhysicsGreen then
    .greenInventRefuse
  else if claimProved then
    .provedWithoutBarRefuse
  else if !nbExceptionContinuumBundleNontrivial b then
    .trivialRefuse
  else if necXorClassifierIncompatible claimXorClassifier b then
    .xorRefuse
  else
    match modality with
    | .unwired =>
        if nbExceptionConcurrentBundleIsConcurrentProduct b then .namedOk else .designOk
    | .assumed | .surrogate => .designOk
    | .proved => .provedWithoutBarRefuse

def evaluateNbExceptionContinuumClose
    (modality : NbExceptionContinuumModality)
    (claimPhysicsGreen : Bool)
    (claimProductionWired : Bool) : NbExceptionContinuumVerdict :=
  if claimPhysicsGreen then
    .greenInventRefuse
  else if claimProductionWired then
    .productionWiredRefuse
  else
    match modality with
    | .unwired => .unwiredOk
    | .assumed | .proved | .surrogate => .namedOk

def nbExceptionContinuumAuthorized (claimPhysicsGreen : Bool) (claimProductionWired : Bool) : Bool :=
  match evaluateNbExceptionContinuumClose .proved claimPhysicsGreen claimProductionWired with
  | .namedOk => true
  | _ => false

def sampleNbExceptionNb41Bundle : NbExceptionConcurrentBundle :=
  nbExceptionContinuumNb41Witness

def sampleTrivialUnwiredBundle : NbExceptionConcurrentBundle :=
  nbExceptionContinuumEmptyWitness

def unwiredDesignOk : Bool :=
  decide (evaluateNbExceptionContinuumClose .unwired false false = .unwiredOk)

def nb41ConcurrentOk : Bool :=
  decide (evaluateNbExceptionContinuumBundle .unwired sampleNbExceptionNb41Bundle
      false false false = .namedOk ∧
    nbExceptionConcurrentBundleIsConcurrentProduct sampleNbExceptionNb41Bundle = true ∧
    niobiumAtomicNumberZ = 41 ∧
    nbObservedOccupancyTag = "4d45s1")

def concurrentProductNotXorOk : Bool :=
  decide (necProductNotXor = true ∧
    nbExceptionConcurrentBundlePresentCount nbExceptionContinuumNb41Witness = 5)

def xorMutuallyExclusiveRefuse : Bool :=
  decide (evaluateNbExceptionContinuumBundle .unwired sampleNbExceptionNb41Bundle
      true false false = .xorRefuse)

def greenInventNbExceptionRefuse : Bool :=
  decide (evaluateNbExceptionContinuumClose .unwired true false = .greenInventRefuse ∧
    evaluateNbExceptionContinuumBundle .unwired sampleNbExceptionNb41Bundle
      false true false = .greenInventRefuse)

def productionWiredRefuse : Bool :=
  decide (evaluateNbExceptionContinuumClose .proved false true = .productionWiredRefuse)

def trivialBundleRefuse : Bool :=
  decide (evaluateNbExceptionContinuumBundle .unwired sampleTrivialUnwiredBundle
      false false false = .trivialRefuse)

/-- PATTERN-00 Nb exception continuum is **not** claimed Proved on the knowing scaffold. -/
def nbExceptionContinuumProved : Bool := false

theorem nb_exception_continuum_proved_false :
    nbExceptionContinuumProved = false := rfl

def nbExceptionContinuumProductionWired : Bool := false

theorem nb_exception_continuum_production_not_wired :
    nbExceptionContinuumProductionWired = false := rfl

def not118SquaredGreenTable : Bool := true

theorem not_118_squared_green_table : not118SquaredGreenTable = true := rfl

def nbExceptionContinuumLandauerLawPin : String := "LandauerLaw.physicalSecondLaw"

theorem nb_exception_continuum_landauer_law_pin_named :
    nbExceptionContinuumLandauerLawPin = "LandauerLaw.physicalSecondLaw" := rfl

def nbExceptionSecondLawConservationFramed : Bool := true

theorem nb_exception_second_law_conservation_framed :
    nbExceptionSecondLawConservationFramed = true := rfl

def wave100LibRsWired : Bool := false
def wave100EosRsWired : Bool := false
def wave100NanoWired : Bool := false

def wave100NotWired : Bool :=
  !wave100LibRsWired && !wave100EosRsWired && !wave100NanoWired

theorem wave100_not_wired : wave100NotWired = true := rfl

def nbExceptionNeSpeciesId : Bool := true
def speciesIdForked : Bool := false

def nbExceptionContinuumAuthority : String :=
  "umst/umst-chem/src/x_rows/occupancy_engine_sort.rs"

theorem nb_exception_continuum_authority_path :
    nbExceptionContinuumAuthority =
      "umst/umst-chem/src/x_rows/occupancy_engine_sort.rs" := rfl

def homologExceptionNotCopyAuthority : String :=
  "umst/umst-chem/src/x_rows/homolog_exception_not_copy.rs"

def madelungWitnessAuthority : String :=
  "umst/umst-chem/src/x_rows/madelung_witness.rs"

def parallelExceptionAxiomTag : String := "26th_periodic_table_axiom"

def homologCopyFraming : String := "ta_z73_occupancy_copied_onto_nb_z41"

def extraElementIdSmuggleFraming : String := "nb_exception_as_extra_element_id_smuggle"

def madelungFamilySmuggleFraming : String :=
  "madelung_family_only_no_observed_override"

def tpFloatPinFraming : String :=
  "bare_298_15_k_1_atm_float_pins_on_nb_exception_scaffold"

def nbExceptionContinuumFraming : String :=
  "second_law_conservation_occupancy_engine_sort_nb_z41_one_axiom"

theorem nb_exception_not_26th_axiom :
    nbExceptionContinuumFraming ≠ parallelExceptionAxiomTag := by decide

def parallelExceptionAxiomRefuse : Bool :=
  decide (nbExceptionContinuumAuthority ≠ parallelExceptionAxiomTag ∧
    nbExceptionContinuumProved = false)

def homologCopyRefuse : Bool :=
  decide (nbExceptionContinuumFraming ≠ homologCopyFraming ∧
    nbObservedOccupancyTag ≠ taHomologObservedOccupancyTag ∧
    niobiumAtomicNumberZ = 41 ∧
    tantalumHomologZ = 73)

def extraElementIdRefuse : Bool :=
  decide (nbExceptionContinuumFraming ≠ extraElementIdSmuggleFraming ∧
    forbiddenZ119Smuggle > iupacTableCardinality ∧
    niobiumAtomicNumberZ = 41)

def madelungFamilySmuggleRefuse : Bool :=
  decide (nbExceptionContinuumFraming ≠ madelungFamilySmuggleFraming ∧
    nbObservedOccupancyTag ≠ nbPredictedOccupancyTag ∧
    nbExceptionContinuumProved = false)

def tpFloatPinRefuse : Bool :=
  decide (nbExceptionContinuumFraming ≠ tpFloatPinFraming ∧
    gStabilityChannelTag = "g_stability")

def occupancyEngineSortFraming : String := "occupancy_engine_sort_dblock_exception_bucket"

def occupancyEngineSortIntAuthority : String :=
  "umst/umst-chem/src/x_rows/occupancy_engine_sort.rs"

/-- Nb Z=41 occupancy-engine sort — dblock_exception bucket; not homolog copy. -/
def nbOccupancyEngineSortOk : Bool :=
  decide (occupancyEngineSortBucketTag = "dblock_exception" ∧
    nbObservedOccupancyTag = "4d45s1" ∧
    nbPredictedOccupancyTag = "5s24d3" ∧
    nbObservedOccupancyTag ≠ taHomologObservedOccupancyTag ∧
    niobiumAtomicNumberZ = 41 ∧
    occupancyEngineSortFraming ≠ parallelExceptionAxiomTag ∧
    nbExceptionContinuumProved = false)

theorem nb_occupancy_engine_sort_not_homolog_copy :
    nbOccupancyEngineSortOk = true ∧
    nbObservedOccupancyTag ≠ taHomologObservedOccupancyTag ∧
    niobiumAtomicNumberZ = 41 ∧
    tantalumHomologZ = 73 := by
  constructor <;> native_decide

def nbExceptionLatticeScaffold : Bool :=
  unwiredDesignOk &&
    nb41ConcurrentOk &&
    concurrentProductNotXorOk &&
    xorMutuallyExclusiveRefuse &&
    greenInventNbExceptionRefuse &&
    parallelExceptionAxiomRefuse &&
    homologCopyRefuse &&
    extraElementIdRefuse &&
    madelungFamilySmuggleRefuse &&
    tpFloatPinRefuse &&
    trivialBundleRefuse &&
    productionWiredRefuse &&
    nbOccupancyEngineSortOk &&
    wave100NotWired

theorem nb_exception_lattice_scaffold_true :
    nbExceptionLatticeScaffold = true := by native_decide

inductive NbExceptionContinuumFiber where
  | quantumKnowing | mesoActing
  deriving DecidableEq, Repr

def nbExceptionContinuumFiberOk (f : NbExceptionContinuumFiber) : Bool :=
  match f with | .quantumKnowing => true | .mesoActing => false

theorem nb_exception_continuum_knowing_fiber_ok :
    nbExceptionContinuumFiberOk .quantumKnowing = true := rfl

theorem nb_exception_continuum_meso_acting_not_ok :
    nbExceptionContinuumFiberOk .mesoActing = false := rfl

def nbExceptionContinuumCellId : String :=
  "CHEM-FORMAL-Q-LEAN-NB-EXCEPTION-CONTINUUM"

def nbExceptionContinuumNonClaim : String :=
  "CHEM-FORMAL-Q-LEAN-NB-EXCEPTION-CONTINUUM NbExceptionContinuumModality Unwired Assumed Proved Surrogate four-step lattice nbExceptionContinuumProved false evaluateNbExceptionContinuumBundle evaluateNbExceptionContinuumClose named Nb Z=41 4d4 5s1 occupancy engine sort dblock_exception ore isotope purify G env concurrent product identity conserved present ge 2 product not XOR xor mutually exclusive refuse parallel exception axiom refuse homolog copy refuse Ta Z=73 extra element id Z=119 refuse madelung family smuggle refuse Nb ne SpeciesId Unwired one axiom second law conservation not 118 squared GREEN table not meso acting not physics GREEN not production_wired WAVE100 not lib.rs"

def nbExceptionContinuumPhysicsGreenAuthorized : Prop := False

theorem nb_exception_continuum_physics_green_false :
    ¬ nbExceptionContinuumPhysicsGreenAuthorized := id

structure NbExceptionContinuumProbe where
  cellIdNamed : Bool
  unwired : Bool
  physicsGreenRefused : Bool
  notProved : Bool
  nb41HostWitness : Bool
  occupancyEngineSort : Bool
  homologNotCopy : Bool
  oreIsotopePurifyGEnvProduct : Bool
  concurrentNotXor : Bool
  nb41WitnessOk : Bool
  xorRefuse : Bool
  greenInventRefuse : Bool
  parallelAxiomRefuse : Bool
  homologCopyRefuse : Bool
  extraElementIdRefuse : Bool
  madelungFamilySmuggleRefuse : Bool
  tpFloatPinRefuse : Bool
  productionWiredRefuse : Bool
  knowingFiberOk : Bool
  wave100NotWired : Bool
  intAuthorityCited : Bool
  deriving DecidableEq, Repr

def nbExceptionContinuumProbe : NbExceptionContinuumProbe :=
  { cellIdNamed :=
      decide (nbExceptionContinuumCellId =
        "CHEM-FORMAL-Q-LEAN-NB-EXCEPTION-CONTINUUM")
    unwired := decide (nbExceptionContinuumModalityCurrent = .unwired)
    physicsGreenRefused := true
    notProved := !nbExceptionContinuumProved
    nb41HostWitness := decide (niobiumAtomicNumberZ = 41)
    occupancyEngineSort := nbOccupancyEngineSortOk
    homologNotCopy := homologCopyRefuse
    oreIsotopePurifyGEnvProduct := decide (oreChannelTag = "ore" ∧
      isotopeMixChannelTag = "isotope_mix" ∧
      purifyRefineChannelTag = "purify_refine_cost" ∧
      gStabilityChannelTag = "g_stability" ∧
      envChannelTag = "env")
    concurrentNotXor := necProductNotXor
    nb41WitnessOk := nb41ConcurrentOk
    xorRefuse := xorMutuallyExclusiveRefuse
    greenInventRefuse := greenInventNbExceptionRefuse
    parallelAxiomRefuse := parallelExceptionAxiomRefuse
    homologCopyRefuse := homologCopyRefuse
    extraElementIdRefuse := extraElementIdRefuse
    madelungFamilySmuggleRefuse := madelungFamilySmuggleRefuse
    tpFloatPinRefuse := tpFloatPinRefuse
    productionWiredRefuse := productionWiredRefuse
    knowingFiberOk := nbExceptionContinuumFiberOk .quantumKnowing
    wave100NotWired := wave100NotWired
    intAuthorityCited := nbExceptionContinuumAuthority ≠ "" }

def nbExceptionContinuumHonest : Bool :=
  let p := nbExceptionContinuumProbe
  p.cellIdNamed &&
    p.unwired &&
    p.physicsGreenRefused &&
    p.notProved &&
    p.nb41HostWitness &&
    p.occupancyEngineSort &&
    p.homologNotCopy &&
    p.oreIsotopePurifyGEnvProduct &&
    p.concurrentNotXor &&
    p.nb41WitnessOk &&
    p.xorRefuse &&
    p.greenInventRefuse &&
    p.parallelAxiomRefuse &&
    p.homologCopyRefuse &&
    p.extraElementIdRefuse &&
    p.madelungFamilySmuggleRefuse &&
    p.tpFloatPinRefuse &&
    p.productionWiredRefuse &&
    p.knowingFiberOk &&
    p.wave100NotWired &&
    p.intAuthorityCited &&
    nbExceptionLatticeScaffold

theorem nb_exception_continuum_honest_true :
    nbExceptionContinuumHonest = true := by native_decide

def nbExceptionContinuumAxiom : Bool :=
  not118SquaredGreenTable &&
    nbExceptionSecondLawConservationFramed &&
    nbExceptionLatticeScaffold &&
    nbExceptionContinuumHonest &&
    !nbExceptionContinuumProved &&
    !nbExceptionContinuumProductionWired &&
    !wave100LibRsWired &&
    !wave100EosRsWired &&
    !wave100NanoWired &&
    nbExceptionNeSpeciesId &&
    !speciesIdForked &&
    decide (nbExceptionContinuumFraming =
      "second_law_conservation_occupancy_engine_sort_nb_z41_one_axiom")

theorem nb_exception_continuum_axiom :
    nbExceptionContinuumAxiom = true := by native_decide

theorem nb_exception_continuum_modality_unwired :
    nbExceptionContinuumModalityCurrent = .unwired := rfl

theorem unwired_close_without_production_wiring :
    evaluateNbExceptionContinuumClose .unwired false false = .unwiredOk := rfl

theorem nb41_witness_named_ok :
    evaluateNbExceptionContinuumBundle .unwired sampleNbExceptionNb41Bundle
      false false false = .namedOk := rfl

theorem trivial_empty_bundle_fail_closed :
    evaluateNbExceptionContinuumBundle .unwired sampleTrivialUnwiredBundle
      false false false = .trivialRefuse := rfl

theorem xor_classifier_refused :
    evaluateNbExceptionContinuumBundle .unwired sampleNbExceptionNb41Bundle
      true false false = .xorRefuse := rfl

theorem green_invent_refuse_unwired :
    evaluateNbExceptionContinuumClose .unwired true false = .greenInventRefuse := rfl

theorem proved_without_bar_refuse :
    evaluateNbExceptionContinuumBundle .unwired sampleNbExceptionNb41Bundle
      false false true = .provedWithoutBarRefuse := rfl

theorem production_wired_refuse :
    evaluateNbExceptionContinuumClose .proved false true = .productionWiredRefuse := rfl

theorem nb_exception_continuum_honest_bundle :
    nbExceptionContinuumProved = false ∧
    nbExceptionContinuumProductionWired = false ∧
    not118SquaredGreenTable = true ∧
    nbExceptionSecondLawConservationFramed = true ∧
    evaluateNbExceptionContinuumClose .unwired false false = .unwiredOk ∧
    evaluateNbExceptionContinuumBundle .unwired sampleNbExceptionNb41Bundle
      false false false = .namedOk ∧
    evaluateNbExceptionContinuumBundle .unwired sampleTrivialUnwiredBundle
      false false false = .trivialRefuse ∧
    evaluateNbExceptionContinuumBundle .unwired sampleNbExceptionNb41Bundle
      true false false = .xorRefuse ∧
    evaluateNbExceptionContinuumClose .unwired true false = .greenInventRefuse ∧
    necProductNotXor = true ∧
    niobiumAtomicNumberZ = 41 ∧
    nbObservedOccupancyTag ≠ taHomologObservedOccupancyTag ∧
    nbExceptionContinuumAxiom = true :=
  ⟨rfl, rfl, not_118_squared_green_table, nb_exception_second_law_conservation_framed,
    unwired_close_without_production_wiring, nb41_witness_named_ok,
    trivial_empty_bundle_fail_closed, xor_classifier_refused, green_invent_refuse_unwired,
    nec_product_not_xor_true, niobium_atomic_number_z_is_41, nb_homolog_occupancy_not_copy,
    nb_exception_continuum_axiom⟩

end UMST.Chem
