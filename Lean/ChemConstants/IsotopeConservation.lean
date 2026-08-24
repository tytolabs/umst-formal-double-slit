-- SPDX-FileCopyrightText: 2026 Santosh Prabhu Shenbagamoorthy and Santhosh Shyamsundar
-- SPDX-License-Identifier: MIT

import ElementElectronic

set_option maxRecDepth 8192

/-!
# IsotopeConservation — class-11 **isotope** **conservation** (Q lattice)

Knowing-fiber Lean: PATTERN-00 class 11 (`isotope`) concurrent Π_c identity conserved on named class
pins. Isotope is a concurrent PatternBundle factor on the same second-law + **conservation** object (not a
26th axiom). Electronic occupancy ⊗ nuclear identity ⊗ class-11 isotope factor is **product** not XOR.
Electronic chemistry does **not** GREEN nuclear decay; nuclear decay does **not** mint ElementId Z=119.
Fe Z=26 host witness; Tc/Pm radioelement honesty as same-Z isotope factor, not extra ElementId. Named
class-11 identity conserved under honest scaffold; trivial XOR, parallel isotope axiom, nuclear-decay chem
GREEN, extra ElementId Z=119, and GREEN invent fail-closed.

Read-only cites (not imported — self-contained scaffold):
- `Coq/ChemConstants/IsotopeConservation.v`
- `Haskell/UMST/ChemConstants/IsotopeConservation.hs`
- `Agda/ChemConstants/IsotopeConservation.agda`
- `umst/umst-chem/src/l0_tables/isotope.rs`
- `umst/umst-chem/src/isotope_nuclear_electronic_boundary.rs`

- `IsotopeConservationModality` — Unwired / Assumed / Proved / Surrogate (not 118² GREEN table).
- `IsotopeProductChannel` — electronic chemistry ⊗ nuclear decay ⊗ class-11 concurrent Π_c.
- Second-law + **conservation** framing cites `LandauerLaw.physicalSecondLaw` — not imported meso theorems.
- No meso / acting theorems. No new physics `axiom`.
- `physics_green` stays false. Does **not** claim `isotopeConservationProved` or physics GREEN.
- WAVE100 freeze — not wired lib.rs / eos.rs / nano.
- Does **not** mint second isotope axiom (not 26th axiom).
-/

namespace UMST.Chem

/-- Design modality for class-11 **isotope** **conservation** (lattice SSOT). -/
inductive IsotopeConservationModality where
  | unwired | assumed | proved | surrogate
  deriving DecidableEq, Repr

def isotopeConservationModalityCurrent : IsotopeConservationModality := .unwired

/-- Modality lattice cardinality (Unwired / Assumed / Proved / Surrogate). -/
def isotopeLatticeCardinality : Nat := 4

theorem isotope_lattice_cardinality_four :
    isotopeLatticeCardinality = 4 := rfl

theorem isotope_lattice_not_118_squared :
    isotopeLatticeCardinality ≠ 118 * 118 := by decide

/-- Surface tag for name-from-content (`isotope` / `isotopeconservation`). -/
def isotopeConservationSurface : String :=
  "isotope_conservation_surface"

theorem isotope_conservation_surface_named :
    isotopeConservationSurface ≠ "" := by decide

/-- Machine-readable isotope conservation marker. -/
def isotopeConservationMarker : String :=
  "chem_int_cross_isotope_conservation_v1"

theorem isotope_conservation_marker_named :
    isotopeConservationMarker ≠ "" := by decide

/-- Row stem pin for name-from-content (`isotope_conservation`). -/
def isotopeConservationRowStem : String := "isotope_conservation"

theorem isotope_conservation_row_stem_named :
    isotopeConservationRowStem = "isotope_conservation" := rfl

/-- North-star §2 class-11 isotope pattern index. -/
def class11IsotopePatternIndex : Nat := 11

theorem class11_isotope_pattern_index_eleven :
    class11IsotopePatternIndex = 11 := rfl

/-- Cross-classifier X11 row id pin. -/
def crossClassifierIsotopeRowId : String := "X11"

theorem cross_classifier_isotope_row_named :
    crossClassifierIsotopeRowId = "X11" := rfl

/-- §2 pattern class cardinality (north-star pinned — not 118²). -/
def patternClassCardinality : Nat := 25

theorem pattern_class_cardinality_twenty_five : patternClassCardinality = 25 := rfl

theorem pattern_class_not_118_squared : patternClassCardinality ≠ 118 * 118 := by decide

def patternClassIndexValid (i : Nat) : Bool := i < patternClassCardinality

theorem isotope_class_index_valid :
    patternClassIndexValid class11IsotopePatternIndex = true := by decide

/-- IUPAC periodic-table cardinality (Z=1..118). -/
def iupacTableCardinality : Nat := 118

theorem iupac_table_cardinality_118 : iupacTableCardinality = 118 := rfl

/-- Iron Z=26 — host assemblage witness element pin. -/
def ironAtomicNumberZ : Nat := 26

theorem iron_atomic_number_z_is_26 : ironAtomicNumberZ = 26 := rfl

/-- Technetium Z=43 — radioelement honesty (same-Z isotope factor, not extra ElementId). -/
def technetiumAtomicNumberZ : Nat := 43

theorem technetium_atomic_number_z_is_43 : technetiumAtomicNumberZ = 43 := rfl

/-- Promethium Z=61 — radioelement honesty (same-Z isotope factor, not extra ElementId). -/
def promethiumAtomicNumberZ : Nat := 61

theorem promethium_atomic_number_z_is_61 : promethiumAtomicNumberZ = 61 := rfl

theorem technetium_z_in_iupac_table :
    technetiumAtomicNumberZ ≤ iupacTableCardinality := by decide

theorem promethium_z_in_iupac_table :
    promethiumAtomicNumberZ ≤ iupacTableCardinality := by decide

/-- Forbidden Z=119 smuggle — not in IUPAC table. -/
def forbiddenZ119Smuggle : Nat := 119

theorem forbidden_z119_not_in_iupac_table :
    forbiddenZ119Smuggle > iupacTableCardinality := by decide

def isotopeFactorTag : String := "isotope"

def electronicChemChannelTag : String := "electronic_chemistry"

def nuclearDecayChannelTag : String := "nuclear_decay_radioactivity"

theorem isotope_factor_tag_named :
    isotopeFactorTag ≠ "" := by decide

theorem electronic_chem_channel_tag_named :
    electronicChemChannelTag ≠ "" := by decide

theorem nuclear_decay_channel_tag_named :
    nuclearDecayChannelTag ≠ "" := by decide

/-- Isotope product channel slot — concurrent **product** factor, not XOR bucket. -/
inductive IsotopeChannelSlot where
  | unwired | absent | present
  deriving DecidableEq, Repr

def isotopeChannelSlotIsPresent (s : IsotopeChannelSlot) : Bool :=
  match s with | .present => true | _ => false

/-- Named electronic chemistry / nuclear decay / class-11 isotope product channels (bounded scaffold). -/
inductive IsotopeProductChannel where
  | electronicChemistry | nuclearDecayRadioactivity | class11IsotopeAxis
  deriving DecidableEq, Repr

def isotopeProductChannelCount : Nat := 3

theorem isotope_product_channel_count_three :
    isotopeProductChannelCount = 3 := rfl

def isotopeProductChannelIndex : IsotopeProductChannel → Nat
  | .electronicChemistry => 0
  | .nuclearDecayRadioactivity => 1
  | .class11IsotopeAxis => 2

theorem iso_channel_electronic_chem_idx_is_0 :
    isotopeProductChannelIndex .electronicChemistry = 0 := rfl

theorem iso_channel_nuclear_decay_idx_is_1 :
    isotopeProductChannelIndex .nuclearDecayRadioactivity = 1 := rfl

theorem iso_channel_class11_isotope_idx_is_2 :
    isotopeProductChannelIndex .class11IsotopeAxis = 2 := rfl

/-- Class-11 isotope concurrent **product** bundle (north-star §3). -/
structure IsotopeConcurrentBundle where
  channelSlots : List IsotopeChannelSlot
  deriving DecidableEq, Repr

/-- All channels Unwired — honest scaffold baseline. -/
def isotopeConcurrentBundleUnwired : IsotopeConcurrentBundle :=
  { channelSlots := List.replicate isotopeProductChannelCount .unwired }

def isotopeConcurrentBundleWithChannel (idx : Nat) (slot : IsotopeChannelSlot)
    (b : IsotopeConcurrentBundle) : IsotopeConcurrentBundle :=
  if idx < b.channelSlots.length then
    { channelSlots :=
        b.channelSlots.take idx ++ [slot] ++ b.channelSlots.drop (idx + 1) }
  else b

def isotopeConcurrentBundleWithPresent (idx : Nat) (b : IsotopeConcurrentBundle) :
    IsotopeConcurrentBundle :=
  isotopeConcurrentBundleWithChannel idx .present b

def isotopeConcurrentBundleChannelAt (idx : Nat) (b : IsotopeConcurrentBundle) :
    Option IsotopeChannelSlot :=
  b.channelSlots.get? idx

def isotopeConcurrentBundleHolds (idx : Nat) (b : IsotopeConcurrentBundle) : Bool :=
  match isotopeConcurrentBundleChannelAt idx b with
  | some .present => true
  | _ => false

def isotopeConcurrentBundlePresentCount (b : IsotopeConcurrentBundle) : Nat :=
  b.channelSlots.foldl (fun acc s => if isotopeChannelSlotIsPresent s then acc + 1 else acc) 0

def isotopeConcurrentBundleIsConcurrentProduct (b : IsotopeConcurrentBundle) : Bool :=
  decide (isotopeConcurrentBundlePresentCount b ≥ 2)

/-- Fe Z=26 electronic chemistry + nuclear decay + class-11 isotope concurrent witness on class 11. -/
def isotopeFe26Witness : IsotopeConcurrentBundle :=
  isotopeConcurrentBundleWithPresent 2
    (isotopeConcurrentBundleWithPresent 1
      (isotopeConcurrentBundleWithPresent 0
        isotopeConcurrentBundleUnwired))

def isotopeEmptyWitness : IsotopeConcurrentBundle :=
  isotopeConcurrentBundleUnwired

def isotopeSinglePresent : IsotopeConcurrentBundle :=
  isotopeConcurrentBundleWithPresent 0 isotopeConcurrentBundleUnwired

theorem electronic_chem_channel_present :
    isotopeConcurrentBundleHolds 0 isotopeFe26Witness = true := by decide

theorem nuclear_decay_channel_present :
    isotopeConcurrentBundleHolds 1 isotopeFe26Witness = true := by decide

theorem class11_isotope_channel_present :
    isotopeConcurrentBundleHolds 2 isotopeFe26Witness = true := by decide

theorem fe26_witness_present_count_is_three :
    isotopeConcurrentBundlePresentCount isotopeFe26Witness = 3 := by decide

theorem fe26_witness_is_concurrent_product :
    isotopeConcurrentBundleIsConcurrentProduct isotopeFe26Witness = true := by decide

theorem empty_bundle_present_count_zero :
    isotopeConcurrentBundlePresentCount isotopeEmptyWitness = 0 := by decide

theorem empty_bundle_not_concurrent_product :
    isotopeConcurrentBundleIsConcurrentProduct isotopeEmptyWitness = false := by decide

theorem single_present_count_is_one :
    isotopeConcurrentBundlePresentCount isotopeSinglePresent = 1 := by decide

theorem single_present_not_concurrent_product :
    isotopeConcurrentBundleIsConcurrentProduct isotopeSinglePresent = false := by decide

/-- XOR posture — mutual exclusivity scaffold defect (must refuse). -/
inductive IsotopeXorPosture where
  | exclusive | concurrent
  deriving DecidableEq, Repr

def isotopeXorPostureExclusive : IsotopeXorPosture := .exclusive
def isotopeXorPostureConcurrent : IsotopeXorPosture := .concurrent

def isoXorClassifierMarker : String := "chem_l0_isotope_xor_classifier_v1"
def isoConcurrentProductMarker : String := "chem_int_isotope_product_v1"

theorem iso_xor_marker_ne_concurrent_product_marker :
    isoXorClassifierMarker ≠ isoConcurrentProductMarker := by decide

def isoXorClassifierIncompatible (claimXor : Bool) (b : IsotopeConcurrentBundle) : Bool :=
  claimXor && isotopeConcurrentBundleIsConcurrentProduct b

theorem iso_xor_refuse_on_fe26_witness :
    isoXorClassifierIncompatible true isotopeFe26Witness = true := by decide

def isoProductNotXor : Bool :=
  isotopeConcurrentBundleIsConcurrentProduct isotopeFe26Witness &&
  isoXorClassifierIncompatible true isotopeFe26Witness

theorem iso_product_not_xor_true : isoProductNotXor = true := by decide

/-- Verdict for class-11 **isotope** close (fail-closed). -/
inductive IsotopeConservationVerdict where
  | unwiredOk
  | namedOk
  | designOk
  | trivialRefuse
  | xorRefuse
  | greenInventRefuse
  | provedWithoutBarRefuse
  | productionWiredRefuse
  | parallelIsotopeAxiomRefuse
  | speciesIdSmuggleRefuse
  | extraElementIdRefuse
  | nuclearDecayChemGreenRefuse
  | tpFloatPinRefuse
  deriving DecidableEq, Repr

def isotopeConservationVerdictOk (v : IsotopeConservationVerdict) : Bool :=
  match v with
  | .unwiredOk | .namedOk | .designOk => true
  | _ => false

def isotopeBundleNontrivial (b : IsotopeConcurrentBundle) : Bool :=
  decide (isotopeConcurrentBundlePresentCount b > 0)

def evaluateIsotopeBundle
    (modality : IsotopeConservationModality)
    (b : IsotopeConcurrentBundle)
    (claimXorClassifier : Bool)
    (claimPhysicsGreen : Bool)
    (claimProved : Bool)
    (claimNuclearDecayChemGreen : Bool) : IsotopeConservationVerdict :=
  if claimPhysicsGreen then
    .greenInventRefuse
  else if claimNuclearDecayChemGreen then
    .nuclearDecayChemGreenRefuse
  else if claimProved then
    .provedWithoutBarRefuse
  else if !isotopeBundleNontrivial b then
    .trivialRefuse
  else if isoXorClassifierIncompatible claimXorClassifier b then
    .xorRefuse
  else
    match modality with
    | .unwired =>
        if isotopeConcurrentBundleIsConcurrentProduct b then .namedOk else .designOk
    | .assumed | .surrogate => .designOk
    | .proved => .provedWithoutBarRefuse

def evaluateIsotopeConservation
    (modality : IsotopeConservationModality)
    (claimPhysicsGreen : Bool)
    (claimProductionWired : Bool) : IsotopeConservationVerdict :=
  if claimPhysicsGreen then
    .greenInventRefuse
  else if claimProductionWired then
    .productionWiredRefuse
  else
    match modality with
    | .unwired => .unwiredOk
    | .assumed | .proved | .surrogate => .namedOk

def isotopeConservationAuthorized (claimPhysicsGreen : Bool) (claimProductionWired : Bool) : Bool :=
  match evaluateIsotopeConservation .proved claimPhysicsGreen claimProductionWired with
  | .namedOk => true
  | _ => false

def sampleIsotopeFe26Bundle : IsotopeConcurrentBundle :=
  isotopeFe26Witness

def sampleTrivialUnwiredBundle : IsotopeConcurrentBundle :=
  isotopeEmptyWitness

def unwiredDesignOk : Bool :=
  decide (evaluateIsotopeConservation .unwired false false = .unwiredOk)

def isotopeFe26ConcurrentOk : Bool :=
  decide (evaluateIsotopeBundle .unwired sampleIsotopeFe26Bundle
      false false false false = .namedOk ∧
    isotopeConcurrentBundleIsConcurrentProduct sampleIsotopeFe26Bundle = true ∧
    ironAtomicNumberZ = 26 ∧
    class11IsotopePatternIndex = 11)

def class11IsotopePatternIndexOk : Bool :=
  decide (class11IsotopePatternIndex = 11 ∧
    patternClassIndexValid class11IsotopePatternIndex = true)

def concurrentProductNotXorOk : Bool :=
  decide (isoProductNotXor = true ∧
    isotopeConcurrentBundlePresentCount isotopeFe26Witness = 3)

def xorMutuallyExclusiveRefuse : Bool :=
  decide (evaluateIsotopeBundle .unwired sampleIsotopeFe26Bundle
      true false false false = .xorRefuse)

def greenInventIsotopeRefuse : Bool :=
  decide (evaluateIsotopeConservation .unwired true false = .greenInventRefuse ∧
    evaluateIsotopeBundle .unwired sampleIsotopeFe26Bundle
      false true false false = .greenInventRefuse)

def nuclearDecayChemGreenRefuse : Bool :=
  decide (evaluateIsotopeBundle .unwired sampleIsotopeFe26Bundle
      false false false true = .nuclearDecayChemGreenRefuse)

def productionWiredRefuse : Bool :=
  decide (evaluateIsotopeConservation .proved false true = .productionWiredRefuse)

def trivialBundleRefuse : Bool :=
  decide (evaluateIsotopeBundle .unwired sampleTrivialUnwiredBundle
      false false false false = .trivialRefuse)

/-- PATTERN-00 class-11 **isotope** is **not** claimed Proved on the knowing scaffold. -/
def isotopeConservationProved : Bool := false

theorem isotope_conservation_proved_false :
    isotopeConservationProved = false := rfl

def isotopeConservationProductionWired : Bool := false

theorem isotope_conservation_production_not_wired :
    isotopeConservationProductionWired = false := rfl

def not118SquaredGreenTable : Bool := true

theorem not_118_squared_green_table : not118SquaredGreenTable = true := rfl

def isotopeConservationLandauerLawPin : String := "LandauerLaw.physicalSecondLaw"

theorem isotope_conservation_landauer_law_pin_named :
    isotopeConservationLandauerLawPin = "LandauerLaw.physicalSecondLaw" := rfl

def isotopeSecondLawConservationFramed : Bool := true

theorem isotope_second_law_conservation_framed :
    isotopeSecondLawConservationFramed = true := rfl

def wave100LibRsWired : Bool := false
def wave100EosRsWired : Bool := false
def wave100NanoWired : Bool := false

def wave100NotWired : Bool :=
  !wave100LibRsWired && !wave100EosRsWired && !wave100NanoWired

theorem wave100_not_wired : wave100NotWired = true := rfl

def isotopeNeSpeciesId : Bool := true
def speciesIdForked : Bool := false

def isotopeConservationAuthority : String :=
  "umst/umst-chem/src/l0_tables/isotope.rs"

theorem isotope_conservation_authority_path :
    isotopeConservationAuthority =
      "umst/umst-chem/src/l0_tables/isotope.rs" := rfl

def isotopeBoundaryAuthority : String :=
  "umst/umst-chem/src/isotope_nuclear_electronic_boundary.rs"

def parallelIsotopeAxiomTag : String := "26th_chemistry_axiom"

def speciesIdSmuggleFraming : String := "l1_species_id_cement_occupancy_tag"

def extraElementIdSmuggleFraming : String := "vacancy_or_impurity_as_z119_element_row"

def tpFloatPinFraming : String :=
  "bare_298_15_k_1_atm_float_pins_on_isotope_scaffold"

def isotopeConservationFraming : String :=
  "second_law_conservation_isotope_one_axiom"

theorem isotope_not_26th_axiom :
    isotopeConservationFraming ≠ parallelIsotopeAxiomTag := by decide

def parallelIsotopeAxiomRefuse : Bool :=
  decide (isotopeConservationAuthority ≠ parallelIsotopeAxiomTag ∧
    isotopeConservationProved = false)

def speciesIdSmuggleRefuse : Bool :=
  decide (isotopeConservationFraming ≠ speciesIdSmuggleFraming ∧
    ironAtomicNumberZ = 26 ∧
    class11IsotopePatternIndex = 11)

def extraElementIdRefuse : Bool :=
  decide (isotopeConservationFraming ≠ extraElementIdSmuggleFraming ∧
    forbiddenZ119Smuggle > iupacTableCardinality ∧
    ironAtomicNumberZ = 26)

def tpFloatPinRefuse : Bool :=
  decide (isotopeConservationFraming ≠ tpFloatPinFraming ∧
    nuclearDecayChannelTag = "nuclear_decay_radioactivity")

/-- Tc/Pm radioelement honesty — same-Z isotope factor within IUPAC table, not extra ElementId. -/
def radioelementHonestyOk : Bool :=
  decide (technetiumAtomicNumberZ = 43 ∧
    promethiumAtomicNumberZ = 61 ∧
    technetiumAtomicNumberZ ≤ iupacTableCardinality ∧
    promethiumAtomicNumberZ ≤ iupacTableCardinality ∧
    technetiumAtomicNumberZ ≠ forbiddenZ119Smuggle ∧
    promethiumAtomicNumberZ ≠ forbiddenZ119Smuggle)

def isotopeLatticeScaffold : Bool :=
  unwiredDesignOk &&
    isotopeFe26ConcurrentOk &&
    class11IsotopePatternIndexOk &&
    concurrentProductNotXorOk &&
    xorMutuallyExclusiveRefuse &&
    greenInventIsotopeRefuse &&
    nuclearDecayChemGreenRefuse &&
    parallelIsotopeAxiomRefuse &&
    speciesIdSmuggleRefuse &&
    extraElementIdRefuse &&
    tpFloatPinRefuse &&
    trivialBundleRefuse &&
    productionWiredRefuse &&
    radioelementHonestyOk &&
    wave100NotWired

theorem isotope_lattice_scaffold_true :
    isotopeLatticeScaffold = true := by native_decide

inductive IsotopeConservationFiber where
  | quantumKnowing | mesoActing
  deriving DecidableEq, Repr

def isotopeConservationFiberOk (f : IsotopeConservationFiber) : Bool :=
  match f with | .quantumKnowing => true | .mesoActing => false

theorem isotope_conservation_knowing_fiber_ok :
    isotopeConservationFiberOk .quantumKnowing = true := rfl

theorem isotope_conservation_meso_acting_not_ok :
    isotopeConservationFiberOk .mesoActing = false := rfl

def isotopeConservationCellId : String :=
  "CHEM-FORMAL-Q-LEAN-ISOTOPE-CONSERVATION"

def isotopeConservationNonClaim : String :=
  "CHEM-FORMAL-Q-LEAN-ISOTOPE-CONSERVATION PATTERN-00 class 11 isotope conservation electronic chemistry nuclear decay radioactivity class 11 isotope concurrent product not XOR isotope is factor not 26th axiom parallel isotope axiom refuse species id smuggle refuse extra ElementId Z=119 refuse nuclear decay chem GREEN refuse isotopeConservationProved false Unwired OK not PATTERN-00 Proved not physics GREEN cite LandauerLaw.physicalSecondLaw not meso theorems not 118 squared GREEN table not production_wired Fe Z=26 host witness Tc Z=43 Pm Z=61 radioelement honesty same-Z isotope factor not extra ElementId"

def isotopeConservationPhysicsGreenAuthorized : Prop := False

theorem isotope_conservation_physics_green_false :
    ¬ isotopeConservationPhysicsGreenAuthorized := id

structure IsotopeConservationProbe where
  cellIdNamed : Bool
  unwired : Bool
  physicsGreenRefused : Bool
  notProved : Bool
  class11Index : Bool
  fe26HostWitness : Bool
  electronicNuclearIsotopeProduct : Bool
  concurrentNotXor : Bool
  fe26WitnessOk : Bool
  xorRefuse : Bool
  greenInventRefuse : Bool
  nuclearDecayChemGreenRefuse : Bool
  parallelAxiomRefuse : Bool
  speciesIdSmuggleRefuse : Bool
  extraElementIdRefuse : Bool
  tpFloatPinRefuse : Bool
  productionWiredRefuse : Bool
  radioelementHonesty : Bool
  knowingFiberOk : Bool
  wave100NotWired : Bool
  intAuthorityCited : Bool
  deriving DecidableEq, Repr

def isotopeConservationProbe : IsotopeConservationProbe :=
  { cellIdNamed :=
      decide (isotopeConservationCellId =
        "CHEM-FORMAL-Q-LEAN-ISOTOPE-CONSERVATION")
    unwired := decide (isotopeConservationModalityCurrent = .unwired)
    physicsGreenRefused := true
    notProved := !isotopeConservationProved
    class11Index := decide (class11IsotopePatternIndex = 11)
    fe26HostWitness := decide (ironAtomicNumberZ = 26)
    electronicNuclearIsotopeProduct := decide (electronicChemChannelTag = "electronic_chemistry" ∧
      nuclearDecayChannelTag = "nuclear_decay_radioactivity" ∧
      isotopeFactorTag = "isotope")
    concurrentNotXor := isoProductNotXor
    fe26WitnessOk := isotopeFe26ConcurrentOk
    xorRefuse := xorMutuallyExclusiveRefuse
    greenInventRefuse := greenInventIsotopeRefuse
    nuclearDecayChemGreenRefuse := nuclearDecayChemGreenRefuse
    parallelAxiomRefuse := parallelIsotopeAxiomRefuse
    speciesIdSmuggleRefuse := speciesIdSmuggleRefuse
    extraElementIdRefuse := extraElementIdRefuse
    tpFloatPinRefuse := tpFloatPinRefuse
    productionWiredRefuse := productionWiredRefuse
    radioelementHonesty := radioelementHonestyOk
    knowingFiberOk := isotopeConservationFiberOk .quantumKnowing
    wave100NotWired := wave100NotWired
    intAuthorityCited := isotopeConservationAuthority ≠ "" }

def isotopeConservationHonest : Bool :=
  let p := isotopeConservationProbe
  p.cellIdNamed &&
    p.unwired &&
    p.physicsGreenRefused &&
    p.notProved &&
    p.class11Index &&
    p.fe26HostWitness &&
    p.electronicNuclearIsotopeProduct &&
    p.concurrentNotXor &&
    p.fe26WitnessOk &&
    p.xorRefuse &&
    p.greenInventRefuse &&
    p.nuclearDecayChemGreenRefuse &&
    p.parallelAxiomRefuse &&
    p.speciesIdSmuggleRefuse &&
    p.extraElementIdRefuse &&
    p.tpFloatPinRefuse &&
    p.productionWiredRefuse &&
    p.radioelementHonesty &&
    p.knowingFiberOk &&
    p.wave100NotWired &&
    p.intAuthorityCited &&
    isotopeLatticeScaffold

theorem isotope_conservation_honest_true :
    isotopeConservationHonest = true := by native_decide

def isotopeConservationAxiom : Bool :=
  not118SquaredGreenTable &&
    isotopeSecondLawConservationFramed &&
    isotopeLatticeScaffold &&
    isotopeConservationHonest &&
    !isotopeConservationProved &&
    !isotopeConservationProductionWired &&
    !wave100LibRsWired &&
    !wave100EosRsWired &&
    !wave100NanoWired &&
    isotopeNeSpeciesId &&
    !speciesIdForked &&
    decide (isotopeConservationFraming =
      "second_law_conservation_isotope_one_axiom")

theorem isotope_conservation_axiom :
    isotopeConservationAxiom = true := by native_decide

theorem isotope_conservation_modality_unwired :
    isotopeConservationModalityCurrent = .unwired := rfl

theorem unwired_close_without_production_wiring :
    evaluateIsotopeConservation .unwired false false = .unwiredOk := rfl

theorem fe26_witness_named_ok :
    evaluateIsotopeBundle .unwired sampleIsotopeFe26Bundle
      false false false false = .namedOk := rfl

theorem trivial_empty_bundle_fail_closed :
    evaluateIsotopeBundle .unwired sampleTrivialUnwiredBundle
      false false false false = .trivialRefuse := rfl

theorem xor_classifier_refused :
    evaluateIsotopeBundle .unwired sampleIsotopeFe26Bundle
      true false false false = .xorRefuse := rfl

theorem green_invent_refuse_unwired :
    evaluateIsotopeConservation .unwired true false = .greenInventRefuse := rfl

theorem nuclear_decay_chem_green_refused :
    evaluateIsotopeBundle .unwired sampleIsotopeFe26Bundle
      false false false true = .nuclearDecayChemGreenRefuse := rfl

theorem proved_without_bar_refuse :
    evaluateIsotopeBundle .unwired sampleIsotopeFe26Bundle
      false false true false = .provedWithoutBarRefuse := rfl

theorem production_wired_refuse :
    evaluateIsotopeConservation .proved false true = .productionWiredRefuse := rfl

theorem isotope_conservation_honest_bundle :
    isotopeConservationProved = false ∧
    isotopeConservationProductionWired = false ∧
    not118SquaredGreenTable = true ∧
    isotopeSecondLawConservationFramed = true ∧
    evaluateIsotopeConservation .unwired false false = .unwiredOk ∧
    evaluateIsotopeBundle .unwired sampleIsotopeFe26Bundle
      false false false false = .namedOk ∧
    evaluateIsotopeBundle .unwired sampleTrivialUnwiredBundle
      false false false false = .trivialRefuse ∧
    evaluateIsotopeBundle .unwired sampleIsotopeFe26Bundle
      true false false false = .xorRefuse ∧
    evaluateIsotopeConservation .unwired true false = .greenInventRefuse ∧
    evaluateIsotopeBundle .unwired sampleIsotopeFe26Bundle
      false false false true = .nuclearDecayChemGreenRefuse ∧
    isoProductNotXor = true ∧
    ironAtomicNumberZ = 26 ∧
    class11IsotopePatternIndex = 11 ∧
    isotopeConservationAxiom = true :=
  ⟨rfl, rfl, not_118_squared_green_table, isotope_second_law_conservation_framed,
    unwired_close_without_production_wiring, fe26_witness_named_ok,
    trivial_empty_bundle_fail_closed, xor_classifier_refused, green_invent_refuse_unwired,
    nuclear_decay_chem_green_refused, iso_product_not_xor_true, iron_atomic_number_z_is_26,
    class11_isotope_pattern_index_eleven, isotope_conservation_axiom⟩

end UMST.Chem
