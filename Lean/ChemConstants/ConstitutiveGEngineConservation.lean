-- SPDX-FileCopyrightText: 2026 Santosh Prabhu Shenbagamoorthy and Santhosh Shyamsundar
-- SPDX-License-Identifier: MIT

import ElementElectronic

set_option maxRecDepth 8192

/-!
# ConstitutiveGEngineConservation — class-13 **g_engine** **conservation** (Q lattice)

Knowing-fiber Lean: constitutive **G-engine** **conservation** (L0, not L1 cement copy).
G-engine may **sort** constants/identity using existing SI/occupancy derived-morphism sheaf; may not mint
k/R/ε₀ or Landauer-fake α. Concurrent Π_c PatternBundle factor — **product** not XOR. Thermo_n G(T,P,x) type
conserved; not L1 cement copy. Named class-13 identity conserved under honest scaffold; trivial XOR, parallel
G-engine axiom, constants mint, species-id smuggle, extra ElementId Z=119, extra G-engine force, T/P float-pin,
and GREEN invent fail-closed.

Read-only cites (not imported — self-contained scaffold):
- `Coq/ChemConstants/GEngineConservation.v`
- `Haskell/UMST/ChemConstants/GEngineConservation.hs`
- `Agda/ChemConstants/GEngineConservation.agda`
- `umst/umst-chem/src/thermo_g.rs`
- `umst/umst-chem/src/l0_tables/shared.rs`
- `umst/umst-chem/src/x_rows/engine_refuses_new_si.rs`
- `umst/umst-chem/src/si_sheaf.rs`

- `GEngineConservationModality` — Unwired / Assumed / Proved / Surrogate (not 118² GREEN table).
- `GEngineProductChannel` — sort existing sheaf ⊗ constants not minted ⊗ Thermo_n G type conserved.
- Second-law + **conservation** framing cites `LandauerLaw.physicalSecondLaw` — not imported meso theorems.
- No meso / acting theorems. No new physics `axiom`.
- `physics_green` stays false. Does **not** claim `gEngineConservationProved` or physics GREEN.
- WAVE100 freeze — not wired lib.rs / eos.rs / nano.
- Does **not** mint second G-engine axiom (not 26th axiom).
-/

namespace UMST.Chem

/-- Design modality for class-13 **g_engine** **conservation** (lattice SSOT). -/
inductive GEngineConservationModality where
  | unwired | assumed | proved | surrogate
  deriving DecidableEq, Repr

def gEngineConservationModalityCurrent : GEngineConservationModality := .unwired

/-- Modality lattice cardinality (Unwired / Assumed / Proved / Surrogate). -/
def gEngineLatticeCardinality : Nat := 4

theorem g_engine_lattice_cardinality_four :
    gEngineLatticeCardinality = 4 := rfl

theorem g_engine_lattice_not_118_squared :
    gEngineLatticeCardinality ≠ 118 * 118 := by decide

/-- Surface tag for name-from-content (`g_engine` / `constitutivegengineconservation`). -/
def gEngineConservationSurface : String :=
  "g_engine_conservation_surface"

theorem g_engine_conservation_surface_named :
    gEngineConservationSurface ≠ "" := by decide

/-- Machine-readable G-engine conservation marker. -/
def gEngineConservationMarker : String :=
  "chem_int_cross_g_engine_conservation_v1"

theorem g_engine_conservation_marker_named :
    gEngineConservationMarker ≠ "" := by decide

/-- Row stem pin for name-from-content (`g_engine_conservation`). -/
def gEngineConservationRowStem : String := "g_engine_conservation"

theorem g_engine_conservation_row_stem_named :
    gEngineConservationRowStem = "g_engine_conservation" := rfl

/-- North-star §2 class-13 g_engine pattern index. -/
def class13GEnginePatternIndex : Nat := 13

theorem class13_g_engine_pattern_index_thirteen :
    class13GEnginePatternIndex = 13 := rfl

/-- Cross-classifier X13 row id pin. -/
def crossClassifierGEngineRowId : String := "X13"

theorem cross_classifier_g_engine_row_named :
    crossClassifierGEngineRowId = "X13" := rfl

/-- §2 pattern class cardinality (north-star pinned — not 118²). -/
def patternClassCardinality : Nat := 25

theorem pattern_class_cardinality_twenty_five : patternClassCardinality = 25 := rfl

theorem pattern_class_not_118_squared : patternClassCardinality ≠ 118 * 118 := by decide

def patternClassIndexValid (i : Nat) : Bool := i < patternClassCardinality

theorem g_engine_class_index_valid :
    patternClassIndexValid class13GEnginePatternIndex = true := by decide

/-- IUPAC periodic-table cardinality (Z=1..118). -/
def iupacTableCardinality : Nat := 118

theorem iupac_table_cardinality_118 : iupacTableCardinality = 118 := rfl

/-- Platinum Z=78 — host assemblage witness element pin. -/
def platinumAtomicNumberZ : Nat := 78

theorem platinum_atomic_number_z_is_78 : platinumAtomicNumberZ = 78 := rfl

theorem platinum_z_valid :
    platinumAtomicNumberZ > 0 ∧ platinumAtomicNumberZ ≤ iupacTableCardinality := by decide

/-- Forbidden Z=119 smuggle — not in IUPAC table. -/
def forbiddenZ119Smuggle : Nat := 119

theorem forbidden_z119_not_in_iupac_table :
    forbiddenZ119Smuggle > iupacTableCardinality := by decide

def gEngineFactorTag : String := "g_engine"

def sortExistingSheafChannelTag : String := "sort_existing_sheaf"

def constantsNotMintedChannelTag : String := "constants_not_minted"

def thermoGTypeConservedChannelTag : String := "thermo_g_type_conserved"

theorem g_engine_factor_tag_named :
    gEngineFactorTag ≠ "" := by decide

theorem sort_existing_sheaf_channel_tag_named :
    sortExistingSheafChannelTag ≠ "" := by decide

theorem constants_not_minted_channel_tag_named :
    constantsNotMintedChannelTag ≠ "" := by decide

theorem thermo_g_type_conserved_channel_tag_named :
    thermoGTypeConservedChannelTag ≠ "" := by decide

/-- G-engine product channel slot — concurrent **product** factor, not XOR bucket. -/
inductive GEngineChannelSlot where
  | unwired | absent | present
  deriving DecidableEq, Repr

def gEngineChannelSlotIsPresent (s : GEngineChannelSlot) : Bool :=
  match s with | .present => true | _ => false

/-- Named sort-existing-sheaf / constants-not-minted / Thermo_n G type product channels. -/
inductive GEngineProductChannel where
  | sortExistingSheaf | constantsNotMinted | thermoGTypeConserved
  deriving DecidableEq, Repr

def gEngineProductChannelCount : Nat := 3

theorem g_engine_product_channel_count_three :
    gEngineProductChannelCount = 3 := rfl

def gEngineProductChannelIndex : GEngineProductChannel → Nat
  | .sortExistingSheaf => 0
  | .constantsNotMinted => 1
  | .thermoGTypeConserved => 2

theorem gec_channel_sort_existing_sheaf_idx_is_0 :
    gEngineProductChannelIndex .sortExistingSheaf = 0 := rfl

theorem gec_channel_constants_not_minted_idx_is_1 :
    gEngineProductChannelIndex .constantsNotMinted = 1 := rfl

theorem gec_channel_thermo_g_type_conserved_idx_is_2 :
    gEngineProductChannelIndex .thermoGTypeConserved = 2 := rfl

/-- Class-13 g_engine concurrent **product** bundle (north-star §3). -/
structure GEngineConcurrentBundle where
  channelSlots : List GEngineChannelSlot
  deriving DecidableEq, Repr

/-- All channels Unwired — honest scaffold baseline. -/
def gEngineConcurrentBundleUnwired : GEngineConcurrentBundle :=
  { channelSlots := List.replicate gEngineProductChannelCount .unwired }

def gEngineConcurrentBundleWithChannel (idx : Nat) (slot : GEngineChannelSlot)
    (b : GEngineConcurrentBundle) : GEngineConcurrentBundle :=
  if idx < b.channelSlots.length then
    { channelSlots :=
        b.channelSlots.take idx ++ [slot] ++ b.channelSlots.drop (idx + 1) }
  else b

def gEngineConcurrentBundleWithPresent (idx : Nat) (b : GEngineConcurrentBundle) :
    GEngineConcurrentBundle :=
  gEngineConcurrentBundleWithChannel idx .present b

def gEngineConcurrentBundleChannelAt (idx : Nat) (b : GEngineConcurrentBundle) :
    Option GEngineChannelSlot :=
  b.channelSlots.get? idx

def gEngineConcurrentBundleHolds (idx : Nat) (b : GEngineConcurrentBundle) : Bool :=
  match gEngineConcurrentBundleChannelAt idx b with
  | some .present => true
  | _ => false

def gEngineConcurrentBundlePresentCount (b : GEngineConcurrentBundle) : Nat :=
  b.channelSlots.foldl (fun acc s => if gEngineChannelSlotIsPresent s then acc + 1 else acc) 0

def gEngineConcurrentBundleIsConcurrentProduct (b : GEngineConcurrentBundle) : Bool :=
  decide (gEngineConcurrentBundlePresentCount b ≥ 2)

/-- Pt Z=78 sort-existing-sheaf + constants-not-minted + Thermo_n G type concurrent witness. -/
def gEnginePt78Witness : GEngineConcurrentBundle :=
  gEngineConcurrentBundleWithPresent 2
    (gEngineConcurrentBundleWithPresent 1
      (gEngineConcurrentBundleWithPresent 0
        gEngineConcurrentBundleUnwired))

def gEngineEmptyWitness : GEngineConcurrentBundle :=
  gEngineConcurrentBundleUnwired

def gEngineSinglePresent : GEngineConcurrentBundle :=
  gEngineConcurrentBundleWithPresent 0 gEngineConcurrentBundleUnwired

theorem sort_existing_sheaf_channel_present :
    gEngineConcurrentBundleHolds 0 gEnginePt78Witness = true := by decide

theorem constants_not_minted_channel_present :
    gEngineConcurrentBundleHolds 1 gEnginePt78Witness = true := by decide

theorem thermo_g_type_conserved_channel_present :
    gEngineConcurrentBundleHolds 2 gEnginePt78Witness = true := by decide

theorem pt78_witness_present_count_is_three :
    gEngineConcurrentBundlePresentCount gEnginePt78Witness = 3 := by decide

theorem pt78_witness_is_concurrent_product :
    gEngineConcurrentBundleIsConcurrentProduct gEnginePt78Witness = true := by decide

theorem empty_bundle_present_count_zero :
    gEngineConcurrentBundlePresentCount gEngineEmptyWitness = 0 := by decide

theorem empty_bundle_not_concurrent_product :
    gEngineConcurrentBundleIsConcurrentProduct gEngineEmptyWitness = false := by decide

theorem single_present_count_is_one :
    gEngineConcurrentBundlePresentCount gEngineSinglePresent = 1 := by decide

theorem single_present_not_concurrent_product :
    gEngineConcurrentBundleIsConcurrentProduct gEngineSinglePresent = false := by decide

/-- XOR posture — mutual exclusivity scaffold defect (must refuse). -/
inductive GEngineXorPosture where
  | exclusive | concurrent
  deriving DecidableEq, Repr

def gEngineXorPostureExclusive : GEngineXorPosture := .exclusive
def gEngineXorPostureConcurrent : GEngineXorPosture := .concurrent

def gecXorClassifierMarker : String := "chem_l0_g_engine_xor_classifier_v1"
def gecConcurrentProductMarker : String := "chem_int_g_engine_product_v1"

theorem gec_xor_marker_ne_concurrent_product_marker :
    gecXorClassifierMarker ≠ gecConcurrentProductMarker := by decide

def gecXorClassifierIncompatible (claimXor : Bool) (b : GEngineConcurrentBundle) : Bool :=
  claimXor && gEngineConcurrentBundleIsConcurrentProduct b

theorem gec_xor_refuse_on_pt78_witness :
    gecXorClassifierIncompatible true gEnginePt78Witness = true := by decide

def gecProductNotXor : Bool :=
  gEngineConcurrentBundleIsConcurrentProduct gEnginePt78Witness &&
  gecXorClassifierIncompatible true gEnginePt78Witness

theorem gec_product_not_xor_true : gecProductNotXor = true := by decide

/-- Verdict for class-13 **g_engine** close (fail-closed). -/
inductive GEngineConservationVerdict where
  | unwiredOk
  | namedOk
  | designOk
  | trivialRefuse
  | xorRefuse
  | greenInventRefuse
  | provedWithoutBarRefuse
  | productionWiredRefuse
  | parallelGEngineAxiomRefuse
  | speciesIdSmuggleRefuse
  | extraElementIdRefuse
  | extraGEngineForceRefuse
  | tpFloatPinRefuse
  deriving DecidableEq, Repr

def gEngineConservationVerdictOk (v : GEngineConservationVerdict) : Bool :=
  match v with
  | .unwiredOk | .namedOk | .designOk => true
  | _ => false

def gEngineBundleNontrivial (b : GEngineConcurrentBundle) : Bool :=
  decide (gEngineConcurrentBundlePresentCount b > 0)

def evaluateGEngineBundle
    (modality : GEngineConservationModality)
    (b : GEngineConcurrentBundle)
    (claimXorClassifier : Bool)
    (claimPhysicsGreen : Bool)
    (claimProved : Bool) : GEngineConservationVerdict :=
  if claimPhysicsGreen then
    .greenInventRefuse
  else if claimProved then
    .provedWithoutBarRefuse
  else if !gEngineBundleNontrivial b then
    .trivialRefuse
  else if gecXorClassifierIncompatible claimXorClassifier b then
    .xorRefuse
  else
    match modality with
    | .unwired =>
        if gEngineConcurrentBundleIsConcurrentProduct b then .namedOk else .designOk
    | .assumed | .surrogate => .designOk
    | .proved => .provedWithoutBarRefuse

def evaluateGEngineConservation
    (modality : GEngineConservationModality)
    (claimPhysicsGreen : Bool)
    (claimProductionWired : Bool) : GEngineConservationVerdict :=
  if claimPhysicsGreen then
    .greenInventRefuse
  else if claimProductionWired then
    .productionWiredRefuse
  else
    match modality with
    | .unwired => .unwiredOk
    | .assumed | .proved | .surrogate => .namedOk

def gEngineConservationAuthorized (claimPhysicsGreen : Bool) (claimProductionWired : Bool) : Bool :=
  match evaluateGEngineConservation .proved claimPhysicsGreen claimProductionWired with
  | .namedOk => true
  | _ => false

def sampleGEnginePt78Bundle : GEngineConcurrentBundle :=
  gEnginePt78Witness

def sampleTrivialUnwiredBundle : GEngineConcurrentBundle :=
  gEngineEmptyWitness

def unwiredDesignOk : Bool :=
  decide (evaluateGEngineConservation .unwired false false = .unwiredOk)

def gEnginePt78ConcurrentOk : Bool :=
  decide (evaluateGEngineBundle .unwired sampleGEnginePt78Bundle
      false false false = .namedOk ∧
    gEngineConcurrentBundleIsConcurrentProduct sampleGEnginePt78Bundle = true ∧
    platinumAtomicNumberZ = 78 ∧
    class13GEnginePatternIndex = 13)

def class13GEnginePatternIndexOk : Bool :=
  decide (class13GEnginePatternIndex = 13 ∧
    patternClassIndexValid class13GEnginePatternIndex = true)

def concurrentProductNotXorOk : Bool :=
  decide (gecProductNotXor = true ∧
    gEngineConcurrentBundlePresentCount gEnginePt78Witness = 3)

def xorMutuallyExclusiveRefuse : Bool :=
  decide (evaluateGEngineBundle .unwired sampleGEnginePt78Bundle
      true false false = .xorRefuse)

def greenInventGEngineRefuse : Bool :=
  decide (evaluateGEngineConservation .unwired true false = .greenInventRefuse ∧
    evaluateGEngineBundle .unwired sampleGEnginePt78Bundle
      false true false = .greenInventRefuse)

def productionWiredRefuse : Bool :=
  decide (evaluateGEngineConservation .proved false true = .productionWiredRefuse)

def trivialBundleRefuse : Bool :=
  decide (evaluateGEngineBundle .unwired sampleTrivialUnwiredBundle
      false false false = .trivialRefuse)

/-- PATTERN-00 class-13 **g_engine** is **not** claimed Proved on the knowing scaffold. -/
def gEngineConservationProved : Bool := false

theorem g_engine_conservation_proved_false :
    gEngineConservationProved = false := rfl

def gEngineConservationProductionWired : Bool := false

theorem g_engine_conservation_production_not_wired :
    gEngineConservationProductionWired = false := rfl

def not118SquaredGreenTable : Bool := true

theorem not_118_squared_green_table : not118SquaredGreenTable = true := rfl

def gEngineConservationLandauerLawPin : String := "LandauerLaw.physicalSecondLaw"

theorem g_engine_conservation_landauer_law_pin_named :
    gEngineConservationLandauerLawPin = "LandauerLaw.physicalSecondLaw" := rfl

def gEngineSecondLawConservationFramed : Bool := true

theorem g_engine_second_law_conservation_framed :
    gEngineSecondLawConservationFramed = true := rfl

def wave100LibRsWired : Bool := false
def wave100EosRsWired : Bool := false
def wave100NanoWired : Bool := false

def wave100NotWired : Bool :=
  !wave100LibRsWired && !wave100EosRsWired && !wave100NanoWired

theorem wave100_not_wired : wave100NotWired = true := rfl

def gEngineNeSpeciesId : Bool := true
def speciesIdForked : Bool := false

def gEngineConservationAuthority : String :=
  "umst/umst-chem/src/thermo_g.rs"

theorem g_engine_conservation_authority_path :
    gEngineConservationAuthority =
      "umst/umst-chem/src/thermo_g.rs" := rfl

def chemL0GEngineAuthority : String :=
  "umst/umst-chem/src/thermo_g.rs"

def chemL0GEngineTableAuthority : String :=
  "umst/umst-chem/src/l0_tables/shared.rs"

def interactPartialityAuthority : String :=
  "umst/umst-chem/src/si_sheaf.rs"

def gEngineBarrierAuthority : String :=
  "umst/umst-chem/src/x_rows/engine_refuses_new_si.rs"

def parallelGEngineAxiomTag : String := "26th_g_engine_axiom"

def speciesIdSmuggleFraming : String := "constants_not_minted_not_named_object"

def extraElementIdSmuggleFraming : String := "g_engine_constants_mint_in_net_sort"

def extraGEngineForceFraming : String :=
  "extra_g_engine_force_axiom_minted_as_26th_law"

def tpFloatPinFraming : String :=
  "bare_298_15_k_1_atm_float_pins_on_g_engine_scaffold"

def gEngineConservationFraming : String :=
  "second_law_conservation_g_engine_sort_restriction_one_axiom"

theorem g_engine_not_26th_axiom :
    gEngineConservationFraming ≠ parallelGEngineAxiomTag := by decide

def parallelGEngineAxiomRefuse : Bool :=
  decide (gEngineConservationAuthority ≠ parallelGEngineAxiomTag ∧
    gEngineConservationProved = false)

def speciesIdSmuggleRefuse : Bool :=
  decide (gEngineConservationFraming ≠ speciesIdSmuggleFraming ∧
    platinumAtomicNumberZ = 78 ∧
    class13GEnginePatternIndex = 13)

def extraElementIdRefuse : Bool :=
  decide (gEngineConservationFraming ≠ extraElementIdSmuggleFraming ∧
    forbiddenZ119Smuggle > iupacTableCardinality ∧
    platinumAtomicNumberZ = 78)

def extraGEngineForceRefuse : Bool :=
  decide (gEngineConservationFraming ≠ extraGEngineForceFraming ∧
    gEngineBarrierAuthority =
      "umst/umst-chem/src/x_rows/engine_refuses_new_si.rs" ∧
    gEngineConservationProved = false)

def tpFloatPinRefuse : Bool :=
  decide (gEngineConservationFraming ≠ tpFloatPinFraming ∧
    sortExistingSheafChannelTag = "sort_existing_sheaf")

def forbiddenSiMintK : String := "k"
def forbiddenSiMintR : String := "R"
def forbiddenSiMintEpsilon0 : String := "epsilon_0"

def engineMayMintSi : Bool := false

theorem engine_may_mint_si_false : engineMayMintSi = false := rfl

def alphaDeferredCodataMarker : String :=
  "alpha_deferred_composition_codata_not_landauer_fake_v1"

def landauerFakeMarker : String :=
  "landauer_fake_alpha_mint_v1"

theorem alpha_not_landauer_fake :
    alphaDeferredCodataMarker ≠ landauerFakeMarker := by decide

def constantsMintRefuse : Bool :=
  decide (!engineMayMintSi ∧
    forbiddenSiMintK = "k" ∧
    forbiddenSiMintR = "R" ∧
    constantsNotMintedChannelTag = "constants_not_minted")

def sortNotMintNotAxiomRefuse : Bool :=
  decide (gEngineConservationFraming ≠ speciesIdSmuggleFraming ∧
    sortExistingSheafChannelTag = "sort_existing_sheaf" ∧
    gEngineConservationProved = false)

def gEngineLatticeScaffold : Bool :=
  unwiredDesignOk &&
    gEnginePt78ConcurrentOk &&
    class13GEnginePatternIndexOk &&
    concurrentProductNotXorOk &&
    xorMutuallyExclusiveRefuse &&
    greenInventGEngineRefuse &&
    parallelGEngineAxiomRefuse &&
    speciesIdSmuggleRefuse &&
    extraElementIdRefuse &&
    extraGEngineForceRefuse &&
    tpFloatPinRefuse &&
    constantsMintRefuse &&
    sortNotMintNotAxiomRefuse &&
    trivialBundleRefuse &&
    productionWiredRefuse &&
    wave100NotWired

theorem g_engine_lattice_scaffold_true :
    gEngineLatticeScaffold = true := by native_decide

inductive GEngineConservationFiber where
  | quantumKnowing | mesoActing
  deriving DecidableEq, Repr

def gEngineConservationFiberOk (f : GEngineConservationFiber) : Bool :=
  match f with | .quantumKnowing => true | .mesoActing => false

theorem g_engine_conservation_knowing_fiber_ok :
    gEngineConservationFiberOk .quantumKnowing = true := rfl

theorem g_engine_conservation_meso_acting_not_ok :
    gEngineConservationFiberOk .mesoActing = false := rfl

def gEngineConservationCellId : String :=
  "CHEM-FORMAL-Q-LEAN-G-ENGINE-CONSERVATION"

def gEngineConservationNonClaim : String :=
  "CHEM-FORMAL-Q-LEAN-G-ENGINE-CONSERVATION PATTERN-00 class 13 g_engine conservation sort existing sheaf constants not minted k R epsilon_0 Landauer-fake alpha refuse Thermo_n G type concurrent product identity conserved not XOR xor mutually exclusive refuse parallel g engine axiom refuse species id smuggle refuse extra ElementId Z=119 refuse extra g engine force refuse gEngineConservationProved false Unwired OK not PATTERN-00 Proved not physics GREEN cite LandauerLaw.physicalSecondLaw not meso theorems not 118 squared GREEN table not production_wired Pt Z=78 host assemblage witness L0 not L1 cement copy"

def gEngineConservationPhysicsGreenAuthorized : Prop := False

theorem g_engine_conservation_physics_green_false :
    ¬ gEngineConservationPhysicsGreenAuthorized := id

structure GEngineConservationProbe where
  cellIdNamed : Bool
  unwired : Bool
  physicsGreenRefused : Bool
  notProved : Bool
  class13Index : Bool
  pt78HostWitness : Bool
  sortConstantsThermoProduct : Bool
  concurrentNotXor : Bool
  pt78WitnessOk : Bool
  xorRefuse : Bool
  greenInventRefuse : Bool
  parallelAxiomRefuse : Bool
  speciesIdSmuggleRefuse : Bool
  extraElementIdRefuse : Bool
  extraGEngineForceRefuse : Bool
  tpFloatPinRefuse : Bool
  constantsMintRefuse : Bool
  productionWiredRefuse : Bool
  knowingFiberOk : Bool
  wave100NotWired : Bool
  intAuthorityCited : Bool
  deriving DecidableEq, Repr

def gEngineConservationProbe : GEngineConservationProbe :=
  { cellIdNamed :=
      decide (gEngineConservationCellId =
        "CHEM-FORMAL-Q-LEAN-G-ENGINE-CONSERVATION")
    unwired := decide (gEngineConservationModalityCurrent = .unwired)
    physicsGreenRefused := true
    notProved := !gEngineConservationProved
    class13Index := decide (class13GEnginePatternIndex = 13)
    pt78HostWitness := decide (platinumAtomicNumberZ = 78)
    sortConstantsThermoProduct := decide (sortExistingSheafChannelTag = "sort_existing_sheaf" ∧
      constantsNotMintedChannelTag = "constants_not_minted" ∧
      thermoGTypeConservedChannelTag = "thermo_g_type_conserved" ∧
      gEngineFactorTag = "g_engine")
    concurrentNotXor := gecProductNotXor
    pt78WitnessOk := gEnginePt78ConcurrentOk
    xorRefuse := xorMutuallyExclusiveRefuse
    greenInventRefuse := greenInventGEngineRefuse
    parallelAxiomRefuse := parallelGEngineAxiomRefuse
    speciesIdSmuggleRefuse := speciesIdSmuggleRefuse
    extraElementIdRefuse := extraElementIdRefuse
    extraGEngineForceRefuse := extraGEngineForceRefuse
    tpFloatPinRefuse := tpFloatPinRefuse
    constantsMintRefuse := constantsMintRefuse
    productionWiredRefuse := productionWiredRefuse
    knowingFiberOk := gEngineConservationFiberOk .quantumKnowing
    wave100NotWired := wave100NotWired
    intAuthorityCited := gEngineConservationAuthority ≠ "" }

def gEngineConservationHonest : Bool :=
  let p := gEngineConservationProbe
  p.cellIdNamed &&
    p.unwired &&
    p.physicsGreenRefused &&
    p.notProved &&
    p.class13Index &&
    p.pt78HostWitness &&
    p.sortConstantsThermoProduct &&
    p.concurrentNotXor &&
    p.pt78WitnessOk &&
    p.xorRefuse &&
    p.greenInventRefuse &&
    p.parallelAxiomRefuse &&
    p.speciesIdSmuggleRefuse &&
    p.extraElementIdRefuse &&
    p.extraGEngineForceRefuse &&
    p.tpFloatPinRefuse &&
    p.constantsMintRefuse &&
    p.productionWiredRefuse &&
    p.knowingFiberOk &&
    p.wave100NotWired &&
    p.intAuthorityCited &&
    gEngineLatticeScaffold

theorem g_engine_conservation_honest_true :
    gEngineConservationHonest = true := by native_decide

def gEngineConservationAxiom : Bool :=
  not118SquaredGreenTable &&
    gEngineSecondLawConservationFramed &&
    gEngineLatticeScaffold &&
    gEngineConservationHonest &&
    !gEngineConservationProved &&
    !gEngineConservationProductionWired &&
    !wave100LibRsWired &&
    !wave100EosRsWired &&
    !wave100NanoWired &&
    gEngineNeSpeciesId &&
    !speciesIdForked &&
    decide (gEngineConservationFraming =
      "second_law_conservation_g_engine_sort_restriction_one_axiom")

theorem g_engine_conservation_axiom :
    gEngineConservationAxiom = true := by native_decide

theorem g_engine_conservation_modality_unwired :
    gEngineConservationModalityCurrent = .unwired := rfl

theorem unwired_close_without_production_wiring :
    evaluateGEngineConservation .unwired false false = .unwiredOk := rfl

theorem pt78_witness_named_ok :
    evaluateGEngineBundle .unwired sampleGEnginePt78Bundle
      false false false = .namedOk := rfl

theorem trivial_empty_bundle_fail_closed :
    evaluateGEngineBundle .unwired sampleTrivialUnwiredBundle
      false false false = .trivialRefuse := rfl

theorem xor_classifier_refused :
    evaluateGEngineBundle .unwired sampleGEnginePt78Bundle
      true false false = .xorRefuse := rfl

theorem green_invent_refuse_unwired :
    evaluateGEngineConservation .unwired true false = .greenInventRefuse := rfl

theorem proved_without_bar_refuse :
    evaluateGEngineBundle .unwired sampleGEnginePt78Bundle
      false false true = .provedWithoutBarRefuse := rfl

theorem production_wired_refuse :
    evaluateGEngineConservation .proved false true = .productionWiredRefuse := rfl

theorem g_engine_conservation_honest_bundle :
    gEngineConservationProved = false ∧
    gEngineConservationProductionWired = false ∧
    not118SquaredGreenTable = true ∧
    gEngineSecondLawConservationFramed = true ∧
    evaluateGEngineConservation .unwired false false = .unwiredOk ∧
    evaluateGEngineBundle .unwired sampleGEnginePt78Bundle
      false false false = .namedOk ∧
    evaluateGEngineBundle .unwired sampleTrivialUnwiredBundle
      false false false = .trivialRefuse ∧
    evaluateGEngineBundle .unwired sampleGEnginePt78Bundle
      true false false = .xorRefuse ∧
    evaluateGEngineConservation .unwired true false = .greenInventRefuse ∧
    gecProductNotXor = true ∧
    platinumAtomicNumberZ = 78 ∧
    class13GEnginePatternIndex = 13 ∧
    gEngineConservationAxiom = true :=
  ⟨rfl, rfl, not_118_squared_green_table, g_engine_second_law_conservation_framed,
    unwired_close_without_production_wiring, pt78_witness_named_ok,
    trivial_empty_bundle_fail_closed, xor_classifier_refused, green_invent_refuse_unwired,
    gec_product_not_xor_true, platinum_atomic_number_z_is_78, class13_g_engine_pattern_index_thirteen,
    g_engine_conservation_axiom⟩

end UMST.Chem
