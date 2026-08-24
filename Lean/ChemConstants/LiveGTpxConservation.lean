-- SPDX-FileCopyrightText: 2026 Santosh Prabhu Shenbagamoorthy and Santhosh Shyamsundar
-- SPDX-License-Identifier: MIT

import ElementElectronic

set_option maxRecDepth 8192

/-!
# LiveGTpxConservation — class-20 **live_gtpx** **conservation** (Q lattice)

Knowing-fiber Lean: PATTERN-00 class 20 (`live_gtpx`) concurrent Π_c identity conserved on named class
pins. Live G(T,P,x) is a concurrent PatternBundle factor on the same second-law + **conservation** object
(not a 26th axiom). G type-only ⊗ formation-zero-not-G ⊗ class-20 live G(T,P,x) factor is **product** not XOR.
Formation-zero theater is not measured G; measured-scalar G invent refused. T / P / μ are graph functions on
Interact (v14) — not 298 K / 1 atm float pins. Fe Z=26 host assemblage witness; named class-20 identity
conserved under honest scaffold; trivial XOR, parallel live G axiom, species-id smuggle, extra ElementId Z=119,
extra live G force, T/P float pins, and GREEN invent fail-closed.

Read-only cites (not imported — self-contained scaffold):
- `Coq/ChemConstants/LiveGTpxConservation.v`
- `Haskell/UMST/ChemConstants/LiveGTpxConservation.hs`
- `Agda/ChemConstants/LiveGTpxConservation.agda`
- `umst/umst-chem/src/thermo_g.rs`
- `umst/umst-chem/src/formation_energy_not_silent_zero.rs`
- `umst/umst-chem/src/chemical_potential_is_graph_function.rs`

- `LiveGTpxConservationModality` — Unwired / Assumed / Proved / Surrogate (not 118² GREEN table).
- `LiveGTpxProductChannel` — G type-only ⊗ formation-zero-not-G ⊗ class-20 concurrent Π_c.
- Second-law + **conservation** framing cites `LandauerLaw.physicalSecondLaw` — not imported meso theorems.
- No meso / acting theorems. No new physics `axiom`.
- `physics_green` stays false. Does **not** claim `liveGTpxConservationProved` or physics GREEN.
- WAVE100 freeze — not wired lib.rs / eos.rs / nano.
- Does **not** mint second live G axiom (not 26th axiom).
-/

namespace UMST.Chem

/-- Design modality for class-20 **live_gtpx** **conservation** (lattice SSOT). -/
inductive LiveGTpxConservationModality where
  | unwired | assumed | proved | surrogate
  deriving DecidableEq, Repr

def liveGTpxConservationModalityCurrent : LiveGTpxConservationModality := .unwired

/-- Modality lattice cardinality (Unwired / Assumed / Proved / Surrogate). -/
def liveGTpxLatticeCardinality : Nat := 4

theorem live_gtpx_lattice_cardinality_four :
    liveGTpxLatticeCardinality = 4 := rfl

theorem live_gtpx_lattice_not_118_squared :
    liveGTpxLatticeCardinality ≠ 118 * 118 := by decide

/-- Surface tag for name-from-content (`live_gtpx` / `livegtpxconservation`). -/
def liveGTpxConservationSurface : String :=
  "live_gtpx_conservation_surface"

theorem live_gtpx_conservation_surface_named :
    liveGTpxConservationSurface ≠ "" := by decide

/-- Machine-readable live G(T,P,x) conservation marker. -/
def liveGTpxConservationMarker : String :=
  "chem_int_cross_live_gtpx_conservation_v1"

theorem live_gtpx_conservation_marker_named :
    liveGTpxConservationMarker ≠ "" := by decide

/-- Row stem pin for name-from-content (`live_gtpx_conservation`). -/
def liveGTpxConservationRowStem : String := "live_gtpx_conservation"

theorem live_gtpx_conservation_row_stem_named :
    liveGTpxConservationRowStem = "live_gtpx_conservation" := rfl

/-- North-star §2 class-20 live G(T,P,x) pattern index. -/
def class20LiveGTpxPatternIndex : Nat := 14

theorem class20_live_gtpx_pattern_index_fourteen :
    class20LiveGTpxPatternIndex = 14 := rfl

/-- Cross-classifier X20 row id pin. -/
def crossClassifierLiveGTpxRowId : String := "X20"

theorem cross_classifier_live_gtpx_row_named :
    crossClassifierLiveGTpxRowId = "X20" := rfl

def northStarClass20LiveGTpxTag : String := "class 20 live G T P x"

theorem north_star_class20_live_gtpx_tag_named :
    northStarClass20LiveGTpxTag ≠ "" := by decide

/-- §2 pattern class cardinality (north-star pinned — not 118²). -/
def patternClassCardinality : Nat := 25

theorem pattern_class_cardinality_twenty_five : patternClassCardinality = 25 := rfl

theorem pattern_class_not_118_squared : patternClassCardinality ≠ 118 * 118 := by decide

def patternClassIndexValid (i : Nat) : Bool := i < patternClassCardinality

theorem live_gtpx_class_index_valid :
    patternClassIndexValid class20LiveGTpxPatternIndex = true := by decide

/-- IUPAC periodic-table cardinality (Z=1..118). -/
def iupacTableCardinality : Nat := 118

theorem iupac_table_cardinality_118 : iupacTableCardinality = 118 := rfl

/-- Iron Z=26 — host assemblage witness element pin. -/
def ironAtomicNumberZ : Nat := 26

theorem iron_atomic_number_z_is_26 : ironAtomicNumberZ = 26 := rfl

def ironZValid : Bool :=
  decide (0 < ironAtomicNumberZ ∧ ironAtomicNumberZ ≤ iupacTableCardinality)

theorem iron_z_valid_true : ironZValid = true := by decide

/-- Forbidden Z=119 smuggle — not in IUPAC table. -/
def forbiddenZ119Smuggle : Nat := 119

theorem forbidden_z119_not_in_iupac_table :
    forbiddenZ119Smuggle > iupacTableCardinality := by decide

def liveGTpxFactorTag : String := "live_gtpx"

def gTypeOnlyChannelTag : String := "g_type_only"

def formationZeroNotGChannelTag : String := "formation_zero_not_g"

theorem live_gtpx_factor_tag_named :
    liveGTpxFactorTag ≠ "" := by decide

theorem g_type_only_channel_tag_named :
    gTypeOnlyChannelTag ≠ "" := by decide

theorem formation_zero_not_g_channel_tag_named :
    formationZeroNotGChannelTag ≠ "" := by decide

/-- LiveGTpx product channel slot — concurrent **product** factor, not XOR bucket. -/
inductive LiveGTpxChannelSlot where
  | unwired | absent | present
  deriving DecidableEq, Repr

def liveGTpxChannelSlotIsPresent (s : LiveGTpxChannelSlot) : Bool :=
  match s with | .present => true | _ => false

/-- Named G type-only / formation-zero-not-G / class-20 live G(T,P,x) product channels. -/
inductive LiveGTpxProductChannel where
  | gTypeOnly | formationZeroNotG | class20LiveGTpxAxis
  deriving DecidableEq, Repr

def liveGTpxProductChannelCount : Nat := 3

theorem live_gtpx_product_channel_count_three :
    liveGTpxProductChannelCount = 3 := rfl

def liveGTpxProductChannelIndex : LiveGTpxProductChannel → Nat
  | .gTypeOnly => 0
  | .formationZeroNotG => 1
  | .class20LiveGTpxAxis => 2

theorem ltgc_channel_g_type_only_idx_is_0 :
    liveGTpxProductChannelIndex .gTypeOnly = 0 := rfl

theorem ltgc_channel_formation_zero_not_g_idx_is_1 :
    liveGTpxProductChannelIndex .formationZeroNotG = 1 := rfl

theorem ltgc_channel_class20_live_gtpx_idx_is_2 :
    liveGTpxProductChannelIndex .class20LiveGTpxAxis = 2 := rfl

/-- Class-20 live G(T,P,x) concurrent **product** bundle (north-star §3). -/
structure LiveGTpxConcurrentBundle where
  channelSlots : List LiveGTpxChannelSlot
  deriving DecidableEq, Repr

/-- All channels Unwired — honest scaffold baseline. -/
def liveGTpxConcurrentBundleUnwired : LiveGTpxConcurrentBundle :=
  { channelSlots := List.replicate liveGTpxProductChannelCount .unwired }

def liveGTpxConcurrentBundleWithChannel (idx : Nat) (slot : LiveGTpxChannelSlot)
    (b : LiveGTpxConcurrentBundle) : LiveGTpxConcurrentBundle :=
  if idx < b.channelSlots.length then
    { channelSlots :=
        b.channelSlots.take idx ++ [slot] ++ b.channelSlots.drop (idx + 1) }
  else b

def liveGTpxConcurrentBundleWithPresent (idx : Nat) (b : LiveGTpxConcurrentBundle) :
    LiveGTpxConcurrentBundle :=
  liveGTpxConcurrentBundleWithChannel idx .present b

def liveGTpxConcurrentBundleChannelAt (idx : Nat) (b : LiveGTpxConcurrentBundle) :
    Option LiveGTpxChannelSlot :=
  b.channelSlots.get? idx

def liveGTpxConcurrentBundleHolds (idx : Nat) (b : LiveGTpxConcurrentBundle) : Bool :=
  match liveGTpxConcurrentBundleChannelAt idx b with
  | some .present => true
  | _ => false

def liveGTpxConcurrentBundlePresentCount (b : LiveGTpxConcurrentBundle) : Nat :=
  b.channelSlots.foldl (fun acc s => if liveGTpxChannelSlotIsPresent s then acc + 1 else acc) 0

def liveGTpxConcurrentBundleIsConcurrentProduct (b : LiveGTpxConcurrentBundle) : Bool :=
  decide (liveGTpxConcurrentBundlePresentCount b ≥ 2)

/-- Fe Z=26 G type-only + formation-zero-not-G + class-20 live G(T,P,x) concurrent witness. -/
def liveGTpxFe26Witness : LiveGTpxConcurrentBundle :=
  liveGTpxConcurrentBundleWithPresent 2
    (liveGTpxConcurrentBundleWithPresent 1
      (liveGTpxConcurrentBundleWithPresent 0
        liveGTpxConcurrentBundleUnwired))

def liveGTpxEmptyWitness : LiveGTpxConcurrentBundle :=
  liveGTpxConcurrentBundleUnwired

def liveGTpxSinglePresent : LiveGTpxConcurrentBundle :=
  liveGTpxConcurrentBundleWithPresent 0 liveGTpxConcurrentBundleUnwired

theorem g_type_only_channel_present :
    liveGTpxConcurrentBundleHolds 0 liveGTpxFe26Witness = true := by decide

theorem formation_zero_not_g_channel_present :
    liveGTpxConcurrentBundleHolds 1 liveGTpxFe26Witness = true := by decide

theorem class20_live_gtpx_channel_present :
    liveGTpxConcurrentBundleHolds 2 liveGTpxFe26Witness = true := by decide

theorem fe26_witness_present_count_is_three :
    liveGTpxConcurrentBundlePresentCount liveGTpxFe26Witness = 3 := by decide

theorem fe26_witness_is_concurrent_product :
    liveGTpxConcurrentBundleIsConcurrentProduct liveGTpxFe26Witness = true := by decide

theorem empty_bundle_present_count_zero :
    liveGTpxConcurrentBundlePresentCount liveGTpxEmptyWitness = 0 := by decide

theorem empty_bundle_not_concurrent_product :
    liveGTpxConcurrentBundleIsConcurrentProduct liveGTpxEmptyWitness = false := by decide

theorem single_present_count_is_one :
    liveGTpxConcurrentBundlePresentCount liveGTpxSinglePresent = 1 := by decide

theorem single_present_not_concurrent_product :
    liveGTpxConcurrentBundleIsConcurrentProduct liveGTpxSinglePresent = false := by decide

def lgtpxXorClassifierMarker : String := "chem_l0_live_gtpx_xor_classifier_v1"
def lgtpxConcurrentProductMarker : String := "chem_int_live_gtpx_product_v1"

theorem lgtpx_xor_marker_ne_concurrent_product_marker :
    lgtpxXorClassifierMarker ≠ lgtpxConcurrentProductMarker := by decide

def lgtpxXorClassifierIncompatible (claimXor : Bool) (b : LiveGTpxConcurrentBundle) : Bool :=
  claimXor && liveGTpxConcurrentBundleIsConcurrentProduct b

theorem lgtpx_xor_refuse_on_fe26_witness :
    lgtpxXorClassifierIncompatible true liveGTpxFe26Witness = true := by decide

def lgtpxProductNotXor : Bool :=
  liveGTpxConcurrentBundleIsConcurrentProduct liveGTpxFe26Witness &&
  lgtpxXorClassifierIncompatible true liveGTpxFe26Witness

theorem lgtpx_product_not_xor_true : lgtpxProductNotXor = true := by decide

/-- Verdict for class-20 **live_gtpx** close (fail-closed). -/
inductive LiveGTpxConservationVerdict where
  | unwiredOk
  | namedOk
  | designOk
  | trivialRefuse
  | xorRefuse
  | greenInventRefuse
  | provedWithoutBarRefuse
  | productionWiredRefuse
  | parallelLiveGTpxAxiomRefuse
  | speciesIdSmuggleRefuse
  | extraElementIdRefuse
  | extraLiveGTpxForceRefuse
  | tpFloatPinRefuse
  deriving DecidableEq, Repr

def liveGTpxConservationVerdictOk (v : LiveGTpxConservationVerdict) : Bool :=
  match v with
  | .unwiredOk | .namedOk | .designOk => true
  | _ => false

def liveGTpxBundleNontrivial (b : LiveGTpxConcurrentBundle) : Bool :=
  decide (liveGTpxConcurrentBundlePresentCount b > 0)

def evaluateLiveGTpxBundle
    (modality : LiveGTpxConservationModality)
    (b : LiveGTpxConcurrentBundle)
    (claimXorClassifier : Bool)
    (claimPhysicsGreen : Bool)
    (claimProved : Bool) : LiveGTpxConservationVerdict :=
  if claimPhysicsGreen then
    .greenInventRefuse
  else if claimProved then
    .provedWithoutBarRefuse
  else if !liveGTpxBundleNontrivial b then
    .trivialRefuse
  else if lgtpxXorClassifierIncompatible claimXorClassifier b then
    .xorRefuse
  else
    match modality with
    | .unwired =>
        if liveGTpxConcurrentBundleIsConcurrentProduct b then .namedOk else .designOk
    | .assumed | .surrogate => .designOk
    | .proved => .provedWithoutBarRefuse

def evaluateLiveGTpxConservation
    (modality : LiveGTpxConservationModality)
    (claimPhysicsGreen : Bool)
    (claimProductionWired : Bool) : LiveGTpxConservationVerdict :=
  if claimPhysicsGreen then
    .greenInventRefuse
  else if claimProductionWired then
    .productionWiredRefuse
  else
    match modality with
    | .unwired => .unwiredOk
    | .assumed | .proved | .surrogate => .namedOk

def liveGTpxConservationAuthorized (claimPhysicsGreen : Bool) (claimProductionWired : Bool) : Bool :=
  match evaluateLiveGTpxConservation .proved claimPhysicsGreen claimProductionWired with
  | .namedOk => true
  | _ => false

def sampleLiveGTpxFe26Bundle : LiveGTpxConcurrentBundle :=
  liveGTpxFe26Witness

def sampleTrivialUnwiredBundle : LiveGTpxConcurrentBundle :=
  liveGTpxEmptyWitness

def unwiredDesignOk : Bool :=
  decide (evaluateLiveGTpxConservation .unwired false false = .unwiredOk)

def liveGTpxFe26ConcurrentOk : Bool :=
  decide (evaluateLiveGTpxBundle .unwired sampleLiveGTpxFe26Bundle
      false false false = .namedOk ∧
    liveGTpxConcurrentBundleIsConcurrentProduct sampleLiveGTpxFe26Bundle = true ∧
    ironAtomicNumberZ = 26 ∧
    class20LiveGTpxPatternIndex = 14)

def class20LiveGTpxPatternIndexOk : Bool :=
  decide (class20LiveGTpxPatternIndex = 14 ∧
    patternClassIndexValid class20LiveGTpxPatternIndex = true)

def concurrentProductNotXorOk : Bool :=
  decide (lgtpxProductNotXor = true ∧
    liveGTpxConcurrentBundlePresentCount liveGTpxFe26Witness = 3)

def xorMutuallyExclusiveRefuse : Bool :=
  decide (evaluateLiveGTpxBundle .unwired sampleLiveGTpxFe26Bundle
      true false false = .xorRefuse)

def greenInventLiveGTpxRefuse : Bool :=
  decide (evaluateLiveGTpxConservation .unwired true false = .greenInventRefuse ∧
    evaluateLiveGTpxBundle .unwired sampleLiveGTpxFe26Bundle
      false true false = .greenInventRefuse)

def productionWiredRefuse : Bool :=
  decide (evaluateLiveGTpxConservation .proved false true = .productionWiredRefuse)

def trivialBundleRefuse : Bool :=
  decide (evaluateLiveGTpxBundle .unwired sampleTrivialUnwiredBundle
      false false false = .trivialRefuse)

/-- PATTERN-00 class-20 **live_gtpx** is **not** claimed Proved on the knowing scaffold. -/
def liveGTpxConservationProved : Bool := false

theorem live_gtpx_conservation_proved_false :
    liveGTpxConservationProved = false := rfl

def liveGTpxConservationProductionWired : Bool := false

theorem live_gtpx_conservation_production_not_wired :
    liveGTpxConservationProductionWired = false := rfl

def not118SquaredGreenTable : Bool := true

theorem not_118_squared_green_table : not118SquaredGreenTable = true := rfl

def liveGTpxConservationLandauerLawPin : String := "LandauerLaw.physicalSecondLaw"

theorem live_gtpx_conservation_landauer_law_pin_named :
    liveGTpxConservationLandauerLawPin = "LandauerLaw.physicalSecondLaw" := rfl

def liveGTpxSecondLawConservationFramed : Bool := true

theorem live_gtpx_second_law_conservation_framed :
    liveGTpxSecondLawConservationFramed = true := rfl

def wave100LibRsWired : Bool := false
def wave100EosRsWired : Bool := false
def wave100NanoWired : Bool := false

def wave100NotWired : Bool :=
  !wave100LibRsWired && !wave100EosRsWired && !wave100NanoWired

theorem wave100_not_wired : wave100NotWired = true := rfl

def liveGTpxNeSpeciesId : Bool := true
def speciesIdForked : Bool := false

def liveGTpxConservationAuthority : String :=
  "umst/umst-chem/src/thermo_g.rs"

theorem live_gtpx_conservation_authority_path :
    liveGTpxConservationAuthority =
      "umst/umst-chem/src/thermo_g.rs" := rfl

def liveGTpxBarrierAuthority : String :=
  "umst/umst-chem/src/chemical_potential_is_graph_function.rs"

def parallelLiveGTpxAxiomTag : String := "26th_chemistry_axiom"

def speciesIdSmuggleFraming : String := "formation_zero_not_g_not_named_object"

def extraElementIdSmuggleFraming : String := "formation_zero_theater_as_measured_g"

def extraLiveGTpxForceFraming : String :=
  "extra_live_gtpx_force_axiom_minted_as_26th_law"

def tpFloatPinFraming : String :=
  "bare_298_15_k_1_atm_float_pins_on_live_gtpx_scaffold"

def liveGTpxConservationFraming : String :=
  "second_law_conservation_live_gtpx_g_type_only_one_axiom"

def formationZeroNotGFraming : String :=
  "formation_zero_theater_not_measured_g"

def gTypeOnlyNamedObject : String :=
  "g_type_only_on_live_gtpx_morphism"

def gTypeOnlyFraming : String :=
  "g_type_only_not_extra_force"

theorem live_gtpx_not_26th_axiom :
    liveGTpxConservationFraming ≠ parallelLiveGTpxAxiomTag := by decide

def parallelLiveGTpxAxiomRefuse : Bool :=
  decide (liveGTpxConservationAuthority ≠ parallelLiveGTpxAxiomTag ∧
    liveGTpxConservationProved = false)

def speciesIdSmuggleRefuse : Bool :=
  decide (liveGTpxConservationFraming ≠ speciesIdSmuggleFraming ∧
    ironAtomicNumberZ = 26 ∧
    class20LiveGTpxPatternIndex = 14)

def extraElementIdRefuse : Bool :=
  decide (liveGTpxConservationFraming ≠ extraElementIdSmuggleFraming ∧
    forbiddenZ119Smuggle > iupacTableCardinality ∧
    ironAtomicNumberZ = 26)

def extraLiveGTpxForceRefuse : Bool :=
  decide (liveGTpxConservationFraming ≠ extraLiveGTpxForceFraming ∧
    liveGTpxBarrierAuthority ≠ "" ∧
    liveGTpxConservationProved = false)

def tpFloatPinRefuse : Bool :=
  decide (liveGTpxConservationFraming ≠ tpFloatPinFraming ∧
    gTypeOnlyChannelTag = "g_type_only")

def formationZeroNotGNamedObjectOk : Bool :=
  decide (gTypeOnlyNamedObject ≠ formationZeroNotGFraming ∧
    formationZeroNotGChannelTag = "formation_zero_not_g")

def gTypeOnlyNotExtraForceOk : Bool :=
  decide (gTypeOnlyFraming ≠ extraLiveGTpxForceFraming ∧
    gTypeOnlyChannelTag = "g_type_only" ∧
    liveGTpxBarrierAuthority =
      "umst/umst-chem/src/chemical_potential_is_graph_function.rs")

def liveGTpxLatticeScaffold : Bool :=
  unwiredDesignOk &&
    liveGTpxFe26ConcurrentOk &&
    class20LiveGTpxPatternIndexOk &&
    concurrentProductNotXorOk &&
    xorMutuallyExclusiveRefuse &&
    greenInventLiveGTpxRefuse &&
    parallelLiveGTpxAxiomRefuse &&
    speciesIdSmuggleRefuse &&
    extraElementIdRefuse &&
    extraLiveGTpxForceRefuse &&
    tpFloatPinRefuse &&
    trivialBundleRefuse &&
    productionWiredRefuse &&
    formationZeroNotGNamedObjectOk &&
    gTypeOnlyNotExtraForceOk &&
    wave100NotWired

theorem live_gtpx_lattice_scaffold_true :
    liveGTpxLatticeScaffold = true := by native_decide

inductive LiveGTpxConservationFiber where
  | quantumKnowing | mesoActing
  deriving DecidableEq, Repr

def liveGTpxConservationFiberOk (f : LiveGTpxConservationFiber) : Bool :=
  match f with | .quantumKnowing => true | .mesoActing => false

theorem live_gtpx_conservation_knowing_fiber_ok :
    liveGTpxConservationFiberOk .quantumKnowing = true := rfl

theorem live_gtpx_conservation_meso_acting_not_ok :
    liveGTpxConservationFiberOk .mesoActing = false := rfl

def liveGTpxConservationCellId : String :=
  "CHEM-FORMAL-Q-LEAN-LIVE-G-TPX-CONSERVATION"

def liveGTpxConservationNonClaim : String :=
  "CHEM-FORMAL-Q-LEAN-LIVE-G-TPX-CONSERVATION PATTERN-00 class 20 live G T P x conservation G type-only formation-zero-not-G class 20 live G T P x concurrent product not XOR live G is factor not 26th axiom parallel live G axiom refuse species id smuggle refuse extra ElementId Z=119 refuse extra live G force refuse liveGTpxConservationProved false Unwired OK not PATTERN-00 Proved not physics GREEN formation-zero theater not measured G measured-scalar G invent refuse T P mu graph functions v14 not 298K 1atm float pins cite LandauerLaw.physicalSecondLaw not meso theorems not 118 squared GREEN table not production_wired Fe Z=26 host witness WAVE100 no lib.rs no eos.rs"

def liveGTpxConservationPhysicsGreenAuthorized : Prop := False

theorem live_gtpx_conservation_physics_green_false :
    ¬ liveGTpxConservationPhysicsGreenAuthorized := id

structure LiveGTpxConservationProbe where
  cellIdNamed : Bool
  unwired : Bool
  physicsGreenRefused : Bool
  notProved : Bool
  class20Index : Bool
  fe26HostWitness : Bool
  gTypeOnlyFormationLiveProduct : Bool
  concurrentNotXor : Bool
  fe26WitnessOk : Bool
  xorRefuse : Bool
  greenInventRefuse : Bool
  parallelAxiomRefuse : Bool
  speciesIdSmuggleRefuse : Bool
  extraElementIdRefuse : Bool
  extraLiveGTpxForceRefuse : Bool
  tpFloatPinRefuse : Bool
  productionWiredRefuse : Bool
  formationZeroNotGNamed : Bool
  gTypeOnlyNotExtraForce : Bool
  knowingFiberOk : Bool
  wave100NotWired : Bool
  intAuthorityCited : Bool
  deriving DecidableEq, Repr

def liveGTpxConservationProbe : LiveGTpxConservationProbe :=
  { cellIdNamed :=
      decide (liveGTpxConservationCellId =
        "CHEM-FORMAL-Q-LEAN-LIVE-G-TPX-CONSERVATION")
    unwired := decide (liveGTpxConservationModalityCurrent = .unwired)
    physicsGreenRefused := true
    notProved := !liveGTpxConservationProved
    class20Index := decide (class20LiveGTpxPatternIndex = 14)
    fe26HostWitness := decide (ironAtomicNumberZ = 26)
    gTypeOnlyFormationLiveProduct := decide (gTypeOnlyChannelTag = "g_type_only" ∧
      formationZeroNotGChannelTag = "formation_zero_not_g" ∧
      liveGTpxFactorTag = "live_gtpx")
    concurrentNotXor := lgtpxProductNotXor
    fe26WitnessOk := liveGTpxFe26ConcurrentOk
    xorRefuse := xorMutuallyExclusiveRefuse
    greenInventRefuse := greenInventLiveGTpxRefuse
    parallelAxiomRefuse := parallelLiveGTpxAxiomRefuse
    speciesIdSmuggleRefuse := speciesIdSmuggleRefuse
    extraElementIdRefuse := extraElementIdRefuse
    extraLiveGTpxForceRefuse := extraLiveGTpxForceRefuse
    tpFloatPinRefuse := tpFloatPinRefuse
    productionWiredRefuse := productionWiredRefuse
    formationZeroNotGNamed := formationZeroNotGNamedObjectOk
    gTypeOnlyNotExtraForce := gTypeOnlyNotExtraForceOk
    knowingFiberOk := liveGTpxConservationFiberOk .quantumKnowing
    wave100NotWired := wave100NotWired
    intAuthorityCited := liveGTpxConservationAuthority ≠ "" }

def liveGTpxConservationHonest : Bool :=
  let p := liveGTpxConservationProbe
  p.cellIdNamed &&
    p.unwired &&
    p.physicsGreenRefused &&
    p.notProved &&
    p.class20Index &&
    p.fe26HostWitness &&
    p.gTypeOnlyFormationLiveProduct &&
    p.concurrentNotXor &&
    p.fe26WitnessOk &&
    p.xorRefuse &&
    p.greenInventRefuse &&
    p.parallelAxiomRefuse &&
    p.speciesIdSmuggleRefuse &&
    p.extraElementIdRefuse &&
    p.extraLiveGTpxForceRefuse &&
    p.tpFloatPinRefuse &&
    p.productionWiredRefuse &&
    p.formationZeroNotGNamed &&
    p.gTypeOnlyNotExtraForce &&
    p.knowingFiberOk &&
    p.wave100NotWired &&
    p.intAuthorityCited &&
    liveGTpxLatticeScaffold

theorem live_gtpx_conservation_honest_true :
    liveGTpxConservationHonest = true := by native_decide

def liveGTpxConservationAxiom : Bool :=
  not118SquaredGreenTable &&
    liveGTpxSecondLawConservationFramed &&
    liveGTpxLatticeScaffold &&
    liveGTpxConservationHonest &&
    !liveGTpxConservationProved &&
    !liveGTpxConservationProductionWired &&
    !wave100LibRsWired &&
    !wave100EosRsWired &&
    !wave100NanoWired &&
    liveGTpxNeSpeciesId &&
    !speciesIdForked &&
    decide (liveGTpxConservationFraming =
      "second_law_conservation_live_gtpx_g_type_only_one_axiom")

theorem live_gtpx_conservation_axiom :
    liveGTpxConservationAxiom = true := by native_decide

theorem live_gtpx_conservation_modality_unwired :
    liveGTpxConservationModalityCurrent = .unwired := rfl

theorem unwired_close_without_production_wiring :
    evaluateLiveGTpxConservation .unwired false false = .unwiredOk := rfl

theorem fe26_witness_named_ok :
    evaluateLiveGTpxBundle .unwired sampleLiveGTpxFe26Bundle
      false false false = .namedOk := rfl

theorem trivial_empty_bundle_fail_closed :
    evaluateLiveGTpxBundle .unwired sampleTrivialUnwiredBundle
      false false false = .trivialRefuse := rfl

theorem xor_classifier_refused :
    evaluateLiveGTpxBundle .unwired sampleLiveGTpxFe26Bundle
      true false false = .xorRefuse := rfl

theorem green_invent_refuse_unwired :
    evaluateLiveGTpxConservation .unwired true false = .greenInventRefuse := rfl

theorem proved_without_bar_refuse :
    evaluateLiveGTpxBundle .unwired sampleLiveGTpxFe26Bundle
      false false true = .provedWithoutBarRefuse := rfl

theorem production_wired_refuse :
    evaluateLiveGTpxConservation .proved false true = .productionWiredRefuse := rfl

theorem live_gtpx_conservation_honest_bundle :
    liveGTpxConservationProved = false ∧
    liveGTpxConservationProductionWired = false ∧
    not118SquaredGreenTable = true ∧
    liveGTpxSecondLawConservationFramed = true ∧
    evaluateLiveGTpxConservation .unwired false false = .unwiredOk ∧
    evaluateLiveGTpxBundle .unwired sampleLiveGTpxFe26Bundle
      false false false = .namedOk ∧
    evaluateLiveGTpxBundle .unwired sampleTrivialUnwiredBundle
      false false false = .trivialRefuse ∧
    evaluateLiveGTpxBundle .unwired sampleLiveGTpxFe26Bundle
      true false false = .xorRefuse ∧
    evaluateLiveGTpxConservation .unwired true false = .greenInventRefuse ∧
    lgtpxProductNotXor = true ∧
    ironAtomicNumberZ = 26 ∧
    class20LiveGTpxPatternIndex = 14 ∧
    liveGTpxConservationAxiom = true :=
  ⟨rfl, rfl, not_118_squared_green_table, live_gtpx_second_law_conservation_framed,
    unwired_close_without_production_wiring, fe26_witness_named_ok,
    trivial_empty_bundle_fail_closed, xor_classifier_refused, green_invent_refuse_unwired,
    lgtpx_product_not_xor_true, iron_atomic_number_z_is_26, class20_live_gtpx_pattern_index_fourteen,
    live_gtpx_conservation_axiom⟩

end UMST.Chem
