-- SPDX-FileCopyrightText: 2026 Santosh Prabhu Shenbagamoorthy and Santhosh Shyamsundar
-- SPDX-License-Identifier: MIT

import ElementElectronic

/-!
# EngineRefusesNewSi — constitutive engines refuse new SI mint **conservation** (Q lattice)

Knowing-fiber Lean: constitutive engines sort using the existing SI/occupancy/derived-morphism
sheaf; they do not mint k, R, or ε₀. ExactSI constants are unit morphisms; engines consult the
sheaf, they do not invent SI. α at current depth is deferred composition (CODATA), not Landauer-fake,
not a 26th axiom. Pairs `umst-chem` scaffold `engine_refuses_new_si` / **conservation** posture.

- `EngineRefusesNewSiModality` — Unwired / Assumed / Proved / Surrogate (not 118² GREEN table).
- `forbiddenSiMintK` / `forbiddenSiMintR` / `forbiddenSiMintEpsilon0` — refused engine mints.
- `engineMayMintSi` — always false @ Unwired.
- `evaluateEngineRefusesNewSi` — Unwired OK; SI-mint refuse; Landauer-fake refuse; 26th-axiom refuse; GREEN invent refuse.
- Second-law + **conservation** framing cites meso `UMST.Chem.Conservation` /
  `LandauerLaw.physicalSecondLaw` — not imported.
- No meso / acting theorems. No new physics `axiom`.
- `physics_green` stays false. Does **not** claim `engineRefusesNewSiProved` or physics GREEN.
- WAVE100 freeze — remainder deferred composition (env/time/cross-domain), not impossibility stop.
-/

namespace UMST.Chem

/-- Design modality for engine refuses new SI **conservation** (lattice SSOT). -/
inductive EngineRefusesNewSiModality where
  | unwired | assumed | proved | surrogate
  deriving DecidableEq, Repr

def engineRefusesNewSiModalityCurrent : EngineRefusesNewSiModality := .unwired

/-- Modality lattice cardinality (Unwired / Assumed / Proved / Surrogate). -/
def engineRefusesModalityLatticeCardinality : Nat := 4

theorem engine_refuses_modality_lattice_cardinality_four :
    engineRefusesModalityLatticeCardinality = 4 := rfl

theorem engine_refuses_modality_lattice_not_118_squared :
    engineRefusesModalityLatticeCardinality ≠ 118 * 118 := by decide

/-- Surface tag for name-from-content. -/
def engineRefusesNewSiSurface : String := "engine_refuses_new_si_surface"

theorem engine_refuses_new_si_surface_named : engineRefusesNewSiSurface ≠ "" := by decide

/-- Forbidden SI mint — Boltzmann k. -/
def forbiddenSiMintK : String := "k"

/-- Forbidden SI mint — gas constant R. -/
def forbiddenSiMintR : String := "R"

/-- Forbidden SI mint — vacuum permittivity ε₀. -/
def forbiddenSiMintEpsilon0 : String := "epsilon_0"

theorem forbidden_mint_k_named : forbiddenSiMintK = "k" := rfl

theorem forbidden_mint_R_named : forbiddenSiMintR = "R" := rfl

theorem forbidden_mint_epsilon_0_named : forbiddenSiMintEpsilon0 = "epsilon_0" := rfl

theorem forbidden_mints_distinct_k_R : forbiddenSiMintK ≠ forbiddenSiMintR := by decide

theorem forbidden_mints_distinct_k_epsilon :
    forbiddenSiMintK ≠ forbiddenSiMintEpsilon0 := by decide

theorem forbidden_mints_distinct_R_epsilon :
    forbiddenSiMintR ≠ forbiddenSiMintEpsilon0 := by decide

/-- Count of forbidden SI mints (k, R, ε₀). -/
def forbiddenSiMintCount : Nat := 3

theorem forbidden_si_mint_count_is_three : forbiddenSiMintCount = 3 := rfl

/-- Whether engines may mint new SI defining/derived constants (always false @ Unwired). -/
def engineMayMintSi : Bool := false

theorem engine_may_mint_si_false : engineMayMintSi = false := rfl

/-- Engines sort using existing SI/occupancy/derived-morphism sheaf only. -/
def engineUsesExistingSheaf : Bool :=
  !engineMayMintSi && decide (forbiddenSiMintCount = 3)

theorem engine_uses_existing_sheaf_true : engineUsesExistingSheaf = true := by decide

/-- SI sheaf consult marker. -/
def siSheafMarker : String := "si_occupancy_derived_morphism_sheaf_consult_v1"

/-- Occupancy sheaf consult marker. -/
def occupancySheafMarker : String := "occupancy_engine_sort_sheaf_consult_v1"

/-- Derived-morphism sheaf consult marker. -/
def derivedMorphismSheafMarker : String := "derived_morphism_sheaf_consult_v1"

theorem si_sheaf_marker_named : siSheafMarker ≠ "" := by decide

theorem occupancy_sheaf_marker_named : occupancySheafMarker ≠ "" := by decide

theorem derived_morphism_sheaf_marker_named : derivedMorphismSheafMarker ≠ "" := by decide

theorem sheaf_markers_distinct_si_occupancy : siSheafMarker ≠ occupancySheafMarker := by decide

/-- Engines sort via existing sheaf — consult, do not mint. -/
def engineSortsViaSheaf : Bool :=
  engineUsesExistingSheaf &&
    decide (siSheafMarker ≠ "") &&
    decide (occupancySheafMarker ≠ "") &&
    decide (derivedMorphismSheafMarker ≠ "")

theorem engine_sorts_via_sheaf_true : engineSortsViaSheaf = true := by decide

/-- α deferred composition (CODATA) — not Landauer-fake. -/
def alphaDeferredCodataMarker : String :=
  "alpha_deferred_composition_codata_not_landauer_fake_v1"

/-- Landauer-fake α marker — refused on honest scaffold. -/
def landauerFakeAlphaMarker : String := "landauer_fake_alpha_mint_v1"

theorem alpha_deferred_codata_marker_named : alphaDeferredCodataMarker ≠ "" := by decide

theorem alpha_not_landauer_fake : alphaDeferredCodataMarker ≠ landauerFakeAlphaMarker := by decide

def alphaIsDeferredCodataNotLandauer : Bool :=
  decide (alphaDeferredCodataMarker ≠ landauerFakeAlphaMarker)

theorem alpha_is_deferred_codata_not_landauer_true :
    alphaIsDeferredCodataNotLandauer = true := by decide

/-- 26th axiom marker — refused; sole axiom is second law + conservation. -/
def twentySixthAxiomMarker : String := "twenty_sixth_axiom_v1"

/-- Sole axiom count — second law + conservation framing only. -/
def soleAxiomCount : Nat := 1

theorem sole_axiom_count_is_one : soleAxiomCount = 1 := rfl

theorem not_twenty_sixth_axiom : decide (soleAxiomCount = 26) = false := by decide

def engineRefuseNot26thAxiom : Bool := decide (soleAxiomCount ≠ 26)

theorem engine_refuse_not_26th_axiom_true : engineRefuseNot26thAxiom = true := by decide

theorem twenty_sixth_axiom_marker_ne_sole :
    twentySixthAxiomMarker ≠ "sole_axiom_second_law_conservation" := by decide

/-- New SI mint marker — engines must not author defining constants. -/
def newSiMintMarker : String := "engine_mints_new_si_defining_constant_v1"

/-- Sheaf consult marker — engines consult existing sheaf. -/
def sheafConsultMarker : String := "engine_consults_existing_sheaf_v1"

theorem new_si_mint_marker_ne_sheaf_consult :
    newSiMintMarker ≠ sheafConsultMarker := by decide

def engineMintRefused : Bool := !engineMayMintSi

theorem engine_mint_refused_true : engineMintRefused = true := rfl

/-- Honest conjunct — sheaf consult + mint refuse + α deferred + not 26th axiom. -/
def engineRefusesNewSiHonestConjunct : Bool :=
  engineMintRefused &&
    engineUsesExistingSheaf &&
    engineSortsViaSheaf &&
    alphaIsDeferredCodataNotLandauer &&
    engineRefuseNot26thAxiom &&
    !engineMayMintSi

theorem engine_refuses_new_si_honest_conjunct_true :
    engineRefusesNewSiHonestConjunct = true := by decide

/-- WAVE100 — lib.rs / eos.rs not wired (deferred composition). -/
def wave100LibRsWired : Bool := false

def wave100EosRsWired : Bool := false

def engineRefusesNewSiProductionWired : Bool := false

theorem wave100_lib_rs_not_wired : wave100LibRsWired = false := rfl

theorem wave100_eos_rs_not_wired : wave100EosRsWired = false := rfl

theorem engine_refuses_new_si_production_not_wired :
    engineRefusesNewSiProductionWired = false := rfl

def wave100NotWired : Bool := !wave100LibRsWired && !wave100EosRsWired

theorem wave100_not_wired_true : wave100NotWired = true := by decide

/-- Verdict for engine refuses new SI close (fail-closed). -/
inductive EngineRefusesNewSiVerdict where
  | unwiredOk
  | engineRefuseNamedOk
  | siMintRefuse
  | greenInventRefuse
  | provedWithoutBarRefuse
  | productionWiredRefuse
  | twentySixthAxiomRefuse
  | landauerFakeRefuse
  deriving DecidableEq, Repr

def engineRefusesVerdictOk (v : EngineRefusesNewSiVerdict) : Bool :=
  match v with
  | .unwiredOk | .engineRefuseNamedOk => true
  | _ => false

/-- Evaluate engine refuses new SI under honest bar (fail-closed). -/
def evaluateEngineRefusesNewSi
    (modality : EngineRefusesNewSiModality)
    (claimPhysicsGreen : Bool)
    (claimProductionWired : Bool)
    (claimMintSi : Bool)
    (claim26thAxiom : Bool)
    (claimLandauerFake : Bool) : EngineRefusesNewSiVerdict :=
  if claimPhysicsGreen then
    .greenInventRefuse
  else if claimProductionWired then
    .productionWiredRefuse
  else if claimMintSi then
    .siMintRefuse
  else if claim26thAxiom then
    .twentySixthAxiomRefuse
  else if claimLandauerFake then
    .landauerFakeRefuse
  else
    match modality with
    | .unwired => .unwiredOk
    | .assumed | .proved | .surrogate => .engineRefuseNamedOk

/-- Unwired engine refuses new SI modality OK — sheaf consult, no mint. -/
def unwiredEngineRefusesNewSiDesignOk : Bool :=
  decide (evaluateEngineRefusesNewSi .unwired false false false false false = .unwiredOk)

/-- GREEN invent on engine refuses new SI promotion is refused. -/
def greenInventEngineRefusesNewSiRefuse : Bool :=
  decide (evaluateEngineRefusesNewSi .unwired true false false false false = .greenInventRefuse)

/-- SI mint smuggle is refused. -/
def siMintRefuse : Bool :=
  decide (evaluateEngineRefusesNewSi .unwired false false true false false = .siMintRefuse)

/-- 26th axiom smuggle is refused. -/
def twentySixthAxiomRefuse : Bool :=
  decide (evaluateEngineRefusesNewSi .unwired false false false true false = .twentySixthAxiomRefuse)

/-- Landauer-fake α smuggle is refused. -/
def landauerFakeRefuse : Bool :=
  decide (evaluateEngineRefusesNewSi .unwired false false false false true = .landauerFakeRefuse)

/-- Production wired without bar is refused. -/
def productionWiredRefuse : Bool :=
  decide (evaluateEngineRefusesNewSi .unwired false true false false false = .productionWiredRefuse)

/-- Engine refuses new SI scaffold pinned. -/
def engineRefusesNewSiScaffold : Bool :=
  unwiredEngineRefusesNewSiDesignOk &&
    engineRefusesNewSiHonestConjunct &&
    engineSortsViaSheaf &&
    greenInventEngineRefusesNewSiRefuse &&
    siMintRefuse &&
    twentySixthAxiomRefuse &&
    landauerFakeRefuse &&
    productionWiredRefuse &&
    wave100NotWired

theorem engine_refuses_new_si_scaffold_true : engineRefusesNewSiScaffold = true := by decide

/-- Engine refuses new SI proved (always false on this Unwired cell). -/
def engineRefusesNewSiProved : Bool := false

theorem engine_refuses_new_si_proved_false : engineRefusesNewSiProved = false := rfl

/-- Lattice is structure — not 118² GREEN periodic enumeration. -/
def engineRefusesNot118GreenTable : Bool := true

theorem engine_refuses_not_118_green_table : engineRefusesNot118GreenTable = true := rfl

/-- WAVE100 — lib.rs / eos.rs smuggle refuse (not wired). -/
def wave100LibRsSmuggleMarker : String := "umst/umst-chem/src/lib.rs"

def wave100EosRsSmuggleMarker : String := "umst/umst-chem/src/eos.rs"

def engineRefusesWiredInLib : Bool := false

def engineRefusesWiredInEos : Bool := false

theorem engine_refuses_not_wired_lib : engineRefusesWiredInLib = false := rfl

theorem engine_refuses_not_wired_eos : engineRefusesWiredInEos = false := rfl

/-- Cell id for the Lean engine refuses new SI **conservation** knowing-fiber. -/
def engineRefusesNewSiCellId : String :=
  "CHEM-FORMAL-Q-LEAN-ENGINE-REFUSES-NEW-SI-CONSERVATION"

/-- Physics GREEN is unauthorized on the knowing engine refuses new SI **conservation** scaffold. -/
def engineRefusesNewSiPhysicsGreenAuthorized : Prop := False

theorem engine_refuses_new_si_physics_green_false :
    ¬ engineRefusesNewSiPhysicsGreenAuthorized := id

/-- Probe bundle for honest posture witnesses. -/
structure EngineRefusesNewSiProbe where
  cellIdNamed : Bool
  unwired : Bool
  physicsGreenRefused : Bool
  soleAxiom : Bool
  notProved : Bool
  deriving DecidableEq, Repr

def engineRefusesNewSiProbe : EngineRefusesNewSiProbe :=
  { cellIdNamed :=
      decide (engineRefusesNewSiCellId =
        "CHEM-FORMAL-Q-LEAN-ENGINE-REFUSES-NEW-SI-CONSERVATION")
    unwired := decide (engineRefusesNewSiModalityCurrent = .unwired)
    physicsGreenRefused := true
    soleAxiom := decide (soleAxiomCount = 1)
    notProved := !engineRefusesNewSiProved }

/-- Honest conjunct on probe bundle. -/
def engineRefusesNewSiHonest : Bool :=
  let p := engineRefusesNewSiProbe
  p.cellIdNamed &&
    p.unwired &&
    p.physicsGreenRefused &&
    p.soleAxiom &&
    p.notProved &&
    engineRefusesNewSiScaffold

theorem engine_refuses_new_si_honest_true : engineRefusesNewSiHonest = true := by decide

/-- One axiom framing: second law + conservation; engine refuse is not a second axiom. -/
def engineRefusesNewSiFraming : String :=
  "second_law_conservation_engine_refuse_one_axiom_not_26th_axiom"

theorem engine_refuse_not_second_axiom :
    engineRefusesNewSiFraming ≠ "second_engine_refuse_axiom" := by decide

theorem engine_refuse_second_law_conservation_framing_named :
    engineRefusesNewSiFraming ≠ "" := by decide

/-- Second-law + **conservation** framing — cites meso SSOT, not wired on knowing scaffold. -/
def engineRefusesNewSiSecondLawConservationFramed : Bool := true

theorem engine_refuse_second_law_conservation_framed :
    engineRefusesNewSiSecondLawConservationFramed = true := rfl

/-- Cited Rust engine refuses new SI authority (views only — lattice is structural here). -/
def engineRefusesNewSiCitedModule : String :=
  "umst/umst-chem/src/x_rows/engine_refuses_new_si.rs"

/-- Cited INT cross engine refuses new SI authority. -/
def chemIntCrossEngineRefusesAuthority : String :=
  "CHEM-INT-CROSS-ENGINE-REFUSES-NEW-SI-CONSERVATION"

/-- Cited SI sheaf authority. -/
def siSheafAuthority : String := "umst/umst-chem/src/si_sheaf.rs"

/-- Non-claim fence — engine refuses new SI Unwired ≠ Proved GREEN. -/
def engineRefusesNewSiNonClaim : String :=
  "CHEM-FORMAL-Q-LEAN-ENGINE-REFUSES-NEW-SI-CONSERVATION constitutive engines sort using existing SI occupancy derived-morphism sheaf do not mint k R epsilon_0 alpha deferred CODATA not Landauer-fake not 26th axiom engineRefusesNewSiProved false Unwired one axiom second law conservation not second engine refuse axiom not GREEN DFT not physics GREEN not production_wired WAVE100 freeze remainder deferred composition env time cross-domain not impossibility"

theorem engine_refuses_new_si_modality_unwired :
    engineRefusesNewSiModalityCurrent = .unwired := rfl

/-- **One** design axiom: second law + **conservation** (structure witness — not meso import). -/
def engineRefusesNewSiAxiom : Bool :=
  engineRefusesNot118GreenTable &&
    engineRefusesNewSiSecondLawConservationFramed &&
    engineRefusesNewSiHonestConjunct &&
    engineSortsViaSheaf &&
    unwiredEngineRefusesNewSiDesignOk &&
    greenInventEngineRefusesNewSiRefuse &&
    siMintRefuse &&
    twentySixthAxiomRefuse &&
    landauerFakeRefuse &&
    productionWiredRefuse &&
    engineRefusesNewSiScaffold &&
    engineRefusesNewSiHonest &&
    !engineMayMintSi &&
    !engineRefusesNewSiProved &&
    !engineRefusesNewSiProductionWired &&
    !engineRefusesWiredInLib &&
    !engineRefusesWiredInEos &&
    decide (engineRefusesNewSiFraming =
      "second_law_conservation_engine_refuse_one_axiom_not_26th_axiom")

theorem engine_refuses_new_si_axiom : engineRefusesNewSiAxiom = true := by decide

theorem engine_refuses_unwired_ok :
    evaluateEngineRefusesNewSi .unwired false false false false false = .unwiredOk := rfl

theorem engine_refuses_green_invent_refuse :
    evaluateEngineRefusesNewSi .unwired true false false false false = .greenInventRefuse := rfl

theorem si_mint_refuse :
    evaluateEngineRefusesNewSi .unwired false false true false false = .siMintRefuse := rfl

theorem twenty_sixth_axiom_refuse :
    evaluateEngineRefusesNewSi .unwired false false false true false = .twentySixthAxiomRefuse := rfl

theorem landauer_fake_refuse :
    evaluateEngineRefusesNewSi .unwired false false false false true = .landauerFakeRefuse := rfl

theorem engine_refuses_production_wired_refuse :
    evaluateEngineRefusesNewSi .unwired false true false false false = .productionWiredRefuse := rfl

theorem engine_refuses_new_si_conservation :
    evaluateEngineRefusesNewSi .unwired false false false false false = .unwiredOk ∧
    engineRefusesNewSiHonestConjunct = true ∧
    engineRefusesNewSiProved = false ∧
    wave100LibRsWired = false ∧
    wave100EosRsWired = false :=
  ⟨rfl, engine_refuses_new_si_honest_conjunct_true, engine_refuses_new_si_proved_false,
    wave100_lib_rs_not_wired, wave100_eos_rs_not_wired⟩

theorem engine_refuses_new_si_honest_bundle :
    engineRefusesNewSiProved = false ∧
    engineRefusesNewSiProductionWired = false ∧
    engineRefusesNot118GreenTable = true ∧
    engineRefusesNewSiSecondLawConservationFramed = true ∧
    engineRefusesNewSiHonestConjunct = true ∧
    engineSortsViaSheaf = true ∧
    evaluateEngineRefusesNewSi .unwired false false false false false = .unwiredOk ∧
    evaluateEngineRefusesNewSi .unwired true false false false false = .greenInventRefuse ∧
    evaluateEngineRefusesNewSi .unwired false false true false false = .siMintRefuse ∧
    evaluateEngineRefusesNewSi .unwired false false false true false = .twentySixthAxiomRefuse ∧
    engineMayMintSi = false ∧
    soleAxiomCount = 1 ∧
    engineRefusesNewSiAxiom = true :=
  ⟨rfl, engine_refuses_new_si_production_not_wired, engine_refuses_not_118_green_table,
    engine_refuse_second_law_conservation_framed, engine_refuses_new_si_honest_conjunct_true,
    engine_sorts_via_sheaf_true, engine_refuses_unwired_ok, engine_refuses_green_invent_refuse,
    si_mint_refuse, twenty_sixth_axiom_refuse, engine_may_mint_si_false, sole_axiom_count_is_one,
    engine_refuses_new_si_axiom⟩

end UMST.Chem
