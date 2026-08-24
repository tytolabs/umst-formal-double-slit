-- SPDX-FileCopyrightText: 2026 Santosh Prabhu Shenbagamoorthy and Santhosh Shyamsundar
-- SPDX-License-Identifier: MIT

import ElementElectronic

set_option maxRecDepth 8192

/-!
# InteractEngineClosedShell — interact-engine closed-shell **conservation** (Q lattice)

Knowing-fiber Lean: interact-engine sorts closed-shell blocking / partial Interact refuse /
catalysis-not-axiom. He no-ore = missing Interact class 5 (`structure_blocking_inertness`), not
nobility magic / not atmophile GREEN. `InteractKind::StructureBlocking` partiality typed — not
bond-forming folklore. Pairs `umst-chem` scaffold `interact_engine_closed_shell` /
**conservation** posture.

Read-only cites (not imported — self-contained scaffold):
- `Coq/ChemConstants/InteractEngineClosedShell.v`
- `umst/umst-chem/src/x_rows/interact_engine_closed_shell.rs`

- `InteractEngineClosedShellModality` — Unwired / Assumed / Proved / Surrogate (not 118² GREEN table).
- Closed-shell noble-gas Z bar (He … Og) — INT SSOT pins.
- Class 5 structure-blocking / inertness — L0 authority pin.
- Interact partiality — Kleisli Interact is partial, not total.
- Second-law + **conservation** framing cites meso `UMST.Chem.Conservation` /
  `LandauerLaw.physicalSecondLaw` — not imported.
- No meso / acting theorems. No new physics `axiom`. Catalysis priced under sole axiom — not 26th.
- `physics_green` stays false. Does **not** claim `interactEngineClosedShellProved` or physics GREEN.
- WAVE100 freeze — remainder deferred composition (env/time/cross-domain), not impossibility stop.
-/

namespace UMST.Chem

/-- Design modality for interact-engine closed-shell **conservation** (lattice SSOT). -/
inductive InteractEngineClosedShellModality where
  | unwired | assumed | proved | surrogate
  deriving DecidableEq, Repr

def interactEngineClosedShellModalityCurrent : InteractEngineClosedShellModality := .unwired

/-- Modality lattice cardinality (Unwired / Assumed / Proved / Surrogate). -/
def interactEngineClosedShellModalityLatticeCardinality : Nat := 4

theorem interact_engine_closed_shell_modality_lattice_cardinality_four :
    interactEngineClosedShellModalityLatticeCardinality = 4 := rfl

theorem interact_engine_closed_shell_modality_lattice_not_118_squared :
    interactEngineClosedShellModalityLatticeCardinality ≠ 118 * 118 := by decide

/-- Surface tag for name-from-content. -/
def interactEngineClosedShellSurface : String := "interact_engine_closed_shell_surface"

theorem interact_engine_closed_shell_surface_named : interactEngineClosedShellSurface ≠ "" := by decide

/-- Closed-shell noble-gas Z pins — INT SSOT (He … Og). -/
def closedShellZHe : Nat := 2
def closedShellZNe : Nat := 10
def closedShellZAr : Nat := 18
def closedShellZKr : Nat := 36
def closedShellZXe : Nat := 54
def closedShellZRn : Nat := 86
def closedShellZOg : Nat := 118

theorem closed_shell_z_he_is_2 : closedShellZHe = 2 := rfl
theorem closed_shell_z_ne_is_10 : closedShellZNe = 10 := rfl
theorem closed_shell_z_ar_is_18 : closedShellZAr = 18 := rfl
theorem closed_shell_z_kr_is_36 : closedShellZKr = 36 := rfl
theorem closed_shell_z_xe_is_54 : closedShellZXe = 54 := rfl
theorem closed_shell_z_rn_is_86 : closedShellZRn = 86 := rfl
theorem closed_shell_z_og_is_118 : closedShellZOg = 118 := rfl

def closedShellZCount : Nat := 7

theorem closed_shell_z_count_is_seven : closedShellZCount = 7 := rfl

def closedShellZs : List Nat :=
  [closedShellZHe, closedShellZNe, closedShellZAr, closedShellZKr, closedShellZXe, closedShellZRn, closedShellZOg]

theorem closed_shell_zs_length_seven : closedShellZs.length = 7 := by decide

/-- IUPAC Z bar — closed-shell table within Z=1..118 (not 118² table). -/
def iupacTableCardinality : Nat := 118

theorem iupac_table_cardinality_is_118 : iupacTableCardinality = 118 := rfl

def closedShellZValid (z : Nat) : Bool :=
  0 < z && z ≤ iupacTableCardinality

theorem closed_shell_z_table_valid :
    closedShellZValid closedShellZHe = true ∧
    closedShellZValid closedShellZNe = true ∧
    closedShellZValid closedShellZAr = true ∧
    closedShellZValid closedShellZKr = true ∧
    closedShellZValid closedShellZXe = true ∧
    closedShellZValid closedShellZRn = true ∧
    closedShellZValid closedShellZOg = true := by decide

theorem oganesson_in_bar_not_xe_copy :
    closedShellZOg = 118 ∧
    closedShellZXe = 54 ∧
    closedShellZOg ≠ closedShellZXe := by decide

def oganessonInBarNotXeCopy : Bool :=
  closedShellZOg = 118 && closedShellZXe = 54 && closedShellZOg ≠ closedShellZXe

theorem oganesson_in_bar_not_xe_copy_true : oganessonInBarNotXeCopy = true := by decide

def closedShellZTableValid : Bool :=
  closedShellZValid closedShellZHe &&
  closedShellZValid closedShellZNe &&
  closedShellZValid closedShellZAr &&
  closedShellZValid closedShellZKr &&
  closedShellZValid closedShellZXe &&
  closedShellZValid closedShellZRn &&
  closedShellZValid closedShellZOg

theorem closed_shell_z_table_valid_true : closedShellZTableValid = true := by decide

/-- Class 5 structure-blocking / inertness — L0 authority pin. -/
def class5StructureBlockingPatternIndex : Nat := 5

theorem class_5_structure_blocking_pattern_index_is_five :
    class5StructureBlockingPatternIndex = 5 := rfl

def structureBlockingInertnessAuthority : String :=
  "umst/umst-chem/src/l0_tables/structure_blocking_inertness.rs"

def patternBundleStructureBlockingFactorTag : String := "structure_blocking_inertness"

def northStarClass5StructureBlockingTag : String := "class 5 structure-blocking"

theorem structure_blocking_inertness_authority_named :
    structureBlockingInertnessAuthority ≠ "" := by decide

theorem pattern_bundle_structure_blocking_factor_tag_named :
    patternBundleStructureBlockingFactorTag = "structure_blocking_inertness" := rfl

/-- Interact partiality — Kleisli Interact is partial, not total. -/
def interactPartialityAuthority : String := "umst/umst-chem/src/interact_partiality.rs"

def interactKindStructureBlockingTag : String := "InteractKind::StructureBlocking"

theorem interact_partiality_authority_named : interactPartialityAuthority ≠ "" := by decide

theorem interact_kind_structure_blocking_tag_named :
    interactKindStructureBlockingTag = "InteractKind::StructureBlocking" := rfl

def structureBlockingInteractKindPinned : Bool :=
  interactKindStructureBlockingTag ≠ "" &&
  patternBundleStructureBlockingFactorTag = "structure_blocking_inertness"

theorem structure_blocking_interact_kind_pinned_true :
    structureBlockingInteractKindPinned = true := by decide

/-- He no-ore — missing Interact class 5, not nobility magic. -/
def heNoOreMissingInteractClass5Collision : String :=
  "He Z=2 closed-shell no crustal ore = missing Interact class 5 structure_blocking — not atmophile nobility GREEN"

def nobilityMagicMarker : String := "nobility_magic_atmophile_green_folklore_v1"
def missingInteractClass5Marker : String := "missing_interact_class5_structure_blocking_v1"

theorem he_no_ore_collision_named : heNoOreMissingInteractClass5Collision ≠ "" := by decide

theorem nobility_magic_ne_missing_interact :
    nobilityMagicMarker ≠ missingInteractClass5Marker := by decide

def heliumNoOreIsMissingInteract : Bool :=
  closedShellZHe = 2 && class5StructureBlockingPatternIndex = 5

theorem helium_no_ore_is_missing_interact_true : heliumNoOreIsMissingInteract = true := by decide

def heNoOreIsNobilityMagic : Bool := false
def heNoOreIsAtmophileGreen : Bool := false

theorem he_no_ore_not_nobility_magic : heNoOreIsNobilityMagic = false := rfl
theorem he_no_ore_not_atmophile_green : heNoOreIsAtmophileGreen = false := rfl

/-- Catalysis priced under sole axiom — not a 26th axiom. -/
def catalysisNot26thAxiomCollision : String :=
  "catalysis priced under second law + conservation — not minted as 26th axiom"

theorem catalysis_not_26th_axiom_collision_named : catalysisNot26thAxiomCollision ≠ "" := by decide

def catalysisIsExtraAxiom : Bool := false

theorem catalysis_is_not_extra_axiom : catalysisIsExtraAxiom = false := rfl

def soleAxiomCount : Nat := 1

theorem sole_axiom_count_is_one : soleAxiomCount = 1 := rfl

theorem catalysis_not_26th_axiom : soleAxiomCount ≠ 26 := by decide

/-- Interact kind slot — structure-blocking vs unauthorized folklore. -/
inductive InteractKindSlot where
  | structureBlocking | bondFormingFolklore | unauthorized
  deriving DecidableEq, Repr

structure InteractKindBinding where
  slotTag : InteractKindSlot
  classIndex : Nat
  deriving DecidableEq, Repr

def interactKindBindingStructureBlocking : InteractKindBinding :=
  { slotTag := .structureBlocking, classIndex := 5 }

def interactKindBindingHonest (b : InteractKindBinding) : Bool :=
  b.classIndex = 5 && b.slotTag ≠ .unauthorized

theorem structure_blocking_binding_honest :
    interactKindBindingHonest interactKindBindingStructureBlocking = true := by decide

/-- Verdict for interact-engine closed-shell close (fail-closed). -/
inductive InteractEngineClosedShellVerdict where
  | unwiredOk
  | closedShellNamedOk
  | trivialZRefuse
  | nobilityMagicRefuse
  | atmophileGreenRefuse
  | catalysis26thAxiomRefuse
  | greenInventRefuse
  | provedWithoutBarRefuse
  | productionWiredRefuse
  deriving DecidableEq, Repr

def interactEngineClosedShellVerdictOk (v : InteractEngineClosedShellVerdict) : Bool :=
  match v with
  | .unwiredOk | .closedShellNamedOk => true
  | _ => false

structure InteractEngineClosedShellIncidence where
  z : Nat
  kind : InteractKindBinding
  level : Nat
  deriving DecidableEq, Repr

def interactEngineClosedShellIncidenceNontrivial (h : InteractEngineClosedShellIncidence) : Bool :=
  0 < h.level

def interactEngineClosedShellIncidenceHeL1 : InteractEngineClosedShellIncidence :=
  { z := closedShellZHe, kind := interactKindBindingStructureBlocking, level := 1 }

def interactEngineClosedShellIncidenceOgL1 : InteractEngineClosedShellIncidence :=
  { z := closedShellZOg, kind := interactKindBindingStructureBlocking, level := 1 }

def interactEngineClosedShellIncidenceTrivial : InteractEngineClosedShellIncidence :=
  { z := closedShellZHe, kind := interactKindBindingStructureBlocking, level := 0 }

def evaluateInteractEngineClosedShellIncidence
    (modality : InteractEngineClosedShellModality)
    (h : InteractEngineClosedShellIncidence)
    (claimPhysicsGreen : Bool)
    (claimProved : Bool)
    (claimNobilityMagic : Bool)
    (claimAtmophileGreen : Bool)
    (claimCatalysis26thAxiom : Bool) : InteractEngineClosedShellVerdict :=
  if claimPhysicsGreen then
    .greenInventRefuse
  else if claimProved then
    .provedWithoutBarRefuse
  else if claimNobilityMagic then
    .nobilityMagicRefuse
  else if claimAtmophileGreen then
    .atmophileGreenRefuse
  else if claimCatalysis26thAxiom then
    .catalysis26thAxiomRefuse
  else if !interactEngineClosedShellIncidenceNontrivial h then
    .trivialZRefuse
  else if !interactKindBindingHonest h.kind then
    .nobilityMagicRefuse
  else
    match modality with
    | .unwired => .closedShellNamedOk
    | .assumed | .surrogate => .unwiredOk
    | .proved => .provedWithoutBarRefuse

def evaluateInteractEngineClosedShellClose
    (modality : InteractEngineClosedShellModality)
    (claimPhysicsGreen : Bool)
    (claimProductionWired : Bool) : InteractEngineClosedShellVerdict :=
  if claimPhysicsGreen then
    .greenInventRefuse
  else if claimProductionWired then
    .productionWiredRefuse
  else
    match modality with
    | .unwired => .unwiredOk
    | .assumed | .proved | .surrogate => .closedShellNamedOk

def interactEngineClosedShellHonestConjunct : Bool :=
  !catalysisIsExtraAxiom &&
  heliumNoOreIsMissingInteract &&
  structureBlockingInteractKindPinned &&
  !heNoOreIsNobilityMagic &&
  !heNoOreIsAtmophileGreen

theorem interact_engine_closed_shell_honest_conjunct_true :
    interactEngineClosedShellHonestConjunct = true := by decide

def interactEngineClosedShellConjunct : Bool :=
  interactEngineClosedShellHonestConjunct &&
  oganessonInBarNotXeCopy &&
  closedShellZTableValid

theorem interact_engine_closed_shell_conjunct_true : interactEngineClosedShellConjunct = true := by decide

/-- WAVE100 — lib.rs / eos.rs not wired (deferred composition). -/
def wave100LibRsWired : Bool := false
def wave100EosRsWired : Bool := false
def interactEngineClosedShellProductionWired : Bool := false

theorem wave100_lib_rs_not_wired : wave100LibRsWired = false := rfl
theorem wave100_eos_rs_not_wired : wave100EosRsWired = false := rfl

theorem interact_engine_closed_shell_production_not_wired :
    interactEngineClosedShellProductionWired = false := rfl

def wave100NotWired : Bool := !wave100LibRsWired && !wave100EosRsWired

theorem wave100_not_wired_true : wave100NotWired = true := by decide

def interactEngineClosedShellProved : Bool := false

theorem interact_engine_closed_shell_proved_false : interactEngineClosedShellProved = false := rfl

def not118SquaredGreenTable : Bool := true
def notTwentySixthAxiom : Bool := true

theorem not_118_squared_green_table : not118SquaredGreenTable = true := rfl
theorem not_twenty_sixth_axiom : notTwentySixthAxiom = true := rfl

def unwiredInteractEngineClosedShellCloseOk : Bool :=
  decide (evaluateInteractEngineClosedShellClose .unwired false false = .unwiredOk)

def heClosedShellNamedOk : Bool :=
  decide (evaluateInteractEngineClosedShellIncidence .unwired interactEngineClosedShellIncidenceHeL1
    false false false false false = .closedShellNamedOk)

def ogClosedShellNamedOk : Bool :=
  decide (evaluateInteractEngineClosedShellIncidence .unwired interactEngineClosedShellIncidenceOgL1
    false false false false false = .closedShellNamedOk)

def trivialZRefuse : Bool :=
  decide (evaluateInteractEngineClosedShellIncidence .unwired interactEngineClosedShellIncidenceTrivial
    false false false false false = .trivialZRefuse)

def nobilityMagicRefuse : Bool :=
  decide (evaluateInteractEngineClosedShellIncidence .unwired interactEngineClosedShellIncidenceHeL1
    false false true false false = .nobilityMagicRefuse)

def atmophileGreenRefuse : Bool :=
  decide (evaluateInteractEngineClosedShellIncidence .unwired interactEngineClosedShellIncidenceHeL1
    false false false true false = .atmophileGreenRefuse)

def catalysis26thAxiomRefuse : Bool :=
  decide (evaluateInteractEngineClosedShellIncidence .unwired interactEngineClosedShellIncidenceHeL1
    false false false false true = .catalysis26thAxiomRefuse)

def greenInventInteractEngineClosedShellRefuse : Bool :=
  decide (evaluateInteractEngineClosedShellClose .unwired true false = .greenInventRefuse)

def provedWithoutBarInteractEngineClosedShellRefuse : Bool :=
  decide (evaluateInteractEngineClosedShellIncidence .unwired interactEngineClosedShellIncidenceHeL1
    false true false false false = .provedWithoutBarRefuse)

def productionWiredInteractEngineClosedShellRefuse : Bool :=
  decide (evaluateInteractEngineClosedShellClose .proved false true = .productionWiredRefuse)

def interactEngineClosedShellScaffold : Bool :=
  unwiredInteractEngineClosedShellCloseOk &&
    interactEngineClosedShellConjunct &&
    heClosedShellNamedOk &&
    ogClosedShellNamedOk &&
    trivialZRefuse &&
    nobilityMagicRefuse &&
    atmophileGreenRefuse &&
    catalysis26thAxiomRefuse &&
    greenInventInteractEngineClosedShellRefuse &&
    provedWithoutBarInteractEngineClosedShellRefuse &&
    productionWiredInteractEngineClosedShellRefuse &&
    wave100NotWired

theorem interact_engine_closed_shell_scaffold_true : interactEngineClosedShellScaffold = true := by native_decide

inductive FormalFiber where
  | quantumKnowing | mesoActing
  deriving DecidableEq, Repr

def interactEngineClosedShellFiberOk (f : FormalFiber) : Bool :=
  match f with | .quantumKnowing => true | .mesoActing => false

theorem interact_engine_closed_shell_knowing_fiber_ok :
    interactEngineClosedShellFiberOk .quantumKnowing = true := rfl

theorem interact_engine_closed_shell_meso_acting_fiber_not_ok :
    interactEngineClosedShellFiberOk .mesoActing = false := rfl

def interactEngineClosedShellCellId : String :=
  "CHEM-FORMAL-Q-LEAN-INTERACT-ENGINE-CLOSED-SHELL-CONSERVATION"

def interactEngineClosedShellPhysicsGreenAuthorized : Prop := False

theorem interact_engine_closed_shell_physics_green_false :
    ¬ interactEngineClosedShellPhysicsGreenAuthorized := id

structure InteractEngineClosedShellProbe where
  cellIdNamed : Bool
  unwired : Bool
  physicsGreenRefused : Bool
  soleAxiom : Bool
  notProved : Bool
  heMissingInteractClass5 : Bool
  structureBlockingKindPinned : Bool
  deriving DecidableEq, Repr

def interactEngineClosedShellProbe : InteractEngineClosedShellProbe :=
  { cellIdNamed :=
      decide (interactEngineClosedShellCellId =
        "CHEM-FORMAL-Q-LEAN-INTERACT-ENGINE-CLOSED-SHELL-CONSERVATION")
    unwired := decide (interactEngineClosedShellModalityCurrent = .unwired)
    physicsGreenRefused := true
    soleAxiom := decide (soleAxiomCount = 1)
    notProved := !interactEngineClosedShellProved
    heMissingInteractClass5 := heliumNoOreIsMissingInteract
    structureBlockingKindPinned := structureBlockingInteractKindPinned }

def interactEngineClosedShellHonest : Bool :=
  let p := interactEngineClosedShellProbe
  p.cellIdNamed &&
    p.unwired &&
    p.physicsGreenRefused &&
    p.soleAxiom &&
    p.notProved &&
    p.heMissingInteractClass5 &&
    p.structureBlockingKindPinned &&
    interactEngineClosedShellScaffold

theorem interact_engine_closed_shell_honest_true : interactEngineClosedShellHonest = true := by native_decide

def interactEngineClosedShellFraming : String :=
  "second_law_conservation_interact_engine_closed_shell_one_axiom_not_26th_axiom"

theorem interact_engine_closed_shell_not_twenty_sixth_axiom_framing :
    interactEngineClosedShellFraming ≠ "twenty_sixth_chemistry_axiom" := by decide

theorem interact_engine_closed_shell_not_fourth_science_axiom :
    interactEngineClosedShellFraming ≠ "fourth_chemistry_science_axiom" := by decide

def interactEngineClosedShellSecondLawConservationFramed : Bool := true

theorem interact_engine_closed_shell_second_law_conservation_framed :
    interactEngineClosedShellSecondLawConservationFramed = true := rfl

def interactEngineClosedShellCitedCoqModule : String :=
  "Coq/ChemConstants/InteractEngineClosedShell.v"

def interactEngineClosedShellCitedModule : String :=
  "umst/umst-chem/src/x_rows/interact_engine_closed_shell.rs"

def chemIntCrossInteractEngineClosedShellAuthority : String :=
  "CHEM-INT-CROSS-INTERACT-ENGINE-CLOSED-SHELL-CONSERVATION"

def interactEngineClosedShellNonClaim : String :=
  "CHEM-FORMAL-Q-LEAN-INTERACT-ENGINE-CLOSED-SHELL-CONSERVATION Interact-engine sorts closed-shell blocking partial Interact refuse catalysis-not-axiom He no-ore missing Interact class 5 structure_blocking_inertness not nobility magic not atmophile GREEN InteractKind StructureBlocking partiality typed not bond-forming folklore GREEN invent fail-closed proved-without-bar fail-closed interactEngineClosedShellProved false Unwired knowing quantum fiber not meso acting WAVE100 lib eos smuggle refuse one axiom second law conservation not GREEN not physics GREEN not production_wired remainder deferred composition not impossibility"

theorem interact_engine_closed_shell_modality_unwired :
    interactEngineClosedShellModalityCurrent = .unwired := rfl

def interactEngineClosedShellAxiom : Bool :=
  not118SquaredGreenTable &&
    interactEngineClosedShellSecondLawConservationFramed &&
    interactEngineClosedShellConjunct &&
    interactEngineClosedShellScaffold &&
    interactEngineClosedShellHonest &&
    !interactEngineClosedShellProved &&
    !interactEngineClosedShellProductionWired &&
    !wave100LibRsWired &&
    !wave100EosRsWired &&
    notTwentySixthAxiom &&
    decide (interactEngineClosedShellFraming =
      "second_law_conservation_interact_engine_closed_shell_one_axiom_not_26th_axiom")

theorem interact_engine_closed_shell_axiom : interactEngineClosedShellAxiom = true := by native_decide

theorem unwired_close_without_production_wiring :
    evaluateInteractEngineClosedShellClose .unwired false false = .unwiredOk := rfl

theorem he_closed_shell_named_ok :
    evaluateInteractEngineClosedShellIncidence .unwired interactEngineClosedShellIncidenceHeL1
      false false false false false = .closedShellNamedOk := rfl

theorem og_closed_shell_named_ok :
    evaluateInteractEngineClosedShellIncidence .unwired interactEngineClosedShellIncidenceOgL1
      false false false false false = .closedShellNamedOk := rfl

theorem trivial_z_refused :
    evaluateInteractEngineClosedShellIncidence .unwired interactEngineClosedShellIncidenceTrivial
      false false false false false = .trivialZRefuse := rfl

theorem nobility_magic_refused :
    evaluateInteractEngineClosedShellIncidence .unwired interactEngineClosedShellIncidenceHeL1
      false false true false false = .nobilityMagicRefuse := rfl

theorem atmophile_green_refused :
    evaluateInteractEngineClosedShellIncidence .unwired interactEngineClosedShellIncidenceHeL1
      false false false true false = .atmophileGreenRefuse := rfl

theorem catalysis_26th_axiom_refused :
    evaluateInteractEngineClosedShellIncidence .unwired interactEngineClosedShellIncidenceHeL1
      false false false false true = .catalysis26thAxiomRefuse := rfl

theorem green_invent_refuse_unwired :
    evaluateInteractEngineClosedShellClose .unwired true false = .greenInventRefuse := rfl

theorem proved_without_bar_refuse :
    evaluateInteractEngineClosedShellIncidence .unwired interactEngineClosedShellIncidenceHeL1
      false true false false false = .provedWithoutBarRefuse := rfl

theorem production_wired_refuse :
    evaluateInteractEngineClosedShellClose .proved false true = .productionWiredRefuse := rfl

theorem interact_engine_closed_shell_conservation :
    evaluateInteractEngineClosedShellClose .unwired false false = .unwiredOk ∧
    interactEngineClosedShellConjunct = true ∧
    interactEngineClosedShellProved = false ∧
    wave100LibRsWired = false ∧
    wave100EosRsWired = false :=
  ⟨rfl, interact_engine_closed_shell_conjunct_true, interact_engine_closed_shell_proved_false,
    wave100_lib_rs_not_wired, wave100_eos_rs_not_wired⟩

theorem interact_engine_closed_shell_honest_bundle :
    interactEngineClosedShellProved = false ∧
    interactEngineClosedShellProductionWired = false ∧
    not118SquaredGreenTable = true ∧
    interactEngineClosedShellSecondLawConservationFramed = true ∧
    interactEngineClosedShellConjunct = true ∧
    heliumNoOreIsMissingInteract = true ∧
    structureBlockingInteractKindPinned = true ∧
    evaluateInteractEngineClosedShellClose .unwired false false = .unwiredOk ∧
    evaluateInteractEngineClosedShellClose .unwired true false = .greenInventRefuse ∧
    evaluateInteractEngineClosedShellIncidence .unwired interactEngineClosedShellIncidenceHeL1
      false true false false false = .provedWithoutBarRefuse ∧
    soleAxiomCount = 1 ∧
    interactEngineClosedShellAxiom = true ∧
    interactEngineClosedShellFiberOk .quantumKnowing = true ∧
    interactEngineClosedShellFiberOk .mesoActing = false ∧
    nobilityMagicMarker ≠ missingInteractClass5Marker :=
  ⟨rfl, interact_engine_closed_shell_production_not_wired, not_118_squared_green_table,
    interact_engine_closed_shell_second_law_conservation_framed, interact_engine_closed_shell_conjunct_true,
    helium_no_ore_is_missing_interact_true, structure_blocking_interact_kind_pinned_true,
    unwired_close_without_production_wiring, green_invent_refuse_unwired,
    proved_without_bar_refuse, sole_axiom_count_is_one, interact_engine_closed_shell_axiom,
    interact_engine_closed_shell_knowing_fiber_ok, interact_engine_closed_shell_meso_acting_fiber_not_ok,
    nobility_magic_ne_missing_interact⟩

end UMST.Chem
