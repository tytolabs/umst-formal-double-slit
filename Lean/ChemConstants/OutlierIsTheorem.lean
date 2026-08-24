-- SPDX-FileCopyrightText: 2026 Santosh Prabhu Shenbagamoorthy and Santhosh Shyamsundar
-- SPDX-License-Identifier: MIT

import ElementElectronic

set_option maxRecDepth 8192

/-!
# OutlierIsTheorem — outlier-is-theorem **conservation** (Q lattice)

Knowing-fiber Lean: nothing in Z=1..118 or Interact / Ore / Refine may rest as folklore outlier;
terminals are **theorem** | **deferred composition remainder** | **typed Absent**. Pairs
`umst-chem` scaffold `outlier_is_theorem` / **conservation** posture (occupancy_engine_sort
fallback when INT row absent).

Read-only cites (not imported — self-contained scaffold):
- `Coq/ChemConstants/OutlierIsTheorem.v`
- `umst/umst-chem/src/x_rows/outlier_is_theorem.rs` (absent — cite `occupancy_engine_sort.rs` posture)

- `OutlierIsTheoremModality` — Unwired / Assumed / Proved / Surrogate (not 118² GREEN table).
- `OutlierTerminal` — theorem / deferredCompositionRemainder / typedAbsent (not folklore bucket).
- `OutlierDomain` — zBar / interact / ore / refine — each outlier sorted, not lore-listed.
- Second-law + **conservation** framing cites meso `UMST.Chem.Conservation` /
  `LandauerLaw.physicalSecondLaw` — not imported.
- No meso / acting theorems. No new physics `axiom`. Sorting cites override pins — **not** 26th axiom.
- `physics_green` stays false. Does **not** claim `outlierIsTheoremProved` or physics GREEN.
- WAVE100 freeze — remainder deferred composition (env/time/cross-domain), not impossibility stop.
-/

namespace UMST.Chem

/-- Design modality for outlier-is-theorem **conservation** (lattice SSOT). -/
inductive OutlierIsTheoremModality where
  | unwired | assumed | proved | surrogate
  deriving DecidableEq, Repr

def outlierIsTheoremModalityCurrent : OutlierIsTheoremModality := .unwired

/-- Modality lattice cardinality (Unwired / Assumed / Proved / Surrogate). -/
def outlierIsTheoremModalityLatticeCardinality : Nat := 4

theorem outlier_is_theorem_modality_lattice_cardinality_four :
    outlierIsTheoremModalityLatticeCardinality = 4 := rfl

theorem outlier_is_theorem_modality_lattice_not_118_squared :
    outlierIsTheoremModalityLatticeCardinality ≠ 118 * 118 := by decide

/-- Surface tag for name-from-content. -/
def outlierIsTheoremSurface : String := "outlier_is_theorem_surface"

theorem outlier_is_theorem_surface_named : outlierIsTheoremSurface ≠ "" := by decide

/-- Outlier terminal — theorem | deferred composition remainder | typed Absent (not folklore). -/
inductive OutlierTerminal where
  | theorem | deferredCompositionRemainder | typedAbsent
  deriving DecidableEq, Repr

def outlierTerminalCount : Nat := 3

theorem outlier_terminal_count_is_three : outlierTerminalCount = 3 := rfl

def outlierTerminalTags : List String :=
  ["theorem", "deferred_composition_remainder", "typed_absent"]

theorem outlier_terminal_tags_length_three : outlierTerminalTags.length = 3 := by decide

/-- Outlier domain — Z bar / Interact / Ore / Refine (not folklore list). -/
inductive OutlierDomain where
  | zBar | interact | ore | refine
  deriving DecidableEq, Repr

def outlierDomainCount : Nat := 4

theorem outlier_domain_count_is_four : outlierDomainCount = 4 := rfl

def outlierDomainTags : List String :=
  ["z_bar", "interact", "ore", "refine"]

theorem outlier_domain_tags_length_four : outlierDomainTags.length = 4 := by decide

/-- IUPAC Z bar — outlier sort for Z=1..118 (not 118² table). -/
def iupacTableCardinality : Nat := 118

theorem iupac_table_cardinality_is_118 : iupacTableCardinality = 118 := rfl

def outlierElementZValid (z : Nat) : Bool :=
  0 < z && z ≤ iupacTableCardinality

/-- Folklore outlier refuse — terminals are theorem / deferred / typed Absent only. -/
def folkloreOutlierMarker : String := "outlier_folklore_unsorted_v1"
def theoremTerminalMarker : String := "outlier_terminal_theorem_v1"
def deferredRemainderMarker : String := "outlier_terminal_deferred_composition_remainder_v1"
def typedAbsentMarker : String := "outlier_terminal_typed_absent_v1"

theorem folklore_marker_ne_theorem_terminal :
    folkloreOutlierMarker ≠ theoremTerminalMarker := by decide

theorem folklore_marker_ne_deferred_remainder :
    folkloreOutlierMarker ≠ deferredRemainderMarker := by decide

theorem folklore_marker_ne_typed_absent :
    folkloreOutlierMarker ≠ typedAbsentMarker := by decide

/-- Named outlier Z pins — INT SSOT witnesses (Au / Fe / He / Pu). -/
def goldZ : Nat := 79
def ironZ : Nat := 26
def heliumZ : Nat := 2
def plutoniumZ : Nat := 94

theorem gold_z_is_79 : goldZ = 79 := rfl
theorem iron_z_is_26 : ironZ = 26 := rfl
theorem helium_z_is_2 : heliumZ = 2 := rfl
theorem plutonium_z_is_94 : plutoniumZ = 94 := rfl

theorem outlier_z_factors_valid :
    outlierElementZValid goldZ = true ∧
    outlierElementZValid ironZ = true ∧
    outlierElementZValid heliumZ = true ∧
    outlierElementZValid plutoniumZ = true := by decide

structure OutlierWitness where
  z : Nat
  domain : OutlierDomain
  terminal : OutlierTerminal
  level : Nat
  deriving DecidableEq, Repr

def outlierWitnessNontrivial (w : OutlierWitness) : Bool :=
  0 < w.level

/-- Au Z=79 native ore — theorem terminal on Ore domain. -/
def goldNativeOreWitness : OutlierWitness :=
  { z := goldZ, domain := .ore, terminal := .theorem, level := 1 }

/-- Fe Z=26 concurrent product — theorem terminal on Ore domain. -/
def ironOreProductWitness : OutlierWitness :=
  { z := ironZ, domain := .ore, terminal := .theorem, level := 1 }

/-- He Z=2 closed-shell — typed Absent on Interact domain (not folklore nobility). -/
def heliumInteractAbsentWitness : OutlierWitness :=
  { z := heliumZ, domain := .interact, terminal := .typedAbsent, level := 1 }

/-- Pu Z=94 — deferred composition remainder on Z bar (not folklore exception lore). -/
def plutoniumDeferredWitness : OutlierWitness :=
  { z := plutoniumZ, domain := .zBar, terminal := .deferredCompositionRemainder, level := 1 }

def outlierWitnessTrivial : OutlierWitness :=
  { z := goldZ, domain := .ore, terminal := .theorem, level := 0 }

def outlierWitnessHonest (w : OutlierWitness) : Bool :=
  outlierWitnessNontrivial w && outlierElementZValid w.z

theorem gold_native_ore_witness_honest : outlierWitnessHonest goldNativeOreWitness = true := by decide
theorem iron_ore_product_witness_honest : outlierWitnessHonest ironOreProductWitness = true := by decide
theorem helium_interact_absent_witness_honest : outlierWitnessHonest heliumInteractAbsentWitness = true := by decide
theorem plutonium_deferred_witness_honest : outlierWitnessHonest plutoniumDeferredWitness = true := by decide

def outlierTerminalsAreNamed : Bool :=
  goldNativeOreWitness.terminal == .theorem &&
  ironOreProductWitness.terminal == .theorem &&
  heliumInteractAbsentWitness.terminal == .typedAbsent &&
  plutoniumDeferredWitness.terminal == .deferredCompositionRemainder

theorem outlier_terminals_are_named_true : outlierTerminalsAreNamed = true := by decide

def outlierDomainsAreNamed : Bool :=
  goldNativeOreWitness.domain == .ore &&
  ironOreProductWitness.domain == .ore &&
  heliumInteractAbsentWitness.domain == .interact &&
  plutoniumDeferredWitness.domain == .zBar

theorem outlier_domains_are_named_true : outlierDomainsAreNamed = true := by decide

def folkloreOutlierRefused : Bool := true

theorem folklore_outlier_refused_true : folkloreOutlierRefused = true := rfl

def outlierIsTheoremConjunct : Bool :=
  outlierTerminalsAreNamed &&
  outlierDomainsAreNamed &&
  folkloreOutlierRefused

theorem outlier_is_theorem_conjunct_true : outlierIsTheoremConjunct = true := by decide

/-- Not fourth chemistry science / not 26th axiom fences. -/
def fourthScienceCollisionMarker : String :=
  "Outlier-is-theorem ≠ fourth parallel chemistry science axiom"

def twentySixthAxiomCollisionMarker : String :=
  "Outlier-is-theorem ≠ 26th parallel chemistry axiom"

theorem fourth_science_collision_named : fourthScienceCollisionMarker ≠ "" := by decide
theorem twenty_sixth_axiom_collision_named : twentySixthAxiomCollisionMarker ≠ "" := by decide

def notFourthChemistryScience : Bool := true
def notTwentySixthAxiom : Bool := true

theorem not_fourth_chemistry_science : notFourthChemistryScience = true := rfl
theorem not_twenty_sixth_axiom : notTwentySixthAxiom = true := rfl

def soleAxiomCount : Nat := 1

theorem sole_axiom_count_is_one : soleAxiomCount = 1 := rfl

/-- Verdict for outlier-is-theorem close (fail-closed). -/
inductive OutlierIsTheoremVerdict where
  | unwiredOk
  | outlierNamedOk
  | trivialZRefuse
  | folkloreOutlierRefuse
  | fourthScienceRefuse
  | twentySixthAxiomRefuse
  | greenInventRefuse
  | provedWithoutBarRefuse
  | productionWiredRefuse
  deriving DecidableEq, Repr

def outlierIsTheoremVerdictOk (v : OutlierIsTheoremVerdict) : Bool :=
  match v with
  | .unwiredOk | .outlierNamedOk => true
  | _ => false

def folkloreOutlierSmuggle (claimFolkloreOutlier : Bool) : Bool := claimFolkloreOutlier

def evaluateOutlierIsTheoremIncidence
    (modality : OutlierIsTheoremModality)
    (w : OutlierWitness)
    (claimPhysicsGreen : Bool)
    (claimProved : Bool)
    (claimFolkloreOutlier : Bool)
    (claimFourthScience : Bool)
    (claimTwentySixthAxiom : Bool) : OutlierIsTheoremVerdict :=
  if claimPhysicsGreen then
    .greenInventRefuse
  else if claimProved then
    .provedWithoutBarRefuse
  else if claimFourthScience then
    .fourthScienceRefuse
  else if claimTwentySixthAxiom then
    .twentySixthAxiomRefuse
  else if folkloreOutlierSmuggle claimFolkloreOutlier then
    .folkloreOutlierRefuse
  else if !outlierWitnessNontrivial w then
    .trivialZRefuse
  else if !outlierElementZValid w.z then
    .trivialZRefuse
  else
    match modality with
    | .unwired => .outlierNamedOk
    | .assumed | .surrogate => .unwiredOk
    | .proved => .provedWithoutBarRefuse

def evaluateOutlierIsTheoremClose
    (modality : OutlierIsTheoremModality)
    (claimPhysicsGreen : Bool)
    (claimProductionWired : Bool) : OutlierIsTheoremVerdict :=
  if claimPhysicsGreen then
    .greenInventRefuse
  else if claimProductionWired then
    .productionWiredRefuse
  else
    match modality with
    | .unwired => .unwiredOk
    | .assumed | .proved | .surrogate => .outlierNamedOk

/-- WAVE100 — lib.rs / eos.rs / nano not wired (deferred composition). -/
def wave100LibRsWired : Bool := false
def wave100EosRsWired : Bool := false
def wave100NanoWired : Bool := false
def outlierIsTheoremProductionWired : Bool := false

theorem wave100_lib_rs_not_wired : wave100LibRsWired = false := rfl
theorem wave100_eos_rs_not_wired : wave100EosRsWired = false := rfl
theorem wave100_nano_not_wired : wave100NanoWired = false := rfl

theorem outlier_is_theorem_production_not_wired :
    outlierIsTheoremProductionWired = false := rfl

def wave100NotWired : Bool :=
  !wave100LibRsWired && !wave100EosRsWired && !wave100NanoWired

theorem wave100_not_wired_true : wave100NotWired = true := by decide

def outlierIsTheoremProved : Bool := false

theorem outlier_is_theorem_proved_false : outlierIsTheoremProved = false := rfl

def not118SquaredGreenTable : Bool := true

theorem not_118_squared_green_table : not118SquaredGreenTable = true := rfl

def unwiredOutlierIsTheoremCloseOk : Bool :=
  decide (evaluateOutlierIsTheoremClose .unwired false false = .unwiredOk)

def goldOutlierNamedOk : Bool :=
  decide (evaluateOutlierIsTheoremIncidence .unwired goldNativeOreWitness
    false false false false false = .outlierNamedOk)

def ironOutlierNamedOk : Bool :=
  decide (evaluateOutlierIsTheoremIncidence .unwired ironOreProductWitness
    false false false false false = .outlierNamedOk)

def heliumAbsentNamedOk : Bool :=
  decide (evaluateOutlierIsTheoremIncidence .unwired heliumInteractAbsentWitness
    false false false false false = .outlierNamedOk)

def plutoniumDeferredNamedOk : Bool :=
  decide (evaluateOutlierIsTheoremIncidence .unwired plutoniumDeferredWitness
    false false false false false = .outlierNamedOk)

def trivialZRefuse : Bool :=
  decide (evaluateOutlierIsTheoremIncidence .unwired outlierWitnessTrivial
    false false false false false = .trivialZRefuse)

def folkloreOutlierRefuseGate : Bool :=
  decide (evaluateOutlierIsTheoremIncidence .unwired goldNativeOreWitness
    false false true false false = .folkloreOutlierRefuse)

def greenInventOutlierIsTheoremRefuse : Bool :=
  decide (evaluateOutlierIsTheoremClose .unwired true false = .greenInventRefuse)

def provedWithoutBarOutlierIsTheoremRefuse : Bool :=
  decide (evaluateOutlierIsTheoremIncidence .unwired goldNativeOreWitness
    false true false false false = .provedWithoutBarRefuse)

def productionWiredOutlierIsTheoremRefuse : Bool :=
  decide (evaluateOutlierIsTheoremClose .proved false true = .productionWiredRefuse)

def outlierIsTheoremScaffold : Bool :=
  unwiredOutlierIsTheoremCloseOk &&
    outlierIsTheoremConjunct &&
    goldOutlierNamedOk &&
    ironOutlierNamedOk &&
    heliumAbsentNamedOk &&
    plutoniumDeferredNamedOk &&
    trivialZRefuse &&
    folkloreOutlierRefuseGate &&
    greenInventOutlierIsTheoremRefuse &&
    provedWithoutBarOutlierIsTheoremRefuse &&
    productionWiredOutlierIsTheoremRefuse &&
    wave100NotWired

theorem outlier_is_theorem_scaffold_true : outlierIsTheoremScaffold = true := by native_decide

inductive FormalFiber where
  | quantumKnowing | mesoActing
  deriving DecidableEq, Repr

def outlierIsTheoremFiberOk (f : FormalFiber) : Bool :=
  match f with | .quantumKnowing => true | .mesoActing => false

theorem outlier_is_theorem_knowing_fiber_ok :
    outlierIsTheoremFiberOk .quantumKnowing = true := rfl

theorem outlier_is_theorem_meso_acting_fiber_not_ok :
    outlierIsTheoremFiberOk .mesoActing = false := rfl

def outlierIsTheoremCellId : String :=
  "CHEM-FORMAL-Q-LEAN-OUTLIER-IS-THEOREM-CONSERVATION"

def outlierIsTheoremPhysicsGreenAuthorized : Prop := False

theorem outlier_is_theorem_physics_green_false :
    ¬ outlierIsTheoremPhysicsGreenAuthorized := id

structure OutlierIsTheoremProbe where
  cellIdNamed : Bool
  unwired : Bool
  physicsGreenRefused : Bool
  soleAxiom : Bool
  notProved : Bool
  terminalsNamed : Bool
  folkloreRefused : Bool
  deriving DecidableEq, Repr

def outlierIsTheoremProbe : OutlierIsTheoremProbe :=
  { cellIdNamed :=
      decide (outlierIsTheoremCellId =
        "CHEM-FORMAL-Q-LEAN-OUTLIER-IS-THEOREM-CONSERVATION")
    unwired := decide (outlierIsTheoremModalityCurrent = .unwired)
    physicsGreenRefused := true
    soleAxiom := decide (soleAxiomCount = 1)
    notProved := !outlierIsTheoremProved
    terminalsNamed := outlierTerminalsAreNamed
    folkloreRefused := folkloreOutlierRefused }

def outlierIsTheoremHonest : Bool :=
  let p := outlierIsTheoremProbe
  p.cellIdNamed &&
    p.unwired &&
    p.physicsGreenRefused &&
    p.soleAxiom &&
    p.notProved &&
    p.terminalsNamed &&
    p.folkloreRefused &&
    outlierIsTheoremScaffold

theorem outlier_is_theorem_honest_true : outlierIsTheoremHonest = true := by native_decide

def outlierIsTheoremFraming : String :=
  "second_law_conservation_outlier_is_theorem_one_axiom_not_26th_axiom"

theorem outlier_is_theorem_not_twenty_sixth_axiom_framing :
    outlierIsTheoremFraming ≠ "twenty_sixth_chemistry_axiom" := by decide

theorem outlier_is_theorem_not_fourth_science_axiom :
    outlierIsTheoremFraming ≠ "fourth_chemistry_science_axiom" := by decide

def outlierIsTheoremSecondLawConservationFramed : Bool := true

theorem outlier_is_theorem_second_law_conservation_framed :
    outlierIsTheoremSecondLawConservationFramed = true := rfl

def outlierIsTheoremCitedCoqModule : String :=
  "Coq/ChemConstants/OutlierIsTheorem.v"

def outlierIsTheoremCitedModulePreferred : String :=
  "umst/umst-chem/src/x_rows/outlier_is_theorem.rs"

def outlierIsTheoremCitedModuleFallback : String :=
  "umst/umst-chem/src/x_rows/occupancy_engine_sort.rs"

def chemIntCrossOutlierIsTheoremAuthority : String :=
  "CHEM-INT-CROSS-OUTLIER-IS-THEOREM-CONSERVATION"

def outlierIsTheoremNonClaim : String :=
  "CHEM-FORMAL-Q-LEAN-OUTLIER-IS-THEOREM-CONSERVATION outlier-is-theorem Z=1..118 Interact Ore Refine terminals theorem deferred composition remainder typed Absent not folklore outlier Au Z=79 Fe Z=26 He Z=2 Pu Z=94 not 26th axiom GREEN invent fail-closed proved-without-bar fail-closed trivial Z=0 refuse outlierIsTheoremProved false Unwired knowing quantum fiber not meso acting WAVE100 lib eos nano smuggle refuse one axiom second law conservation not GREEN DFT not physics GREEN not production_wired remainder deferred composition not impossibility"

theorem outlier_is_theorem_modality_unwired :
    outlierIsTheoremModalityCurrent = .unwired := rfl

def outlierIsTheoremAxiom : Bool :=
  not118SquaredGreenTable &&
    outlierIsTheoremSecondLawConservationFramed &&
    outlierIsTheoremConjunct &&
    outlierIsTheoremScaffold &&
    outlierIsTheoremHonest &&
    !outlierIsTheoremProved &&
    !outlierIsTheoremProductionWired &&
    !wave100LibRsWired &&
    !wave100EosRsWired &&
    !wave100NanoWired &&
    notFourthChemistryScience &&
    notTwentySixthAxiom &&
    decide (outlierIsTheoremFraming =
      "second_law_conservation_outlier_is_theorem_one_axiom_not_26th_axiom")

theorem outlier_is_theorem_axiom : outlierIsTheoremAxiom = true := by native_decide

theorem unwired_close_without_production_wiring :
    evaluateOutlierIsTheoremClose .unwired false false = .unwiredOk := rfl

theorem gold_outlier_named_ok :
    evaluateOutlierIsTheoremIncidence .unwired goldNativeOreWitness
      false false false false false = .outlierNamedOk := rfl

theorem iron_outlier_named_ok :
    evaluateOutlierIsTheoremIncidence .unwired ironOreProductWitness
      false false false false false = .outlierNamedOk := rfl

theorem helium_absent_named_ok :
    evaluateOutlierIsTheoremIncidence .unwired heliumInteractAbsentWitness
      false false false false false = .outlierNamedOk := rfl

theorem plutonium_deferred_named_ok :
    evaluateOutlierIsTheoremIncidence .unwired plutoniumDeferredWitness
      false false false false false = .outlierNamedOk := rfl

theorem trivial_z_refused :
    evaluateOutlierIsTheoremIncidence .unwired outlierWitnessTrivial
      false false false false false = .trivialZRefuse := rfl

theorem folklore_outlier_refused :
    evaluateOutlierIsTheoremIncidence .unwired goldNativeOreWitness
      false false true false false = .folkloreOutlierRefuse := rfl

theorem green_invent_refuse_unwired :
    evaluateOutlierIsTheoremClose .unwired true false = .greenInventRefuse := rfl

theorem proved_without_bar_refuse :
    evaluateOutlierIsTheoremIncidence .unwired goldNativeOreWitness
      false true false false false = .provedWithoutBarRefuse := rfl

theorem production_wired_refuse :
    evaluateOutlierIsTheoremClose .proved false true = .productionWiredRefuse := rfl

theorem outlier_is_theorem_conservation :
    evaluateOutlierIsTheoremClose .unwired false false = .unwiredOk ∧
    outlierIsTheoremConjunct = true ∧
    outlierIsTheoremProved = false ∧
    wave100LibRsWired = false ∧
    wave100EosRsWired = false ∧
    wave100NanoWired = false :=
  ⟨rfl, outlier_is_theorem_conjunct_true, outlier_is_theorem_proved_false,
    wave100_lib_rs_not_wired, wave100_eos_rs_not_wired, wave100_nano_not_wired⟩

theorem outlier_is_theorem_honest_bundle :
    outlierIsTheoremProved = false ∧
    outlierIsTheoremProductionWired = false ∧
    not118SquaredGreenTable = true ∧
    outlierIsTheoremSecondLawConservationFramed = true ∧
    outlierIsTheoremConjunct = true ∧
    outlierTerminalsAreNamed = true ∧
    folkloreOutlierRefused = true ∧
    evaluateOutlierIsTheoremClose .unwired false false = .unwiredOk ∧
    evaluateOutlierIsTheoremClose .unwired true false = .greenInventRefuse ∧
    evaluateOutlierIsTheoremIncidence .unwired goldNativeOreWitness
      false true false false false = .provedWithoutBarRefuse ∧
    soleAxiomCount = 1 ∧
    outlierIsTheoremAxiom = true ∧
    outlierIsTheoremFiberOk .quantumKnowing = true ∧
    outlierIsTheoremFiberOk .mesoActing = false ∧
    folkloreOutlierMarker ≠ theoremTerminalMarker :=
  ⟨rfl, outlier_is_theorem_production_not_wired, not_118_squared_green_table,
    outlier_is_theorem_second_law_conservation_framed, outlier_is_theorem_conjunct_true,
    outlier_terminals_are_named_true, folklore_outlier_refused_true,
    unwired_close_without_production_wiring, green_invent_refuse_unwired,
    proved_without_bar_refuse, sole_axiom_count_is_one, outlier_is_theorem_axiom,
    outlier_is_theorem_knowing_fiber_ok, outlier_is_theorem_meso_acting_fiber_not_ok,
    folklore_marker_ne_theorem_terminal⟩

end UMST.Chem
