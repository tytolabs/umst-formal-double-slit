-- SPDX-FileCopyrightText: 2026 Santosh Prabhu Shenbagamoorthy and Santhosh Shyamsundar
-- SPDX-License-Identifier: MIT

import ElementElectronic

set_option maxRecDepth 8192

/-!
# ComposerResearchBleedingEdge — composer research bleeding-edge **conservation** (Q lattice)

Knowing-fiber Lean: `umst-chem-research` (composer-2.5, never fast) emits **named hypotheses only**;
coding remains umst-admit. Research chart conservation on one second-law + conservation axiom object;
literature requiring new axiom refused; not a 26th axiom; not physics GREEN. Hypothesis rows map to
v50 `COMPOSER-RESEARCH-BLEEDING-EDGE` stem. Pairs `umst-chem` scaffold
`composer_research_bleeding_edge` / **conservation** posture.

Read-only cites (not imported — self-contained scaffold):
- `Coq/ChemConstants/ComposerResearchBleedingEdge.v`
- `umst/umst-chem/src/x_rows/composer_research_bleeding_edge.rs` (absent — cite `occupancy_engine_sort.rs` posture)

- `ComposerResearchBleedingEdgeModality` — Unwired / Assumed / Proved / Surrogate (not 118² GREEN table).
- `ResearchHypothesisClass` — theoremCandidate / namedMeasuredRemainder / alreadyUnwired / absent.
- `BleedingEdgeHypothesisRow` — v50 hypothesis ids with chart conservation pins.
- Cites `workspace/ops/CHEM_NS_V50_RESEARCH_HYPOTHESES.json` read-only — not fork.
- Second-law + **conservation** framing cites meso `UMST.Chem.Conservation` /
  `LandauerLaw.physicalSecondLaw` — not imported.
- No meso / acting theorems. No new physics `axiom`. Research does not write WAVE100 or mint SI (k/R/ε₀).
- `physics_green` stays false. Does **not** claim `composerResearchBleedingEdgeProved` or physics GREEN.
- WAVE100 freeze — remainder deferred composition (env/time/cross-domain), not impossibility stop.
- Does **not** Landauer-fake α.
-/

namespace UMST.Chem

/-- Design modality for composer research bleeding-edge **conservation** (lattice SSOT). -/
inductive ComposerResearchBleedingEdgeModality where
  | unwired | assumed | proved | surrogate
  deriving DecidableEq, Repr

def composerResearchBleedingEdgeModalityCurrent : ComposerResearchBleedingEdgeModality := .unwired

/-- Modality lattice cardinality (Unwired / Assumed / Proved / Surrogate). -/
def composerResearchBleedingEdgeModalityLatticeCardinality : Nat := 4

theorem composer_research_bleeding_edge_modality_lattice_cardinality_four :
    composerResearchBleedingEdgeModalityLatticeCardinality = 4 := rfl

theorem composer_research_bleeding_edge_modality_lattice_not_118_squared :
    composerResearchBleedingEdgeModalityLatticeCardinality ≠ 118 * 118 := by decide

/-- Surface tag for name-from-content. -/
def composerResearchBleedingEdgeSurface : String := "composer_research_bleeding_edge_surface"

theorem composer_research_bleeding_edge_surface_named :
    composerResearchBleedingEdgeSurface ≠ "" := by decide

/-- Machine-readable composer research bleeding-edge marker. -/
def composerResearchBleedingEdgeMarker : String :=
  "chem_int_cross_composer_research_bleeding_edge_v1"

theorem composer_research_bleeding_edge_marker_named :
    composerResearchBleedingEdgeMarker ≠ "" := by decide

/-- v50 bleeding-edge stem pin. -/
def composerResearchBleedingEdgeV50Stem : String := "COMPOSER-RESEARCH-BLEEDING-EDGE"

theorem composer_research_bleeding_edge_v50_stem_named :
    composerResearchBleedingEdgeV50Stem = "COMPOSER-RESEARCH-BLEEDING-EDGE" := rfl

def composerResearchBleedingEdgeRowStem : String := "composer_research_bleeding_edge"

theorem composer_research_bleeding_edge_row_stem_named :
    composerResearchBleedingEdgeRowStem = "composer_research_bleeding_edge" := rfl

/-- Research hypothesis class — named chart entries, not XOR enum. -/
inductive ResearchHypothesisClass where
  | theoremCandidate | namedMeasuredRemainder | alreadyUnwired | absent
  deriving DecidableEq, Repr

def researchHypothesisClassTag (c : ResearchHypothesisClass) : String :=
  match c with
  | .theoremCandidate => "theorem-candidate"
  | .namedMeasuredRemainder => "named-measured-remainder"
  | .alreadyUnwired => "already-unwired"
  | .absent => "absent"

theorem research_hypothesis_theorem_candidate_tag :
    researchHypothesisClassTag .theoremCandidate = "theorem-candidate" := rfl

theorem research_hypothesis_named_measured_remainder_tag :
    researchHypothesisClassTag .namedMeasuredRemainder = "named-measured-remainder" := rfl

theorem research_hypothesis_already_unwired_tag :
    researchHypothesisClassTag .alreadyUnwired = "already-unwired" := rfl

theorem research_hypothesis_absent_tag :
    researchHypothesisClassTag .absent = "absent" := rfl

def researchHypothesisClassCount : Nat := 4

theorem research_hypothesis_class_count_is_four : researchHypothesisClassCount = 4 := rfl

/-- Bleeding-edge hypothesis ids — cite JSON, no fork. -/
def refuseCatalysisAxiomHypothesisId : String := "H-V50-REFUSE-CATALYSIS-AXIOM"
def chemPhysicsIsomorphismHypothesisId : String := "H-V50-CHEM-PHYSICS-ISOMORPHISM"

def bleedingEdgeHypothesisIds : List String :=
  [refuseCatalysisAxiomHypothesisId, chemPhysicsIsomorphismHypothesisId]

theorem refuse_catalysis_axiom_hypothesis_id_named :
    refuseCatalysisAxiomHypothesisId = "H-V50-REFUSE-CATALYSIS-AXIOM" := rfl

theorem chem_physics_isomorphism_hypothesis_id_named :
    chemPhysicsIsomorphismHypothesisId = "H-V50-CHEM-PHYSICS-ISOMORPHISM" := rfl

def bleedingEdgeHypothesisCount : Nat := 2

theorem bleeding_edge_hypothesis_count_is_two : bleedingEdgeHypothesisCount = 2 := rfl

def stringInList (s : String) (ids : List String) : Bool :=
  ids.any (· == s)

theorem refuse_catalysis_axiom_in_bleeding_edge_ids :
    stringInList refuseCatalysisAxiomHypothesisId bleedingEdgeHypothesisIds = true := by decide

theorem chem_physics_isomorphism_in_bleeding_edge_ids :
    stringInList chemPhysicsIsomorphismHypothesisId bleedingEdgeHypothesisIds = true := by decide

structure BleedingEdgeHypothesisRow where
  hypothesisId : String
  hypothesisClass : ResearchHypothesisClass
  mapsToStem : Bool
  notA26thAxiom : Bool
  deriving DecidableEq, Repr

def researchChartConservationHolds (row : BleedingEdgeHypothesisRow) : Bool :=
  row.mapsToStem && row.notA26thAxiom

/-- Refuse catalysis axiom — absent class, maps to v50 stem. -/
def refuseCatalysisAxiomRow : BleedingEdgeHypothesisRow :=
  { hypothesisId := refuseCatalysisAxiomHypothesisId
    hypothesisClass := .absent
    mapsToStem := true
    notA26thAxiom := true }

/-- Chem-physics isomorphism — already unwired class, maps to v50 stem. -/
def chemPhysicsIsomorphismRow : BleedingEdgeHypothesisRow :=
  { hypothesisId := chemPhysicsIsomorphismHypothesisId
    hypothesisClass := .alreadyUnwired
    mapsToStem := true
    notA26thAxiom := true }

def bleedingEdgeHypothesisRows : List BleedingEdgeHypothesisRow :=
  [refuseCatalysisAxiomRow, chemPhysicsIsomorphismRow]

def bleedingEdgeHypothesisRowCount : Nat := 2

theorem bleeding_edge_hypothesis_row_count_is_two : bleedingEdgeHypothesisRowCount = 2 := rfl

theorem refuse_catalysis_axiom_row_conservation :
    researchChartConservationHolds refuseCatalysisAxiomRow = true := by decide

theorem chem_physics_isomorphism_row_conservation :
    researchChartConservationHolds chemPhysicsIsomorphismRow = true := by decide

theorem refuse_catalysis_axiom_row_class_absent :
    refuseCatalysisAxiomRow.hypothesisClass = .absent := rfl

theorem chem_physics_isomorphism_row_class_already_unwired :
    chemPhysicsIsomorphismRow.hypothesisClass = .alreadyUnwired := rfl

def bleedingEdgeHypothesesConserved : Bool :=
  researchChartConservationHolds refuseCatalysisAxiomRow &&
  researchChartConservationHolds chemPhysicsIsomorphismRow

theorem bleeding_edge_hypotheses_conserved : bleedingEdgeHypothesesConserved = true := by decide

/-- Research hypotheses JSON authority — cite read-only, not fork. -/
def researchHypothesesAuthority : String :=
  "workspace/ops/CHEM_NS_V50_RESEARCH_HYPOTHESES.json"

theorem research_hypotheses_authority_named : researchHypothesesAuthority ≠ "" := by decide

def researchHypothesesCitedNotForked : Bool :=
  researchHypothesesAuthority ≠ "" &&
  composerResearchBleedingEdgeMarker ≠ "" &&
  researchHypothesesAuthority ≠ composerResearchBleedingEdgeMarker

theorem research_hypotheses_cited_not_forked_true : researchHypothesesCitedNotForked = true := by decide

def composerResearchIsNewAxiom : Bool := false

theorem composer_research_not_new_axiom : composerResearchIsNewAxiom = false := rfl

def researchChartNot26thAxiomOrPhysicsGreen : String :=
  "composer research bleeding-edge is named research chart conservation — not 26th axiom not physics GREEN"

theorem research_chart_not_26th_axiom_or_physics_green_named :
    researchChartNot26thAxiomOrPhysicsGreen ≠ "" := by decide

def literatureNewAxiomRefused : Bool :=
  researchChartNot26thAxiomOrPhysicsGreen ≠ "" && !composerResearchIsNewAxiom

theorem literature_new_axiom_refused_true : literatureNewAxiomRefused = true := by decide

def secondLawConservationAxiomPin : String :=
  "second law conservation — research chart on one axiom object; not physics GREEN"

theorem second_law_conservation_axiom_pin_named : secondLawConservationAxiomPin ≠ "" := by decide

/-- Not fourth chemistry science / not 26th axiom fences. -/
def fourthScienceCollisionMarker : String :=
  "Composer-research-bleeding-edge ≠ fourth parallel chemistry science axiom"

def twentySixthAxiomCollisionMarker : String :=
  "Composer-research-bleeding-edge ≠ 26th parallel chemistry axiom"

theorem fourth_science_collision_named : fourthScienceCollisionMarker ≠ "" := by decide
theorem twenty_sixth_axiom_collision_named : twentySixthAxiomCollisionMarker ≠ "" := by decide

def notFourthChemistryScience : Bool := true
def notTwentySixthAxiom : Bool := true

theorem not_fourth_chemistry_science : notFourthChemistryScience = true := rfl
theorem not_twenty_sixth_axiom : notTwentySixthAxiom = true := rfl

def composerResearchBleedingEdgeConjunct : Bool :=
  !composerResearchIsNewAxiom &&
  bleedingEdgeHypothesesConserved &&
  researchHypothesesCitedNotForked &&
  literatureNewAxiomRefused &&
  notTwentySixthAxiom

theorem composer_research_bleeding_edge_conjunct_true :
    composerResearchBleedingEdgeConjunct = true := by decide

def soleAxiomCount : Nat := 1

theorem sole_axiom_count_is_one : soleAxiomCount = 1 := rfl

/-- Verdict for composer research bleeding-edge close (fail-closed). -/
inductive ComposerResearchBleedingEdgeVerdict where
  | unwiredOk
  | hypothesisNamedOk
  | newAxiomRefuse
  | literatureNewAxiomRefuse
  | fourthScienceRefuse
  | twentySixthAxiomRefuse
  | greenInventRefuse
  | provedWithoutBarRefuse
  | productionWiredRefuse
  | siMintRefuse
  deriving DecidableEq, Repr

def composerResearchBleedingEdgeVerdictOk (v : ComposerResearchBleedingEdgeVerdict) : Bool :=
  match v with
  | .unwiredOk | .hypothesisNamedOk => true
  | _ => false

def evaluateBleedingEdgeHypothesisRow
    (modality : ComposerResearchBleedingEdgeModality)
    (row : BleedingEdgeHypothesisRow)
    (claimPhysicsGreen : Bool)
    (claimProved : Bool)
    (claimNewAxiom : Bool)
    (claimFourthScience : Bool)
    (claimTwentySixthAxiom : Bool)
    (claimSiMint : Bool) : ComposerResearchBleedingEdgeVerdict :=
  if claimPhysicsGreen then
    .greenInventRefuse
  else if claimProved then
    .provedWithoutBarRefuse
  else if claimFourthScience then
    .fourthScienceRefuse
  else if claimTwentySixthAxiom then
    .twentySixthAxiomRefuse
  else if claimSiMint then
    .siMintRefuse
  else if claimNewAxiom then
    .newAxiomRefuse
  else if !researchChartConservationHolds row then
    .literatureNewAxiomRefuse
  else
    match modality with
    | .unwired => .hypothesisNamedOk
    | .assumed | .surrogate => .unwiredOk
    | .proved => .provedWithoutBarRefuse

def evaluateComposerResearchBleedingEdgeClose
    (modality : ComposerResearchBleedingEdgeModality)
    (claimPhysicsGreen : Bool)
    (claimProductionWired : Bool) : ComposerResearchBleedingEdgeVerdict :=
  if claimPhysicsGreen then
    .greenInventRefuse
  else if claimProductionWired then
    .productionWiredRefuse
  else
    match modality with
    | .unwired => .unwiredOk
    | .assumed | .proved | .surrogate => .hypothesisNamedOk

/-- WAVE100 — lib.rs / eos.rs / nano not wired (deferred composition). -/
def wave100LibRsWired : Bool := false
def wave100EosRsWired : Bool := false
def wave100NanoWired : Bool := false
def composerResearchBleedingEdgeProductionWired : Bool := false

theorem wave100_lib_rs_not_wired : wave100LibRsWired = false := rfl
theorem wave100_eos_rs_not_wired : wave100EosRsWired = false := rfl
theorem wave100_nano_not_wired : wave100NanoWired = false := rfl

theorem composer_research_bleeding_edge_production_not_wired :
    composerResearchBleedingEdgeProductionWired = false := rfl

def wave100NotWiredLibOrEos : String :=
  "WAVE100 freeze — deferred composition not impossibility; not wired lib.rs eos.rs"

theorem wave100_not_wired_lib_or_eos : wave100NotWiredLibOrEos ≠ "" := by decide

def wave100NotWired : Bool :=
  !wave100LibRsWired && !wave100EosRsWired && !wave100NanoWired

theorem wave100_not_wired_true : wave100NotWired = true := by decide

def composerResearchBleedingEdgeProved : Bool := false

theorem composer_research_bleeding_edge_not_proved : composerResearchBleedingEdgeProved = false := rfl

def not118SquaredGreenTable : Bool := true

theorem not_118_squared_green_table : not118SquaredGreenTable = true := rfl

/-- Does not mint k, R, or ε₀. -/
def siMintK : Bool := false
def siMintR : Bool := false
def siMintEpsilon0 : Bool := false

theorem si_mint_k_refused : siMintK = false := rfl
theorem si_mint_r_refused : siMintR = false := rfl
theorem si_mint_epsilon0_refused : siMintEpsilon0 = false := rfl

def siMintRefused : Bool := !siMintK && !siMintR && !siMintEpsilon0

theorem si_mint_refused_true : siMintRefused = true := by decide

def unwiredComposerResearchBleedingEdgeCloseOk : Bool :=
  decide (evaluateComposerResearchBleedingEdgeClose .unwired false false = .unwiredOk)

def refuseCatalysisAxiomRowOk : Bool :=
  decide (evaluateBleedingEdgeHypothesisRow .unwired refuseCatalysisAxiomRow
    false false false false false false = .hypothesisNamedOk)

def chemPhysicsIsomorphismRowOk : Bool :=
  decide (evaluateBleedingEdgeHypothesisRow .unwired chemPhysicsIsomorphismRow
    false false false false false false = .hypothesisNamedOk)

def newAxiomRefuseGate : Bool :=
  decide (evaluateBleedingEdgeHypothesisRow .unwired refuseCatalysisAxiomRow
    false false true false false false = .newAxiomRefuse)

def siMintRefuseGate : Bool :=
  decide (evaluateBleedingEdgeHypothesisRow .unwired chemPhysicsIsomorphismRow
    false false false false false true = .siMintRefuse)

def greenInventComposerResearchBleedingEdgeRefuse : Bool :=
  decide (evaluateComposerResearchBleedingEdgeClose .unwired true false = .greenInventRefuse)

def provedWithoutBarComposerResearchBleedingEdgeRefuse : Bool :=
  decide (evaluateBleedingEdgeHypothesisRow .unwired refuseCatalysisAxiomRow
    false true false false false false = .provedWithoutBarRefuse)

def productionWiredComposerResearchBleedingEdgeRefuse : Bool :=
  decide (evaluateComposerResearchBleedingEdgeClose .proved false true = .productionWiredRefuse)

def composerResearchBleedingEdgeScaffold : Bool :=
  unwiredComposerResearchBleedingEdgeCloseOk &&
    composerResearchBleedingEdgeConjunct &&
    refuseCatalysisAxiomRowOk &&
    chemPhysicsIsomorphismRowOk &&
    newAxiomRefuseGate &&
    siMintRefuseGate &&
    greenInventComposerResearchBleedingEdgeRefuse &&
    provedWithoutBarComposerResearchBleedingEdgeRefuse &&
    productionWiredComposerResearchBleedingEdgeRefuse &&
    wave100NotWired &&
    siMintRefused

theorem composer_research_bleeding_edge_scaffold_true :
    composerResearchBleedingEdgeScaffold = true := by native_decide

inductive FormalFiber where
  | quantumKnowing | mesoActing
  deriving DecidableEq, Repr

def composerResearchBleedingEdgeFiberOk (f : FormalFiber) : Bool :=
  match f with | .quantumKnowing => true | .mesoActing => false

theorem composer_research_bleeding_edge_knowing_fiber_ok :
    composerResearchBleedingEdgeFiberOk .quantumKnowing = true := rfl

theorem composer_research_bleeding_edge_meso_acting_fiber_not_ok :
    composerResearchBleedingEdgeFiberOk .mesoActing = false := rfl

def composerResearchBleedingEdgeCellId : String :=
  "CHEM-FORMAL-Q-LEAN-COMPOSER-RESEARCH-BLEEDING-EDGE-CONSERVATION"

def composerResearchBleedingEdgePhysicsGreenAuthorized : Prop := False

theorem composer_research_bleeding_edge_physics_green_false :
    ¬ composerResearchBleedingEdgePhysicsGreenAuthorized := id

structure ComposerResearchBleedingEdgeProbe where
  cellIdNamed : Bool
  unwired : Bool
  physicsGreenRefused : Bool
  soleAxiom : Bool
  notProved : Bool
  hypothesesConserved : Bool
  jsonCitedNotForked : Bool
  deriving DecidableEq, Repr

def composerResearchBleedingEdgeProbe : ComposerResearchBleedingEdgeProbe :=
  { cellIdNamed :=
      decide (composerResearchBleedingEdgeCellId =
        "CHEM-FORMAL-Q-LEAN-COMPOSER-RESEARCH-BLEEDING-EDGE-CONSERVATION")
    unwired := decide (composerResearchBleedingEdgeModalityCurrent = .unwired)
    physicsGreenRefused := true
    soleAxiom := decide (soleAxiomCount = 1)
    notProved := !composerResearchBleedingEdgeProved
    hypothesesConserved := bleedingEdgeHypothesesConserved
    jsonCitedNotForked := researchHypothesesCitedNotForked }

def composerResearchBleedingEdgeHonest : Bool :=
  let p := composerResearchBleedingEdgeProbe
  p.cellIdNamed &&
    p.unwired &&
    p.physicsGreenRefused &&
    p.soleAxiom &&
    p.notProved &&
    p.hypothesesConserved &&
    p.jsonCitedNotForked &&
    composerResearchBleedingEdgeScaffold

theorem composer_research_bleeding_edge_honest_true :
    composerResearchBleedingEdgeHonest = true := by native_decide

def composerResearchBleedingEdgeFraming : String :=
  "second_law_conservation_composer_research_bleeding_edge_one_axiom_not_26th_axiom"

theorem composer_research_bleeding_edge_not_twenty_sixth_axiom_framing :
    composerResearchBleedingEdgeFraming ≠ "twenty_sixth_chemistry_axiom" := by decide

theorem composer_research_bleeding_edge_not_fourth_science_axiom :
    composerResearchBleedingEdgeFraming ≠ "fourth_chemistry_science_axiom" := by decide

def composerResearchBleedingEdgeSecondLawConservationFramed : Bool := true

theorem composer_research_bleeding_edge_second_law_conservation_framed :
    composerResearchBleedingEdgeSecondLawConservationFramed = true := rfl

def composerResearchBleedingEdgeCitedCoqModule : String :=
  "Coq/ChemConstants/ComposerResearchBleedingEdge.v"

def composerResearchBleedingEdgeCitedModulePreferred : String :=
  "umst/umst-chem/src/x_rows/composer_research_bleeding_edge.rs"

def composerResearchBleedingEdgeCitedModuleFallback : String :=
  "umst/umst-chem/src/x_rows/occupancy_engine_sort.rs"

def chemIntCrossComposerResearchBleedingEdgeAuthority : String :=
  "CHEM-INT-CROSS-COMPOSER-RESEARCH-BLEEDING-EDGE-CONSERVATION"

def composerResearchBleedingEdgeNonClaim : String :=
  "CHEM-FORMAL-Q-LEAN-COMPOSER-RESEARCH-BLEEDING-EDGE-CONSERVATION composer research bleeding-edge lane named research chart Unwired — cite CHEM_NS_V50_RESEARCH_HYPOTHESES.json read-only not fork; umst-chem-research composer-2.5 never fast named hypotheses only; literature requiring new axiom refused; not 26th axiom; not physics GREEN; not production_wired remainder deferred composition not impossibility no k R epsilon0 mint no Landauer-fake alpha WAVE100 lib eos nano smuggle refuse"

theorem composer_research_bleeding_edge_modality_unwired :
    composerResearchBleedingEdgeModalityCurrent = .unwired := rfl

theorem composer_research_bleeding_edge_cites_coq_module :
    composerResearchBleedingEdgeCitedCoqModule =
      "Coq/ChemConstants/ComposerResearchBleedingEdge.v" := rfl

theorem composer_research_bleeding_edge_cites_int_authority :
    composerResearchBleedingEdgeCitedModulePreferred =
      "umst/umst-chem/src/x_rows/composer_research_bleeding_edge.rs" := rfl

theorem composer_research_bleeding_edge_cites_int_cell_id :
    chemIntCrossComposerResearchBleedingEdgeAuthority =
      "CHEM-INT-CROSS-COMPOSER-RESEARCH-BLEEDING-EDGE-CONSERVATION" := rfl

theorem composer_research_bleeding_edge_cites_fallback_module :
    composerResearchBleedingEdgeCitedModuleFallback =
      "umst/umst-chem/src/x_rows/occupancy_engine_sort.rs" := rfl

def composerResearchBleedingEdgeAxiom : Bool :=
  not118SquaredGreenTable &&
    composerResearchBleedingEdgeSecondLawConservationFramed &&
    composerResearchBleedingEdgeConjunct &&
    composerResearchBleedingEdgeScaffold &&
    composerResearchBleedingEdgeHonest &&
    !composerResearchBleedingEdgeProved &&
    !composerResearchBleedingEdgeProductionWired &&
    !wave100LibRsWired &&
    !wave100EosRsWired &&
    !wave100NanoWired &&
    notFourthChemistryScience &&
    notTwentySixthAxiom &&
    siMintRefused &&
    decide (composerResearchBleedingEdgeFraming =
      "second_law_conservation_composer_research_bleeding_edge_one_axiom_not_26th_axiom")

theorem composer_research_bleeding_edge_axiom : composerResearchBleedingEdgeAxiom = true := by native_decide

theorem unwired_close_without_production_wiring :
    evaluateComposerResearchBleedingEdgeClose .unwired false false = .unwiredOk := rfl

theorem refuse_catalysis_axiom_row_ok :
    evaluateBleedingEdgeHypothesisRow .unwired refuseCatalysisAxiomRow
      false false false false false false = .hypothesisNamedOk := rfl

theorem chem_physics_isomorphism_row_ok :
    evaluateBleedingEdgeHypothesisRow .unwired chemPhysicsIsomorphismRow
      false false false false false false = .hypothesisNamedOk := rfl

theorem new_axiom_refused :
    evaluateBleedingEdgeHypothesisRow .unwired refuseCatalysisAxiomRow
      false false true false false false = .newAxiomRefuse := rfl

theorem si_mint_refused_gate :
    evaluateBleedingEdgeHypothesisRow .unwired chemPhysicsIsomorphismRow
      false false false false false true = .siMintRefuse := rfl

theorem green_invent_refuse_unwired :
    evaluateComposerResearchBleedingEdgeClose .unwired true false = .greenInventRefuse := rfl

theorem proved_without_bar_refuse :
    evaluateBleedingEdgeHypothesisRow .unwired refuseCatalysisAxiomRow
      false true false false false false = .provedWithoutBarRefuse := rfl

theorem production_wired_refuse :
    evaluateComposerResearchBleedingEdgeClose .proved false true = .productionWiredRefuse := rfl

theorem composer_research_bleeding_edge_conservation :
    evaluateComposerResearchBleedingEdgeClose .unwired false false = .unwiredOk ∧
    composerResearchBleedingEdgeConjunct = true ∧
    composerResearchBleedingEdgeProved = false ∧
    wave100LibRsWired = false ∧
    wave100EosRsWired = false ∧
    wave100NanoWired = false ∧
    siMintRefused = true :=
  ⟨rfl, composer_research_bleeding_edge_conjunct_true, composer_research_bleeding_edge_not_proved,
    wave100_lib_rs_not_wired, wave100_eos_rs_not_wired, wave100_nano_not_wired, si_mint_refused_true⟩

theorem research_hypothesis_theorem_candidate_ne_absent_tag :
    researchHypothesisClassTag .theoremCandidate ≠ researchHypothesisClassTag .absent := by decide

theorem composer_research_bleeding_edge_honest_bundle :
    composerResearchBleedingEdgeProved = false ∧
    composerResearchBleedingEdgeProductionWired = false ∧
    not118SquaredGreenTable = true ∧
    composerResearchBleedingEdgeSecondLawConservationFramed = true ∧
    composerResearchBleedingEdgeConjunct = true ∧
    bleedingEdgeHypothesesConserved = true ∧
    researchHypothesesCitedNotForked = true ∧
    evaluateComposerResearchBleedingEdgeClose .unwired false false = .unwiredOk ∧
    evaluateComposerResearchBleedingEdgeClose .unwired true false = .greenInventRefuse ∧
    evaluateBleedingEdgeHypothesisRow .unwired refuseCatalysisAxiomRow
      false true false false false false = .provedWithoutBarRefuse ∧
    soleAxiomCount = 1 ∧
    composerResearchBleedingEdgeAxiom = true ∧
    composerResearchBleedingEdgeFiberOk .quantumKnowing = true ∧
    composerResearchBleedingEdgeFiberOk .mesoActing = false ∧
    researchHypothesisClassTag .theoremCandidate ≠ researchHypothesisClassTag .absent :=
  ⟨rfl, composer_research_bleeding_edge_production_not_wired, not_118_squared_green_table,
    composer_research_bleeding_edge_second_law_conservation_framed,
    composer_research_bleeding_edge_conjunct_true, bleeding_edge_hypotheses_conserved,
    research_hypotheses_cited_not_forked_true, unwired_close_without_production_wiring,
    green_invent_refuse_unwired, proved_without_bar_refuse, sole_axiom_count_is_one,
    composer_research_bleeding_edge_axiom,
    composer_research_bleeding_edge_knowing_fiber_ok,
    composer_research_bleeding_edge_meso_acting_fiber_not_ok,
    research_hypothesis_theorem_candidate_ne_absent_tag⟩

end UMST.Chem
