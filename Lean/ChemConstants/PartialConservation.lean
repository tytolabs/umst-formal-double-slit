-- SPDX-FileCopyrightText: 2026 Santosh Prabhu Shenbagamoorthy and Santhosh Shyamsundar
-- SPDX-License-Identifier: MIT

import ElementElectronic

/-!
# PartialConservation — knowing-fiber TYPE-05 partial Interact conservation (Q lattice)

North-star TYPE-05 claim **partial** Interact lattice on the quantum / knowing formal fiber —
Kleisli `Interact` between element pairs is **partial** (admissible vs forbidden). Pairs
`umst-chem` scaffold `CHEM-L0-TYPE-05` / `CHEM-INT-PROVE-TYPE-05-PARTIAL` **conservation** posture.

- `PartialConservationModality` — Unwired / Assumed / Proved / Surrogate (not 118² GREEN table).
- `InteractKind` — bond-forming / bond-repelling / structure-enabling / structure-blocking scaffold.
- `evaluatePartialConservation` — Unwired OK; Proved admissible scaffold OK; forbidden pairs refuse;
  total-claim refuse; GREEN invent refuse.
- Second-law + **conservation** framing cites meso `UMST.Chem.Conservation` / `LandauerLaw.physicalSecondLaw` — not imported.
- No meso / acting theorems. No new physics `axiom`.
- `physics_green` stays false. Does **not** claim TYPE-05 Proved or physics GREEN.
-/

namespace UMST.Chem

/-- Design modality for TYPE-05 claim partial Interact conservation (lattice SSOT). -/
inductive PartialConservationModality where
  | unwired | assumed | proved | surrogate
  deriving DecidableEq, Repr

def partialConservationModalityCurrent : PartialConservationModality := .unwired

/-- Bounded ElementId scaffold (H / O / Ca / Si — mirrors `umst-chem` L0 index). -/
inductive PartialElementId where
  | H | O | Ca | Si
  deriving DecidableEq, Repr

def partialElementIdString : PartialElementId → String
  | .H => "H"
  | .O => "O"
  | .Ca => "Ca"
  | .Si => "Si"

theorem partial_element_id_h : partialElementIdString .H = "H" := rfl

theorem partial_element_id_o : partialElementIdString .O = "O" := rfl

theorem partial_element_id_ca : partialElementIdString .Ca = "Ca" := rfl

theorem partial_element_id_si : partialElementIdString .Si = "Si" := rfl

/-- North-star Interact kind scaffold (pattern taxonomy preview). -/
inductive InteractKind where
  | bondForming | bondRepelling | structureEnabling | structureBlocking
  deriving DecidableEq, Repr

def interactKindString : InteractKind → String
  | .bondForming => "bond_forming"
  | .bondRepelling => "bond_repelling"
  | .structureEnabling => "structure_enabling"
  | .structureBlocking => "structure_blocking"

theorem interact_kind_bond_forming_str :
    interactKindString .bondForming = "bond_forming" := rfl

theorem interact_kind_structure_blocking_str :
    interactKindString .structureBlocking = "structure_blocking" := rfl

/-- Ordered element pair for a partial Interact attempt. -/
structure InteractPair where
  lhs : PartialElementId
  rhs : PartialElementId
  deriving DecidableEq, Repr

/-- A partial Interact attempt before thermo witness. -/
structure InteractAttempt where
  pair : InteractPair
  kind : InteractKind
  deriving DecidableEq, Repr

/-- Why a partial Interact is forbidden (partiality refusal). -/
inductive ForbiddenInteractReason where
  | selfSameElementBondForming
  | structureBlockingOnEnablingPair
  | conservationAxiomRefuse
  | nuclearElectronicBoundaryUnwired
  | totalInteractClaimRefuse
  deriving DecidableEq, Repr

def forbiddenInteractReasonString : ForbiddenInteractReason → String
  | .selfSameElementBondForming => "self_same_element_bond_forming"
  | .structureBlockingOnEnablingPair => "structure_blocking_on_enabling_pair"
  | .conservationAxiomRefuse => "conservation_axiom_refuse"
  | .nuclearElectronicBoundaryUnwired => "nuclear_electronic_boundary_unwired"
  | .totalInteractClaimRefuse => "total_interact_claim_refuse"

theorem forbidden_self_same_str :
    forbiddenInteractReasonString .selfSameElementBondForming =
      "self_same_element_bond_forming" := rfl

theorem forbidden_total_claim_str :
    forbiddenInteractReasonString .totalInteractClaimRefuse =
      "total_interact_claim_refuse" := rfl

/-- Admissible thermo-step scaffold (Unwired — not a proved thermo witness). -/
structure AdmissibleThermoStepScaffold where
  pair : InteractPair
  kind : InteractKind
  modalityTag : String
  deriving DecidableEq, Repr

/-- Verdict of a partial Interact close attempt (fail-closed). -/
inductive PartialInteractVerdict where
  | unwiredOk
  | admissibleOk
  | forbiddenRefuse
  | totalClaimRefuse
  | greenInventRefuse
  deriving DecidableEq, Repr

/-- Whether an unordered element pair matches a pinned forbidden row. -/
def interactPairMatches (tableLhs tableRhs : PartialElementId) (pair : InteractPair) : Bool :=
  decide ((pair.lhs == tableLhs && pair.rhs == tableRhs) ||
    (pair.lhs == tableRhs && pair.rhs == tableLhs))

/-- Lookup forbidden Interact rows (design table — Unwired, not exhaustive chemistry). -/
def lookupForbiddenInteract (attempt : InteractAttempt) : Option ForbiddenInteractReason :=
  let pair := attempt.pair
  let kind := attempt.kind
  if kind == .bondForming then
    if interactPairMatches .H .H pair then some .selfSameElementBondForming
    else if interactPairMatches .O .O pair then some .selfSameElementBondForming
    else if interactPairMatches .H .Ca pair then some .nuclearElectronicBoundaryUnwired
    else none
  else if kind == .structureBlocking then
    if interactPairMatches .H .Si pair then some .structureBlockingOnEnablingPair
    else none
  else none

/-- Sample forbidden self same-element bond-forming attempt. -/
def interactAttemptSelfHH : InteractAttempt :=
  { pair := { lhs := .H, rhs := .H }, kind := .bondForming }

/-- Sample admissible Ca–O bond-forming attempt. -/
def interactAttemptCaO : InteractAttempt :=
  { pair := { lhs := .Ca, rhs := .O }, kind := .bondForming }

/-- Sample forbidden H–Si structure-blocking attempt. -/
def interactAttemptHSiBlocking : InteractAttempt :=
  { pair := { lhs := .H, rhs := .Si }, kind := .structureBlocking }

/-- Evaluate partial Interact typing against the TYPE-05 partial conservation bar. -/
def evaluatePartialConservation
    (modality : PartialConservationModality)
    (attempt : InteractAttempt)
    (claimTotalInteract : Bool)
    (claimPhysicsGreen : Bool) : PartialInteractVerdict :=
  if claimPhysicsGreen then
    .greenInventRefuse
  else if claimTotalInteract then
    .totalClaimRefuse
  else
    match modality with
    | .unwired | .assumed | .surrogate => .unwiredOk
    | .proved =>
      match lookupForbiddenInteract attempt with
      | some _ => .forbiddenRefuse
      | none => .admissibleOk

/-- Whether a partial Interact attempt is admissible under TYPE-05 (never GREEN). -/
def partialInteractAdmissible
    (attempt : InteractAttempt) (claimTotalInteract claimPhysicsGreen : Bool) : Bool :=
  decide (evaluatePartialConservation .proved attempt claimTotalInteract claimPhysicsGreen =
    .admissibleOk)

/-- Whether a close attempt is admissible under TYPE-05 partial conservation. -/
def partialInteractVerdictOk (v : PartialInteractVerdict) : Bool :=
  match v with
  | .unwiredOk | .admissibleOk => true
  | _ => false

theorem unwired_partial_ok :
    evaluatePartialConservation .unwired interactAttemptCaO false false = .unwiredOk := rfl

theorem assumed_partial_ok :
    evaluatePartialConservation .assumed interactAttemptSelfHH false false = .unwiredOk := rfl

theorem surrogate_partial_ok :
    evaluatePartialConservation .surrogate interactAttemptHSiBlocking false false = .unwiredOk := rfl

theorem proved_admissible_ca_o_ok :
    evaluatePartialConservation .proved interactAttemptCaO false false = .admissibleOk := rfl

theorem proved_self_hh_forbidden :
    evaluatePartialConservation .proved interactAttemptSelfHH false false = .forbiddenRefuse := rfl

theorem proved_h_si_blocking_forbidden :
    evaluatePartialConservation .proved interactAttemptHSiBlocking false false = .forbiddenRefuse := rfl

theorem total_claim_refuse :
    evaluatePartialConservation .unwired interactAttemptCaO true false = .totalClaimRefuse := rfl

theorem green_invent_refuse :
    evaluatePartialConservation .unwired interactAttemptCaO false true = .greenInventRefuse := rfl

theorem partial_interact_admissible_ca_o :
    partialInteractAdmissible interactAttemptCaO false false = true := rfl

theorem partial_interact_not_admissible_self_hh :
    partialInteractAdmissible interactAttemptSelfHH false false = false := rfl

theorem unwired_verdict_ok :
    partialInteractVerdictOk
      (evaluatePartialConservation .unwired interactAttemptCaO false false) = true := rfl

theorem self_hh_verdict_not_ok :
    partialInteractVerdictOk
      (evaluatePartialConservation .proved interactAttemptSelfHH false false) = false := rfl

/-- Quantum / knowing formal fiber root (structure witness — not meso acting). -/
def partialConservationQuantumKnowingFiber : String :=
  "umst/umst-formal-double-slit"

/-- Meso / acting formal fiber root (cite only — not wired on knowing scaffold). -/
def partialConservationMesoActingFiber : String :=
  "umst/umst-formal"

theorem partial_conservation_quantum_knowing_fiber_pinned :
    partialConservationQuantumKnowingFiber =
      "umst/umst-formal-double-slit" := rfl

/-- Cited Rust interact-partiality authority (views only — lattice is structural here). -/
def partialConservationCitedModule : String :=
  "umst/umst-chem/src/interact_partiality.rs"

/-- Partial lattice is structure — not 118² GREEN periodic enumeration. -/
def partialConservationNot118GreenTable : Bool := true

theorem partial_conservation_not_118_green_table :
    partialConservationNot118GreenTable = true := rfl

/-- Second-law + conservation framing — cites meso SSOT, not wired on knowing scaffold. -/
def partialConservationSecondLawFramed : Bool := true

theorem partial_conservation_second_law_framed :
    partialConservationSecondLawFramed = true := rfl

/-- TYPE-05 claim partial Interact is **not** claimed Proved on the knowing scaffold. -/
def type05PartialProved : Bool := false

theorem type05_partial_not_proved : type05PartialProved = false := rfl

/-- Production wiring is **not** claimed on the knowing scaffold. -/
def partialConservationProductionWired : Bool := false

theorem partial_conservation_production_not_wired :
    partialConservationProductionWired = false := rfl

/-- Cell id for the Lean TYPE-05 partial Interact conservation knowing-fiber. -/
def partialConservationCellId : String :=
  "CHEM-FORMAL-Q-LEAN-PARTIAL-CONSERVATION"

/-- Non-claim fence — partial Interact admissible forbidden; conservation; TYPE-05 Unwired. -/
def partialConservationNonClaim : String :=
  "CHEM-FORMAL-Q-LEAN-PARTIAL-CONSERVATION TYPE-05 partial Interact conservation Unwired Assumed Proved Surrogate admissible forbidden pairs refuse total Interact claim refuse type05PartialProved false Unwired OK partial not total not TYPE-05 Proved not physics GREEN; not 118² GREEN DFT"

/-- Physics GREEN is unauthorized on the knowing TYPE-05 partial conservation scaffold. -/
def partialConservationPhysicsGreenAuthorized : Prop := False

theorem partial_conservation_physics_green_false :
    ¬ partialConservationPhysicsGreenAuthorized := id

theorem partial_conservation_modality_unwired :
    partialConservationModalityCurrent = .unwired := rfl

theorem partial_conservation_honest_bundle :
    type05PartialProved = false ∧
    partialConservationProductionWired = false ∧
    partialConservationNot118GreenTable = true ∧
    partialConservationSecondLawFramed = true ∧
    evaluatePartialConservation .unwired interactAttemptCaO false false = .unwiredOk ∧
    evaluatePartialConservation .proved interactAttemptCaO false false = .admissibleOk ∧
    evaluatePartialConservation .proved interactAttemptSelfHH false false = .forbiddenRefuse ∧
    evaluatePartialConservation .proved interactAttemptHSiBlocking false false = .forbiddenRefuse ∧
    evaluatePartialConservation .unwired interactAttemptCaO true false = .totalClaimRefuse ∧
    evaluatePartialConservation .unwired interactAttemptCaO false true = .greenInventRefuse ∧
    partialInteractAdmissible interactAttemptCaO false false = true ∧
    partialInteractAdmissible interactAttemptSelfHH false false = false :=
  ⟨rfl, rfl, partial_conservation_not_118_green_table, partial_conservation_second_law_framed,
    unwired_partial_ok, proved_admissible_ca_o_ok, proved_self_hh_forbidden,
    proved_h_si_blocking_forbidden, total_claim_refuse, green_invent_refuse,
    partial_interact_admissible_ca_o, partial_interact_not_admissible_self_hh⟩

end UMST.Chem
