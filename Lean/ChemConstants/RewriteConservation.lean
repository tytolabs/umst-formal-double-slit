-- SPDX-FileCopyrightText: 2026 Santosh Prabhu Shenbagamoorthy and Santhosh Shyamsundar
-- SPDX-License-Identifier: MIT

import ElementElectronic

/-!
# RewriteConservation — knowing-fiber FP-03 thermo-preserving rewrite conservation (Q lattice)

North-star FP-03 claim **rewrite** lattice on the quantum / knowing formal fiber —
thermo-preserving morphism **rewrite** steps and fusion identity for §2 pattern taxonomy.
Pairs `umst-chem` scaffold `CHEM-L0-FP-03` / `CHEM-INT-PROVE-FP-03-REWRITE` **conservation** posture.

- `RewriteConservationModality` — Unwired / Assumed / Proved / Surrogate (not 118² GREEN table).
- `thermoPreservingRewriteStep` / `fusionRewrite` — thermo-preserving fusion identity conserved.
- `evaluateRewriteConservation` — Unwired OK; Proved rewrite-identity scaffold OK; non-preserving step fail-closed; GREEN invent refuse.
- Second-law + **conservation** framing cites meso `UMST.Chem.Conservation` / `LandauerLaw.physicalSecondLaw` — not imported.
- No meso / acting theorems. No new physics `axiom`.
- `physics_green` stays false. Does **not** claim FP-03 Proved or physics GREEN.
-/

namespace UMST.Chem

/-- Design modality for FP-03 claim rewrite conservation (lattice SSOT). -/
inductive RewriteConservationModality where
  | unwired | assumed | proved | surrogate
  deriving DecidableEq, Repr

def rewriteConservationModalityCurrent : RewriteConservationModality := .unwired

/-- Scaffold thermodynamic ledger for **rewrite** steps (knowing fiber). -/
structure ThermoRewriteState where
  chemStamp : Nat
  landauerWitness : Nat
  deriving DecidableEq, Repr

/-- Zero thermo baseline for **rewrite** identity tests. -/
def thermoRewriteZero : ThermoRewriteState :=
  { chemStamp := 0, landauerWitness := 0 }

/-- Sample positive thermo state for preserving **rewrite** tests. -/
def thermoRewritePositive : ThermoRewriteState :=
  { chemStamp := 1, landauerWitness := 1 }

/-- Kind of **rewrite** step — preserving vs non-preserving (fail-closed). -/
inductive RewriteStepKind where
  | thermoPreserving | nonPreserving
  deriving DecidableEq, Repr

def rewriteStepKindString : RewriteStepKind → String
  | .thermoPreserving => "thermo_preserving"
  | .nonPreserving => "non_preserving"

theorem rewrite_step_preserving_str :
    rewriteStepKindString .thermoPreserving = "thermo_preserving" := rfl

theorem rewrite_step_non_preserving_str :
    rewriteStepKindString .nonPreserving = "non_preserving" := rfl

/-- Thermo-preserving **rewrite** step — never decreases Landauer witness; stamp monotone. -/
def thermoPreservingRewriteStep (state : ThermoRewriteState) (delta : Nat) : ThermoRewriteState :=
  { chemStamp := state.chemStamp + delta,
    landauerWitness := state.landauerWitness + delta }

/-- Non-preserving **rewrite** step — decreases witness (forbidden on knowing scaffold). -/
def nonPreservingRewriteStep (state : ThermoRewriteState) (delta : Nat) : ThermoRewriteState :=
  if state.landauerWitness ≥ delta then
    { chemStamp := state.chemStamp, landauerWitness := state.landauerWitness - delta }
  else
    { chemStamp := state.chemStamp, landauerWitness := 0 }

/-- Whether a **rewrite** step kind is thermo-preserving. -/
def rewriteStepIsPreserving (k : RewriteStepKind) : Bool :=
  match k with | .thermoPreserving => true | .nonPreserving => false

theorem preserving_step_kind_ok :
    rewriteStepIsPreserving .thermoPreserving = true := rfl

theorem non_preserving_step_kind_refuse :
    rewriteStepIsPreserving .nonPreserving = false := rfl

/-- Apply a **rewrite** step by kind (preserving vs non-preserving). -/
def applyRewriteStep (k : RewriteStepKind) (state : ThermoRewriteState) (delta : Nat) :
    ThermoRewriteState :=
  match k with
  | .thermoPreserving => thermoPreservingRewriteStep state delta
  | .nonPreserving => nonPreservingRewriteStep state delta

theorem preserving_rewrite_increases_witness :
    (thermoPreservingRewriteStep thermoRewritePositive 1).landauerWitness = 2 := rfl

theorem non_preserving_rewrite_decreases_witness :
    (nonPreservingRewriteStep thermoRewritePositive 1).landauerWitness = 0 := rfl

/-- Thermo-preserving fusion of two **rewrite** states — identity conserved (additive). -/
def fusionRewrite (a b : ThermoRewriteState) : ThermoRewriteState :=
  { chemStamp := a.chemStamp + b.chemStamp,
    landauerWitness := a.landauerWitness + b.landauerWitness }

theorem fusion_rewrite_commutative_stamp :
    (fusionRewrite thermoRewritePositive thermoRewriteZero).chemStamp =
      (fusionRewrite thermoRewriteZero thermoRewritePositive).chemStamp := rfl

theorem fusion_rewrite_commutative_witness :
    (fusionRewrite thermoRewritePositive thermoRewriteZero).landauerWitness =
      (fusionRewrite thermoRewriteZero thermoRewritePositive).landauerWitness := rfl

theorem fusion_rewrite_associative_stamp :
    (fusionRewrite (fusionRewrite thermoRewritePositive thermoRewritePositive) thermoRewriteZero).chemStamp =
      (fusionRewrite thermoRewritePositive (fusionRewrite thermoRewritePositive thermoRewriteZero)).chemStamp := rfl

theorem fusion_rewrite_zero_identity_stamp :
    (fusionRewrite thermoRewriteZero thermoRewritePositive).chemStamp =
      thermoRewritePositive.chemStamp := rfl

theorem fusion_rewrite_zero_identity_witness :
    (fusionRewrite thermoRewriteZero thermoRewritePositive).landauerWitness =
      thermoRewritePositive.landauerWitness := rfl

/-- Verdict of a single **rewrite** step close attempt (fail-closed). -/
inductive RewriteStepVerdict where
  | preservingOk
  | nonPreservingRefuse
  deriving DecidableEq, Repr

/-- Evaluate a **rewrite** step against the thermo-preserving bar. -/
def evaluateRewriteStep (k : RewriteStepKind) : RewriteStepVerdict :=
  match k with
  | .thermoPreserving => .preservingOk
  | .nonPreserving => .nonPreservingRefuse

theorem preserving_step_verdict_ok :
    evaluateRewriteStep .thermoPreserving = .preservingOk := rfl

theorem non_preserving_step_verdict_refuse :
    evaluateRewriteStep .nonPreserving = .nonPreservingRefuse := rfl

/-- Verdict of a rewrite conservation close attempt (fail-closed). -/
inductive RewriteConservationVerdict where
  | unwiredOk
  | rewriteIdentityOk
  | nonPreservingRefuse
  | greenInventRefuse
  deriving DecidableEq, Repr

/-- Evaluate **rewrite** conservation against the FP-03 bar. -/
def evaluateRewriteConservation
    (modality : RewriteConservationModality)
    (stepKind : RewriteStepKind)
    (claimPhysicsGreen : Bool) : RewriteConservationVerdict :=
  if claimPhysicsGreen then
    .greenInventRefuse
  else if stepKind = .nonPreserving then
    .nonPreservingRefuse
  else
    match modality with
    | .unwired | .assumed | .surrogate => .unwiredOk
    | .proved => .rewriteIdentityOk

/-- Whether thermo-preserving fusion identity is conserved on pinned states. -/
def fusionIdentityConserved : Bool :=
  decide (fusionRewrite thermoRewriteZero thermoRewritePositive =
    thermoRewritePositive ∧
    fusionRewrite thermoRewritePositive thermoRewriteZero =
      fusionRewrite thermoRewriteZero thermoRewritePositive ∧
    (fusionRewrite thermoRewritePositive thermoRewritePositive).landauerWitness = 2 ∧
    (thermoPreservingRewriteStep thermoRewritePositive 1).landauerWitness = 2)

/-- Whether non-preserving **rewrite** step is refused (fail-closed). -/
def nonPreservingStepRefused : Bool :=
  decide (evaluateRewriteStep .nonPreserving = .nonPreservingRefuse ∧
    evaluateRewriteConservation .unwired .nonPreserving false = .nonPreservingRefuse ∧
    evaluateRewriteConservation .proved .nonPreserving false = .nonPreservingRefuse)

/-- Whether preserving **rewrite** step passes under Unwired modality. -/
def preservingStepUnwiredOk : Bool :=
  decide (evaluateRewriteConservation .unwired .thermoPreserving false = .unwiredOk)

/-- Whether preserving **rewrite** step passes under Proved modality. -/
def preservingStepProvedOk : Bool :=
  decide (evaluateRewriteConservation .proved .thermoPreserving false = .rewriteIdentityOk)

/-- Whether a close attempt is admissible under FP-03 **rewrite** conservation. -/
def rewriteConservationVerdictOk (v : RewriteConservationVerdict) : Bool :=
  match v with
  | .unwiredOk | .rewriteIdentityOk => true
  | _ => false

theorem unwired_rewrite_ok :
    evaluateRewriteConservation .unwired .thermoPreserving false = .unwiredOk := rfl

theorem assumed_rewrite_ok :
    evaluateRewriteConservation .assumed .thermoPreserving false = .unwiredOk := rfl

theorem surrogate_rewrite_ok :
    evaluateRewriteConservation .surrogate .thermoPreserving false = .unwiredOk := rfl

theorem proved_rewrite_identity_ok :
    evaluateRewriteConservation .proved .thermoPreserving false = .rewriteIdentityOk := rfl

theorem non_preserving_unwired_refuse :
    evaluateRewriteConservation .unwired .nonPreserving false = .nonPreservingRefuse := rfl

theorem non_preserving_proved_refuse :
    evaluateRewriteConservation .proved .nonPreserving false = .nonPreservingRefuse := rfl

theorem green_invent_refuse :
    evaluateRewriteConservation .unwired .thermoPreserving true = .greenInventRefuse := rfl

theorem fusion_identity_conserved :
    fusionIdentityConserved = true := rfl

theorem non_preserving_step_refused :
    nonPreservingStepRefused = true := rfl

theorem preserving_step_unwired_ok :
    preservingStepUnwiredOk = true := rfl

theorem preserving_step_proved_ok :
    preservingStepProvedOk = true := rfl

theorem unwired_verdict_ok :
    rewriteConservationVerdictOk (evaluateRewriteConservation .unwired .thermoPreserving false) = true := rfl

theorem non_preserving_verdict_not_ok :
    rewriteConservationVerdictOk (evaluateRewriteConservation .unwired .nonPreserving false) = false := rfl

theorem green_invent_verdict_not_ok :
    rewriteConservationVerdictOk (evaluateRewriteConservation .unwired .thermoPreserving true) = false := rfl

/-- Quantum / knowing formal fiber root (structure witness — not meso acting). -/
def rewriteConservationQuantumKnowingFiber : String :=
  "umst/umst-formal-double-slit"

/-- Meso / acting formal fiber root (cite only — not wired on knowing scaffold). -/
def rewriteConservationMesoActingFiber : String :=
  "umst/umst-formal"

theorem rewrite_conservation_quantum_knowing_fiber_pinned :
    rewriteConservationQuantumKnowingFiber =
      "umst/umst-formal-double-slit" := rfl

/-- Cited Rust pattern-**rewrite** authority (views only — lattice is structural here). -/
def rewriteConservationCitedModule : String :=
  "umst/umst-chem/src/pattern_rewrites.rs"

/-- **Rewrite** lattice is structure — not 118² GREEN periodic enumeration. -/
def rewriteConservationNot118GreenTable : Bool := true

theorem rewrite_conservation_not_118_green_table :
    rewriteConservationNot118GreenTable = true := rfl

/-- Second-law + **conservation** framing — cites meso SSOT, not wired on knowing scaffold. -/
def rewriteConservationSecondLawFramed : Bool := true

theorem rewrite_conservation_second_law_framed :
    rewriteConservationSecondLawFramed = true := rfl

/-- FP-03 claim **rewrite** is **not** claimed Proved on the knowing scaffold. -/
def fp03RewriteProved : Bool := false

theorem fp03_rewrite_not_proved : fp03RewriteProved = false := rfl

/-- Production wiring is **not** claimed on the knowing scaffold. -/
def rewriteConservationProductionWired : Bool := false

theorem rewrite_conservation_production_not_wired :
    rewriteConservationProductionWired = false := rfl

/-- Cell id for the Lean FP-03 **rewrite** conservation knowing-fiber. -/
def rewriteConservationCellId : String :=
  "CHEM-FORMAL-Q-LEAN-REWRITE-CONSERVATION"

/-- Non-claim fence — thermo-preserving **rewrite** fusion identity; non-preserving fail-closed; **conservation**; FP-03 Unwired. -/
def rewriteConservationNonClaim : String :=
  "CHEM-FORMAL-Q-LEAN-REWRITE-CONSERVATION FP-03 thermo-preserving rewrite fusion identity conserved non-preserving step refuse fp03RewriteProved false Unwired OK not FP-03 Proved not physics GREEN; not 118² GREEN DFT"

/-- Physics GREEN is unauthorized on the knowing FP-03 **rewrite** conservation scaffold. -/
def rewriteConservationPhysicsGreenAuthorized : Prop := False

theorem rewrite_conservation_physics_green_false :
    ¬ rewriteConservationPhysicsGreenAuthorized := id

theorem rewrite_conservation_modality_unwired :
    rewriteConservationModalityCurrent = .unwired := rfl

theorem rewrite_conservation_honest_bundle :
    fp03RewriteProved = false ∧
    rewriteConservationProductionWired = false ∧
    rewriteConservationNot118GreenTable = true ∧
    rewriteConservationSecondLawFramed = true ∧
    evaluateRewriteConservation .unwired .thermoPreserving false = .unwiredOk ∧
    evaluateRewriteConservation .proved .thermoPreserving false = .rewriteIdentityOk ∧
    evaluateRewriteConservation .unwired .nonPreserving false = .nonPreservingRefuse ∧
    evaluateRewriteConservation .unwired .thermoPreserving true = .greenInventRefuse ∧
    fusionIdentityConserved = true ∧
    nonPreservingStepRefused = true ∧
    preservingStepUnwiredOk = true ∧
    preservingStepProvedOk = true ∧
    rewriteStepIsPreserving .thermoPreserving = true ∧
    rewriteStepIsPreserving .nonPreserving = false :=
  ⟨rfl, rfl, rewrite_conservation_not_118_green_table, rewrite_conservation_second_law_framed,
    unwired_rewrite_ok, proved_rewrite_identity_ok, non_preserving_unwired_refuse,
    green_invent_refuse, fusion_identity_conserved, non_preserving_step_refused,
    preserving_step_unwired_ok, preserving_step_proved_ok,
    preserving_step_kind_ok, non_preserving_step_kind_refuse⟩

end UMST.Chem
