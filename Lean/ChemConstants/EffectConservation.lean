-- SPDX-FileCopyrightText: 2026 Santosh Prabhu Shenbagamoorthy and Santhosh Shyamsundar
-- SPDX-License-Identifier: MIT

import ElementElectronic

/-!
# EffectConservation — knowing-fiber TYPE-04 dissipative effect conservation (Q lattice)

North-star TYPE-04 claim **effect** lattice on the quantum / knowing formal fiber —
dissipative Refine effect types. Pairs `umst-chem` scaffold
`CHEM-L0-TYPE-04` / `CHEM-INT-PROVE-TYPE-04-EFFECT` **conservation** posture.

- `EffectConservationModality` — Unwired / Assumed / Proved / Surrogate (not 118² GREEN table).
- `RefineDirection` — Forward Refine requires positive ChemStamp / Landauer witness.
- `ChemStampWitness` — scaffold dissipation ledger (microjoules, knowing fiber).
- `evaluateEffectConservation` — Unwired OK; forward Refine without witness refuse (free purification);
  reverse contaminate typed; GREEN invent refuse.
- Second-law + **conservation** framing cites meso `UMST.Chem.Conservation` / `LandauerLaw.physicalSecondLaw` — not imported.
- No meso / acting theorems. No new physics `axiom`.
- `physics_green` stays false. Does **not** claim TYPE-04 Proved or physics GREEN.
-/

namespace UMST.Chem

/-- Design modality for TYPE-04 claim effect conservation (lattice SSOT). -/
inductive EffectConservationModality where
  | unwired | assumed | proved | surrogate
  deriving DecidableEq, Repr

def effectConservationModalityCurrent : EffectConservationModality := .unwired

/-- Refine morphism direction under the second-law + conservation axiom. -/
inductive RefineDirection where
  | forwardRefine | reverseContaminate
  deriving DecidableEq, Repr

def refineDirectionString : RefineDirection → String
  | .forwardRefine => "forward_refine"
  | .reverseContaminate => "reverse_contaminate"

theorem refine_direction_forward_str :
    refineDirectionString .forwardRefine = "forward_refine" := rfl

theorem refine_direction_reverse_str :
    refineDirectionString .reverseContaminate = "reverse_contaminate" := rfl

/-- Whether forward Refine requires a positive dissipation witness. -/
def forwardRefineRequiresWitness (d : RefineDirection) : Bool :=
  match d with | .forwardRefine => true | .reverseContaminate => false

theorem forward_refine_requires_witness :
    forwardRefineRequiresWitness .forwardRefine = true := rfl

theorem reverse_contaminate_does_not_require_witness :
    forwardRefineRequiresWitness .reverseContaminate = false := rfl

/-- Scaffold ChemStamp / Landauer dissipation witness (knowing scaffold). -/
structure ChemStampWitness where
  dissipationMicrojoules : Nat
  deriving DecidableEq, Repr

/-- Zero dissipation — forward Refine must refuse (no free purification). -/
def chemStampWitnessZero : ChemStampWitness :=
  { dissipationMicrojoules := 0 }

/-- Scaffold positive dissipation for typed forward Refine. -/
def chemStampWitnessPositive : ChemStampWitness :=
  { dissipationMicrojoules := 1 }

/-- Whether witness carries positive dissipation. -/
def chemStampWitnessIsPositive (w : ChemStampWitness) : Bool :=
  decide (w.dissipationMicrojoules > 0)

theorem chem_stamp_witness_zero_not_positive :
    chemStampWitnessIsPositive chemStampWitnessZero = false := rfl

theorem chem_stamp_witness_positive_ok :
    chemStampWitnessIsPositive chemStampWitnessPositive = true := rfl

/-- Verdict of a Refine effect-type close attempt (fail-closed). -/
inductive RefineEffectVerdict where
  | unwiredOk
  | forwardDissipativeOk
  | freePurificationRefuse
  | reverseContaminateOk
  | greenInventRefuse
  deriving DecidableEq, Repr

/-- Evaluate Refine effect typing against the TYPE-04 effect conservation bar. -/
def evaluateEffectConservation
    (modality : EffectConservationModality)
    (direction : RefineDirection)
    (witness : ChemStampWitness)
    (claimPhysicsGreen : Bool) : RefineEffectVerdict :=
  if claimPhysicsGreen then
    .greenInventRefuse
  else
    match modality with
    | .unwired | .assumed | .surrogate => .unwiredOk
    | .proved =>
      match direction with
      | .reverseContaminate => .reverseContaminateOk
      | .forwardRefine =>
        if witness.dissipationMicrojoules > 0 then .forwardDissipativeOk
        else .freePurificationRefuse

/-- Whether forward Refine is authorized for this witness (⇔ positive, never GREEN). -/
def forwardRefineAuthorized (witness : ChemStampWitness) (claimPhysicsGreen : Bool) : Bool :=
  decide (evaluateEffectConservation .proved .forwardRefine witness claimPhysicsGreen =
    .forwardDissipativeOk)

/-- Whether a close attempt is admissible under TYPE-04. -/
def refineEffectVerdictOk (v : RefineEffectVerdict) : Bool :=
  match v with
  | .unwiredOk | .forwardDissipativeOk | .reverseContaminateOk => true
  | _ => false

theorem unwired_effect_ok :
    evaluateEffectConservation .unwired .forwardRefine chemStampWitnessZero false =
      .unwiredOk := rfl

theorem assumed_effect_ok :
    evaluateEffectConservation .assumed .forwardRefine chemStampWitnessZero false =
      .unwiredOk := rfl

theorem surrogate_effect_ok :
    evaluateEffectConservation .surrogate .reverseContaminate chemStampWitnessZero false =
      .unwiredOk := rfl

theorem forward_refine_zero_witness_refuse :
    evaluateEffectConservation .proved .forwardRefine chemStampWitnessZero false =
      .freePurificationRefuse := rfl

theorem forward_refine_positive_witness_ok :
    evaluateEffectConservation .proved .forwardRefine chemStampWitnessPositive false =
      .forwardDissipativeOk := rfl

theorem reverse_contaminate_typed_ok :
    evaluateEffectConservation .proved .reverseContaminate chemStampWitnessZero false =
      .reverseContaminateOk := rfl

theorem green_invent_refuse :
    evaluateEffectConservation .unwired .forwardRefine chemStampWitnessPositive true =
      .greenInventRefuse := rfl

theorem forward_refine_authorized_positive :
    forwardRefineAuthorized chemStampWitnessPositive false = true := rfl

theorem forward_refine_not_authorized_zero :
    forwardRefineAuthorized chemStampWitnessZero false = false := rfl

theorem unwired_verdict_ok :
    refineEffectVerdictOk
      (evaluateEffectConservation .unwired .forwardRefine chemStampWitnessZero false) =
      true := rfl

theorem forward_zero_verdict_not_ok :
    refineEffectVerdictOk
      (evaluateEffectConservation .proved .forwardRefine chemStampWitnessZero false) =
      false := rfl

/-- Quantum / knowing formal fiber root (structure witness — not meso acting). -/
def effectConservationQuantumKnowingFiber : String :=
  "umst/umst-formal-double-slit"

/-- Meso / acting formal fiber root (cite only — not wired on knowing scaffold). -/
def effectConservationMesoActingFiber : String :=
  "umst/umst-formal"

theorem effect_conservation_quantum_knowing_fiber_pinned :
    effectConservationQuantumKnowingFiber =
      "umst/umst-formal-double-slit" := rfl

/-- Cited Rust refine-effect authority (views only — lattice is structural here). -/
def effectConservationCitedModule : String :=
  "umst/umst-chem/src/refine_effect_types.rs"

/-- Effect lattice is structure — not 118² GREEN periodic enumeration. -/
def effectConservationNot118GreenTable : Bool := true

theorem effect_conservation_not_118_green_table :
    effectConservationNot118GreenTable = true := rfl

/-- Second-law + conservation framing — cites meso SSOT, not wired on knowing scaffold. -/
def effectConservationSecondLawFramed : Bool := true

theorem effect_conservation_second_law_framed :
    effectConservationSecondLawFramed = true := rfl

/-- TYPE-04 claim effect is **not** claimed Proved on the knowing scaffold. -/
def type04EffectProved : Bool := false

theorem type04_effect_not_proved : type04EffectProved = false := rfl

/-- Production wiring is **not** claimed on the knowing scaffold. -/
def effectConservationProductionWired : Bool := false

theorem effect_conservation_production_not_wired :
    effectConservationProductionWired = false := rfl

/-- Cell id for the Lean TYPE-04 effect conservation knowing-fiber. -/
def effectConservationCellId : String :=
  "CHEM-FORMAL-Q-LEAN-EFFECT-CONSERVATION"

/-- Non-claim fence — dissipative effect; ChemStamp witness; conservation; TYPE-04 Unwired. -/
def effectConservationNonClaim : String :=
  "CHEM-FORMAL-Q-LEAN-EFFECT-CONSERVATION TYPE-04 dissipative effect conservation Unwired Assumed Proved Surrogate forward Refine positive ChemStamp Landauer witness free purification refuse reverse contaminate typed type04EffectProved false Unwired OK forward Refine requires witness zero witness refuse not TYPE-04 Proved not physics GREEN; not 118² GREEN DFT"

/-- Physics GREEN is unauthorized on the knowing TYPE-04 effect conservation scaffold. -/
def effectConservationPhysicsGreenAuthorized : Prop := False

theorem effect_conservation_physics_green_false :
    ¬ effectConservationPhysicsGreenAuthorized := id

theorem effect_conservation_modality_unwired :
    effectConservationModalityCurrent = .unwired := rfl

theorem effect_conservation_honest_bundle :
    type04EffectProved = false ∧
    effectConservationProductionWired = false ∧
    effectConservationNot118GreenTable = true ∧
    effectConservationSecondLawFramed = true ∧
    forwardRefineRequiresWitness .forwardRefine = true ∧
    forwardRefineRequiresWitness .reverseContaminate = false ∧
    evaluateEffectConservation .unwired .forwardRefine chemStampWitnessZero false = .unwiredOk ∧
    evaluateEffectConservation .proved .forwardRefine chemStampWitnessZero false =
      .freePurificationRefuse ∧
    evaluateEffectConservation .proved .forwardRefine chemStampWitnessPositive false =
      .forwardDissipativeOk ∧
    evaluateEffectConservation .proved .reverseContaminate chemStampWitnessZero false =
      .reverseContaminateOk ∧
    evaluateEffectConservation .unwired .forwardRefine chemStampWitnessPositive true =
      .greenInventRefuse ∧
    forwardRefineAuthorized chemStampWitnessPositive false = true ∧
    forwardRefineAuthorized chemStampWitnessZero false = false :=
  ⟨rfl, rfl, effect_conservation_not_118_green_table, effect_conservation_second_law_framed,
    forward_refine_requires_witness, reverse_contaminate_does_not_require_witness,
    unwired_effect_ok, forward_refine_zero_witness_refuse, forward_refine_positive_witness_ok,
    reverse_contaminate_typed_ok, green_invent_refuse, forward_refine_authorized_positive,
    forward_refine_not_authorized_zero⟩

end UMST.Chem
