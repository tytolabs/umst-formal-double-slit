-- SPDX-FileCopyrightText: 2026 Santosh Prabhu Shenbagamoorthy and Santhosh Shyamsundar
-- SPDX-License-Identifier: MIT

import ElementElectronic

/-!
# PullbackConservation — knowing-fiber CAT-02 pullback/pushout conservation (Q lattice)

Pullback / pushout diagram algebra on `PullbackStep` — shared-substructure identity, leg nodes,
binary pullback / pushout cones; universal properties **not** Proved. Pairs `umst-chem` scaffold
`CHEM-L0-CAT-02` / `CHEM-INT-PROVE-CAT-02-PULLBACK` conservation posture.

- `PullbackStep` — `identity` / `leg` / `pullback` / `pushout` (not list-backed, not allocate antichain).
- `pullbackStepIdentity` / `pullbackCone` / `pushoutCocone` — structure witnesses; laws Unwired not Proved.
- Shared-substructure identity conserved on the knowing scaffold (structure only).
- No meso / acting theorems. No new physics `axiom`.
- `physics_green` stays false. Does **not** claim CAT-02 Proved or physics GREEN.
-/

namespace UMST.Chem

/-- Design modality for CAT-02 pullback/pushout conservation claims (TYPE-03 preview). -/
inductive PullbackConservationModality where
  | unwired | assumed | proved | surrogate
  deriving DecidableEq, Repr

def pullbackConservationModalityCurrent : PullbackConservationModality := .unwired

/-- Named shared-substructure leg tags (bounded scaffold — not spatial cells). -/
inductive SharedSubstructureTag where
  | substrateScaffold | interfaceScaffold | limitScaffold
  deriving DecidableEq, Repr

def sharedSubstructureTagString : SharedSubstructureTag → String
  | .substrateScaffold => "substrate_scaffold"
  | .interfaceScaffold => "interface_scaffold"
  | .limitScaffold => "limit_scaffold"

theorem shared_substructure_tag_substrate :
    sharedSubstructureTagString .substrateScaffold = "substrate_scaffold" := rfl

theorem shared_substructure_tag_interface :
    sharedSubstructureTagString .interfaceScaffold = "interface_scaffold" := rfl

theorem shared_substructure_tag_limit :
    sharedSubstructureTagString .limitScaffold = "limit_scaffold" := rfl

/-- Cardinality of named shared-substructure leg tags. -/
def sharedSubstructureLegCardinality : Nat := 3

theorem shared_substructure_leg_cardinality_three :
    sharedSubstructureLegCardinality = 3 := rfl

/-- Shared-substructure slot posture — pullback leg, not spatial write_set cell. -/
inductive SharedSubstructureSlot where
  | unwired | absent | present
  deriving DecidableEq, Repr

def sharedSubstructureSlotPresent (s : SharedSubstructureSlot) : Bool :=
  match s with | .present => true | _ => false

/-- Algebraic PullbackStep — identity, leg morphisms, binary pullback / pushout cones. -/
inductive PullbackStep where
  | identity : PullbackStep
  | leg (tag : SharedSubstructureTag) : PullbackStep
  | pullback (left right : PullbackStep) : PullbackStep
  | pushout (left right : PullbackStep) : PullbackStep
  deriving DecidableEq, Repr

/-- Shared-substructure identity morphism `id` — inert / vacuum limit on the knowing scaffold. -/
def pullbackStepIdentity : PullbackStep := .identity

/-- Pullback cone — limit over a span (binary pullback node). -/
def pullbackCone (left right : PullbackStep) : PullbackStep := .pullback left right

/-- Pushout cocone — colimit over a cospan (binary pushout node). -/
def pushoutCocone (left right : PullbackStep) : PullbackStep := .pushout left right

def pullbackStepIsIdentity (s : PullbackStep) : Bool :=
  match s with | .identity => true | _ => false

def pullbackStepIsPullback (s : PullbackStep) : Bool :=
  match s with | .pullback _ _ => true | _ => false

def pullbackStepIsPushout (s : PullbackStep) : Bool :=
  match s with | .pushout _ _ => true | _ => false

def pullbackStepIsLeg (s : PullbackStep) : Bool :=
  match s with | .leg _ => true | _ => false

/-- Sample leg for unit-law scaffold witnesses. -/
def pullbackSampleLeg : PullbackStep := .leg .substrateScaffold

theorem pullback_sample_leg_is_leg : pullbackStepIsLeg pullbackSampleLeg = true := rfl

theorem pullback_step_identity_is_identity :
    pullbackStepIsIdentity pullbackStepIdentity = true := rfl

/-- Left identity scaffold — `id` paired in pullback with identity left child (structure only). -/
def pullbackLeftIdentityScaffold (a : PullbackStep) : Bool :=
  match pullbackCone pullbackStepIdentity a with
  | .pullback left _ => pullbackStepIsIdentity left
  | _ => false

/-- Right identity scaffold — `id` paired in pullback with identity right child (structure only). -/
def pullbackRightIdentityScaffold (a : PullbackStep) : Bool :=
  match pullbackCone a pullbackStepIdentity with
  | .pullback _ right => pullbackStepIsIdentity right
  | _ => false

theorem pullback_left_identity_scaffold_sample :
    pullbackLeftIdentityScaffold pullbackSampleLeg = true := rfl

theorem pullback_right_identity_scaffold_sample :
    pullbackRightIdentityScaffold pullbackSampleLeg = true := rfl

/-- Shared-substructure identity conserved — `id` pullback `id` remains identity legs (structure witness). -/
def sharedSubstructureIdentityConserved : Bool :=
  match pullbackCone pullbackStepIdentity pullbackStepIdentity with
  | .pullback left right =>
      pullbackStepIsIdentity left && pullbackStepIsIdentity right
  | _ => false

theorem shared_substructure_identity_conserved :
    sharedSubstructureIdentityConserved = true := rfl

/-- Left-associated pullback bracketing `(a ↓ b) ↓ c` — associator witness (Unwired). -/
def pullbackAssociatorLeft (a b c : PullbackStep) : PullbackStep :=
  pullbackCone (pullbackCone a b) c

/-- Right-associated pullback bracketing `a ↓ (b ↓ c)` — associator witness (Unwired). -/
def pullbackAssociatorRight (a b c : PullbackStep) : PullbackStep :=
  pullbackCone a (pullbackCone b c)

/-- Pullback associativity scaffold — both bracketings are pullback trees, distinct (laws not Proved). -/
def pullbackAssociativeScaffold (a b c : PullbackStep) : Bool :=
  let la := pullbackAssociatorLeft a b c
  let ra := pullbackAssociatorRight a b c
  pullbackStepIsPullback la && pullbackStepIsPullback ra && decide (la ≠ ra)

theorem pullback_associative_scaffold_triple :
    pullbackAssociativeScaffold
      (.leg .substrateScaffold)
      (.leg .interfaceScaffold)
      (.leg .limitScaffold) = true := rfl

/-- Whether a named shared-substructure tag appears anywhere in a PullbackStep. -/
def sharedSubstructureTagPresent (s : PullbackStep) (tag : SharedSubstructureTag) : Bool :=
  match s with
  | .identity => false
  | .leg t' => decide (t' == tag)
  | .pullback left right =>
      sharedSubstructureTagPresent left tag || sharedSubstructureTagPresent right tag
  | .pushout left right =>
      sharedSubstructureTagPresent left tag || sharedSubstructureTagPresent right tag

/-- Count of distinct present shared-substructure tags in a PullbackStep. -/
def sharedSubstructureConcurrentTagCount (s : PullbackStep) : Nat :=
  (if sharedSubstructureTagPresent s .substrateScaffold then 1 else 0) +
  (if sharedSubstructureTagPresent s .interfaceScaffold then 1 else 0) +
  (if sharedSubstructureTagPresent s .limitScaffold then 1 else 0)

def pullbackStepIsConcurrentSpan (s : PullbackStep) : Bool :=
  decide (sharedSubstructureConcurrentTagCount s ≥ 2)

/-- Triple-leg pullback witness — three legs in pullback cone, not spatial antichain. -/
def pullbackTripleCone : PullbackStep :=
  pullbackCone
    (pullbackCone (.leg .substrateScaffold) (.leg .interfaceScaffold))
    (.leg .limitScaffold)

theorem pullback_triple_cone_is_pullback :
    pullbackStepIsPullback pullbackTripleCone = true := rfl

theorem pullback_triple_concurrent_tag_count :
    sharedSubstructureConcurrentTagCount pullbackTripleCone = 3 := rfl

theorem pullback_triple_is_concurrent_span :
    pullbackStepIsConcurrentSpan pullbackTripleCone = true := rfl

/-- Dual triple-leg pushout witness — three legs in pushout cocone, not spatial antichain. -/
def pushoutTripleCocone : PullbackStep :=
  pushoutCocone
    (pushoutCocone (.leg .substrateScaffold) (.leg .interfaceScaffold))
    (.leg .limitScaffold)

theorem pushout_triple_cocone_is_pushout :
    pullbackStepIsPushout pushoutTripleCocone = true := rfl

theorem pushout_triple_concurrent_tag_count :
    sharedSubstructureConcurrentTagCount pushoutTripleCocone = 3 := rfl

/-- Pullback cone is shared-substructure span — not spatial write_set antichain growth. -/
def pullbackConeNotAntichain : Bool :=
  pullbackStepIsConcurrentSpan pullbackTripleCone &&
    decide (sharedSubstructureConcurrentTagCount pullbackTripleCone = sharedSubstructureLegCardinality)

theorem pullback_cone_not_antichain : pullbackConeNotAntichain = true := rfl

/-- Pushout cocone is distinct from pullback cone (dual constructors, not XOR enum). -/
def pullbackPushoutDistinctScaffold : Bool :=
  pullbackStepIsPullback pullbackTripleCone &&
    pullbackStepIsPushout pushoutTripleCocone &&
    decide (pullbackTripleCone ≠ pushoutTripleCocone)

theorem pullback_pushout_distinct_scaffold :
    pullbackPushoutDistinctScaffold = true := rfl

/-- Diagram algebra is not list-backed (binary pullback / pushout tree only). -/
def pullbackAlgebraNotListBacked : Bool := true

theorem pullback_algebra_not_list_backed : pullbackAlgebraNotListBacked = true := rfl

/-- Universal properties are **not** claimed Proved on the knowing scaffold. -/
def universalPropertiesProved : Bool := false

theorem universal_properties_not_proved : universalPropertiesProved = false := rfl

/-- CAT-02 pullback category is **not** claimed Proved on the knowing scaffold. -/
def cat02PullbackProved : Bool := false

theorem cat02_pullback_not_proved : cat02PullbackProved = false := rfl

/-- Cell id for the Lean CAT-02 pullback/pushout conservation knowing-fiber. -/
def pullbackConservationCellId : String :=
  "CHEM-FORMAL-Q-LEAN-PULLBACK-CONSERVATION"

/-- Non-claim fence — PullbackStep identity pullback pushout; shared-substructure identity conserved; laws Unwired. -/
def pullbackConservationNonClaim : String :=
  "CHEM-FORMAL-Q-LEAN-PULLBACK-CONSERVATION PullbackStep identity pullback pushout shared-substructure identity conserved universalPropertiesProved false Unwired not CAT-02 Proved not physics GREEN; not GREEN DFT"

/-- Physics GREEN is unauthorized on the knowing CAT-02 pullback scaffold. -/
def pullbackConservationPhysicsGreenAuthorized : Prop := False

theorem pullback_conservation_physics_green_false :
    ¬ pullbackConservationPhysicsGreenAuthorized := id

theorem pullback_conservation_modality_unwired :
    pullbackConservationModalityCurrent = .unwired := rfl

theorem pullback_conservation_honest_bundle :
    universalPropertiesProved = false ∧
    cat02PullbackProved = false ∧
    pullbackConeNotAntichain = true ∧
    sharedSubstructureIdentityConserved = true ∧
    pullbackPushoutDistinctScaffold = true ∧
    pullbackLeftIdentityScaffold pullbackSampleLeg = true ∧
    pullbackRightIdentityScaffold pullbackSampleLeg = true ∧
    pullbackAssociativeScaffold
      (.leg .substrateScaffold)
      (.leg .interfaceScaffold)
      (.leg .limitScaffold) = true :=
  ⟨rfl, rfl, pullback_cone_not_antichain, shared_substructure_identity_conserved,
    pullback_pushout_distinct_scaffold, pullback_left_identity_scaffold_sample,
    pullback_right_identity_scaffold_sample, pullback_associative_scaffold_triple⟩

end UMST.Chem
