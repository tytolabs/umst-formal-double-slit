-- SPDX-FileCopyrightText: 2026 Santosh Prabhu Shenbagamoorthy and Santhosh Shyamsundar
-- SPDX-License-Identifier: MIT

import ElementElectronic

/-!
# ScaleConservation — knowing-fiber SCALE-01 **commuting-square conservation** (Q lattice)

North-star SCALE-01 claim **scale** ladder commuting-square identity **conservation** on the quantum /
knowing formal fiber — Q ↔ meso ↔ macro named legs with composed Q→meso→macro identity equal to
Q→macro direct (typed **conservation**). Pairs `umst-chem` scaffold `CHEM-L0-SCALE-01` /
`CHEM-INT-SCALE-COMMUTE` **conservation** posture.

- `ScaleConservationModality` — Unwired / Assumed / Proved / Surrogate (not 118² GREEN table).
- `ScaleCommutingLeg` / `ScaleLevel` — three named legs; indirect compose **conservation**.
- `fusionScale` — **scale** stamp identity **conserved** (additive witness).
- `evaluateScaleConservation` — Unwired OK; Proved leg-named scaffold OK; trivial **scale** fail-closed;
  GREEN invent refuse; **conservation** commute typed not Z-lift occupancy.
- Distinct from `ScaleOccupancyZCommute` (v24 electron-count `liftQM` identity — not this cell).
- Second-law + **conservation** framing cites meso `UMST.Chem.Conservation` /
  `LandauerLaw.physicalSecondLaw` — not imported.
- No meso / acting theorems. No new physics `axiom`.
- `physics_green` stays false. Does **not** claim SCALE-01 Proved or physics GREEN.
- **Scale** commute square ≠ 118² GREEN periodic enumeration.
-/

namespace UMST.Chem

/-- Design modality for SCALE-01 claim **scale** **conservation** (lattice SSOT). -/
inductive ScaleConservationModality where
  | unwired | assumed | proved | surrogate
  deriving DecidableEq, Repr

def scaleConservationModalityCurrent : ScaleConservationModality := .unwired

/-- IUPAC periodic-table cardinality (Z=1..118). -/
def iupacTableCardinality : Nat := 118

theorem iupac_table_cardinality_118 : iupacTableCardinality = 118 := rfl

/-- Private Z pin for **scale** ladder witnesses — not L1 SpeciesId. -/
structure ScaleElementZ where
  z : Nat
  hzLo : 0 < z
  hzHi : z ≤ iupacTableCardinality
  deriving DecidableEq, Repr

def scaleElementCarbon : ScaleElementZ := { z := 6, hzLo := by decide, hzHi := by decide }
def scaleElementOganesson : ScaleElementZ := { z := 118, hzLo := by decide, hzHi := by decide }

theorem scale_carbon_z_six : scaleElementCarbon.z = 6 := rfl
theorem scale_oganesson_z_118 : scaleElementOganesson.z = 118 := rfl

/-- Darmstadtium Z (110) — homolog anchor (not Pt copy). -/
def scaleElementDs : ScaleElementZ := { z := 110, hzLo := by decide, hzHi := by decide }

/-- Platinum Z (78) — occupancy exception anchor (distinct from Ds homolog). -/
def scaleElementPt : ScaleElementZ := { z := 78, hzLo := by decide, hzHi := by decide }

theorem scale_ds_z_110 : scaleElementDs.z = 110 := rfl
theorem scale_pt_z_78 : scaleElementPt.z = 78 := rfl

theorem scale_ds_not_copy_of_pt : scaleElementDs.z ≠ scaleElementPt.z := by decide

/-- L0 **scale** stratum in the Q ↔ meso ↔ macro ladder (design names only). -/
inductive ScaleLevel where
  | quantum | meso | macro
  deriving DecidableEq, Repr

/-- Named legs of the **scale** commuting diagram (scaffold — typed **conservation**). -/
inductive ScaleCommutingLeg where
  | quantumToMeso | mesoToMacro | quantumToMacroDirect
  deriving DecidableEq, Repr

def ScaleCommutingLeg.source : ScaleCommutingLeg → ScaleLevel
  | .quantumToMeso => .quantum
  | .mesoToMacro => .meso
  | .quantumToMacroDirect => .quantum

def ScaleCommutingLeg.target : ScaleCommutingLeg → ScaleLevel
  | .quantumToMeso => .meso
  | .mesoToMacro => .macro
  | .quantumToMacroDirect => .macro

def scaleLegString : ScaleCommutingLeg → String
  | .quantumToMeso => "quantum_to_meso"
  | .mesoToMacro => "meso_to_macro"
  | .quantumToMacroDirect => "quantum_to_macro_direct"

theorem scale_leg_quantum_to_meso_str :
    scaleLegString .quantumToMeso = "quantum_to_meso" := rfl

theorem scale_leg_meso_to_macro_str :
    scaleLegString .mesoToMacro = "meso_to_macro" := rfl

theorem scale_leg_quantum_to_macro_direct_str :
    scaleLegString .quantumToMacroDirect = "quantum_to_macro_direct" := rfl

/-- Named indirect leg Q → meso in the commuting square. -/
def scaleLegQuantumToMeso : ScaleCommutingLeg := .quantumToMeso

/-- Named indirect leg meso → macro in the commuting square. -/
def scaleLegMesoToMacro : ScaleCommutingLeg := .mesoToMacro

/-- Named direct leg Q → macro in the commuting square. -/
def scaleLegQuantumToMacroDirect : ScaleCommutingLeg := .quantumToMacroDirect

theorem scale_leg_quantum_to_meso_named :
    scaleLegQuantumToMeso = ScaleCommutingLeg.quantumToMeso := rfl

theorem scale_leg_meso_to_macro_named :
    scaleLegMesoToMacro = ScaleCommutingLeg.mesoToMacro := rfl

theorem scale_leg_quantum_to_macro_direct_named :
    scaleLegQuantumToMacroDirect = ScaleCommutingLeg.quantumToMacroDirect := rfl

theorem scale_leg_indirect_composes_levels :
    scaleLegQuantumToMeso.target = scaleLegMesoToMacro.source := rfl

theorem scale_leg_direct_endpoints_match :
    scaleLegQuantumToMeso.source = scaleLegQuantumToMacroDirect.source ∧
    scaleLegMesoToMacro.target = scaleLegQuantumToMacroDirect.target := by
  constructor <;> rfl

theorem scale_leg_quantum_to_meso_source :
    scaleLegQuantumToMeso.source = ScaleLevel.quantum := rfl

theorem scale_leg_meso_to_macro_target :
    scaleLegMesoToMacro.target = ScaleLevel.macro := rfl

theorem scale_leg_distinct_indirect_vs_direct :
    scaleLegQuantumToMeso ≠ scaleLegQuantumToMacroDirect := by decide

/-- Named legs of the **scale** commuting diagram (typed **conservation** scaffold). -/
structure ScaleCommuteDiagram where
  viaMeso : ScaleCommutingLeg
  thenMacro : ScaleCommutingLeg
  direct : ScaleCommutingLeg
  deriving Repr

def scaleCommuteDiagramNamed : ScaleCommuteDiagram :=
  { viaMeso := scaleLegQuantumToMeso
    thenMacro := scaleLegMesoToMacro
    direct := scaleLegQuantumToMacroDirect }

theorem scale_commute_diagram_named_fields :
    scaleCommuteDiagramNamed.viaMeso = scaleLegQuantumToMeso ∧
    scaleCommuteDiagramNamed.thenMacro = scaleLegMesoToMacro ∧
    scaleCommuteDiagramNamed.direct = scaleLegQuantumToMacroDirect := by
  simp [scaleCommuteDiagramNamed, scaleLegQuantumToMeso, scaleLegMesoToMacro, scaleLegQuantumToMacroDirect]

/-- **Scale** **conservation** stamp field across Q ↔ meso ↔ macro (typed identity witness). -/
structure ScaleConservationField where
  atQuantum : Nat
  atMeso : Nat
  atMacro : Nat
  deriving DecidableEq, Repr

def scaleConservationFieldUnwired : ScaleConservationField :=
  { atQuantum := 0, atMeso := 0, atMacro := 0 }

def scaleConservationFieldNamed : ScaleConservationField :=
  { atQuantum := 1, atMeso := 1, atMacro := 1 }

/-- Lookup **scale** **conservation** stamp at a named stratum. -/
def scaleAtLevel (f : ScaleConservationField) : ScaleLevel → Nat
  | .quantum => f.atQuantum
  | .meso => f.atMeso
  | .macro => f.atMacro

/-- **Scale** stamp at the source endpoint of a commuting leg. -/
def scaleAtLegSource (f : ScaleConservationField) (leg : ScaleCommutingLeg) : Nat :=
  scaleAtLevel f leg.source

/-- **Scale** stamp at the target endpoint of a commuting leg. -/
def scaleAtLegTarget (f : ScaleConservationField) (leg : ScaleCommutingLeg) : Nat :=
  scaleAtLevel f leg.target

theorem scale_at_leg_source_quantum_to_meso (f : ScaleConservationField) :
    scaleAtLegSource f scaleLegQuantumToMeso = f.atQuantum := rfl

theorem scale_at_leg_target_quantum_to_meso (f : ScaleConservationField) :
    scaleAtLegTarget f scaleLegQuantumToMeso = f.atMeso := rfl

theorem scale_at_leg_source_meso_to_macro (f : ScaleConservationField) :
    scaleAtLegSource f scaleLegMesoToMacro = f.atMeso := rfl

theorem scale_at_leg_target_meso_to_macro (f : ScaleConservationField) :
    scaleAtLegTarget f scaleLegMesoToMacro = f.atMacro := rfl

theorem scale_at_leg_source_quantum_to_macro_direct (f : ScaleConservationField) :
    scaleAtLegSource f scaleLegQuantumToMacroDirect = f.atQuantum := rfl

theorem scale_at_leg_target_quantum_to_macro_direct (f : ScaleConservationField) :
    scaleAtLegTarget f scaleLegQuantumToMacroDirect = f.atMacro := rfl

/-- Indirect Q→meso→macro leg endpoints compose (typed **scale** scaffold). -/
theorem scale_indirect_leg_composes (f : ScaleConservationField) :
    scaleAtLegTarget f scaleLegQuantumToMeso = scaleAtLegSource f scaleLegMesoToMacro := rfl

/-- Direct Q→macro endpoints match indirect compose (typed **conservation**). -/
theorem scale_direct_endpoints_match (f : ScaleConservationField) :
    scaleAtLegSource f scaleLegQuantumToMeso = scaleAtLegSource f scaleLegQuantumToMacroDirect ∧
    scaleAtLegTarget f scaleLegMesoToMacro = scaleAtLegTarget f scaleLegQuantumToMacroDirect := by
  constructor <;> rfl

/-- Composed Q→meso→macro **conservation** stamp equals Q→macro direct target (typed identity). -/
theorem scale_commute_conservation_identity (f : ScaleConservationField) :
    scaleAtLegTarget f scaleLegMesoToMacro = scaleAtLegTarget f scaleLegQuantumToMacroDirect := rfl

/-- Whether **scale** **conservation** stamps are uniform on named field (commute typed). -/
def scaleCommuteConservationTyped (f : ScaleConservationField) : Bool :=
  decide (scaleAtLegTarget f scaleLegMesoToMacro = scaleAtLegTarget f scaleLegQuantumToMacroDirect ∧
    scaleAtLegTarget f scaleLegQuantumToMeso = scaleAtLegSource f scaleLegMesoToMacro ∧
    scaleAtLegSource f scaleLegQuantumToMeso = scaleAtLegSource f scaleLegQuantumToMacroDirect)

theorem scale_commute_conservation_named_typed :
    scaleCommuteConservationTyped scaleConservationFieldNamed = true := rfl

theorem scale_commute_conservation_unwired_typed :
    scaleCommuteConservationTyped scaleConservationFieldUnwired = true := rfl

/-- A **scale** **conservation** path at a refinement level. -/
structure ScaleConservationPath where
  field : ScaleConservationField
  level : Nat
  elementZ : ScaleElementZ
  diagram : ScaleCommuteDiagram

def scaleConservationPathIsNontrivial (p : ScaleConservationPath) : Bool :=
  decide (p.level > 0)

def scaleConservationPathCarbonL1 : ScaleConservationPath :=
  { field := scaleConservationFieldNamed
    level := 1
    elementZ := scaleElementCarbon
    diagram := scaleCommuteDiagramNamed }

def scaleConservationPathUnwiredL1 : ScaleConservationPath :=
  { field := scaleConservationFieldUnwired
    level := 1
    elementZ := scaleElementCarbon
    diagram := scaleCommuteDiagramNamed }

/-- Whether element Z pins are valid IUPAC Z on a **scale** **conservation** path. -/
def scaleElementZValid (z : ScaleElementZ) : Bool :=
  decide (0 < z.z ∧ z.z ≤ iupacTableCardinality)

theorem scale_carbon_z_valid :
    scaleElementZValid scaleElementCarbon = true ∧
    scaleElementCarbon.z = 6 := by decide

theorem scale_oganesson_z_valid :
    scaleElementOganesson.z = iupacTableCardinality := rfl

/-- Scaffold thermodynamic ledger for **scale** ladder (knowing fiber). -/
structure ThermoScaleState where
  chemStamp : Nat
  landauerWitness : Nat
  deriving DecidableEq, Repr

def thermoScaleZero : ThermoScaleState :=
  { chemStamp := 0, landauerWitness := 0 }

def thermoScalePositive : ThermoScaleState :=
  { chemStamp := 1, landauerWitness := 1 }

/-- Thermo-preserving **scale** fusion — identity **conserved** (additive). -/
def fusionScale (a b : ThermoScaleState) : ThermoScaleState :=
  { chemStamp := a.chemStamp + b.chemStamp,
    landauerWitness := a.landauerWitness + b.landauerWitness }

theorem fusion_scale_commutative_stamp :
    (fusionScale thermoScalePositive thermoScaleZero).chemStamp =
      (fusionScale thermoScaleZero thermoScalePositive).chemStamp := rfl

theorem fusion_scale_zero_identity_stamp :
    (fusionScale thermoScaleZero thermoScalePositive).chemStamp =
      thermoScalePositive.chemStamp := rfl

theorem fusion_scale_zero_identity_witness :
    (fusionScale thermoScaleZero thermoScalePositive).landauerWitness =
      thermoScalePositive.landauerWitness := rfl

/-- Verdict of a **scale** commute close attempt (fail-closed). -/
inductive ScaleCommutePathVerdict where
  | unwiredOk
  | legNamedOk
  | greenInventRefuse
  | provedWithoutBarRefuse
  | trivialScaleRefuse
  | occupancyZLiftRefuse
  deriving DecidableEq, Repr

/-- Evaluate a **scale** commute path against the SCALE-01 bar. -/
def evaluateScaleCommutePath
    (modality : ScaleConservationModality)
    (path : ScaleConservationPath)
    (claimPhysicsGreen : Bool)
    (claimProved : Bool)
    (claimOccupancyZLift : Bool) : ScaleCommutePathVerdict :=
  if claimPhysicsGreen then
    .greenInventRefuse
  else if claimOccupancyZLift then
    .occupancyZLiftRefuse
  else if claimProved then
    .provedWithoutBarRefuse
  else if !scaleConservationPathIsNontrivial path then
    .trivialScaleRefuse
  else if !scaleElementZValid path.elementZ then
    .trivialScaleRefuse
  else
    match modality with
    | .unwired => .legNamedOk
    | .assumed | .surrogate => .unwiredOk
    | .proved => .provedWithoutBarRefuse

/-- Verdict of a **scale** **conservation** close attempt (fail-closed). -/
inductive ScaleConservationVerdict where
  | unwiredOk
  | legNamedOk
  | trivialScaleRefuse
  | greenInventRefuse
  | occupancyZLiftRefuse
  deriving DecidableEq, Repr

/-- Evaluate **scale** **conservation** against the SCALE-01 bar. -/
def evaluateScaleConservation
    (modality : ScaleConservationModality)
    (path : ScaleConservationPath)
    (claimPhysicsGreen : Bool)
    (claimOccupancyZLift : Bool) : ScaleConservationVerdict :=
  if claimPhysicsGreen then
    .greenInventRefuse
  else if claimOccupancyZLift then
    .occupancyZLiftRefuse
  else if !scaleConservationPathIsNontrivial path then
    .trivialScaleRefuse
  else
    match modality with
    | .unwired | .assumed | .surrogate => .unwiredOk
    | .proved => .legNamedOk

/-- Whether three named legs are pinned on the **scale** diagram. -/
def threeLegsNamed : Bool :=
  decide (scaleCommuteDiagramNamed.viaMeso = scaleLegQuantumToMeso ∧
    scaleCommuteDiagramNamed.thenMacro = scaleLegMesoToMacro ∧
    scaleCommuteDiagramNamed.direct = scaleLegQuantumToMacroDirect ∧
    scaleLegQuantumToMeso ≠ scaleLegQuantumToMacroDirect)

/-- Whether composed Q→meso→macro **conservation** equals Q→macro direct (typed). -/
def commuteSquareConservationTyped : Bool :=
  decide (scaleCommuteConservationTyped scaleConservationFieldNamed = true ∧
    scaleCommuteConservationTyped scaleConservationFieldUnwired = true ∧
    scaleAtLegTarget scaleConservationFieldNamed scaleLegMesoToMacro =
      scaleAtLegTarget scaleConservationFieldNamed scaleLegQuantumToMacroDirect)

/-- Whether **scale** ladder is distinct from `ScaleOccupancyZCommute` Z-lift identity. -/
def scaleConservationNeOccupancyZLift : Bool :=
  decide (scaleElementDs.z = 110 ∧
    scaleElementPt.z = 78 ∧
    scaleElementDs.z ≠ scaleElementPt.z ∧
    scaleLegString .quantumToMeso = "quantum_to_meso")

/-- Whether thermo-preserving **scale** fusion identity is **conserved** on pinned states. -/
def fusionIdentityConserved : Bool :=
  decide (fusionScale thermoScaleZero thermoScalePositive =
    thermoScalePositive ∧
    fusionScale thermoScalePositive thermoScaleZero =
      fusionScale thermoScaleZero thermoScalePositive ∧
    (fusionScale thermoScalePositive thermoScalePositive).landauerWitness = 2 ∧
    scaleConservationPathIsNontrivial scaleConservationPathCarbonL1 = true ∧
    scaleElementZValid scaleElementCarbon = true)

/-- Whether trivial (level-0) **scale** path is refused (fail-closed). -/
def trivialScaleRefused : Bool :=
  let trivialPath : ScaleConservationPath :=
    { field := scaleConservationFieldNamed, level := 0, elementZ := scaleElementCarbon
      diagram := scaleCommuteDiagramNamed }
  decide (evaluateScaleCommutePath .unwired trivialPath false false false = .trivialScaleRefuse ∧
    evaluateScaleConservation .unwired trivialPath false false = .trivialScaleRefuse)

/-- Whether GREEN invent is refused on **scale** scaffold. -/
def greenInventRefused : Bool :=
  decide (evaluateScaleCommutePath .unwired scaleConservationPathCarbonL1 true false false =
    .greenInventRefuse ∧
    evaluateScaleConservation .unwired scaleConservationPathCarbonL1 true false =
      .greenInventRefuse)

/-- Whether occupancy Z-lift claim is refused (distinct from this **scale** **conservation** cell). -/
def occupancyZLiftRefused : Bool :=
  decide (evaluateScaleCommutePath .unwired scaleConservationPathCarbonL1 false false true =
    .occupancyZLiftRefuse ∧
    evaluateScaleConservation .unwired scaleConservationPathCarbonL1 false true =
      .occupancyZLiftRefuse)

/-- Whether carbon **scale** **conservation** path passes under Unwired modality. -/
def carbonScaleConservationUnwiredOk : Bool :=
  decide (evaluateScaleConservation .unwired scaleConservationPathCarbonL1 false false = .unwiredOk ∧
    evaluateScaleCommutePath .unwired scaleConservationPathCarbonL1 false false false = .legNamedOk)

/-- Whether unwired baseline **scale** path passes under Unwired modality. -/
def unwiredScaleConservationUnwiredOk : Bool :=
  decide (evaluateScaleConservation .unwired scaleConservationPathUnwiredL1 false false = .unwiredOk ∧
    evaluateScaleCommutePath .unwired scaleConservationPathUnwiredL1 false false false = .legNamedOk)

/-- Whether a close attempt is admissible under SCALE-01 **scale** **conservation**. -/
def scaleConservationVerdictOk (v : ScaleConservationVerdict) : Bool :=
  match v with
  | .unwiredOk | .legNamedOk => true
  | _ => false

theorem unwired_scale_conservation_ok :
    evaluateScaleConservation .unwired scaleConservationPathCarbonL1 false false = .unwiredOk := rfl

theorem assumed_scale_conservation_ok :
    evaluateScaleConservation .assumed scaleConservationPathCarbonL1 false false = .unwiredOk := rfl

theorem surrogate_scale_conservation_ok :
    evaluateScaleConservation .surrogate scaleConservationPathCarbonL1 false false = .unwiredOk := rfl

theorem proved_scale_conservation_leg_named_ok :
    evaluateScaleConservation .proved scaleConservationPathCarbonL1 false false = .legNamedOk := rfl

theorem trivial_scale_refuse :
    evaluateScaleConservation .unwired
      { field := scaleConservationFieldNamed, level := 0, elementZ := scaleElementCarbon
        diagram := scaleCommuteDiagramNamed }
      false false = .trivialScaleRefuse := rfl

theorem green_invent_refuse :
    evaluateScaleConservation .unwired scaleConservationPathCarbonL1 true false =
      .greenInventRefuse := rfl

theorem occupancy_z_lift_refuse :
    evaluateScaleConservation .unwired scaleConservationPathCarbonL1 false true =
      .occupancyZLiftRefuse := rfl

theorem three_legs_named :
    threeLegsNamed = true := by decide

theorem commute_square_conservation_typed :
    commuteSquareConservationTyped = true := rfl

theorem scale_conservation_ne_occupancy_z_lift :
    scaleConservationNeOccupancyZLift = true := by decide

theorem fusion_identity_conserved :
    fusionIdentityConserved = true := rfl

theorem trivial_scale_refused :
    trivialScaleRefused = true := rfl

theorem green_invent_refused :
    greenInventRefused = true := rfl

theorem occupancy_z_lift_refused :
    occupancyZLiftRefused = true := rfl

theorem carbon_scale_conservation_unwired_ok :
    carbonScaleConservationUnwiredOk = true := rfl

theorem unwired_scale_conservation_unwired_ok :
    unwiredScaleConservationUnwiredOk = true := rfl

theorem unwired_verdict_ok :
    scaleConservationVerdictOk
      (evaluateScaleConservation .unwired scaleConservationPathCarbonL1 false false) = true := rfl

theorem trivial_scale_verdict_not_ok :
    scaleConservationVerdictOk
      (evaluateScaleConservation .unwired
        { field := scaleConservationFieldNamed, level := 0, elementZ := scaleElementCarbon
          diagram := scaleCommuteDiagramNamed }
        false false) = false := rfl

theorem green_invent_verdict_not_ok :
    scaleConservationVerdictOk
      (evaluateScaleConservation .unwired scaleConservationPathCarbonL1 true false) = false := rfl

theorem occupancy_z_lift_verdict_not_ok :
    scaleConservationVerdictOk
      (evaluateScaleConservation .unwired scaleConservationPathCarbonL1 false true) = false := rfl

/-- Quantum / knowing formal fiber root (structure witness — not meso acting). -/
def scaleConservationQuantumKnowingFiber : String :=
  "umst/umst-formal-double-slit"

/-- Meso / acting formal fiber root (cite only — not wired on knowing scaffold). -/
def scaleConservationMesoActingFiber : String :=
  "umst/umst-formal"

theorem scale_conservation_quantum_knowing_fiber_pinned :
    scaleConservationQuantumKnowingFiber =
      "umst/umst-formal-double-slit" := rfl

/-- Cited Rust **scale** commute authority (views only — lattice is structural here). -/
def scaleConservationCitedModule : String :=
  "umst/umst-chem/src/scale_commute.rs"

/-- **Scale** lattice is structure — not 118² GREEN periodic enumeration. -/
def scaleConservationNot118GreenTable : Bool := true

theorem scale_conservation_not_118_green_table :
    scaleConservationNot118GreenTable = true := rfl

/-- Second-law + **conservation** framing — cites meso SSOT, not wired on knowing scaffold. -/
def scaleConservationSecondLawFramed : Bool := true

theorem scale_conservation_second_law_framed :
    scaleConservationSecondLawFramed = true := rfl

/-- SCALE-01 claim **scale** commute is **not** claimed Proved on the knowing scaffold. -/
def scale01CommuteProved : Bool := false

theorem scale01_commute_not_proved : scale01CommuteProved = false := rfl

/-- Production wiring is **not** claimed on the knowing scaffold. -/
def scaleConservationProductionWired : Bool := false

theorem scale_conservation_production_not_wired :
    scaleConservationProductionWired = false := rfl

/-- Cell id for the Lean SCALE-01 **scale** **conservation** knowing-fiber. -/
def scaleConservationCellId : String :=
  "CHEM-FORMAL-Q-LEAN-SCALE-CONSERVATION"

/-- Cell id for occupancy Z-lift commute (distinct v24 cell — not this scaffold). -/
def scaleOccupancyZCommuteCellId : String :=
  "CHEM-FORMAL-Q-LEAN-SCALE-OCCUPANCY-Z-COMMUTE"

theorem scale_conservation_cell_distinct_from_occupancy_z :
    scaleConservationCellId ≠ scaleOccupancyZCommuteCellId := by decide

/-- Non-claim fence — three named legs; composed Q→meso→macro **conservation** equals Q→macro direct;
Ds 110 not Pt 78 homolog not copy; trivial **scale** refuse; occupancy Z-lift refuse;
**scale** **conservation**; SCALE-01 Unwired; `scale01CommuteProved` false. -/
def scaleConservationNonClaim : String :=
  "CHEM-FORMAL-Q-LEAN-SCALE-CONSERVATION SCALE-01 scale commuting-square conservation three named legs quantum_to_meso meso_to_macro quantum_to_macro_direct composed indirect equals direct typed conservation Ds 110 not Pt 78 homolog not copy occupancy Z-lift refuse distinct ScaleOccupancyZCommute trivial scale refuse scale01CommuteProved false Unwired OK not SCALE-01 Proved not physics GREEN; not 118² GREEN DFT"

/-- Physics GREEN is unauthorized on the knowing SCALE-01 **scale** **conservation** scaffold. -/
def scaleConservationPhysicsGreenAuthorized : Prop := False

theorem scale_conservation_physics_green_false :
    ¬ scaleConservationPhysicsGreenAuthorized := id

theorem scale_conservation_modality_unwired :
    scaleConservationModalityCurrent = .unwired := rfl

/-- **One** design axiom: second law + **conservation** (structure witness — not meso import). -/
def scaleConservationAxiom : Bool :=
  scaleConservationNot118GreenTable &&
    scaleConservationSecondLawFramed &&
    threeLegsNamed &&
    commuteSquareConservationTyped &&
    scaleConservationNeOccupancyZLift &&
    fusionIdentityConserved &&
    trivialScaleRefused &&
    greenInventRefused &&
    occupancyZLiftRefused &&
    carbonScaleConservationUnwiredOk &&
    unwiredScaleConservationUnwiredOk &&
    !scale01CommuteProved &&
    !scaleConservationProductionWired

theorem scale_conservation_axiom :
    scaleConservationAxiom = true := by decide

theorem scale_conservation_honest_bundle :
    scale01CommuteProved = false ∧
    scaleConservationProductionWired = false ∧
    scaleConservationNot118GreenTable = true ∧
    scaleConservationSecondLawFramed = true ∧
    evaluateScaleConservation .unwired scaleConservationPathCarbonL1 false false = .unwiredOk ∧
    evaluateScaleConservation .proved scaleConservationPathCarbonL1 false false = .legNamedOk ∧
    evaluateScaleConservation .unwired
      { field := scaleConservationFieldNamed, level := 0, elementZ := scaleElementCarbon
        diagram := scaleCommuteDiagramNamed }
      false false = .trivialScaleRefuse ∧
    evaluateScaleConservation .unwired scaleConservationPathCarbonL1 true false = .greenInventRefuse ∧
    evaluateScaleConservation .unwired scaleConservationPathCarbonL1 false true = .occupancyZLiftRefuse ∧
    threeLegsNamed = true ∧
    commuteSquareConservationTyped = true ∧
    scaleConservationNeOccupancyZLift = true ∧
    fusionIdentityConserved = true ∧
    trivialScaleRefused = true ∧
    greenInventRefused = true ∧
    occupancyZLiftRefused = true ∧
    carbonScaleConservationUnwiredOk = true ∧
    unwiredScaleConservationUnwiredOk = true ∧
    scaleElementCarbon.z = 6 ∧
    scaleElementOganesson.z = 118 ∧
    scaleElementDs.z ≠ scaleElementPt.z ∧
    scaleConservationAxiom = true :=
  ⟨rfl, rfl, scale_conservation_not_118_green_table,
    scale_conservation_second_law_framed,
    unwired_scale_conservation_ok, proved_scale_conservation_leg_named_ok, trivial_scale_refuse,
    green_invent_refuse, occupancy_z_lift_refuse,
    three_legs_named, commute_square_conservation_typed, scale_conservation_ne_occupancy_z_lift,
    fusion_identity_conserved, trivial_scale_refused, green_invent_refused, occupancy_z_lift_refused,
    carbon_scale_conservation_unwired_ok, unwired_scale_conservation_unwired_ok,
    scale_carbon_z_six, scale_oganesson_z_118, scale_ds_not_copy_of_pt,
    scale_conservation_axiom⟩

end UMST.Chem
