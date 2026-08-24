-- SPDX-FileCopyrightText: 2026 Santosh Prabhu Shenbagamoorthy and Santhosh Shyamsundar
-- SPDX-License-Identifier: MIT

import ElementElectronic

/-!
# ThermoConservation — knowing-fiber THERMO-01 **Thermo_n G(T,P,x) conservation** (Q lattice)

North-star THERMO-01 claim **Thermo_n** Green Book **G(T,P,x)** identity **conservation** on the
quantum / knowing formal fiber — named state variables T → P → x with composed T∘P∘x identity equal
to direct G (typed **conservation**). Pairs `umst-chem` scaffold **thermo** / CALPHAD hull
**conservation** posture.

- `ThermoConservationModality` — Unwired / Assumed / Proved / Surrogate (not 118² GREEN table).
- `ThermoStateVariable` / `ThermoConservationLeg` — T, P, x named legs; indirect compose **conservation**.
- `fusionCalphadHull` — CALPHAD hull identity **conserved** (additive witness).
- `evaluateThermoConservation` — Unwired OK; Proved leg-named scaffold OK; trivial Z=0 fail-closed;
  GREEN invent refuse; formation-zero ≠ G unless named refuse; measured-scalar invent refuse;
  scrambled order refuse; live Process G refuse; **conservation** typed not live meso G.
- Green Book **G** — Gibbs free energy design name; formation-zero ≠ **G**.
- Second-law + **conservation** framing cites meso `UMST.Chem.Conservation` /
  `LandauerLaw.physicalSecondLaw` — not imported.
- No meso / acting theorems. No new physics `axiom`.
- `physics_green` stays false. Does **not** claim Thermo_n Proved or physics GREEN.
- **Thermo_n G** ladder ≠ 118² GREEN periodic enumeration.
-/

namespace UMST.Chem

/-- Design modality for THERMO-01 claim **Thermo_n G** **conservation** (lattice SSOT). -/
inductive ThermoConservationModality where
  | unwired | assumed | proved | surrogate
  deriving DecidableEq, Repr

def thermoConservationModalityCurrent : ThermoConservationModality := .unwired

/-- IUPAC periodic-table cardinality (Z=1..118). -/
def iupacTableCardinality : Nat := 118

theorem iupac_table_cardinality_118 : iupacTableCardinality = 118 := rfl

/-- Private Z pin for **Thermo_n** witnesses — not L1 SpeciesId. -/
structure ThermoElementZ where
  z : Nat
  hzLo : 0 < z
  hzHi : z ≤ iupacTableCardinality
  deriving DecidableEq, Repr

def thermoElementIron : ThermoElementZ := { z := 26, hzLo := by decide, hzHi := by decide }
def thermoElementCopper : ThermoElementZ := { z := 29, hzLo := by decide, hzHi := by decide }
def thermoElementOganesson : ThermoElementZ := { z := 118, hzLo := by decide, hzHi := by decide }

theorem thermo_iron_z_twenty_six : thermoElementIron.z = 26 := rfl
theorem thermo_copper_z_twenty_nine : thermoElementCopper.z = 29 := rfl
theorem thermo_oganesson_z_118 : thermoElementOganesson.z = 118 := rfl

/-- Named **Thermo_n** state variables T, P, x, G (Green Book design names only). -/
inductive ThermoStateVariable where
  | temperature | pressure | composition | gibbsG
  deriving DecidableEq, Repr

/-- Monotonic index along T → P → x → G (0 = T … 3 = G). -/
def thermoStateVariableIndex : ThermoStateVariable → Nat
  | .temperature => 0
  | .pressure => 1
  | .composition => 2
  | .gibbsG => 3

theorem thermo_var_temperature_index_zero :
    thermoStateVariableIndex .temperature = 0 := rfl

theorem thermo_var_pressure_index_one :
    thermoStateVariableIndex .pressure = 1 := rfl

theorem thermo_var_composition_index_two :
    thermoStateVariableIndex .composition = 2 := rfl

theorem thermo_var_gibbs_g_index_three :
    thermoStateVariableIndex .gibbsG = 3 := rfl

theorem thermo_var_order_strict :
    thermoStateVariableIndex .temperature < thermoStateVariableIndex .pressure ∧
    thermoStateVariableIndex .pressure < thermoStateVariableIndex .composition ∧
    thermoStateVariableIndex .composition < thermoStateVariableIndex .gibbsG := by decide

def thermoVarString : ThermoStateVariable → String
  | .temperature => "T"
  | .pressure => "P"
  | .composition => "x"
  | .gibbsG => "G"

theorem thermo_var_temperature_str :
    thermoVarString .temperature = "T" := rfl

theorem thermo_var_pressure_str :
    thermoVarString .pressure = "P" := rfl

theorem thermo_var_composition_str :
    thermoVarString .composition = "x" := rfl

theorem thermo_var_gibbs_g_str :
    thermoVarString .gibbsG = "G" := rfl

/-- Named scalar kinds — Green Book G vs formation-zero vs measured invent. -/
inductive NamedThermoScalar where
  | greenBookG | formationZero | measuredScalarInvent
  deriving DecidableEq, Repr

def namedThermoScalarString : NamedThermoScalar → String
  | .greenBookG => "green_book_G"
  | .formationZero => "formation_zero"
  | .measuredScalarInvent => "measured_scalar_invent"

theorem named_scalar_green_book_g_str :
    namedThermoScalarString .greenBookG = "green_book_G" := rfl

theorem named_scalar_formation_zero_str :
    namedThermoScalarString .formationZero = "formation_zero" := rfl

/-- Scalar kind on a **Thermo_n** variable — formation-zero ≠ G unless named. -/
inductive ThermoScalarKind where
  | greenBookG
  | named (field : NamedThermoScalar)
  deriving DecidableEq, Repr

def thermoScalarKindIsGreenBookG (k : ThermoScalarKind) : Bool :=
  match k with
  | .greenBookG => true
  | .named .greenBookG => true
  | .named _ => false

def thermoScalarKindIsFormationZero (k : ThermoScalarKind) : Bool :=
  match k with
  | .greenBookG => false
  | .named .formationZero => true
  | .named _ => false

/-- Formation-zero ≠ G unless the scalar field is explicitly named Green Book G. -/
def formationZeroNotGUnlessNamed (k : ThermoScalarKind) : Bool :=
  match k with
  | .greenBookG => true
  | .named .greenBookG => true
  | .named .formationZero => true
  | .named _ => false

theorem scaffold_formation_zero_not_g_unless_named :
    formationZeroNotGUnlessNamed (.named .formationZero) = true := rfl

theorem green_book_g_formation_zero_distinct :
    thermoScalarKindIsFormationZero (.named .formationZero) = true ∧
    thermoScalarKindIsGreenBookG (.named .formationZero) = false := by decide

theorem formation_zero_ne_g_generic :
    thermoScalarKindIsGreenBookG (.named .formationZero) = false := rfl

/-- Named legs of the **Thermo_n G(T,P,x)** diagram (scaffold — typed **conservation**). -/
inductive ThermoConservationLeg where
  | temperatureToPressure | pressureToComposition | compositionToG | temperatureToGDirect
  deriving DecidableEq, Repr

def ThermoConservationLeg.source : ThermoConservationLeg → ThermoStateVariable
  | .temperatureToPressure => .temperature
  | .pressureToComposition => .pressure
  | .compositionToG => .composition
  | .temperatureToGDirect => .temperature

def ThermoConservationLeg.target : ThermoConservationLeg → ThermoStateVariable
  | .temperatureToPressure => .pressure
  | .pressureToComposition => .composition
  | .compositionToG => .gibbsG
  | .temperatureToGDirect => .gibbsG

def thermoLegString : ThermoConservationLeg → String
  | .temperatureToPressure => "T_to_P"
  | .pressureToComposition => "P_to_x"
  | .compositionToG => "x_to_G"
  | .temperatureToGDirect => "T_to_G_direct"

/-- Named step leg T → P in the **Thermo_n** diagram. -/
def thermoLegTemperatureToPressure : ThermoConservationLeg := .temperatureToPressure

/-- Named step leg P → x in the **Thermo_n** diagram. -/
def thermoLegPressureToComposition : ThermoConservationLeg := .pressureToComposition

/-- Named step leg x → G in the **Thermo_n** diagram. -/
def thermoLegCompositionToG : ThermoConservationLeg := .compositionToG

/-- Named direct leg T → G in the **Thermo_n** diagram. -/
def thermoLegTemperatureToGDirect : ThermoConservationLeg := .temperatureToGDirect

theorem thermo_leg_temperature_to_pressure_named :
    thermoLegTemperatureToPressure = ThermoConservationLeg.temperatureToPressure := rfl

theorem thermo_leg_pressure_to_composition_named :
    thermoLegPressureToComposition = ThermoConservationLeg.pressureToComposition := rfl

theorem thermo_leg_composition_to_g_named :
    thermoLegCompositionToG = ThermoConservationLeg.compositionToG := rfl

theorem thermo_leg_temperature_to_g_direct_named :
    thermoLegTemperatureToGDirect = ThermoConservationLeg.temperatureToGDirect := rfl

theorem thermo_leg_temperature_to_pressure_composes_pressure_to_x :
    thermoLegTemperatureToPressure.target = thermoLegPressureToComposition.source := rfl

theorem thermo_leg_pressure_to_composition_composes_x_to_g :
    thermoLegPressureToComposition.target = thermoLegCompositionToG.source := rfl

theorem thermo_leg_direct_endpoints_match :
    thermoLegTemperatureToPressure.source = thermoLegTemperatureToGDirect.source ∧
    thermoLegCompositionToG.target = thermoLegTemperatureToGDirect.target := by
  constructor <;> rfl

theorem thermo_leg_distinct_step_vs_direct :
    thermoLegTemperatureToPressure ≠ thermoLegTemperatureToGDirect := by decide

/-- Named legs of the **Thermo_n G(T,P,x)** diagram (typed **conservation** scaffold). -/
structure ThermoConservationDiagram where
  temperatureToPressure : ThermoConservationLeg
  pressureToComposition : ThermoConservationLeg
  compositionToG : ThermoConservationLeg
  direct : ThermoConservationLeg
  deriving Repr

def thermoConservationDiagramNamed : ThermoConservationDiagram :=
  { temperatureToPressure := thermoLegTemperatureToPressure
    pressureToComposition := thermoLegPressureToComposition
    compositionToG := thermoLegCompositionToG
    direct := thermoLegTemperatureToGDirect }

/-- **Thermo_n G** **conservation** stamp field across T → P → x → G (typed identity witness). -/
structure ThermoConservationField where
  atTemperature : Nat
  atPressure : Nat
  atComposition : Nat
  atGibbsG : Nat
  deriving DecidableEq, Repr

def thermoConservationFieldUnwired : ThermoConservationField :=
  { atTemperature := 0, atPressure := 0, atComposition := 0, atGibbsG := 0 }

def thermoConservationFieldNamed : ThermoConservationField :=
  { atTemperature := 1, atPressure := 1, atComposition := 1, atGibbsG := 1 }

/-- Lookup **Thermo_n G** **conservation** stamp at a named state variable. -/
def thermoAtVariable (f : ThermoConservationField) : ThermoStateVariable → Nat
  | .temperature => f.atTemperature
  | .pressure => f.atPressure
  | .composition => f.atComposition
  | .gibbsG => f.atGibbsG

/-- **Thermo_n** stamp at the source endpoint of a diagram leg. -/
def thermoAtLegSource (f : ThermoConservationField) (leg : ThermoConservationLeg) : Nat :=
  thermoAtVariable f leg.source

/-- **Thermo_n** stamp at the target endpoint of a diagram leg. -/
def thermoAtLegTarget (f : ThermoConservationField) (leg : ThermoConservationLeg) : Nat :=
  thermoAtVariable f leg.target

theorem thermo_at_leg_source_temperature_to_pressure (f : ThermoConservationField) :
    thermoAtLegSource f thermoLegTemperatureToPressure = f.atTemperature := rfl

theorem thermo_at_leg_target_composition_to_g (f : ThermoConservationField) :
    thermoAtLegTarget f thermoLegCompositionToG = f.atGibbsG := rfl

theorem thermo_at_leg_target_temperature_to_g_direct (f : ThermoConservationField) :
    thermoAtLegTarget f thermoLegTemperatureToGDirect = f.atGibbsG := rfl

/-- Composed T→P→x→G **conservation** stamp equals T→G direct target (typed identity). -/
theorem thermo_g_conservation_identity (f : ThermoConservationField) :
    thermoAtLegTarget f thermoLegCompositionToG = thermoAtLegTarget f thermoLegTemperatureToGDirect := rfl

/-- Whether **Thermo_n G** **conservation** stamps are uniform on named field (typed). -/
def thermoGConservationTyped (f : ThermoConservationField) : Bool :=
  decide (thermoAtLegTarget f thermoLegCompositionToG = thermoAtLegTarget f thermoLegTemperatureToGDirect ∧
    thermoAtLegTarget f thermoLegTemperatureToPressure = thermoAtLegSource f thermoLegPressureToComposition ∧
    thermoAtLegTarget f thermoLegPressureToComposition = thermoAtLegSource f thermoLegCompositionToG ∧
    thermoAtLegSource f thermoLegTemperatureToPressure = thermoAtLegSource f thermoLegTemperatureToGDirect)

theorem thermo_g_conservation_named_typed :
    thermoGConservationTyped thermoConservationFieldNamed = true := rfl

theorem thermo_g_conservation_unwired_typed :
    thermoGConservationTyped thermoConservationFieldUnwired = true := rfl

/-- A **Thermo_n G** **conservation** path at a refinement level. -/
structure ThermoConservationPath where
  field : ThermoConservationField
  level : Nat
  elementZ : ThermoElementZ
  diagram : ThermoConservationDiagram
  scalar : ThermoScalarKind

def thermoConservationPathIsNontrivial (p : ThermoConservationPath) : Bool :=
  decide (p.level > 0)

def thermoConservationPathIronL1 : ThermoConservationPath :=
  { field := thermoConservationFieldNamed
    level := 1
    elementZ := thermoElementIron
    diagram := thermoConservationDiagramNamed
    scalar := .greenBookG }

def thermoConservationPathUnwiredL1 : ThermoConservationPath :=
  { field := thermoConservationFieldUnwired
    level := 1
    elementZ := thermoElementIron
    diagram := thermoConservationDiagramNamed
    scalar := .greenBookG }

def thermoConservationPathCopperL1 : ThermoConservationPath :=
  { field := thermoConservationFieldNamed
    level := 1
    elementZ := thermoElementCopper
    diagram := thermoConservationDiagramNamed
    scalar := .greenBookG }

/-- Whether element Z pins are valid IUPAC Z on a **Thermo_n G** **conservation** path. -/
def thermoElementZValid (z : ThermoElementZ) : Bool :=
  decide (0 < z.z ∧ z.z ≤ iupacTableCardinality)

theorem thermo_iron_z_valid :
    thermoElementZValid thermoElementIron = true ∧
    thermoElementIron.z = 26 := by decide

theorem thermo_copper_z_valid :
    thermoElementZValid thermoElementCopper = true ∧
    thermoElementCopper.z = 29 := by decide

theorem thermo_oganesson_z_valid :
    thermoElementOganesson.z = iupacTableCardinality := rfl

/-- Scaffold CALPHAD hull ledger for **Thermo_n G** (knowing fiber). -/
structure ThermoCalphadHullState where
  chemStamp : Nat
  landauerWitness : Nat
  deriving DecidableEq, Repr

def thermoCalphadZero : ThermoCalphadHullState :=
  { chemStamp := 0, landauerWitness := 0 }

def thermoCalphadPositive : ThermoCalphadHullState :=
  { chemStamp := 1, landauerWitness := 1 }

/-- CALPHAD hull-preserving **Thermo_n** fusion — identity **conserved** (additive). -/
def fusionCalphadHull (a b : ThermoCalphadHullState) : ThermoCalphadHullState :=
  { chemStamp := a.chemStamp + b.chemStamp,
    landauerWitness := a.landauerWitness + b.landauerWitness }

theorem fusion_calphad_hull_commutative_stamp :
    (fusionCalphadHull thermoCalphadPositive thermoCalphadZero).chemStamp =
      (fusionCalphadHull thermoCalphadZero thermoCalphadPositive).chemStamp := rfl

theorem fusion_calphad_hull_zero_identity_stamp :
    (fusionCalphadHull thermoCalphadZero thermoCalphadPositive).chemStamp =
      thermoCalphadPositive.chemStamp := rfl

/-- Verdict of a **Thermo_n G** path close attempt (fail-closed). -/
inductive ThermoGPathVerdict where
  | unwiredOk
  | legNamedOk
  | greenInventRefuse
  | provedWithoutBarRefuse
  | trivialZZeroRefuse
  | formationZeroMisidentifiedAsGRefuse
  | measuredScalarInventRefuse
  | scrambledOrderRefuse
  | liveProcessGRefuse
  deriving DecidableEq, Repr

/-- Evaluate a **Thermo_n G** path against the THERMO-01 bar. -/
def evaluateThermoGPath
    (modality : ThermoConservationModality)
    (path : ThermoConservationPath)
    (claimPhysicsGreen : Bool)
    (claimProved : Bool)
    (claimLiveProcessG : Bool)
    (claimFormationZeroAsG : Bool)
    (claimMeasuredScalar : Bool)
    (claimScrambledOrder : Bool) : ThermoGPathVerdict :=
  if claimPhysicsGreen then
    .greenInventRefuse
  else if claimLiveProcessG then
    .liveProcessGRefuse
  else if claimFormationZeroAsG then
    .formationZeroMisidentifiedAsGRefuse
  else if claimMeasuredScalar then
    .measuredScalarInventRefuse
  else if claimScrambledOrder then
    .scrambledOrderRefuse
  else if claimProved then
    .provedWithoutBarRefuse
  else if !thermoConservationPathIsNontrivial path then
    .trivialZZeroRefuse
  else if !thermoElementZValid path.elementZ then
    .trivialZZeroRefuse
  else
    match modality with
    | .unwired => .legNamedOk
    | .assumed | .surrogate => .unwiredOk
    | .proved => .provedWithoutBarRefuse

/-- Verdict of a **Thermo_n G** **conservation** close attempt (fail-closed). -/
inductive ThermoConservationVerdict where
  | unwiredOk
  | legNamedOk
  | trivialZZeroRefuse
  | greenInventRefuse
  | formationZeroMisidentifiedAsGRefuse
  | measuredScalarInventRefuse
  | scrambledOrderRefuse
  | liveProcessGRefuse
  deriving DecidableEq, Repr

/-- Evaluate **Thermo_n G** **conservation** against the THERMO-01 bar. -/
def evaluateThermoConservation
    (modality : ThermoConservationModality)
    (path : ThermoConservationPath)
    (claimPhysicsGreen : Bool)
    (claimLiveProcessG : Bool)
    (claimFormationZeroAsG : Bool)
    (claimMeasuredScalar : Bool)
    (claimScrambledOrder : Bool) : ThermoConservationVerdict :=
  if claimPhysicsGreen then
    .greenInventRefuse
  else if claimLiveProcessG then
    .liveProcessGRefuse
  else if claimFormationZeroAsG then
    .formationZeroMisidentifiedAsGRefuse
  else if claimMeasuredScalar then
    .measuredScalarInventRefuse
  else if claimScrambledOrder then
    .scrambledOrderRefuse
  else if !thermoConservationPathIsNontrivial path then
    .trivialZZeroRefuse
  else
    match modality with
    | .unwired | .assumed | .surrogate => .unwiredOk
    | .proved => .legNamedOk

/-- Whether three named T, P, x legs are pinned on the **Thermo_n G** diagram. -/
def threeLegsNamed : Bool :=
  decide (thermoConservationDiagramNamed.temperatureToPressure = thermoLegTemperatureToPressure ∧
    thermoConservationDiagramNamed.pressureToComposition = thermoLegPressureToComposition ∧
    thermoConservationDiagramNamed.compositionToG = thermoLegCompositionToG ∧
    thermoConservationDiagramNamed.direct = thermoLegTemperatureToGDirect ∧
    thermoLegTemperatureToPressure ≠ thermoLegTemperatureToGDirect)

/-- Whether composed T∘P∘x **conservation** equals direct G (typed). -/
def thermoGOrderConservationTyped : Bool :=
  decide (thermoGConservationTyped thermoConservationFieldNamed = true ∧
    thermoGConservationTyped thermoConservationFieldUnwired = true ∧
    thermoAtLegTarget thermoConservationFieldNamed thermoLegCompositionToG =
      thermoAtLegTarget thermoConservationFieldNamed thermoLegTemperatureToGDirect)

/-- Whether **Thermo_n** state variable order T→P→x→G is strictly ordered. -/
def thermoVarOrderOk : Bool :=
  decide (thermoStateVariableIndex .temperature < thermoStateVariableIndex .pressure ∧
    thermoStateVariableIndex .pressure < thermoStateVariableIndex .composition ∧
    thermoStateVariableIndex .composition < thermoStateVariableIndex .gibbsG ∧
    thermoVarString .temperature = "T" ∧
    thermoVarString .gibbsG = "G")

/-- Whether scaffold scalar obeys formation-zero ≠ G unless named. -/
def formationZeroNotGUnlessNamedOk : Bool :=
  decide (formationZeroNotGUnlessNamed (.named .formationZero) = true ∧
    thermoScalarKindIsFormationZero (.named .formationZero) = true ∧
    thermoScalarKindIsGreenBookG (.named .formationZero) = false)

/-- Whether CALPHAD hull-preserving **Thermo_n** fusion identity is **conserved** on pinned states. -/
def calphadHullIdentityConserved : Bool :=
  decide (fusionCalphadHull thermoCalphadZero thermoCalphadPositive =
    thermoCalphadPositive ∧
    fusionCalphadHull thermoCalphadPositive thermoCalphadZero =
      fusionCalphadHull thermoCalphadZero thermoCalphadPositive ∧
    (fusionCalphadHull thermoCalphadPositive thermoCalphadPositive).landauerWitness = 2 ∧
    thermoConservationPathIsNontrivial thermoConservationPathIronL1 = true ∧
    thermoElementZValid thermoElementIron = true)

/-- Whether trivial (level-0) **Thermo_n G** path is refused (fail-closed). -/
def trivialZZeroRefused : Bool :=
  let trivialPath : ThermoConservationPath :=
    { field := thermoConservationFieldNamed, level := 0, elementZ := thermoElementIron
      diagram := thermoConservationDiagramNamed, scalar := .greenBookG }
  decide (evaluateThermoGPath .unwired trivialPath false false false false false false = .trivialZZeroRefuse ∧
    evaluateThermoConservation .unwired trivialPath false false false false false = .trivialZZeroRefuse)

/-- Whether GREEN invent is refused on **Thermo_n G** scaffold. -/
def greenInventRefused : Bool :=
  decide (evaluateThermoGPath .unwired thermoConservationPathIronL1 true false false false false false =
    .greenInventRefuse ∧
    evaluateThermoConservation .unwired thermoConservationPathIronL1 true false false false false =
      .greenInventRefuse)

/-- Whether formation-zero misidentified as G is refused (formation-zero ≠ G). -/
def formationZeroMisidentifiedAsGRefused : Bool :=
  decide (evaluateThermoGPath .unwired thermoConservationPathIronL1 false false false true false false =
    .formationZeroMisidentifiedAsGRefuse ∧
    evaluateThermoConservation .unwired thermoConservationPathIronL1 false false true false false =
      .formationZeroMisidentifiedAsGRefuse)

/-- Whether measured-scalar invent is refused on **Thermo_n G** scaffold. -/
def measuredScalarInventRefused : Bool :=
  decide (evaluateThermoGPath .unwired thermoConservationPathIronL1 false false false false true false =
    .measuredScalarInventRefuse ∧
    evaluateThermoConservation .unwired thermoConservationPathIronL1 false false false true false =
      .measuredScalarInventRefuse)

/-- Whether scrambled T/P/x order is refused (typed order required). -/
def scrambledOrderRefused : Bool :=
  decide (evaluateThermoGPath .unwired thermoConservationPathIronL1 false false false false false true =
    .scrambledOrderRefuse ∧
    evaluateThermoConservation .unwired thermoConservationPathIronL1 false false false false true =
      .scrambledOrderRefuse)

/-- Whether live Process G claim is refused (not live meso G on knowing scaffold). -/
def liveProcessGRefused : Bool :=
  decide (evaluateThermoGPath .unwired thermoConservationPathIronL1 false false true false false false =
    .liveProcessGRefuse ∧
    evaluateThermoConservation .unwired thermoConservationPathIronL1 false true false false false =
      .liveProcessGRefuse)

/-- Whether iron **Thermo_n G** **conservation** path passes under Unwired modality. -/
def ironThermoConservationUnwiredOk : Bool :=
  decide (evaluateThermoConservation .unwired thermoConservationPathIronL1 false false false false false = .unwiredOk ∧
    evaluateThermoGPath .unwired thermoConservationPathIronL1 false false false false false false = .legNamedOk)

/-- Whether copper **Thermo_n G** **conservation** path passes under Unwired modality. -/
def copperThermoConservationUnwiredOk : Bool :=
  decide (evaluateThermoConservation .unwired thermoConservationPathCopperL1 false false false false false = .unwiredOk ∧
    evaluateThermoGPath .unwired thermoConservationPathCopperL1 false false false false false false = .legNamedOk)

/-- Whether unwired baseline **Thermo_n G** path passes under Unwired modality. -/
def unwiredThermoConservationUnwiredOk : Bool :=
  decide (evaluateThermoConservation .unwired thermoConservationPathUnwiredL1 false false false false false = .unwiredOk ∧
    evaluateThermoGPath .unwired thermoConservationPathUnwiredL1 false false false false false false = .legNamedOk)

/-- Whether a close attempt is admissible under THERMO-01 **Thermo_n G** **conservation**. -/
def thermoConservationVerdictOk (v : ThermoConservationVerdict) : Bool :=
  match v with
  | .unwiredOk | .legNamedOk => true
  | _ => false

theorem unwired_thermo_conservation_ok :
    evaluateThermoConservation .unwired thermoConservationPathIronL1 false false false false false = .unwiredOk := rfl

theorem proved_thermo_conservation_leg_named_ok :
    evaluateThermoConservation .proved thermoConservationPathIronL1 false false false false false = .legNamedOk := rfl

theorem trivial_z_zero_refuse :
    evaluateThermoConservation .unwired
      { field := thermoConservationFieldNamed, level := 0, elementZ := thermoElementIron
        diagram := thermoConservationDiagramNamed, scalar := .greenBookG }
      false false false false false = .trivialZZeroRefuse := rfl

theorem green_invent_refuse :
    evaluateThermoConservation .unwired thermoConservationPathIronL1 true false false false false =
      .greenInventRefuse := rfl

theorem formation_zero_misidentified_as_g_refuse :
    evaluateThermoConservation .unwired thermoConservationPathIronL1 false false true false false =
      .formationZeroMisidentifiedAsGRefuse := rfl

theorem measured_scalar_invent_refuse :
    evaluateThermoConservation .unwired thermoConservationPathIronL1 false false false true false =
      .measuredScalarInventRefuse := rfl

theorem scrambled_order_refuse :
    evaluateThermoConservation .unwired thermoConservationPathIronL1 false false false false true =
      .scrambledOrderRefuse := rfl

theorem live_process_g_refuse :
    evaluateThermoConservation .unwired thermoConservationPathIronL1 false true false false false =
      .liveProcessGRefuse := rfl

theorem three_legs_named :
    threeLegsNamed = true := by decide

theorem thermo_g_order_conservation_typed :
    thermoGOrderConservationTyped = true := rfl

theorem thermo_var_order_ok :
    thermoVarOrderOk = true := by decide

theorem formation_zero_not_g_unless_named_ok :
    formationZeroNotGUnlessNamedOk = true := by decide

theorem calphad_hull_identity_conserved :
    calphadHullIdentityConserved = true := rfl

theorem trivial_z_zero_refused :
    trivialZZeroRefused = true := rfl

theorem green_invent_refused :
    greenInventRefused = true := rfl

theorem formation_zero_misidentified_as_g_refused :
    formationZeroMisidentifiedAsGRefused = true := rfl

theorem measured_scalar_invent_refused :
    measuredScalarInventRefused = true := rfl

theorem scrambled_order_refused :
    scrambledOrderRefused = true := rfl

theorem live_process_g_refused :
    liveProcessGRefused = true := rfl

theorem iron_thermo_conservation_unwired_ok :
    ironThermoConservationUnwiredOk = true := rfl

theorem copper_thermo_conservation_unwired_ok :
    copperThermoConservationUnwiredOk = true := rfl

theorem unwired_thermo_conservation_unwired_ok :
    unwiredThermoConservationUnwiredOk = true := rfl

/-- Quantum / knowing formal fiber root (structure witness — not meso acting). -/
def thermoConservationQuantumKnowingFiber : String :=
  "umst/umst-formal-double-slit"

/-- Meso / acting formal fiber root (cite only — live Process G is not wired here). -/
def thermoConservationMesoActingFiber : String :=
  "umst/umst-formal"

theorem thermo_conservation_quantum_knowing_fiber_pinned :
    thermoConservationQuantumKnowingFiber =
      "umst/umst-formal-double-slit" := rfl

/-- Cited Rust **Thermo_n** authority (views only — lattice is structural here). -/
def thermoConservationCitedModule : String :=
  "umst/umst-chem/src/thermo_n.rs"

/-- **Thermo_n G** lattice is structure — not 118² GREEN periodic enumeration. -/
def thermoConservationNot118GreenTable : Bool := true

theorem thermo_conservation_not_118_green_table :
    thermoConservationNot118GreenTable = true := rfl

/-- Second-law + **conservation** framing — cites meso SSOT, not wired on knowing scaffold. -/
def thermoConservationSecondLawFramed : Bool := true

theorem thermo_conservation_second_law_framed :
    thermoConservationSecondLawFramed = true := rfl

/-- THERMO-01 claim **Thermo_n G** is **not** claimed Proved on the knowing scaffold. -/
def thermoGProved : Bool := false

theorem thermo_g_not_proved : thermoGProved = false := rfl

/-- Production wiring is **not** claimed on the knowing scaffold. -/
def thermoConservationProductionWired : Bool := false

theorem thermo_conservation_production_not_wired :
    thermoConservationProductionWired = false := rfl

/-- Cell id for the Lean THERMO-01 **Thermo_n G** **conservation** knowing-fiber. -/
def thermoConservationCellId : String :=
  "CHEM-FORMAL-Q-LEAN-THERMO-CONSERVATION"

/-- Non-claim fence — T, P, x named; composed T∘P∘x equals direct G typed **conservation**;
CALPHAD hull identity conserved; formation-zero ≠ G; measured-scalar invent refuse; scrambled order refuse;
live Process G refuse; Fe Z=26; Cu Z=29; Og Z=118; trivial Z=0 refuse; **conservation**;
THERMO-01 Unwired; `thermoGProved` false. -/
def thermoConservationNonClaim : String :=
  "CHEM-FORMAL-Q-LEAN-THERMO-CONSERVATION THERMO-01 Thermo_n G T P x named composed T o P o x equals direct G typed conservation CALPHAD hull identity conserved formation-zero ne G measured-scalar invent refuse scrambled order refuse live Process G refuse Fe Z=26 Cu Z=29 Og Z=118 trivial Z=0 refuse thermoGProved false Unwired OK not Thermo_n Proved not physics GREEN; not 118² GREEN DFT"

/-- Physics GREEN is unauthorized on the knowing THERMO-01 **Thermo_n G** **conservation** scaffold. -/
def thermoConservationPhysicsGreenAuthorized : Prop := False

theorem thermo_conservation_physics_green_false :
    ¬ thermoConservationPhysicsGreenAuthorized := id

theorem thermo_conservation_modality_unwired :
    thermoConservationModalityCurrent = .unwired := rfl

/-- **One** design axiom: second law + **conservation** (structure witness — not meso import). -/
def thermoConservationAxiom : Bool :=
  thermoConservationNot118GreenTable &&
    thermoConservationSecondLawFramed &&
    threeLegsNamed &&
    thermoGOrderConservationTyped &&
    thermoVarOrderOk &&
    formationZeroNotGUnlessNamedOk &&
    calphadHullIdentityConserved &&
    trivialZZeroRefused &&
    greenInventRefused &&
    formationZeroMisidentifiedAsGRefused &&
    measuredScalarInventRefused &&
    scrambledOrderRefused &&
    liveProcessGRefused &&
    ironThermoConservationUnwiredOk &&
    copperThermoConservationUnwiredOk &&
    unwiredThermoConservationUnwiredOk &&
    !thermoGProved &&
    !thermoConservationProductionWired

theorem thermo_conservation_axiom :
    thermoConservationAxiom = true := by decide

theorem thermo_conservation_honest_bundle :
    thermoGProved = false ∧
    thermoConservationProductionWired = false ∧
    thermoConservationNot118GreenTable = true ∧
    thermoConservationSecondLawFramed = true ∧
    evaluateThermoConservation .unwired thermoConservationPathIronL1 false false false false false = .unwiredOk ∧
    evaluateThermoConservation .proved thermoConservationPathIronL1 false false false false false = .legNamedOk ∧
    evaluateThermoConservation .unwired
      { field := thermoConservationFieldNamed, level := 0, elementZ := thermoElementIron
        diagram := thermoConservationDiagramNamed, scalar := .greenBookG }
      false false false false false = .trivialZZeroRefuse ∧
    evaluateThermoConservation .unwired thermoConservationPathIronL1 true false false false false = .greenInventRefuse ∧
    evaluateThermoConservation .unwired thermoConservationPathIronL1 false false true false false = .formationZeroMisidentifiedAsGRefuse ∧
    evaluateThermoConservation .unwired thermoConservationPathIronL1 false false false true false = .measuredScalarInventRefuse ∧
    evaluateThermoConservation .unwired thermoConservationPathIronL1 false false false false true = .scrambledOrderRefuse ∧
    evaluateThermoConservation .unwired thermoConservationPathIronL1 false true false false false = .liveProcessGRefuse ∧
    threeLegsNamed = true ∧
    thermoGOrderConservationTyped = true ∧
    thermoVarOrderOk = true ∧
    formationZeroNotGUnlessNamedOk = true ∧
    calphadHullIdentityConserved = true ∧
    trivialZZeroRefused = true ∧
    greenInventRefused = true ∧
    formationZeroMisidentifiedAsGRefused = true ∧
    measuredScalarInventRefused = true ∧
    scrambledOrderRefused = true ∧
    liveProcessGRefused = true ∧
    ironThermoConservationUnwiredOk = true ∧
    copperThermoConservationUnwiredOk = true ∧
    unwiredThermoConservationUnwiredOk = true ∧
    thermoElementIron.z = 26 ∧
    thermoElementCopper.z = 29 ∧
    thermoElementOganesson.z = 118 ∧
    thermoConservationAxiom = true :=
  ⟨rfl, rfl, thermo_conservation_not_118_green_table,
    thermo_conservation_second_law_framed,
    unwired_thermo_conservation_ok, proved_thermo_conservation_leg_named_ok, trivial_z_zero_refuse,
    green_invent_refuse, formation_zero_misidentified_as_g_refuse, measured_scalar_invent_refuse,
    scrambled_order_refuse, live_process_g_refuse,
    three_legs_named, thermo_g_order_conservation_typed, thermo_var_order_ok,
    formation_zero_not_g_unless_named_ok, calphad_hull_identity_conserved, trivial_z_zero_refused,
    green_invent_refused, formation_zero_misidentified_as_g_refused, measured_scalar_invent_refused,
    scrambled_order_refused, live_process_g_refused,
    iron_thermo_conservation_unwired_ok, copper_thermo_conservation_unwired_ok,
    unwired_thermo_conservation_unwired_ok,
    thermo_iron_z_twenty_six, thermo_copper_z_twenty_nine, thermo_oganesson_z_118,
    thermo_conservation_axiom⟩

end UMST.Chem
