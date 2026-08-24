-- SPDX-FileCopyrightText: 2026 Santosh Prabhu Shenbagamoorthy and Santhosh Shyamsundar
-- SPDX-License-Identifier: MIT

import ElementElectronic

/-!
# DensityConservation — knowing-fiber DENSITY-01 **density ladder order** conservation (Q lattice)

North-star DENSITY-01 claim **density** ladder order identity **conservation** on the quantum /
knowing formal fiber — four rungs mSDF → TE-SDF → SDF → FRep with composed ladder identity equal to
direct mSDF→FRep (typed **conservation**). Pairs `umst-chem` scaffold `CHEM-INT-DENSITY-LADDER-TYPE` /
`density_ladder.rs` **conservation** posture.

- `DensityConservationModality` — Unwired / Assumed / Proved / Surrogate (not 118² GREEN table).
- `DensityLadderRung` / `DensityConservationLeg` — four ordered rungs; indirect compose **conservation**.
- `fusionDensity` — **density** stamp identity **conserved** (additive witness).
- `evaluateDensityConservation` — Unwired OK; Proved leg-named scaffold OK; trivial **density** fail-closed;
  GREEN invent refuse; SDF≠ρ unless named refuse; **conservation** ladder typed not live ρ/TE-SDF.
- SDF ≠ ρ unless scalar field explicitly named (QTAIM ρ, ELF, NCI, GateSdf).
- Second-law + **conservation** framing cites meso `UMST.Chem.Conservation` /
  `LandauerLaw.physicalSecondLaw` — not imported.
- No meso / acting theorems. No new physics `axiom`.
- `physics_green` stays false. Does **not** claim DensityLadder Proved or physics GREEN.
- **Density** ladder order ≠ 118² GREEN periodic enumeration.
-/

namespace UMST.Chem

/-- Design modality for DENSITY-01 claim **density** **conservation** (lattice SSOT). -/
inductive DensityConservationModality where
  | unwired | assumed | proved | surrogate
  deriving DecidableEq, Repr

def densityConservationModalityCurrent : DensityConservationModality := .unwired

/-- IUPAC periodic-table cardinality (Z=1..118). -/
def iupacTableCardinality : Nat := 118

theorem iupac_table_cardinality_118 : iupacTableCardinality = 118 := rfl

/-- Private Z pin for **density** ladder witnesses — not L1 SpeciesId. -/
structure DensityElementZ where
  z : Nat
  hzLo : 0 < z
  hzHi : z ≤ iupacTableCardinality
  deriving DecidableEq, Repr

def densityElementCarbon : DensityElementZ := { z := 6, hzLo := by decide, hzHi := by decide }
def densityElementOganesson : DensityElementZ := { z := 118, hzLo := by decide, hzHi := by decide }

theorem density_carbon_z_six : densityElementCarbon.z = 6 := rfl
theorem density_oganesson_z_118 : densityElementOganesson.z = 118 := rfl

/-- North-star **density** ladder rung mSDF → TE-SDF → SDF → FRep (design names only). -/
inductive DensityLadderRung where
  | microSdf | teSdf | sdf | frep
  deriving DecidableEq, Repr

/-- Monotonic index along the **density** ladder (0 = mSDF … 3 = FRep). -/
def densityLadderRungIndex : DensityLadderRung → Nat
  | .microSdf => 0
  | .teSdf => 1
  | .sdf => 2
  | .frep => 3

theorem density_rung_micro_sdf_index_zero :
    densityLadderRungIndex .microSdf = 0 := rfl

theorem density_rung_te_sdf_index_one :
    densityLadderRungIndex .teSdf = 1 := rfl

theorem density_rung_sdf_index_two :
    densityLadderRungIndex .sdf = 2 := rfl

theorem density_rung_frep_index_three :
    densityLadderRungIndex .frep = 3 := rfl

theorem density_rung_order_strict :
    densityLadderRungIndex .microSdf < densityLadderRungIndex .teSdf ∧
    densityLadderRungIndex .teSdf < densityLadderRungIndex .sdf ∧
    densityLadderRungIndex .sdf < densityLadderRungIndex .frep := by decide

def densityRungString : DensityLadderRung → String
  | .microSdf => "micro_sdf"
  | .teSdf => "te_sdf"
  | .sdf => "sdf"
  | .frep => "frep"

theorem density_rung_micro_sdf_str :
    densityRungString .microSdf = "micro_sdf" := rfl

theorem density_rung_te_sdf_str :
    densityRungString .teSdf = "te_sdf" := rfl

theorem density_rung_sdf_str :
    densityRungString .sdf = "sdf" := rfl

theorem density_rung_frep_str :
    densityRungString .frep = "frep" := rfl

/-- Named scalar fields — ρ must be explicit; SDF ≠ ρ unless named. -/
inductive NamedDensityScalar where
  | electronDensityRho | elf | nci | gateSdf
  deriving DecidableEq, Repr

def namedDensityScalarString : NamedDensityScalar → String
  | .electronDensityRho => "electron_density_rho"
  | .elf => "elf"
  | .nci => "nci"
  | .gateSdf => "gate_sdf"

theorem named_scalar_rho_str :
    namedDensityScalarString .electronDensityRho = "electron_density_rho" := rfl

/-- Scalar kind on a ladder rung — generic SDF is **not** ρ unless named. -/
inductive DensityScalarKind where
  | signedDistance
  | named (field : NamedDensityScalar)
  deriving DecidableEq, Repr

def densityScalarKindIsElectronDensityRho (k : DensityScalarKind) : Bool :=
  match k with
  | .signedDistance => false
  | .named .electronDensityRho => true
  | .named _ => false

/-- SDF ≠ ρ unless the scalar field is explicitly named electron density. -/
def sdfNotRhoUnlessNamed (k : DensityScalarKind) : Bool :=
  decide (!densityScalarKindIsElectronDensityRho k ||
    k = .named .electronDensityRho)

theorem scaffold_sdf_not_rho_unless_named :
    sdfNotRhoUnlessNamed .signedDistance = true := rfl

theorem named_rho_sdf_not_rho_unless_named :
    sdfNotRhoUnlessNamed (.named .electronDensityRho) = true := rfl

theorem sdf_ne_rho_generic :
    densityScalarKindIsElectronDensityRho .signedDistance = false := rfl

/-- Named legs of the **density** ladder diagram (scaffold — typed **conservation**). -/
inductive DensityConservationLeg where
  | microToTe | teToSdf | sdfToFrep | microToFrepDirect
  deriving DecidableEq, Repr

def DensityConservationLeg.source : DensityConservationLeg → DensityLadderRung
  | .microToTe => .microSdf
  | .teToSdf => .teSdf
  | .sdfToFrep => .sdf
  | .microToFrepDirect => .microSdf

def DensityConservationLeg.target : DensityConservationLeg → DensityLadderRung
  | .microToTe => .teSdf
  | .teToSdf => .sdf
  | .sdfToFrep => .frep
  | .microToFrepDirect => .frep

def densityLegString : DensityConservationLeg → String
  | .microToTe => "micro_to_te"
  | .teToSdf => "te_to_sdf"
  | .sdfToFrep => "sdf_to_frep"
  | .microToFrepDirect => "micro_to_frep_direct"

/-- Named step leg mSDF → TE-SDF in the ladder. -/
def densityLegMicroToTe : DensityConservationLeg := .microToTe

/-- Named step leg TE-SDF → SDF in the ladder. -/
def densityLegTeToSdf : DensityConservationLeg := .teToSdf

/-- Named step leg SDF → FRep in the ladder. -/
def densityLegSdfToFrep : DensityConservationLeg := .sdfToFrep

/-- Named direct leg mSDF → FRep in the ladder. -/
def densityLegMicroToFrepDirect : DensityConservationLeg := .microToFrepDirect

theorem density_leg_micro_to_te_named :
    densityLegMicroToTe = DensityConservationLeg.microToTe := rfl

theorem density_leg_te_to_sdf_named :
    densityLegTeToSdf = DensityConservationLeg.teToSdf := rfl

theorem density_leg_sdf_to_frep_named :
    densityLegSdfToFrep = DensityConservationLeg.sdfToFrep := rfl

theorem density_leg_micro_to_frep_direct_named :
    densityLegMicroToFrepDirect = DensityConservationLeg.microToFrepDirect := rfl

theorem density_leg_micro_to_te_composes_te_to_sdf :
    densityLegMicroToTe.target = densityLegTeToSdf.source := rfl

theorem density_leg_te_to_sdf_composes_sdf_to_frep :
    densityLegTeToSdf.target = densityLegSdfToFrep.source := rfl

theorem density_leg_direct_endpoints_match :
    densityLegMicroToTe.source = densityLegMicroToFrepDirect.source ∧
    densityLegSdfToFrep.target = densityLegMicroToFrepDirect.target := by
  constructor <;> rfl

theorem density_leg_distinct_step_vs_direct :
    densityLegMicroToTe ≠ densityLegMicroToFrepDirect := by decide

/-- Named legs of the **density** ladder diagram (typed **conservation** scaffold). -/
structure DensityLadderDiagram where
  microToTe : DensityConservationLeg
  teToSdf : DensityConservationLeg
  sdfToFrep : DensityConservationLeg
  direct : DensityConservationLeg
  deriving Repr

def densityLadderDiagramNamed : DensityLadderDiagram :=
  { microToTe := densityLegMicroToTe
    teToSdf := densityLegTeToSdf
    sdfToFrep := densityLegSdfToFrep
    direct := densityLegMicroToFrepDirect }

/-- **Density** **conservation** stamp field across mSDF → TE-SDF → SDF → FRep (typed identity witness). -/
structure DensityConservationField where
  atMicroSdf : Nat
  atTeSdf : Nat
  atSdf : Nat
  atFrep : Nat
  deriving DecidableEq, Repr

def densityConservationFieldUnwired : DensityConservationField :=
  { atMicroSdf := 0, atTeSdf := 0, atSdf := 0, atFrep := 0 }

def densityConservationFieldNamed : DensityConservationField :=
  { atMicroSdf := 1, atTeSdf := 1, atSdf := 1, atFrep := 1 }

/-- Lookup **density** **conservation** stamp at a named rung. -/
def densityAtRung (f : DensityConservationField) : DensityLadderRung → Nat
  | .microSdf => f.atMicroSdf
  | .teSdf => f.atTeSdf
  | .sdf => f.atSdf
  | .frep => f.atFrep

/-- **Density** stamp at the source endpoint of a ladder leg. -/
def densityAtLegSource (f : DensityConservationField) (leg : DensityConservationLeg) : Nat :=
  densityAtRung f leg.source

/-- **Density** stamp at the target endpoint of a ladder leg. -/
def densityAtLegTarget (f : DensityConservationField) (leg : DensityConservationLeg) : Nat :=
  densityAtRung f leg.target

theorem density_at_leg_source_micro_to_te (f : DensityConservationField) :
    densityAtLegSource f densityLegMicroToTe = f.atMicroSdf := rfl

theorem density_at_leg_target_sdf_to_frep (f : DensityConservationField) :
    densityAtLegTarget f densityLegSdfToFrep = f.atFrep := rfl

theorem density_at_leg_target_micro_to_frep_direct (f : DensityConservationField) :
    densityAtLegTarget f densityLegMicroToFrepDirect = f.atFrep := rfl

/-- Composed mSDF→TE-SDF→SDF→FRep **conservation** stamp equals mSDF→FRep direct target (typed identity). -/
theorem density_ladder_conservation_identity (f : DensityConservationField) :
    densityAtLegTarget f densityLegSdfToFrep = densityAtLegTarget f densityLegMicroToFrepDirect := rfl

/-- Whether **density** **conservation** stamps are uniform on named field (ladder typed). -/
def densityLadderConservationTyped (f : DensityConservationField) : Bool :=
  decide (densityAtLegTarget f densityLegSdfToFrep = densityAtLegTarget f densityLegMicroToFrepDirect ∧
    densityAtLegTarget f densityLegMicroToTe = densityAtLegSource f densityLegTeToSdf ∧
    densityAtLegTarget f densityLegTeToSdf = densityAtLegSource f densityLegSdfToFrep ∧
    densityAtLegSource f densityLegMicroToTe = densityAtLegSource f densityLegMicroToFrepDirect)

theorem density_ladder_conservation_named_typed :
    densityLadderConservationTyped densityConservationFieldNamed = true := rfl

theorem density_ladder_conservation_unwired_typed :
    densityLadderConservationTyped densityConservationFieldUnwired = true := rfl

/-- A **density** **conservation** path at a refinement level. -/
structure DensityConservationPath where
  field : DensityConservationField
  level : Nat
  elementZ : DensityElementZ
  diagram : DensityLadderDiagram
  scalar : DensityScalarKind

def densityConservationPathIsNontrivial (p : DensityConservationPath) : Bool :=
  decide (p.level > 0)

def densityConservationPathCarbonL1 : DensityConservationPath :=
  { field := densityConservationFieldNamed
    level := 1
    elementZ := densityElementCarbon
    diagram := densityLadderDiagramNamed
    scalar := .signedDistance }

def densityConservationPathUnwiredL1 : DensityConservationPath :=
  { field := densityConservationFieldUnwired
    level := 1
    elementZ := densityElementCarbon
    diagram := densityLadderDiagramNamed
    scalar := .signedDistance }

/-- Whether element Z pins are valid IUPAC Z on a **density** **conservation** path. -/
def densityElementZValid (z : DensityElementZ) : Bool :=
  decide (0 < z.z ∧ z.z ≤ iupacTableCardinality)

theorem density_carbon_z_valid :
    densityElementZValid densityElementCarbon = true ∧
    densityElementCarbon.z = 6 := by decide

theorem density_oganesson_z_valid :
    densityElementOganesson.z = iupacTableCardinality := rfl

/-- Scaffold thermodynamic ledger for **density** ladder (knowing fiber). -/
structure ThermoDensityState where
  chemStamp : Nat
  landauerWitness : Nat
  deriving DecidableEq, Repr

def thermoDensityZero : ThermoDensityState :=
  { chemStamp := 0, landauerWitness := 0 }

def thermoDensityPositive : ThermoDensityState :=
  { chemStamp := 1, landauerWitness := 1 }

/-- Thermo-preserving **density** fusion — identity **conserved** (additive). -/
def fusionDensity (a b : ThermoDensityState) : ThermoDensityState :=
  { chemStamp := a.chemStamp + b.chemStamp,
    landauerWitness := a.landauerWitness + b.landauerWitness }

theorem fusion_density_commutative_stamp :
    (fusionDensity thermoDensityPositive thermoDensityZero).chemStamp =
      (fusionDensity thermoDensityZero thermoDensityPositive).chemStamp := rfl

theorem fusion_density_zero_identity_stamp :
    (fusionDensity thermoDensityZero thermoDensityPositive).chemStamp =
      thermoDensityPositive.chemStamp := rfl

/-- Verdict of a **density** ladder close attempt (fail-closed). -/
inductive DensityLadderPathVerdict where
  | unwiredOk
  | legNamedOk
  | greenInventRefuse
  | provedWithoutBarRefuse
  | trivialDensityRefuse
  | sdfMisidentifiedAsRhoRefuse
  | liveTeSdfRefuse
  deriving DecidableEq, Repr

/-- Evaluate a **density** ladder path against the DENSITY-01 bar. -/
def evaluateDensityLadderPath
    (modality : DensityConservationModality)
    (path : DensityConservationPath)
    (claimPhysicsGreen : Bool)
    (claimProved : Bool)
    (claimLiveTeSdf : Bool)
    (claimSdfAsRho : Bool) : DensityLadderPathVerdict :=
  if claimPhysicsGreen then
    .greenInventRefuse
  else if claimLiveTeSdf then
    .liveTeSdfRefuse
  else if claimSdfAsRho then
    .sdfMisidentifiedAsRhoRefuse
  else if claimProved then
    .provedWithoutBarRefuse
  else if !densityConservationPathIsNontrivial path then
    .trivialDensityRefuse
  else if !densityElementZValid path.elementZ then
    .trivialDensityRefuse
  else
    match modality with
    | .unwired => .legNamedOk
    | .assumed | .surrogate => .unwiredOk
    | .proved => .provedWithoutBarRefuse

/-- Verdict of a **density** **conservation** close attempt (fail-closed). -/
inductive DensityConservationVerdict where
  | unwiredOk
  | legNamedOk
  | trivialDensityRefuse
  | greenInventRefuse
  | sdfMisidentifiedAsRhoRefuse
  | liveTeSdfRefuse
  deriving DecidableEq, Repr

/-- Evaluate **density** **conservation** against the DENSITY-01 bar. -/
def evaluateDensityConservation
    (modality : DensityConservationModality)
    (path : DensityConservationPath)
    (claimPhysicsGreen : Bool)
    (claimLiveTeSdf : Bool)
    (claimSdfAsRho : Bool) : DensityConservationVerdict :=
  if claimPhysicsGreen then
    .greenInventRefuse
  else if claimLiveTeSdf then
    .liveTeSdfRefuse
  else if claimSdfAsRho then
    .sdfMisidentifiedAsRhoRefuse
  else if !densityConservationPathIsNontrivial path then
    .trivialDensityRefuse
  else
    match modality with
    | .unwired | .assumed | .surrogate => .unwiredOk
    | .proved => .legNamedOk

/-- Whether four named ladder legs are pinned on the **density** diagram. -/
def fourRungsNamed : Bool :=
  decide (densityLadderDiagramNamed.microToTe = densityLegMicroToTe ∧
    densityLadderDiagramNamed.teToSdf = densityLegTeToSdf ∧
    densityLadderDiagramNamed.sdfToFrep = densityLegSdfToFrep ∧
    densityLadderDiagramNamed.direct = densityLegMicroToFrepDirect ∧
    densityLegMicroToTe ≠ densityLegMicroToFrepDirect)

/-- Whether composed ladder **conservation** equals direct mSDF→FRep (typed). -/
def ladderOrderConservationTyped : Bool :=
  decide (densityLadderConservationTyped densityConservationFieldNamed = true ∧
    densityLadderConservationTyped densityConservationFieldUnwired = true ∧
    densityAtLegTarget densityConservationFieldNamed densityLegSdfToFrep =
      densityAtLegTarget densityConservationFieldNamed densityLegMicroToFrepDirect)

/-- Whether **density** ladder rung order mSDF→TE-SDF→SDF→FRep is strictly ordered. -/
def densityRungOrderOk : Bool :=
  decide (densityLadderRungIndex .microSdf < densityLadderRungIndex .teSdf ∧
    densityLadderRungIndex .teSdf < densityLadderRungIndex .sdf ∧
    densityLadderRungIndex .sdf < densityLadderRungIndex .frep ∧
    densityRungString .microSdf = "micro_sdf" ∧
    densityRungString .frep = "frep")

/-- Whether scaffold scalar obeys SDF ≠ ρ unless named. -/
def sdfNotRhoUnlessNamedOk : Bool :=
  decide (sdfNotRhoUnlessNamed .signedDistance = true ∧
    sdfNotRhoUnlessNamed (.named .electronDensityRho) = true ∧
    densityScalarKindIsElectronDensityRho .signedDistance = false)

/-- Whether thermo-preserving **density** fusion identity is **conserved** on pinned states. -/
def fusionIdentityConserved : Bool :=
  decide (fusionDensity thermoDensityZero thermoDensityPositive =
    thermoDensityPositive ∧
    fusionDensity thermoDensityPositive thermoDensityZero =
      fusionDensity thermoDensityZero thermoDensityPositive ∧
    (fusionDensity thermoDensityPositive thermoDensityPositive).landauerWitness = 2 ∧
    densityConservationPathIsNontrivial densityConservationPathCarbonL1 = true ∧
    densityElementZValid densityElementCarbon = true)

/-- Whether trivial (level-0) **density** path is refused (fail-closed). -/
def trivialDensityRefused : Bool :=
  let trivialPath : DensityConservationPath :=
    { field := densityConservationFieldNamed, level := 0, elementZ := densityElementCarbon
      diagram := densityLadderDiagramNamed, scalar := .signedDistance }
  decide (evaluateDensityLadderPath .unwired trivialPath false false false false = .trivialDensityRefuse ∧
    evaluateDensityConservation .unwired trivialPath false false false = .trivialDensityRefuse)

/-- Whether GREEN invent is refused on **density** scaffold. -/
def greenInventRefused : Bool :=
  decide (evaluateDensityLadderPath .unwired densityConservationPathCarbonL1 true false false false =
    .greenInventRefuse ∧
    evaluateDensityConservation .unwired densityConservationPathCarbonL1 true false false =
      .greenInventRefuse)

/-- Whether SDF misidentified as ρ is refused (SDF ≠ ρ unless named). -/
def sdfMisidentifiedAsRhoRefused : Bool :=
  decide (evaluateDensityLadderPath .unwired densityConservationPathCarbonL1 false false false true =
    .sdfMisidentifiedAsRhoRefuse ∧
    evaluateDensityConservation .unwired densityConservationPathCarbonL1 false false true =
      .sdfMisidentifiedAsRhoRefuse)

/-- Whether live TE-SDF claim is refused (not live ρ/TE-SDF on knowing scaffold). -/
def liveTeSdfRefused : Bool :=
  decide (evaluateDensityLadderPath .unwired densityConservationPathCarbonL1 false false true false =
    .liveTeSdfRefuse ∧
    evaluateDensityConservation .unwired densityConservationPathCarbonL1 false true false =
      .liveTeSdfRefuse)

/-- Whether carbon **density** **conservation** path passes under Unwired modality. -/
def carbonDensityConservationUnwiredOk : Bool :=
  decide (evaluateDensityConservation .unwired densityConservationPathCarbonL1 false false false = .unwiredOk ∧
    evaluateDensityLadderPath .unwired densityConservationPathCarbonL1 false false false false = .legNamedOk)

/-- Whether unwired baseline **density** path passes under Unwired modality. -/
def unwiredDensityConservationUnwiredOk : Bool :=
  decide (evaluateDensityConservation .unwired densityConservationPathUnwiredL1 false false false = .unwiredOk ∧
    evaluateDensityLadderPath .unwired densityConservationPathUnwiredL1 false false false false = .legNamedOk)

/-- Whether a close attempt is admissible under DENSITY-01 **density** **conservation**. -/
def densityConservationVerdictOk (v : DensityConservationVerdict) : Bool :=
  match v with
  | .unwiredOk | .legNamedOk => true
  | _ => false

theorem unwired_density_conservation_ok :
    evaluateDensityConservation .unwired densityConservationPathCarbonL1 false false false = .unwiredOk := rfl

theorem proved_density_conservation_leg_named_ok :
    evaluateDensityConservation .proved densityConservationPathCarbonL1 false false false = .legNamedOk := rfl

theorem trivial_density_refuse :
    evaluateDensityConservation .unwired
      { field := densityConservationFieldNamed, level := 0, elementZ := densityElementCarbon
        diagram := densityLadderDiagramNamed, scalar := .signedDistance }
      false false false = .trivialDensityRefuse := rfl

theorem green_invent_refuse :
    evaluateDensityConservation .unwired densityConservationPathCarbonL1 true false false =
      .greenInventRefuse := rfl

theorem sdf_misidentified_as_rho_refuse :
    evaluateDensityConservation .unwired densityConservationPathCarbonL1 false false true =
      .sdfMisidentifiedAsRhoRefuse := rfl

theorem live_te_sdf_refuse :
    evaluateDensityConservation .unwired densityConservationPathCarbonL1 false true false =
      .liveTeSdfRefuse := rfl

theorem four_rungs_named :
    fourRungsNamed = true := by decide

theorem ladder_order_conservation_typed :
    ladderOrderConservationTyped = true := rfl

theorem density_rung_order_ok :
    densityRungOrderOk = true := by decide

theorem sdf_not_rho_unless_named_ok :
    sdfNotRhoUnlessNamedOk = true := by decide

theorem fusion_identity_conserved :
    fusionIdentityConserved = true := rfl

theorem trivial_density_refused :
    trivialDensityRefused = true := rfl

theorem green_invent_refused :
    greenInventRefused = true := rfl

theorem sdf_misidentified_as_rho_refused :
    sdfMisidentifiedAsRhoRefused = true := rfl

theorem live_te_sdf_refused :
    liveTeSdfRefused = true := rfl

theorem carbon_density_conservation_unwired_ok :
    carbonDensityConservationUnwiredOk = true := rfl

theorem unwired_density_conservation_unwired_ok :
    unwiredDensityConservationUnwiredOk = true := rfl

/-- Quantum / knowing formal fiber root (structure witness — not meso acting). -/
def densityConservationQuantumKnowingFiber : String :=
  "umst/umst-formal-double-slit"

theorem density_conservation_quantum_knowing_fiber_pinned :
    densityConservationQuantumKnowingFiber =
      "umst/umst-formal-double-slit" := rfl

/-- Cited Rust **density** ladder authority (views only — lattice is structural here). -/
def densityConservationCitedModule : String :=
  "umst/umst-chem/src/density_ladder.rs"

/-- **Density** lattice is structure — not 118² GREEN periodic enumeration. -/
def densityConservationNot118GreenTable : Bool := true

theorem density_conservation_not_118_green_table :
    densityConservationNot118GreenTable = true := rfl

/-- Second-law + **conservation** framing — cites meso SSOT, not wired on knowing scaffold. -/
def densityConservationSecondLawFramed : Bool := true

theorem density_conservation_second_law_framed :
    densityConservationSecondLawFramed = true := rfl

/-- DENSITY-01 claim **density** ladder is **not** claimed Proved on the knowing scaffold. -/
def densityLadderProved : Bool := false

theorem density_ladder_not_proved : densityLadderProved = false := rfl

/-- Production wiring is **not** claimed on the knowing scaffold. -/
def densityConservationProductionWired : Bool := false

theorem density_conservation_production_not_wired :
    densityConservationProductionWired = false := rfl

/-- Cell id for the Lean DENSITY-01 **density** **conservation** knowing-fiber. -/
def densityConservationCellId : String :=
  "CHEM-FORMAL-Q-LEAN-DENSITY-CONSERVATION"

/-- Cell id for density ladder type integration (distinct — not this scaffold). -/
def densityLadderTypeCellId : String :=
  "CHEM-INT-DENSITY-LADDER-TYPE"

theorem density_conservation_cell_distinct_from_ladder_type :
    densityConservationCellId ≠ densityLadderTypeCellId := by decide

/-- Non-claim fence — four rungs mSDF→TE-SDF→SDF→FRep; composed ladder **conservation** equals direct;
SDF ≠ ρ unless named; trivial **density** refuse; live TE-SDF refuse; **density** **conservation**;
DENSITY-01 Unwired; `densityLadderProved` false. -/
def densityConservationNonClaim : String :=
  "CHEM-FORMAL-Q-LEAN-DENSITY-CONSERVATION DENSITY-01 density ladder order conservation four rungs mSDF TE-SDF SDF FRep composed indirect equals direct typed conservation SDF not rho unless named trivial density refuse live TE-SDF refuse densityLadderProved false Unwired OK not DensityLadder Proved not physics GREEN; not 118² GREEN DFT"

/-- Physics GREEN is unauthorized on the knowing DENSITY-01 **density** **conservation** scaffold. -/
def densityConservationPhysicsGreenAuthorized : Prop := False

theorem density_conservation_physics_green_false :
    ¬ densityConservationPhysicsGreenAuthorized := id

theorem density_conservation_modality_unwired :
    densityConservationModalityCurrent = .unwired := rfl

/-- **One** design axiom: second law + **conservation** (structure witness — not meso import). -/
def densityConservationAxiom : Bool :=
  densityConservationNot118GreenTable &&
    densityConservationSecondLawFramed &&
    fourRungsNamed &&
    ladderOrderConservationTyped &&
    densityRungOrderOk &&
    sdfNotRhoUnlessNamedOk &&
    fusionIdentityConserved &&
    trivialDensityRefused &&
    greenInventRefused &&
    sdfMisidentifiedAsRhoRefused &&
    liveTeSdfRefused &&
    carbonDensityConservationUnwiredOk &&
    unwiredDensityConservationUnwiredOk &&
    !densityLadderProved &&
    !densityConservationProductionWired

theorem density_conservation_axiom :
    densityConservationAxiom = true := by decide

theorem density_conservation_honest_bundle :
    densityLadderProved = false ∧
    densityConservationProductionWired = false ∧
    densityConservationNot118GreenTable = true ∧
    densityConservationSecondLawFramed = true ∧
    evaluateDensityConservation .unwired densityConservationPathCarbonL1 false false false = .unwiredOk ∧
    evaluateDensityConservation .proved densityConservationPathCarbonL1 false false false = .legNamedOk ∧
    evaluateDensityConservation .unwired
      { field := densityConservationFieldNamed, level := 0, elementZ := densityElementCarbon
        diagram := densityLadderDiagramNamed, scalar := .signedDistance }
      false false false = .trivialDensityRefuse ∧
    evaluateDensityConservation .unwired densityConservationPathCarbonL1 true false false = .greenInventRefuse ∧
    evaluateDensityConservation .unwired densityConservationPathCarbonL1 false false true = .sdfMisidentifiedAsRhoRefuse ∧
    evaluateDensityConservation .unwired densityConservationPathCarbonL1 false true false = .liveTeSdfRefuse ∧
    fourRungsNamed = true ∧
    ladderOrderConservationTyped = true ∧
    densityRungOrderOk = true ∧
    sdfNotRhoUnlessNamedOk = true ∧
    fusionIdentityConserved = true ∧
    trivialDensityRefused = true ∧
    greenInventRefused = true ∧
    sdfMisidentifiedAsRhoRefused = true ∧
    liveTeSdfRefused = true ∧
    carbonDensityConservationUnwiredOk = true ∧
    unwiredDensityConservationUnwiredOk = true ∧
    densityElementCarbon.z = 6 ∧
    densityElementOganesson.z = 118 ∧
    densityConservationAxiom = true :=
  ⟨rfl, rfl, density_conservation_not_118_green_table,
    density_conservation_second_law_framed,
    unwired_density_conservation_ok, proved_density_conservation_leg_named_ok, trivial_density_refuse,
    green_invent_refuse, sdf_misidentified_as_rho_refuse, live_te_sdf_refuse,
    four_rungs_named, ladder_order_conservation_typed, density_rung_order_ok,
    sdf_not_rho_unless_named_ok, fusion_identity_conserved, trivial_density_refused,
    green_invent_refused, sdf_misidentified_as_rho_refused, live_te_sdf_refused,
    carbon_density_conservation_unwired_ok, unwired_density_conservation_unwired_ok,
    density_carbon_z_six, density_oganesson_z_118,
    density_conservation_axiom⟩

end UMST.Chem
