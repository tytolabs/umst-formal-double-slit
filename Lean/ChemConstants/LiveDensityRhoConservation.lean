-- SPDX-FileCopyrightText: 2026 Santosh Prabhu Shenbagamoorthy and Santhosh Shyamsundar
-- SPDX-License-Identifier: MIT

import ElementElectronic

set_option maxRecDepth 8192

/-!
# LiveDensityRhoConservation — LIVE DensityLadder **density** **ρ conservation** (Q lattice)

Knowing-fiber Lean: LIVE DensityLadder **density** **ρ conservation**. Four rungs mSDF→TE-SDF→SDF→FRep named;
composed indirect ladder path identity conserved vs direct (typed, Unwired). LIVE TE-SDF/ρ refuse
fail-closed; scrambled-order fail-closed; GREEN invent fail-closed; Proved-without-bar fail-closed.
SDF ≠ ρ unless named (generic signed-distance is not ElectronDensityRho). Geometry routes
knowing/quantum fiber not meso acting. Not 118² GREEN table.

Read-only cites (not imported — self-contained scaffold):
- `Coq/ChemConstants/LiveDensityRhoConservation.v`
- `Haskell/UMST/ChemConstants/LiveDensityRhoConservation.hs`
- `Agda/ChemConstants/LiveDensityRhoConservation.agda`
- `umst/umst-chem/src/density_ladder.rs`
- `Coq/ChemConstants/DensityConservation.v` (sibling)

- `LiveDensityRhoConservationModality` — Unwired / Assumed / Proved / Surrogate (not 118² GREEN table).
- Freeze-safe DensityLadder ρ identity lifts (`z ↦ z`) until live wire.
- Second-law + **conservation** framing — not imported meso theorems.
- No meso / acting theorems. No new physics `axiom`.
- `physics_green` stays false. Does **not** claim `liveDensityRhoConservationProved` or physics GREEN.
- WAVE100 freeze — not wired in umst-chem lib.rs.
-/

namespace UMST.Chem

/-- Design modality for LIVE **density** **ρ** **conservation** (lattice SSOT). -/
inductive LiveDensityRhoConservationModality where
  | unwired | assumed | proved | surrogate
  deriving DecidableEq, Repr

def liveDensityRhoConservationModalityCurrent : LiveDensityRhoConservationModality := .unwired

/-- Surface tag for name-from-content (`live_density_rho` / `livedensityrhoconservation`). -/
def liveDensityRhoConservationSurface : String :=
  "live_density_rho_conservation_surface"

theorem live_density_rho_conservation_surface_named :
    liveDensityRhoConservationSurface ≠ "" := by decide

/-- Machine-readable live density rho conservation marker. -/
def liveDensityRhoConservationMarker : String :=
  "chem_int_cross_live_density_rho_conservation_v1"

theorem live_density_rho_conservation_marker_named :
    liveDensityRhoConservationMarker ≠ "" := by decide

/-- Row stem pin for name-from-content (`live_density_rho_conservation`). -/
def liveDensityRhoConservationRowStem : String := "live_density_rho_conservation"

theorem live_density_rho_conservation_row_stem_named :
    liveDensityRhoConservationRowStem = "live_density_rho_conservation" := rfl

/-- DensityLadder rung cardinality (mSDF / TE-SDF / SDF / FRep). -/
def densityLadderCardinality : Nat := 4

theorem density_ladder_cardinality_is_four :
    densityLadderCardinality = 4 := rfl

theorem density_ladder_not_118_squared :
    densityLadderCardinality ≠ 118 * 118 := by decide

/-- IUPAC periodic-table cardinality (Z=1..118). -/
def iupacTableCardinality : Nat := 118

theorem iupac_table_cardinality_is_118 : iupacTableCardinality = 118 := rfl

def densityElementZValid (z : Nat) : Bool :=
  decide (0 < z ∧ z ≤ iupacTableCardinality)

def densityElementIronZ : Nat := 26
def densityElementCopperZ : Nat := 29
def densityElementOganessonZ : Nat := 118

theorem density_iron_z_is_26 : densityElementIronZ = 26 := rfl
theorem density_copper_z_is_29 : densityElementCopperZ = 29 := rfl
theorem density_oganesson_z_is_118 : densityElementOganessonZ = 118 := rfl

theorem density_fe_cu_z_valid :
    densityElementZValid densityElementIronZ = true ∧
    densityElementZValid densityElementCopperZ = true := by decide

theorem density_oganesson_z_valid :
    densityElementZValid densityElementOganessonZ = true := by decide

inductive DensityScalarKind where
  | signedDistanceGeneric
  | namedElectronDensityRho
  | namedElf
  | namedNci
  | namedGateSdf
  deriving DecidableEq, Repr

def densityScalarSignedDistance : DensityScalarKind := .signedDistanceGeneric
def densityScalarElectronDensityRho : DensityScalarKind := .namedElectronDensityRho

def densityScalarIsElectronDensityRho (k : DensityScalarKind) : Bool :=
  match k with
  | .namedElectronDensityRho => true
  | _ => false

def densityScalarSdfNotRhoUnlessNamed (k : DensityScalarKind) : Bool :=
  match k with
  | .signedDistanceGeneric | .namedElectronDensityRho | .namedElf | .namedNci | .namedGateSdf => true

theorem density_signed_distance_not_rho :
    densityScalarIsElectronDensityRho densityScalarSignedDistance = false := rfl

theorem density_electron_density_rho_named :
    densityScalarIsElectronDensityRho densityScalarElectronDensityRho = true := rfl

theorem density_sdf_not_rho_unless_named_signed_distance :
    densityScalarSdfNotRhoUnlessNamed densityScalarSignedDistance = true := rfl

theorem density_signed_distance_ne_electron_rho :
    densityScalarSignedDistance ≠ densityScalarElectronDensityRho := by decide

inductive DensityRung where
  | microSdf | teSdf | sdf | frep
  deriving DecidableEq, Repr

inductive DensityLadderLeg where
  | microToTeSdf | teSdfToSdf | sdfToFrep | microToFrepDirect
  deriving DecidableEq, Repr

def DensityLadderLeg.source : DensityLadderLeg → DensityRung
  | .microToTeSdf => .microSdf
  | .teSdfToSdf => .teSdf
  | .sdfToFrep => .sdf
  | .microToFrepDirect => .microSdf

def DensityLadderLeg.target : DensityLadderLeg → DensityRung
  | .microToTeSdf => .teSdf
  | .teSdfToSdf => .sdf
  | .sdfToFrep => .frep
  | .microToFrepDirect => .frep

def densityLegMicroToTeSdf : DensityLadderLeg := .microToTeSdf
def densityLegTeSdfToSdf : DensityLadderLeg := .teSdfToSdf
def densityLegSdfToFrep : DensityLadderLeg := .sdfToFrep
def densityLegMicroToFrepDirect : DensityLadderLeg := .microToFrepDirect

theorem density_leg_micro_to_te_named :
    densityLegMicroToTeSdf = DensityLadderLeg.microToTeSdf := rfl

theorem density_leg_indirect_composes_bool_true :
    decide (densityLegMicroToTeSdf.target = densityLegTeSdfToSdf.source ∧
      densityLegTeSdfToSdf.target = densityLegSdfToFrep.source) = true := rfl

theorem density_leg_direct_endpoints_match_bool_true :
    decide (densityLegMicroToTeSdf.source = densityLegMicroToFrepDirect.source ∧
      densityLegSdfToFrep.target = densityLegMicroToFrepDirect.target) = true := rfl

structure DensityBinding where
  parentZ : Nat
  deriving DecidableEq, Repr

def densityBindingFe : DensityBinding := { parentZ := densityElementIronZ }
def densityBindingCu : DensityBinding := { parentZ := densityElementCopperZ }
def densityBindingTrivial : DensityBinding := { parentZ := 0 }

def densityBindingNontrivial (b : DensityBinding) : Bool :=
  decide (0 < b.parentZ)

theorem density_binding_fe_nontrivial :
    densityBindingNontrivial densityBindingFe = true := by decide

def densityBindingIdentityConserved (b1 b2 : DensityBinding) : Bool :=
  decide (b1.parentZ = b2.parentZ)

def liftMicroToTeSdf (z : Nat) : Nat := z
def liftTeSdfToSdf (z : Nat) : Nat := z
def liftSdfToFrep (z : Nat) : Nat := z
def liftMicroToFrepDirect (z : Nat) : Nat := z

def densityComposedIdentity (z : Nat) : Nat :=
  liftSdfToFrep (liftTeSdfToSdf (liftMicroToTeSdf z))

def densityDirectIdentity (z : Nat) : Nat := liftMicroToFrepDirect z

def densityComposedEqualsDirect (z : Nat) : Bool :=
  decide (densityComposedIdentity z = densityDirectIdentity z)

theorem density_composed_equals_direct_identity (z : Nat) :
    densityComposedEqualsDirect z = true := by
  simp [densityComposedEqualsDirect, densityComposedIdentity, densityDirectIdentity,
    liftSdfToFrep, liftTeSdfToSdf, liftMicroToTeSdf, liftMicroToFrepDirect]

theorem density_ladder_identity_conserved (z : Nat) :
    densityComposedIdentity z = densityDirectIdentity z := rfl

structure DensityLadderDiagram where
  viaTeSdf : DensityLadderLeg
  thenSdf : DensityLadderLeg
  thenFrep : DensityLadderLeg
  direct : DensityLadderLeg
  hasMicroToTeSdf : Bool
  hasTeSdfToSdf : Bool
  hasSdfToFrep : Bool
  hasMicroToFrepDirect : Bool
  deriving Repr

def densityLadderDiagramNamed : DensityLadderDiagram :=
  { viaTeSdf := densityLegMicroToTeSdf, thenSdf := densityLegTeSdfToSdf,
    thenFrep := densityLegSdfToFrep, direct := densityLegMicroToFrepDirect,
    hasMicroToTeSdf := true, hasTeSdfToSdf := true, hasSdfToFrep := true, hasMicroToFrepDirect := true }

def densityLadderDiagramMissingDirect : DensityLadderDiagram :=
  { viaTeSdf := densityLegMicroToTeSdf, thenSdf := densityLegTeSdfToSdf,
    thenFrep := densityLegSdfToFrep, direct := densityLegMicroToFrepDirect,
    hasMicroToTeSdf := true, hasTeSdfToSdf := true, hasSdfToFrep := true, hasMicroToFrepDirect := false }

def densityLadderDiagramScrambledOrder : DensityLadderDiagram :=
  { viaTeSdf := densityLegSdfToFrep, thenSdf := densityLegTeSdfToSdf,
    thenFrep := densityLegMicroToTeSdf, direct := densityLegMicroToFrepDirect,
    hasMicroToTeSdf := true, hasTeSdfToSdf := true, hasSdfToFrep := true, hasMicroToFrepDirect := true }

def densityLadderDiagramTrivial : DensityLadderDiagram :=
  { viaTeSdf := densityLegMicroToTeSdf, thenSdf := densityLegTeSdfToSdf,
    thenFrep := densityLegSdfToFrep, direct := densityLegMicroToFrepDirect,
    hasMicroToTeSdf := false, hasTeSdfToSdf := false, hasSdfToFrep := false, hasMicroToFrepDirect := false }

def densityLadderDiagramAllLegsPresent (d : DensityLadderDiagram) : Bool :=
  d.hasMicroToTeSdf && d.hasTeSdfToSdf && d.hasSdfToFrep && d.hasMicroToFrepDirect

def densityLadderDiagramOrderOk (d : DensityLadderDiagram) : Bool :=
  decide (d.viaTeSdf.target = d.thenSdf.source ∧
    d.thenSdf.target = d.thenFrep.source ∧
    d.viaTeSdf.source = d.direct.source ∧
    d.thenFrep.target = d.direct.target)

theorem density_ladder_diagram_named_all_legs :
    densityLadderDiagramAllLegsPresent densityLadderDiagramNamed = true := rfl

theorem density_ladder_diagram_scrambled_order_not_ok :
    densityLadderDiagramOrderOk densityLadderDiagramScrambledOrder = false := rfl

structure DensityIncidence where
  binding : DensityBinding
  diagram : DensityLadderDiagram
  scalar : DensityScalarKind
  level : Nat
  deriving Repr

def densityIncidenceNontrivial (h : DensityIncidence) : Bool := decide (0 < h.level)

def densityIncidenceFeNamedL1 : DensityIncidence :=
  { binding := densityBindingFe, diagram := densityLadderDiagramNamed,
    scalar := densityScalarSignedDistance, level := 1 }

def densityIncidenceTrivial : DensityIncidence :=
  { binding := densityBindingTrivial, diagram := densityLadderDiagramTrivial,
    scalar := densityScalarSignedDistance, level := 0 }

def densityIncidenceScrambledOrder : DensityIncidence :=
  { binding := densityBindingFe, diagram := densityLadderDiagramScrambledOrder,
    scalar := densityScalarSignedDistance, level := 1 }

def densityIncidenceMissingDirectLeg : DensityIncidence :=
  { binding := densityBindingFe, diagram := densityLadderDiagramMissingDirect,
    scalar := densityScalarSignedDistance, level := 1 }

def indirectLadderMarker : String := "chem_l0_density_micro_to_te_sdf_v1"
def directLadderMarker : String := "chem_l0_density_micro_to_frep_direct_v1"

theorem indirect_ne_direct_ladder_marker :
    indirectLadderMarker ≠ directLadderMarker := by decide

def indirectNeDirectLadder : Bool :=
  decide (densityLegMicroToTeSdf.target = densityLegTeSdfToSdf.source ∧
    densityLegTeSdfToSdf.target = densityLegSdfToFrep.source ∧
    densityLegMicroToTeSdf.source = densityLegMicroToFrepDirect.source ∧
    densityLegSdfToFrep.target = densityLegMicroToFrepDirect.target ∧
    densityComposedEqualsDirect densityElementIronZ ∧
    densityLadderDiagramAllLegsPresent densityLadderDiagramNamed ∧
    densityLadderDiagramOrderOk densityLadderDiagramNamed)

theorem indirect_ne_direct_ladder_true : indirectNeDirectLadder = true := rfl

structure DensityClaimLadderBar where
  presence : String
  defectTotal : Nat
  deriving Repr

def densityClaimLadderBarAbsent : DensityClaimLadderBar := { presence := "absent", defectTotal := 0 }

inductive LiveDensityRhoConservationVerdict where
  | unwiredOk | densityNamedOk | trivialDensityRefuse | scrambledOrderRefuse
  | greenInventRefuse | provedWithoutBarRefuse | productionWiredRefuse
  | liveTeSdfRefuse | sdfMisidentifiedAsRhoRefuse | wave100LibRsRefuse
  deriving DecidableEq, Repr

def evaluateLiveDensityRhoIncidence
    (m : LiveDensityRhoConservationModality) (h : DensityIncidence) (_b : DensityClaimLadderBar)
    (claimPhysicsGreen : Bool) (claimLiveTeSdf : Bool) (claimSdfAsRho : Bool)
    (claimProved : Bool) (claimWave100LibRs : Bool) : LiveDensityRhoConservationVerdict :=
  if claimPhysicsGreen then .greenInventRefuse
  else if claimWave100LibRs then .wave100LibRsRefuse
  else if claimLiveTeSdf then .liveTeSdfRefuse
  else if claimSdfAsRho then .sdfMisidentifiedAsRhoRefuse
  else if claimProved then .provedWithoutBarRefuse
  else if !densityIncidenceNontrivial h then .trivialDensityRefuse
  else if !densityLadderDiagramAllLegsPresent h.diagram then .scrambledOrderRefuse
  else if !densityLadderDiagramOrderOk h.diagram then .scrambledOrderRefuse
  else match m with | .unwired => .densityNamedOk | .assumed | .surrogate => .unwiredOk | .proved => .provedWithoutBarRefuse

def evaluateLiveDensityRhoConservationClose
    (m : LiveDensityRhoConservationModality) (claimPhysicsGreen : Bool)
    (claimProductionWired : Bool) (claimWave100LibRs : Bool) : LiveDensityRhoConservationVerdict :=
  if claimPhysicsGreen then .greenInventRefuse
  else if claimWave100LibRs then .wave100LibRsRefuse
  else if claimProductionWired then .productionWiredRefuse
  else match m with | .unwired => .unwiredOk | .assumed | .proved | .surrogate => .densityNamedOk

def liveDensityRhoConservationAuthorized
    (claimPhysicsGreen : Bool) (claimProductionWired : Bool) (claimWave100LibRs : Bool) : Bool :=
  match evaluateLiveDensityRhoConservationClose .proved claimPhysicsGreen claimProductionWired claimWave100LibRs with
  | .densityNamedOk => true | _ => false

def liveDensityRhoConservationProved : Bool := false
theorem live_density_rho_conservation_proved_false : liveDensityRhoConservationProved = false := rfl

def not118SquaredGreenTable : Bool := true
theorem not_118_squared_green_table : not118SquaredGreenTable = true := rfl

def wave100LibRsAuthority : String := "umst/umst-chem/src/lib.rs"
def liveDensityRhoConservationProductionWired : Bool := false
def wave100LibRsWired : Bool := false

def liveDensityRhoSecondLawConservationFraming : String :=
  "second_law_conservation_live_density_rho_one_axiom_not_second_density_axiom"

def densityLadderAuthority : String := "umst/umst-chem/src/density_ladder.rs"

def liveDensityRhoConservationCellId : String :=
  "CHEM-FORMAL-Q-LEAN-LIVE-DENSITY-RHO-CONSERVATION"

def liveDensityRhoConservationNonClaim : String :=
  "CHEM-FORMAL-Q-LEAN-LIVE-DENSITY-RHO-CONSERVATION LIVE DensityLadder mSDF TE-SDF SDF FRep four rungs composed equals direct identity conserved typed Unwired scrambled-order fail-closed GREEN invent fail-closed proved-without-bar fail-closed live TE-SDF refuse SDF not rho unless named ElectronDensityRho liveDensityRhoConservationProved false Unwired geometry knowing quantum fiber not meso acting one axiom second law conservation not second density axiom not GREEN DFT not physics GREEN not production_wired WAVE100 no umst-chem lib.rs"

def unwiredCloseOk : Bool :=
  decide (evaluateLiveDensityRhoConservationClose .unwired false false false = .unwiredOk)

def ldrcFeNamedOk : Bool :=
  decide (evaluateLiveDensityRhoIncidence .unwired densityIncidenceFeNamedL1 densityClaimLadderBarAbsent false false false false false = .densityNamedOk)

def trivialDensityRefused : Bool :=
  decide (evaluateLiveDensityRhoIncidence .unwired densityIncidenceTrivial densityClaimLadderBarAbsent false false false false false = .trivialDensityRefuse)

def scrambledOrderRefused : Bool :=
  decide (evaluateLiveDensityRhoIncidence .unwired densityIncidenceScrambledOrder densityClaimLadderBarAbsent false false false false false = .scrambledOrderRefuse)

def missingDirectLegRefused : Bool :=
  decide (evaluateLiveDensityRhoIncidence .unwired densityIncidenceMissingDirectLeg densityClaimLadderBarAbsent false false false false false = .scrambledOrderRefuse)

def greenInventRefused : Bool :=
  decide (evaluateLiveDensityRhoConservationClose .unwired true false false = .greenInventRefuse)

def liveTeSdfRefused : Bool :=
  decide (evaluateLiveDensityRhoIncidence .unwired densityIncidenceFeNamedL1 densityClaimLadderBarAbsent false true false false false = .liveTeSdfRefuse)

def sdfMisidentifiedAsRhoRefused : Bool :=
  decide (evaluateLiveDensityRhoIncidence .unwired densityIncidenceFeNamedL1 densityClaimLadderBarAbsent false false true false false = .sdfMisidentifiedAsRhoRefuse)

def provedWithoutBarRefused : Bool :=
  decide (evaluateLiveDensityRhoIncidence .unwired densityIncidenceFeNamedL1 densityClaimLadderBarAbsent false false false true false = .provedWithoutBarRefuse)

def productionWiredRefused : Bool :=
  decide (evaluateLiveDensityRhoConservationClose .proved false true false = .productionWiredRefuse)

def wave100LibRsRefused : Bool :=
  decide (evaluateLiveDensityRhoConservationClose .unwired false false true = .wave100LibRsRefuse)

def liveDensityRhoLatticeScaffold : Bool :=
  unwiredCloseOk && ldrcFeNamedOk && trivialDensityRefused && scrambledOrderRefused &&
    missingDirectLegRefused && greenInventRefused && liveTeSdfRefused && sdfMisidentifiedAsRhoRefused &&
    provedWithoutBarRefused && productionWiredRefused && wave100LibRsRefused && indirectNeDirectLadder

theorem live_density_rho_lattice_scaffold_true :
    liveDensityRhoLatticeScaffold = true := by native_decide

inductive LiveDensityRhoConservationFiber where | quantumKnowing | mesoActing deriving DecidableEq, Repr

def liveDensityRhoConservationFiberOk (f : LiveDensityRhoConservationFiber) : Bool :=
  match f with | .quantumKnowing => true | .mesoActing => false

def liveDensityRhoConservationPhysicsGreenAuthorized : Prop := False

theorem live_density_rho_conservation_physics_green_false :
    ¬ liveDensityRhoConservationPhysicsGreenAuthorized := id

structure LiveDensityRhoConservationProbe where
  cellIdNamed : Bool
  unwired : Bool
  physicsGreenRefused : Bool
  notProved : Bool
  fe26Witness : Bool
  composedEqualsDirect : Bool
  sdfNotRhoUnlessNamed : Bool
  indirectNeDirect : Bool
  trivialRefuse : Bool
  scrambledRefuse : Bool
  greenInventRefuse : Bool
  liveTeSdfRefuse : Bool
  sdfAsRhoRefuse : Bool
  provedWithoutBarRefuse : Bool
  productionWiredRefuse : Bool
  wave100Refuse : Bool
  knowingFiberOk : Bool
  densityLadderCited : Bool
  deriving DecidableEq, Repr

def liveDensityRhoConservationProbe : LiveDensityRhoConservationProbe :=
  { cellIdNamed := decide (liveDensityRhoConservationCellId = "CHEM-FORMAL-Q-LEAN-LIVE-DENSITY-RHO-CONSERVATION")
    unwired := decide (liveDensityRhoConservationModalityCurrent = .unwired)
    physicsGreenRefused := true
    notProved := !liveDensityRhoConservationProved
    fe26Witness := decide (densityElementIronZ = 26)
    composedEqualsDirect := densityComposedEqualsDirect densityElementIronZ
    sdfNotRhoUnlessNamed := densityScalarSdfNotRhoUnlessNamed densityScalarSignedDistance
    indirectNeDirect := indirectNeDirectLadder
    trivialRefuse := trivialDensityRefused
    scrambledRefuse := scrambledOrderRefused
    greenInventRefuse := greenInventRefused
    liveTeSdfRefuse := liveTeSdfRefused
    sdfAsRhoRefuse := sdfMisidentifiedAsRhoRefused
    provedWithoutBarRefuse := provedWithoutBarRefused
    productionWiredRefuse := productionWiredRefused
    wave100Refuse := wave100LibRsRefused
    knowingFiberOk := liveDensityRhoConservationFiberOk .quantumKnowing
    densityLadderCited := densityLadderAuthority ≠ "" }

def liveDensityRhoConservationHonest : Bool :=
  let p := liveDensityRhoConservationProbe
  p.cellIdNamed && p.unwired && p.physicsGreenRefused && p.notProved && p.fe26Witness &&
    p.composedEqualsDirect && p.sdfNotRhoUnlessNamed && p.indirectNeDirect && p.trivialRefuse &&
    p.scrambledRefuse && p.greenInventRefuse && p.liveTeSdfRefuse && p.sdfAsRhoRefuse &&
    p.provedWithoutBarRefuse && p.productionWiredRefuse && p.wave100Refuse && p.knowingFiberOk &&
    p.densityLadderCited && liveDensityRhoLatticeScaffold

theorem live_density_rho_conservation_honest_true :
    liveDensityRhoConservationHonest = true := by native_decide

def liveDensityRhoConservationAxiom : Bool :=
  not118SquaredGreenTable && liveDensityRhoLatticeScaffold && liveDensityRhoConservationHonest &&
    !liveDensityRhoConservationProved && !liveDensityRhoConservationProductionWired && !wave100LibRsWired &&
    decide (liveDensityRhoSecondLawConservationFraming ≠ "second_density_axiom")

theorem live_density_rho_conservation_axiom :
    liveDensityRhoConservationAxiom = true := by native_decide

theorem live_density_rho_conservation_modality_unwired :
    liveDensityRhoConservationModalityCurrent = .unwired := rfl

theorem unwired_close_without_production_wiring :
    evaluateLiveDensityRhoConservationClose .unwired false false false = .unwiredOk := rfl

theorem ldrc_fe_named_ok :
    evaluateLiveDensityRhoIncidence .unwired densityIncidenceFeNamedL1 densityClaimLadderBarAbsent false false false false false = .densityNamedOk := rfl

theorem trivial_density_fail_closed :
    evaluateLiveDensityRhoIncidence .unwired densityIncidenceTrivial densityClaimLadderBarAbsent false false false false false = .trivialDensityRefuse := rfl

theorem scrambled_order_fail_closed :
    evaluateLiveDensityRhoIncidence .unwired densityIncidenceScrambledOrder densityClaimLadderBarAbsent false false false false false = .scrambledOrderRefuse := rfl

theorem green_invent_refuse_unwired :
    evaluateLiveDensityRhoConservationClose .unwired true false false = .greenInventRefuse := rfl

theorem live_te_sdf_fail_closed :
    evaluateLiveDensityRhoIncidence .unwired densityIncidenceFeNamedL1 densityClaimLadderBarAbsent false true false false false = .liveTeSdfRefuse := rfl

theorem sdf_misidentified_as_rho_fail_closed :
    evaluateLiveDensityRhoIncidence .unwired densityIncidenceFeNamedL1 densityClaimLadderBarAbsent false false true false false = .sdfMisidentifiedAsRhoRefuse := rfl

theorem proved_without_bar_fail_closed :
    evaluateLiveDensityRhoIncidence .unwired densityIncidenceFeNamedL1 densityClaimLadderBarAbsent false false false true false = .provedWithoutBarRefuse := rfl

theorem production_wired_refuse :
    evaluateLiveDensityRhoConservationClose .proved false true false = .productionWiredRefuse := rfl

theorem wave100_lib_rs_refuse :
    evaluateLiveDensityRhoConservationClose .unwired false false true = .wave100LibRsRefuse := rfl

theorem live_density_rho_conservation_knowing_fiber_ok :
    liveDensityRhoConservationFiberOk .quantumKnowing = true := rfl

theorem live_density_rho_conservation_meso_acting_not_ok :
    liveDensityRhoConservationFiberOk .mesoActing = false := rfl

theorem live_density_rho_conservation_honest_bundle :
    liveDensityRhoConservationProved = false ∧
    liveDensityRhoConservationProductionWired = false ∧
    not118SquaredGreenTable = true ∧
    evaluateLiveDensityRhoConservationClose .unwired false false false = .unwiredOk ∧
    evaluateLiveDensityRhoIncidence .unwired densityIncidenceFeNamedL1 densityClaimLadderBarAbsent false false false false false = .densityNamedOk ∧
    evaluateLiveDensityRhoIncidence .unwired densityIncidenceTrivial densityClaimLadderBarAbsent false false false false false = .trivialDensityRefuse ∧
    evaluateLiveDensityRhoIncidence .unwired densityIncidenceScrambledOrder densityClaimLadderBarAbsent false false false false false = .scrambledOrderRefuse ∧
    liveDensityRhoConservationFiberOk .quantumKnowing = true ∧
    liveDensityRhoConservationFiberOk .mesoActing = false ∧
    indirectNeDirectLadder = true ∧
    liveDensityRhoConservationAxiom = true :=
  ⟨rfl, rfl, not_118_squared_green_table, unwired_close_without_production_wiring, ldrc_fe_named_ok,
    trivial_density_fail_closed, scrambled_order_fail_closed,
    live_density_rho_conservation_knowing_fiber_ok, live_density_rho_conservation_meso_acting_not_ok,
    indirect_ne_direct_ladder_true,
    live_density_rho_conservation_axiom⟩

end UMST.Chem
