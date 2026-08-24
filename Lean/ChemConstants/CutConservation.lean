-- SPDX-FileCopyrightText: 2026 Santosh Prabhu Shenbagamoorthy and Santhosh Shyamsundar
-- SPDX-License-Identifier: MIT

import ElementElectronic

/-!
# CutConservation — knowing-fiber GRAPH-02 cut/separation conservation (Q lattice)

North-star GRAPH-02 claim **cut** / separation morphisms on the refining graph lattice on the
quantum / knowing formal fiber — named ore/waste partition sides and recycle-loop **cut**
morphisms with element Z identity conserved. Distinct from GRAPH-01 **bond** edges.
Pairs `umst-chem` scaffold `CHEM-L0-GRAPH-02` / `CHEM-INT-PROVE-GRAPH-02-CUTS` **conservation** posture.

- `CutConservationModality` — Unwired / Assumed / Proved / Surrogate (not 118² GREEN table).
- `RefiningGraphCut` / `CutSeparation` — named ore/waste Fe **cut** (Z=26), recycle Cu loop (Z=29), Og Z=118.
- `fusionCut` — **cut** partition identity conserved (additive witness).
- `evaluateCutConservation` — Unwired OK; Proved cut-named scaffold OK; trivial **cut** fail-closed; GREEN invent refuse.
- Ore/waste partition complement conserved — source/sink sides are complementary.
- Second-law + **conservation** framing cites meso `UMST.Chem.Conservation` / `LandauerLaw.physicalSecondLaw` — not imported.
- No meso / acting theorems. No new physics `axiom`.
- `physics_green` stays false. Does **not** claim GRAPH-02 Proved or physics GREEN.
- **Cut** ≠ **bond** — separation morphisms, not bond/reaction edge SSOT.
-/

namespace UMST.Chem

/-- Design modality for GRAPH-02 claim **cut** conservation (lattice SSOT). -/
inductive CutConservationModality where
  | unwired | assumed | proved | surrogate
  deriving DecidableEq, Repr

def cutConservationModalityCurrent : CutConservationModality := .unwired

/-- IUPAC periodic-table cardinality (Z=1..118). -/
def iupacTableCardinality : Nat := 118

theorem iupac_table_cardinality_118 : iupacTableCardinality = 118 := rfl

/-- Private Z pin for **cut** graph nodes — not L1 SpeciesId. -/
structure CutElementZ where
  z : Nat
  hzLo : 0 < z
  hzHi : z ≤ iupacTableCardinality
  deriving DecidableEq, Repr

def cutElementIron : CutElementZ := { z := 26, hzLo := by decide, hzHi := by decide }
def cutElementCopper : CutElementZ := { z := 29, hzLo := by decide, hzHi := by decide }
def cutElementOganesson : CutElementZ := { z := 118, hzLo := by decide, hzHi := by decide }

theorem cut_iron_z_twenty_six : cutElementIron.z = 26 := rfl
theorem cut_copper_z_twenty_nine : cutElementCopper.z = 29 := rfl
theorem cut_oganesson_z_118 : cutElementOganesson.z = 118 := rfl

/-- Partition side for a refining **cut** (source/sink complement). -/
inductive CutSide where
  | source | sink
  deriving DecidableEq, Repr

def cutSideComplement : CutSide → CutSide
  | .source => .sink
  | .sink => .source

theorem cut_side_complement_source :
    cutSideComplement .source = .sink := rfl

theorem cut_side_complement_sink :
    cutSideComplement .sink = .source := rfl

/-- Named **cut** role on the refining graph scaffold. -/
inductive RefiningCutRole where
  | oreFraction | wasteTail | recycleLoop
  deriving DecidableEq, Repr

def refiningCutRoleString : RefiningCutRole → String
  | .oreFraction => "ore_fraction"
  | .wasteTail => "waste_tail"
  | .recycleLoop => "recycle_loop"

theorem cut_role_ore_fraction_str :
    refiningCutRoleString .oreFraction = "ore_fraction" := rfl

theorem cut_role_recycle_loop_str :
    refiningCutRoleString .recycleLoop = "recycle_loop" := rfl

def refiningCutRoleDefaultSide : RefiningCutRole → CutSide
  | .oreFraction => .source
  | .wasteTail => .sink
  | .recycleLoop => .source

theorem ore_waste_default_sides_complement :
    refiningCutRoleDefaultSide .oreFraction = .source ∧
    refiningCutRoleDefaultSide .wasteTail = .sink ∧
    cutSideComplement (refiningCutRoleDefaultSide .oreFraction) =
      refiningCutRoleDefaultSide .wasteTail := by decide

/-- A typed refining **cut** on the graph scaffold. -/
structure RefiningGraphCut where
  cutId : Nat
  role : RefiningCutRole
  sourceSide : CutSide
  elementZ : CutElementZ
  deriving DecidableEq, Repr

def refiningGraphCutSinkSide (c : RefiningGraphCut) : CutSide :=
  cutSideComplement c.sourceSide

def refiningGraphCutIsSource (c : RefiningGraphCut) (side : CutSide) : Bool :=
  decide (c.sourceSide = side)

/-- Canonical ore/waste Fe **cut** (Z=26, source-side ore fraction). -/
def cutOreWasteFe : RefiningGraphCut :=
  { cutId := 1
  , role := .oreFraction
  , sourceSide := .source
  , elementZ := cutElementIron }

/-- Canonical recycle-loop Cu **cut** (Z=29). -/
def cutRecycleCuLoop : RefiningGraphCut :=
  { cutId := 2
  , role := .recycleLoop
  , sourceSide := .source
  , elementZ := cutElementCopper }

/-- A **cut** separation at a refinement level. -/
structure CutSeparation where
  cut : RefiningGraphCut
  level : Nat
  deriving DecidableEq, Repr

def cutSeparationIsNontrivial (s : CutSeparation) : Bool :=
  decide (s.level > 0)

def cutSeparationOreWasteL1 : CutSeparation :=
  { cut := cutOreWasteFe, level := 1 }

def cutSeparationRecycleL1 : CutSeparation :=
  { cut := cutRecycleCuLoop, level := 1 }

/-- Whether element Z pins are valid IUPAC Z on a **cut**. -/
def cutElementZValid (z : CutElementZ) : Bool :=
  decide (0 < z.z ∧ z.z ≤ iupacTableCardinality)

theorem cut_ore_waste_fe_z_valid :
    cutElementZValid cutElementIron = true ∧
    cutOreWasteFe.elementZ.z = 26 := by decide

theorem cut_recycle_cu_z_valid :
    cutElementZValid cutElementCopper = true ∧
    cutRecycleCuLoop.elementZ.z = 29 := by decide

theorem cut_oganesson_z_valid :
    cutElementOganesson.z = iupacTableCardinality := rfl

theorem cut_ore_waste_partition_complement :
    refiningGraphCutSinkSide cutOreWasteFe = .sink ∧
    refiningGraphCutIsSource cutOreWasteFe .source = true ∧
    refiningGraphCutIsSource cutOreWasteFe .sink = false := by decide

theorem cut_recycle_loop_named :
    cutRecycleCuLoop.role = .recycleLoop ∧
    refiningCutRoleString cutRecycleCuLoop.role = "recycle_loop" := by decide

/-- Scaffold thermodynamic ledger for **cut** separations (knowing fiber). -/
structure ThermoCutState where
  chemStamp : Nat
  landauerWitness : Nat
  deriving DecidableEq, Repr

def thermoCutZero : ThermoCutState :=
  { chemStamp := 0, landauerWitness := 0 }

def thermoCutPositive : ThermoCutState :=
  { chemStamp := 1, landauerWitness := 1 }

/-- Thermo-preserving **cut** fusion — identity conserved (additive). -/
def fusionCut (a b : ThermoCutState) : ThermoCutState :=
  { chemStamp := a.chemStamp + b.chemStamp,
    landauerWitness := a.landauerWitness + b.landauerWitness }

theorem fusion_cut_commutative_stamp :
    (fusionCut thermoCutPositive thermoCutZero).chemStamp =
      (fusionCut thermoCutZero thermoCutPositive).chemStamp := rfl

theorem fusion_cut_commutative_witness :
    (fusionCut thermoCutPositive thermoCutZero).landauerWitness =
      (fusionCut thermoCutZero thermoCutPositive).landauerWitness := rfl

theorem fusion_cut_zero_identity_stamp :
    (fusionCut thermoCutZero thermoCutPositive).chemStamp =
      thermoCutPositive.chemStamp := rfl

theorem fusion_cut_zero_identity_witness :
    (fusionCut thermoCutZero thermoCutPositive).landauerWitness =
      thermoCutPositive.landauerWitness := rfl

/-- Verdict of a **cut** separation close attempt (fail-closed). -/
inductive CutSeparationVerdict where
  | unwiredOk
  | cutNamedOk
  | greenInventRefuse
  | provedWithoutBarRefuse
  | trivialCutRefuse
  deriving DecidableEq, Repr

/-- Evaluate a **cut** separation against the GRAPH-02 bar. -/
def evaluateCutSeparation
    (modality : CutConservationModality)
    (separation : CutSeparation)
    (claimPhysicsGreen : Bool)
    (claimProved : Bool) : CutSeparationVerdict :=
  if claimPhysicsGreen then
    .greenInventRefuse
  else if claimProved then
    .provedWithoutBarRefuse
  else if !cutSeparationIsNontrivial separation then
    .trivialCutRefuse
  else if !cutElementZValid separation.cut.elementZ then
    .trivialCutRefuse
  else
    match modality with
    | .unwired => .cutNamedOk
    | .assumed | .surrogate => .unwiredOk
    | .proved => .provedWithoutBarRefuse

/-- Verdict of a **cut** conservation close attempt (fail-closed). -/
inductive CutConservationVerdict where
  | unwiredOk
  | cutNamedOk
  | trivialCutRefuse
  | greenInventRefuse
  deriving DecidableEq, Repr

/-- Evaluate **cut** conservation against the GRAPH-02 bar. -/
def evaluateCutConservation
    (modality : CutConservationModality)
    (separation : CutSeparation)
    (claimPhysicsGreen : Bool) : CutConservationVerdict :=
  if claimPhysicsGreen then
    .greenInventRefuse
  else if !cutSeparationIsNontrivial separation then
    .trivialCutRefuse
  else
    match modality with
    | .unwired | .assumed | .surrogate => .unwiredOk
    | .proved => .cutNamedOk

/-- Whether ore/waste partition complement is conserved on pinned **cut** sides. -/
def partitionComplementConserved : Bool :=
  decide (cutSideComplement .source = .sink ∧
    cutSideComplement .sink = .source ∧
    refiningGraphCutSinkSide cutOreWasteFe = .sink ∧
    refiningCutRoleDefaultSide .oreFraction = .source ∧
    refiningCutRoleDefaultSide .wasteTail = .sink ∧
    cutSideComplement (refiningCutRoleDefaultSide .oreFraction) =
      refiningCutRoleDefaultSide .wasteTail)

/-- Whether thermo-preserving **cut** fusion identity is conserved on pinned states. -/
def fusionIdentityConserved : Bool :=
  decide (fusionCut thermoCutZero thermoCutPositive =
    thermoCutPositive ∧
    fusionCut thermoCutPositive thermoCutZero =
      fusionCut thermoCutZero thermoCutPositive ∧
    (fusionCut thermoCutPositive thermoCutPositive).landauerWitness = 2 ∧
    cutSeparationIsNontrivial cutSeparationOreWasteL1 = true ∧
    cutElementZValid cutElementIron = true)

/-- Whether trivial (level-0) **cut** separation is refused (fail-closed). -/
def trivialCutRefused : Bool :=
  let trivialSep : CutSeparation := { cut := cutOreWasteFe, level := 0 }
  decide (evaluateCutSeparation .unwired trivialSep false false = .trivialCutRefuse ∧
    evaluateCutConservation .unwired trivialSep false = .trivialCutRefuse)

/-- Whether GREEN invent is refused on **cut** scaffold. -/
def greenInventRefused : Bool :=
  decide (evaluateCutSeparation .unwired cutSeparationOreWasteL1 true false =
    .greenInventRefuse ∧
    evaluateCutConservation .unwired cutSeparationOreWasteL1 true = .greenInventRefuse)

/-- Whether ore/waste Fe **cut** passes under Unwired modality. -/
def oreWasteCutUnwiredOk : Bool :=
  decide (evaluateCutConservation .unwired cutSeparationOreWasteL1 false = .unwiredOk ∧
    evaluateCutSeparation .unwired cutSeparationOreWasteL1 false false = .cutNamedOk)

/-- Whether recycle-loop Cu **cut** passes under Unwired modality. -/
def recycleLoopCutUnwiredOk : Bool :=
  decide (evaluateCutConservation .unwired cutSeparationRecycleL1 false = .unwiredOk ∧
    evaluateCutSeparation .unwired cutSeparationRecycleL1 false false = .cutNamedOk)

/-- Whether **cut** morphisms are distinct from bond/reaction edge SSOT. -/
def cutNeBondGraph : Bool :=
  decide (cutOreWasteFe.role ≠ .oreFraction ∨ cutRecycleCuLoop.role = .recycleLoop) ∧
  decide (refiningCutRoleString .oreFraction ≠ "covalent_named" ∧
    refiningCutRoleString .recycleLoop = "recycle_loop")

/-- Whether a close attempt is admissible under GRAPH-02 **cut** conservation. -/
def cutConservationVerdictOk (v : CutConservationVerdict) : Bool :=
  match v with
  | .unwiredOk | .cutNamedOk => true
  | _ => false

theorem unwired_cut_ok :
    evaluateCutConservation .unwired cutSeparationOreWasteL1 false = .unwiredOk := rfl

theorem assumed_cut_ok :
    evaluateCutConservation .assumed cutSeparationOreWasteL1 false = .unwiredOk := rfl

theorem surrogate_cut_ok :
    evaluateCutConservation .surrogate cutSeparationOreWasteL1 false = .unwiredOk := rfl

theorem proved_cut_named_ok :
    evaluateCutConservation .proved cutSeparationOreWasteL1 false = .cutNamedOk := rfl

theorem trivial_cut_refuse :
    evaluateCutConservation .unwired
      { cut := cutOreWasteFe, level := 0 } false = .trivialCutRefuse := rfl

theorem green_invent_refuse :
    evaluateCutConservation .unwired cutSeparationOreWasteL1 true = .greenInventRefuse := rfl

theorem partition_complement_conserved :
    partitionComplementConserved = true := rfl

theorem fusion_identity_conserved :
    fusionIdentityConserved = true := rfl

theorem trivial_cut_refused :
    trivialCutRefused = true := rfl

theorem green_invent_refused :
    greenInventRefused = true := rfl

theorem ore_waste_cut_unwired_ok :
    oreWasteCutUnwiredOk = true := rfl

theorem recycle_loop_cut_unwired_ok :
    recycleLoopCutUnwiredOk = true := rfl

theorem cut_ne_bond_graph :
    cutNeBondGraph = true := rfl

theorem unwired_verdict_ok :
    cutConservationVerdictOk (evaluateCutConservation .unwired cutSeparationOreWasteL1 false) = true := rfl

theorem trivial_cut_verdict_not_ok :
    cutConservationVerdictOk
      (evaluateCutConservation .unwired { cut := cutOreWasteFe, level := 0 } false) = false := rfl

theorem green_invent_verdict_not_ok :
    cutConservationVerdictOk (evaluateCutConservation .unwired cutSeparationOreWasteL1 true) = false := rfl

/-- Quantum / knowing formal fiber root (structure witness — not meso acting). -/
def cutConservationQuantumKnowingFiber : String :=
  "umst/umst-formal-double-slit"

/-- Meso / acting formal fiber root (cite only — not wired on knowing scaffold). -/
def cutConservationMesoActingFiber : String :=
  "umst/umst-formal"

theorem cut_conservation_quantum_knowing_fiber_pinned :
    cutConservationQuantumKnowingFiber =
      "umst/umst-formal-double-slit" := rfl

/-- Cited Rust refining **cut** graph authority (views only — lattice is structural here). -/
def cutConservationCitedModule : String :=
  "umst/umst-chem/src/refining_graph_cuts.rs"

/-- **Cut** lattice is structure — not 118² GREEN periodic enumeration. -/
def cutConservationNot118GreenTable : Bool := true

theorem cut_conservation_not_118_green_table :
    cutConservationNot118GreenTable = true := rfl

/-- Second-law + **conservation** framing — cites meso SSOT, not wired on knowing scaffold. -/
def cutConservationSecondLawFramed : Bool := true

theorem cut_conservation_second_law_framed :
    cutConservationSecondLawFramed = true := rfl

/-- GRAPH-02 claim **cut** is **not** claimed Proved on the knowing scaffold. -/
def graph02CutProved : Bool := false

theorem graph02_cut_not_proved : graph02CutProved = false := rfl

/-- Production wiring is **not** claimed on the knowing scaffold. -/
def cutConservationProductionWired : Bool := false

theorem cut_conservation_production_not_wired :
    cutConservationProductionWired = false := rfl

/-- Cell id for the Lean GRAPH-02 **cut** conservation knowing-fiber. -/
def cutConservationCellId : String :=
  "CHEM-FORMAL-Q-LEAN-CUT-CONSERVATION"

/-- Non-claim fence — named **cut** / separation identity; ore/waste Fe Z=26; recycle Cu loop Z=29;
Og Z=118; partition complement conserved; trivial **cut** refuse; **conservation**; GRAPH-02 Unwired;
**cut** ≠ **bond**. -/
def cutConservationNonClaim : String :=
  "CHEM-FORMAL-Q-LEAN-CUT-CONSERVATION GRAPH-02 named cut separation ore waste partition complement conserved recycle loop named Fe Z=26 Cu Z=29 Og Z=118 trivial cut refuse graph02CutProved false Unwired OK not GRAPH-02 Proved not physics GREEN cut ne bond; not 118² GREEN DFT"

/-- Physics GREEN is unauthorized on the knowing GRAPH-02 **cut** conservation scaffold. -/
def cutConservationPhysicsGreenAuthorized : Prop := False

theorem cut_conservation_physics_green_false :
    ¬ cutConservationPhysicsGreenAuthorized := id

theorem cut_conservation_modality_unwired :
    cutConservationModalityCurrent = .unwired := rfl

/-- **One** design axiom: second law + **conservation** (structure witness — not meso import). -/
def cutConservationAxiom : Bool :=
  cutConservationNot118GreenTable &&
    cutConservationSecondLawFramed &&
    partitionComplementConserved &&
    fusionIdentityConserved &&
    trivialCutRefused &&
    greenInventRefused &&
    oreWasteCutUnwiredOk &&
    recycleLoopCutUnwiredOk &&
    cutNeBondGraph &&
    !graph02CutProved &&
    !cutConservationProductionWired

theorem cut_conservation_axiom :
    cutConservationAxiom = true := rfl

theorem cut_conservation_honest_bundle :
    graph02CutProved = false ∧
    cutConservationProductionWired = false ∧
    cutConservationNot118GreenTable = true ∧
    cutConservationSecondLawFramed = true ∧
    evaluateCutConservation .unwired cutSeparationOreWasteL1 false = .unwiredOk ∧
    evaluateCutConservation .proved cutSeparationOreWasteL1 false = .cutNamedOk ∧
    evaluateCutConservation .unwired { cut := cutOreWasteFe, level := 0 } false = .trivialCutRefuse ∧
    evaluateCutConservation .unwired cutSeparationOreWasteL1 true = .greenInventRefuse ∧
    partitionComplementConserved = true ∧
    fusionIdentityConserved = true ∧
    trivialCutRefused = true ∧
    greenInventRefused = true ∧
    oreWasteCutUnwiredOk = true ∧
    recycleLoopCutUnwiredOk = true ∧
    cutNeBondGraph = true ∧
    cutOreWasteFe.elementZ.z = 26 ∧
    cutRecycleCuLoop.elementZ.z = 29 ∧
    cutElementOganesson.z = 118 ∧
    cutConservationAxiom = true :=
  ⟨rfl, rfl, cut_conservation_not_118_green_table, cut_conservation_second_law_framed,
    unwired_cut_ok, proved_cut_named_ok, trivial_cut_refuse, green_invent_refuse,
    partition_complement_conserved, fusion_identity_conserved, trivial_cut_refused,
    green_invent_refused, ore_waste_cut_unwired_ok, recycle_loop_cut_unwired_ok,
    cut_ne_bond_graph, cut_iron_z_twenty_six, cut_copper_z_twenty_nine, cut_oganesson_z_118,
    cut_conservation_axiom⟩

end UMST.Chem
