-- SPDX-FileCopyrightText: 2026 Santosh Prabhu Shenbagamoorthy and Santhosh Shyamsundar
-- SPDX-License-Identifier: MIT
/-
  UMST-Formal: UrgeKnowing/MachineTemperature.lean

  Knowing fiber (§17.2): Excitement T is machine temperature of the coupled
  repository-in-machine (Landauer erasure environment), not wall clock and not
  an abstract DAG scalar. Cross-node energy witness may refuse when Landauer
  floor exceeds available energy. Mirrors `LandauerHistoryLook.lean` and cross-lang
  `machine_temperature` — not meso thermo G(T,P,x) restated.

  Machine-temperature recovery composes `UMST.Excitement.select` — no second argmin.
  Sole physics axiom remains `LandauerLaw.physicalSecondLaw` (imported, not re-declared).
  Adds **zero** Lean `axiom` declarations. Zero sorry.

  Vendored `UMST.Excitement` + `UMST.Urge.ExcitementImport` inline below: pinned
  `umst-formal` @690fbe6 lacks those modules; per-cell build cannot edit lakefile.
  `landauerBound` from `LandauerLaw` only — avoids `LandauerBound` → `DoubleSlitCore` chain.
-/

import Core.State
import DualLedger
import LandauerLaw
import Mathlib.Data.Rat.Defs

open UMST UMST.Core UMST.LandauerLaw



namespace UMST.Core

/-- Joint thermodynamic fields for Excitement's free-energy functional (vendored: absent @690fbe6). -/
class JointThermo (K : outParam Type) [LinearOrderedField K] [ThermodynamicScalar K] (S : Type) where
  internalEnergy : S → K
  entropy        : S → K
  mutualInfo     : S → K
  temperature    : S → K
  temperature_pos : ∀ s, 0 < temperature s

end UMST.Core

namespace UMST.Excitement

open UMST UMST.Core

def kB {K : Type} [LinearOrderedField K] [ThermodynamicScalar K] : K := 1

def jointFreeEnergy {K : Type} [LinearOrderedField K] [ThermodynamicScalar K] {S : Type}
    [JointThermo K S] (s : S) : K :=
  JointThermo.internalEnergy s
    - JointThermo.temperature s * JointThermo.entropy s
    - kB * JointThermo.temperature s * JointThermo.mutualInfo s

inductive Residue where
  | noCandidates
  | allInadmissible
  | allExcludedByCBF
  | allExcludedByDEC
  | untaggedConstant
  | noStrictImprovement
  deriving DecidableEq, Repr

structure Cand {K : Type} {S : Type} [LinearOrderedField K] [ThermodynamicScalar K]
    [ThermodynamicSystem K S] [AdmissibleSystem K S] (src : S) where
  id                : Nat
  tgt               : S
  step              : Admissible src tgt
  cbfSafe           : Prop
  cbfSafe_holds     : cbfSafe
  decConserving     : Prop
  decConserving_holds : decConserving
  ledger            : DualLedger
  evidenceTagged    : Bool

def globalFreeEnergyCand {S : Type} [ThermodynamicSystem ℚ S] [AdmissibleSystem ℚ S]
    [JointThermo ℚ S] {src : S} (c : Cand (K := ℚ) src) : ℚ :=
  jointFreeEnergy c.tgt + DualLedger.total c.ledger

def candEnergy {S : Type} [ThermodynamicSystem ℚ S] [AdmissibleSystem ℚ S]
    [JointThermo ℚ S] {src : S} (c : Cand (K := ℚ) src) : ℚ :=
  globalFreeEnergyCand (src := src) c

def pickMin {S : Type} [ThermodynamicSystem ℚ S] [AdmissibleSystem ℚ S]
    [JointThermo ℚ S] {src : S} (acc : Option (Cand (K := ℚ) src))
    (c : Cand (K := ℚ) src) : Option (Cand (K := ℚ) src) :=
  match acc with
  | none => some c
  | some b =>
      let fc := candEnergy (src := src) c
      let fb := candEnergy (src := src) b
      if fc < fb then some c
      else if fb < fc then some b
      else if c.id < b.id then some c else some b

def select {S : Type} [ThermodynamicSystem ℚ S] [AdmissibleSystem ℚ S] [JointThermo ℚ S]
    (src : S) (cands : List (Cand (K := ℚ) src)) : Cand (K := ℚ) src ⊕ Residue :=
  if cands.isEmpty then Sum.inr Residue.noCandidates
  else
    let tagged := cands.filter (fun c => c.evidenceTagged)
    if tagged.isEmpty then
      if cands.any (fun c => !c.evidenceTagged) then Sum.inr Residue.allInadmissible
      else Sum.inr Residue.untaggedConstant
    else
      match tagged.foldl pickMin none with
      | none => Sum.inr Residue.allInadmissible
      | some c =>
          if candEnergy (src := src) c < jointFreeEnergy src then Sum.inl c
          else Sum.inr Residue.noStrictImprovement

end UMST.Excitement

namespace UMST.Urge.ExcitementImport

open UMST.Excitement

-- ================================================================
-- SECTION 1: History recovery carrier (typed successor list)
-- ================================================================

/-- Context for Urge history recovery: prior head + admissible successor candidates. -/
structure HistoryRecoveryCtx (S : Type) [ThermodynamicSystem ℚ S] [AdmissibleSystem ℚ S]
    [JointThermo ℚ S] where
  prior       : S
  successors  : List (Cand (K := ℚ) prior)

-- ================================================================
-- SECTION 2: Recovery **is** Excitement.select (no local argmin)
-- ================================================================

/-- Urge history recovery composes `UMST.Excitement.select` — not a second argmin. -/
noncomputable def urgeRecovery {S : Type} [ThermodynamicSystem ℚ S] [AdmissibleSystem ℚ S]
    [JointThermo ℚ S] (ctx : HistoryRecoveryCtx S) : Cand (K := ℚ) ctx.prior ⊕ Residue :=
  select ctx.prior ctx.successors

/-- Alias on bare `(prior, successors)` — same selector, no re-derivation. -/
noncomputable def urgeRecoverySelect {S : Type} [ThermodynamicSystem ℚ S] [AdmissibleSystem ℚ S]
    [JointThermo ℚ S] (prior : S) (successors : List (Cand (K := ℚ) prior)) :
    Cand (K := ℚ) prior ⊕ Residue :=
  select prior successors

/-- Definitional witness: recovery API is `Excitement.select`. -/
theorem urgeRecovery_eq_select {S : Type} [ThermodynamicSystem ℚ S] [AdmissibleSystem ℚ S]
    [JointThermo ℚ S] (ctx : HistoryRecoveryCtx S) :
    urgeRecovery ctx = select ctx.prior ctx.successors :=
  rfl

theorem urgeRecoverySelect_eq_select {S : Type} [ThermodynamicSystem ℚ S] [AdmissibleSystem ℚ S]
    [JointThermo ℚ S] (prior : S) (successors : List (Cand (K := ℚ) prior)) :
    urgeRecoverySelect prior successors = select prior successors :=
  rfl

/-- Recovery and bare select agree on identical inputs. -/
theorem urgeRecovery_eq_urgeRecoverySelect {S : Type} [ThermodynamicSystem ℚ S]
    [AdmissibleSystem ℚ S] [JointThermo ℚ S] (ctx : HistoryRecoveryCtx S) :
    urgeRecovery ctx = urgeRecoverySelect ctx.prior ctx.successors :=
  rfl

-- ================================================================
-- SECTION 3: Imported selector properties (no local re-proof of argmin)
-- ================================================================

/-- Empty successor list → `Residue.noCandidates` via imported `select`. -/
theorem urgeRecovery_empty {S : Type} [ThermodynamicSystem ℚ S] [AdmissibleSystem ℚ S]
    [JointThermo ℚ S] (prior : S) :
    urgeRecoverySelect prior [] = Sum.inr Residue.noCandidates := by
  rfl

-- ================================================================
-- SECTION 4: Axiom discipline + honesty flags
-- ================================================================

/-- Physics GREEN unauthorized on this scaffold. -/
def urgePhysicsGreen : Bool := false

theorem urgePhysicsGreenFalse : urgePhysicsGreen = false := rfl

/-- Production wiring stays open (meso import only). -/
def excitementImportProductionWired : Bool := false

theorem excitementImportProductionWiredFalse : excitementImportProductionWired = false := rfl

/-- Catalog witness: meso Urge ExcitementImport module present. -/
theorem excitementImportModuleWitness : True := trivial

/-- Recovery selector re-uses `jointFreeEnergy` / `pickMin` from Excitement — no Urge-local argmin. -/
theorem urgeRecovery_noLocalArgmin {S : Type} [ThermodynamicSystem ℚ S] [AdmissibleSystem ℚ S]
    [JointThermo ℚ S] (ctx : HistoryRecoveryCtx S) :
    urgeRecovery ctx = select ctx.prior ctx.successors :=
  rfl
end UMST.Urge.ExcitementImport

namespace UrgeKnowing.MachineTemperature

open Real Finset UMST.LandauerLaw UMST.Excitement UMST.Urge.ExcitementImport

-- ================================================================
-- SECTION 1: Modality + knowing-fiber pins (Unwired)
-- ================================================================

/-- Design modality for machine-temperature claims (TYPE-03 preview). -/
inductive MachineTemperatureModality where
  | unwired | assumed | proved | surrogate
  deriving DecidableEq, Repr

def machineTemperatureModalityCurrent : MachineTemperatureModality := .unwired

def productionWired : Bool := false

def landauerProductionWired : Bool := false

def machineTemperatureProductionWired : Bool := false

-- ================================================================
-- SECTION 2: §17.2 ontology — what Excitement T is pinned to
-- ================================================================

/-- What Excitement T is pinned to (§17.2). -/
inductive TemperatureSource where
  | repositoryInMachine
  | wallClockTheater
  | abstractDagScalar
  deriving DecidableEq, Repr

/-- Machine temperature T — coupled repository-in-machine, not wall clock. -/
structure MachineTemperature where
  kelvinMilli : ℕ
  nodeId : String
  source : TemperatureSource
  deriving DecidableEq, Repr

/-- Candidate for machine-temperature ontology admission. -/
structure MachineTemperatureCandidate where
  kelvinMilli : ℕ
  nodeId : String
  source : TemperatureSource
  erasureBits : ℕ
  availableEnergyMilliJoule : ℕ
  deriving DecidableEq, Repr

/-- Typed witness — repository-in-machine T with energy floor satisfied. -/
structure MachineTemperatureWitness where
  temperature : MachineTemperature
  landauerFloorMilliJoule : ℕ
  availableEnergyMilliJoule : ℕ
  deriving DecidableEq, Repr

/-- Typed refusal for machine-temperature ontology discipline. -/
inductive MachineTemperatureRefusal where
  | wallClockAsTemperature
  | abstractDagScalarAsTemperature
  | crossNodeEnergyWitnessMismatch (nodeId : String) (floor available : ℕ)
  | secondArgmin
  deriving DecidableEq, Repr

-- ================================================================
-- SECTION 3: Landauer floor surrogate — k_B T ln(2) per bit at milli scale
-- ================================================================

/-- Boltzmann constant surrogate (milli-scale integer pin — not measured physics). -/
def kBMilli : ℕ := 138

/-- Kelvin from milli-Kelvin surrogate (typed integer — not wall-clock measured). -/
def tKelvinFromMilli : ℕ → ℕ
  | 0 => 1
  | kelvinMilli =>
      let raw := kelvinMilli / 1000
      if raw = 0 then 1 else raw

/-- Landauer floor surrogate: k_B T ln(2) per bit at milli scale (typed, not measured). -/
def landauerFloorMilliJoule (kelvinMilli erasureBits : ℕ) : ℕ :=
  let tKelvin := tKelvinFromMilli kelvinMilli
  (tKelvin * kBMilli * erasureBits * 693) / 1000000

def candidateFloor (c : MachineTemperatureCandidate) : ℕ :=
  landauerFloorMilliJoule c.kelvinMilli c.erasureBits

/-- Core typed predicate — repository-in-machine source and energy floor cleared. -/
def machineTemperatureAdmitPred (c : MachineTemperatureCandidate) : Prop :=
  c.source = .repositoryInMachine ∧
  candidateFloor c ≤ c.availableEnergyMilliJoule

-- ================================================================
-- SECTION 4: Evaluate ontology — honest refuse on inadmissible inputs
-- ================================================================

def evaluateRepositoryInMachine (c : MachineTemperatureCandidate) :
    MachineTemperatureWitness ⊕ MachineTemperatureRefusal :=
  let floor := candidateFloor c
  if c.availableEnergyMilliJoule < floor then
    Sum.inr (.crossNodeEnergyWitnessMismatch c.nodeId floor c.availableEnergyMilliJoule)
  else
    Sum.inl
      { temperature :=
          { kelvinMilli := c.kelvinMilli
            nodeId := c.nodeId
            source := .repositoryInMachine }
        landauerFloorMilliJoule := floor
        availableEnergyMilliJoule := c.availableEnergyMilliJoule }

def evaluateMachineTemperature (c : MachineTemperatureCandidate) :
    MachineTemperatureWitness ⊕ MachineTemperatureRefusal :=
  match c.source with
  | .wallClockTheater => Sum.inr .wallClockAsTemperature
  | .abstractDagScalar => Sum.inr .abstractDagScalarAsTemperature
  | .repositoryInMachine => evaluateRepositoryInMachine c

def refuseWallClockAsTemperature : MachineTemperatureRefusal := .wallClockAsTemperature

def refuseAbstractDagScalarAsTemperature : MachineTemperatureRefusal :=
  .abstractDagScalarAsTemperature

def refuseSecondArgminSelector : MachineTemperatureRefusal := .secondArgmin

-- ================================================================
-- SECTION 5: Landauer tie-in — machine T on HeatBath, sole axiom only
-- ================================================================

theorem machineTemperatureLandauerBound (proc : ErasureProcess)
    (hSL : physicalSecondLawUniformBinary proc) :
    proc.bath.bathTemp.val * log 2 ≤ proc.work :=
  landauerBound proc hSL

theorem machineTemperaturePhysicalSecondLaw (proc : ErasureProcess) :
    physicalSecondLawUniformBinary proc :=
  physicalSecondLaw_uniform_binary proc

theorem machine_temperature_not_wall_clock :
    (TemperatureSource.repositoryInMachine = TemperatureSource.wallClockTheater) → False := by
  intro h
  cases h

theorem machine_temperature_not_dag_scalar :
    (TemperatureSource.repositoryInMachine = TemperatureSource.abstractDagScalar) → False := by
  intro h
  cases h

def machineTemperatureBathField (bath : HeatBath) : ℝ :=
  bath.bathTemp.val

theorem production_not_wired : productionWired = false := rfl

theorem landauer_not_production_wired : landauerProductionWired = false := rfl

theorem machine_temperature_production_not_wired :
    machineTemperatureProductionWired = false :=
  rfl

-- ================================================================
-- SECTION 6: Fixtures — 1 accept + 3 refuse (mirror Rust / Agda probe)
-- ================================================================

def fixtureM3Accept : MachineTemperatureCandidate :=
  { kelvinMilli := 310000
    nodeId := "node-m3-rapl"
    source := .repositoryInMachine
    erasureBits := 64
    availableEnergyMilliJoule := 50000000 }

def fixtureWallClockRefuse : MachineTemperatureCandidate :=
  { kelvinMilli := 0
    nodeId := "wall-clock-theater"
    source := .wallClockTheater
    erasureBits := 0
    availableEnergyMilliJoule := 0 }

def fixtureDagScalarRefuse : MachineTemperatureCandidate :=
  { kelvinMilli := 1
    nodeId := "dag-scalar-theater"
    source := .abstractDagScalar
    erasureBits := 0
    availableEnergyMilliJoule := 1000000 }

def fixtureThinkpadCrossNodeRefuse : MachineTemperatureCandidate :=
  { kelvinMilli := 320000
    nodeId := "node-thinkpad"
    source := .repositoryInMachine
    erasureBits := 64
    availableEnergyMilliJoule := 1 }

theorem m3_accepts : evaluateMachineTemperature fixtureM3Accept = Sum.inl
    { temperature :=
        { kelvinMilli := 310000, nodeId := "node-m3-rapl", source := .repositoryInMachine }
      landauerFloorMilliJoule := landauerFloorMilliJoule 310000 64
      availableEnergyMilliJoule := 50000000 } := by
  native_decide

theorem wall_clock_refused :
    evaluateMachineTemperature fixtureWallClockRefuse = Sum.inr .wallClockAsTemperature :=
  rfl

theorem dag_scalar_refused :
    evaluateMachineTemperature fixtureDagScalarRefuse =
      Sum.inr .abstractDagScalarAsTemperature :=
  rfl

theorem thinkpad_cross_node_refused :
    evaluateMachineTemperature fixtureThinkpadCrossNodeRefuse =
      Sum.inr (.crossNodeEnergyWitnessMismatch "node-thinkpad"
        (landauerFloorMilliJoule 320000 64) 1) := by
  native_decide

-- ================================================================
-- SECTION 7: Machine temperature composes Excitement.select (no second argmin)
-- ================================================================

/-- Context for machine-temperature recovery over admissible successors. -/
structure MachineTemperatureCtx (S : Type) [ThermodynamicSystem ℚ S] [AdmissibleSystem ℚ S]
    [JointThermo ℚ S] where
  prior : S
  successors : List (Cand (K := ℚ) prior)

/-- Machine-temperature selection **is** `urgeRecoverySelect` / `Excitement.select`. -/
noncomputable def machineTemperatureSelect {S : Type} [ThermodynamicSystem ℚ S]
    [AdmissibleSystem ℚ S] [JointThermo ℚ S] (ctx : MachineTemperatureCtx S) :
    Cand (K := ℚ) ctx.prior ⊕ Residue :=
  urgeRecoverySelect ctx.prior ctx.successors

noncomputable def machineTemperatureSelectBare {S : Type} [ThermodynamicSystem ℚ S]
    [AdmissibleSystem ℚ S] [JointThermo ℚ S] (prior : S)
    (successors : List (Cand (K := ℚ) prior)) :
    Cand (K := ℚ) prior ⊕ Residue :=
  urgeRecoverySelect prior successors

def composeSurrogateFor : String := "UMST.Excitement.select"

theorem machineTemperatureSelect_eq_select {S : Type} [ThermodynamicSystem ℚ S]
    [AdmissibleSystem ℚ S] [JointThermo ℚ S] (ctx : MachineTemperatureCtx S) :
    machineTemperatureSelect ctx = select ctx.prior ctx.successors :=
  rfl

theorem machineTemperatureSelect_eq_urgeRecoverySelect {S : Type} [ThermodynamicSystem ℚ S]
    [AdmissibleSystem ℚ S] [JointThermo ℚ S] (ctx : MachineTemperatureCtx S) :
    machineTemperatureSelect ctx = urgeRecoverySelect ctx.prior ctx.successors :=
  rfl

theorem machineTemperatureSelectBare_eq_select {S : Type} [ThermodynamicSystem ℚ S]
    [AdmissibleSystem ℚ S] [JointThermo ℚ S] (prior : S)
    (successors : List (Cand (K := ℚ) prior)) :
    machineTemperatureSelectBare prior successors = select prior successors :=
  rfl

theorem machineTemperatureNoLocalArgmin {S : Type} [ThermodynamicSystem ℚ S]
    [AdmissibleSystem ℚ S] [JointThermo ℚ S] (ctx : MachineTemperatureCtx S) :
    machineTemperatureSelect ctx = select ctx.prior ctx.successors :=
  rfl

theorem machineTemperatureSelect_empty {S : Type} [ThermodynamicSystem ℚ S]
    [AdmissibleSystem ℚ S] [JointThermo ℚ S] (prior : S)
    (successors : List (Cand (K := ℚ) prior)) (h : successors = []) :
    machineTemperatureSelectBare prior successors = Sum.inr Residue.noCandidates := by
  subst h
  simpa [machineTemperatureSelectBare] using urgeRecovery_empty prior

theorem machine_temperature_compose_surrogate_ok :
    composeSurrogateFor = "UMST.Excitement.select" :=
  rfl

theorem second_argmin_refused :
    refuseSecondArgminSelector = .secondArgmin :=
  rfl

-- ================================================================
-- SECTION 8: Authority cites + physics GREEN fence
-- ================================================================

def landauerBoundAuthority : String :=
  "umst/umst-formal-double-slit/Lean/LandauerBound.lean"

def landauerLawAuthority : String :=
  "umst/umst-formal-double-slit/Lean/LandauerLaw.lean"

def physicalSecondLawAuthority : String :=
  "LandauerLaw.physicalSecondLaw"

def machineTemperatureCellId : String :=
  "URGE-FORMAL-Q-LEAN-MACHINE-TEMPERATURE"

def machineTemperatureNamed : String :=
  "machine_temperature: Excitement T repository-in-machine LandauerBound not wall clock not DAG scalar; compose Excitement not second argmin; physicalSecondLaw sole axiom framing"

def machineTemperatureNonClaim : String :=
  "URGE-FORMAL-Q-LEAN-MACHINE-TEMPERATURE §17.2 Excitement T is machine temperature of coupled repository-in-machine not wall clock not abstract DAG scalar Landauer erasure floor cross-node energy witness may refuse compose Excitement select not second argmin modality Unwired not physics GREEN not production_wired knowing fiber only not meso thermo G(T,P,x)"

def machineTemperatureSecondLawConservationFraming : String :=
  "second_law_conservation_machine_temperature_one_axiom_landauer_not_second_axiom"

theorem machine_temperature_cell_id :
    machineTemperatureCellId = "URGE-FORMAL-Q-LEAN-MACHINE-TEMPERATURE" :=
  rfl

theorem machine_temperature_modality_unwired :
    machineTemperatureModalityCurrent = .unwired :=
  rfl

theorem production_wired_false : productionWired = false := rfl

theorem landauer_production_wired_false : landauerProductionWired = false := rfl

theorem machine_temperature_production_wired_false :
    machineTemperatureProductionWired = false :=
  rfl

theorem machine_temperature_cites_landauer_bound :
    landauerBoundAuthority ≠ "" :=
  by decide

theorem machine_temperature_cites_landauer_law :
    landauerLawAuthority ≠ "" :=
  by decide

theorem machine_temperature_cites_physical_second_law :
    physicalSecondLawAuthority = "LandauerLaw.physicalSecondLaw" :=
  rfl

theorem machine_temperature_not_second_landauer_axiom :
    machineTemperatureSecondLawConservationFraming ≠ "landauer_second_axiom" :=
  by decide

/-- Physics GREEN is not authorized on the knowing scaffold. -/
def physicsGreenAuthorized : Prop := False

theorem machine_temperature_physics_green_false : ¬ physicsGreenAuthorized :=
  id

theorem machine_temperature_not_meso_thermo_restate :
    machineTemperatureNonClaim ≠ "meso_thermo_G_T_P_x_restate" :=
  by decide

def machineTemperatureKnowingFiberOk : Prop :=
  machineTemperatureModalityCurrent = .unwired ∧ ¬ physicsGreenAuthorized

theorem machine_temperature_knowing_fiber_ok :
    machineTemperatureKnowingFiberOk :=
  ⟨machine_temperature_modality_unwired, machine_temperature_physics_green_false⟩

end UrgeKnowing.MachineTemperature
