-- SPDX-FileCopyrightText: 2026 Santosh Prabhu Shenbagamoorthy and Santhosh Shyamsundar
-- SPDX-License-Identifier: MIT
------------------------------------------------------------------------
-- UMST-Formal: UrgeKnowing.MachineTemperature.agda
--
-- Knowing fiber (§17.2): Excitement T is machine temperature of the coupled
--   repository-in-machine (Landauer erasure environment), not wall clock and
--   not an abstract DAG scalar. Cross-node energy witness may refuse.
--   * sole postulate `physicalSecondLaw` imported from LandauerHistoryLook
--   * compose Excitement select — no second argmin
--
-- Mirrors Rust `machine_temperature` ontology scaffold.
-- Modality Unwired; physics GREEN false.
------------------------------------------------------------------------

{-# OPTIONS --without-K #-}

module UrgeKnowing.MachineTemperature where

open import Data.Bool using (Bool; false; true)
open import Data.Empty using (⊥)
open import Data.Nat using (ℕ; zero; suc; _≤_; _/_; _*_)
open import Data.Nat.Base using (z≤n)
open import Data.Nat.Properties using (_<?_)
open import Data.Product using (_×_; _,_; ∃)
open import Data.String using (String)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Relation.Nullary using (yes; no; ¬_)

open import UrgeKnowing.LandauerHistoryLook
  using ( physicalSecondLaw; PhysicalSecondLaw; ErasureProcess
        ; HeatBath; landauerBound; productionWired; landauerProductionWired )

------------------------------------------------------------------------
-- Modality + machine-temperature pins (knowing fiber — Unwired)
------------------------------------------------------------------------

data MachineTemperatureModality : Set where
  machine-temperature-unwired machine-temperature-assumed
    machine-temperature-proved machine-temperature-surrogate
    : MachineTemperatureModality

machineTemperatureModalityCurrent : MachineTemperatureModality
machineTemperatureModalityCurrent = machine-temperature-unwired

machineTemperatureProductionWired : Bool
machineTemperatureProductionWired = false

------------------------------------------------------------------------
-- §17.2 ontology — what Excitement T is pinned to
------------------------------------------------------------------------

data TemperatureSource : Set where
  repository-in-machine wall-clock-theater abstract-dag-scalar
    : TemperatureSource

record MachineTemperature : Set where
  field
    kelvinMilli : ℕ
    nodeId : String
    source : TemperatureSource

record MachineTemperatureCandidate : Set where
  field
    kelvinMilli : ℕ
    nodeId : String
    source : TemperatureSource
    erasureBits : ℕ
    availableEnergyMilliJoule : ℕ

record MachineTemperatureWitness : Set where
  field
    temperature : MachineTemperature
    landauerFloorMilliJoule : ℕ
    availableEnergyMilliJoule : ℕ

data MachineTemperatureRefusal : Set where
  wall-clock-as-temperature abstract-dag-scalar-as-temperature
    second-argmin : MachineTemperatureRefusal
  cross-node-energy-witness-mismatch :
    (nodeId : String) (floor available : ℕ) → MachineTemperatureRefusal

------------------------------------------------------------------------
-- Landauer floor surrogate — k_B T ln(2) per bit at milli scale
------------------------------------------------------------------------

kBMilli : ℕ
kBMilli = 138

tKelvinFromMilli : ℕ → ℕ
tKelvinFromMilli zero = suc zero
tKelvinFromMilli kelvinMilli with kelvinMilli / 1000
... | zero       = suc zero
... | raw@(suc _) = raw

landauerFloorMilliJoule : ℕ → ℕ → ℕ
landauerFloorMilliJoule kelvinMilli erasureBits =
  let tKelvin = tKelvinFromMilli kelvinMilli
  in (tKelvin * kBMilli * erasureBits * 693) / 1000000

machineTemperatureAdmitPred : MachineTemperatureCandidate → Set
machineTemperatureAdmitPred c =
  MachineTemperatureCandidate.source c ≡ repository-in-machine ×
  landauerFloorMilliJoule (MachineTemperatureCandidate.kelvinMilli c)
                          (MachineTemperatureCandidate.erasureBits c)
  ≤ MachineTemperatureCandidate.availableEnergyMilliJoule c

------------------------------------------------------------------------
-- Evaluate ontology — honest refuse on inadmissible inputs
------------------------------------------------------------------------

candidateFloor : MachineTemperatureCandidate → ℕ
candidateFloor c =
  landauerFloorMilliJoule
    (MachineTemperatureCandidate.kelvinMilli c)
    (MachineTemperatureCandidate.erasureBits c)

evaluateRepositoryInMachine :
  (c : MachineTemperatureCandidate) →
  MachineTemperatureWitness ⊎ MachineTemperatureRefusal
evaluateRepositoryInMachine c with
  MachineTemperatureCandidate.availableEnergyMilliJoule c <? candidateFloor c
... | yes _ = inj₂ (cross-node-energy-witness-mismatch
                    (MachineTemperatureCandidate.nodeId c)
                    (candidateFloor c)
                    (MachineTemperatureCandidate.availableEnergyMilliJoule c))
... | no _ = inj₁ record
  { temperature = record
    { kelvinMilli = MachineTemperatureCandidate.kelvinMilli c
    ; nodeId = MachineTemperatureCandidate.nodeId c
    ; source = repository-in-machine
    }
  ; landauerFloorMilliJoule = candidateFloor c
  ; availableEnergyMilliJoule = MachineTemperatureCandidate.availableEnergyMilliJoule c
  }

evaluateMachineTemperature :
  (c : MachineTemperatureCandidate) →
  MachineTemperatureWitness ⊎ MachineTemperatureRefusal
evaluateMachineTemperature c with MachineTemperatureCandidate.source c
... | wall-clock-theater = inj₂ wall-clock-as-temperature
... | abstract-dag-scalar = inj₂ abstract-dag-scalar-as-temperature
... | repository-in-machine = evaluateRepositoryInMachine c

refuseWallClockAsTemperature : MachineTemperatureRefusal
refuseWallClockAsTemperature = wall-clock-as-temperature

refuseAbstractDagScalarAsTemperature : MachineTemperatureRefusal
refuseAbstractDagScalarAsTemperature = abstract-dag-scalar-as-temperature

refuseSecondArgminSelector : MachineTemperatureRefusal
refuseSecondArgminSelector = second-argmin

------------------------------------------------------------------------
-- Landauer tie-in — machine T on HeatBath, sole postulate only
------------------------------------------------------------------------

machineTemperatureLandauerBound :
  ∀ (proc : ErasureProcess) (entropyDecrease : ℕ) →
  PhysicalSecondLaw proc entropyDecrease →
  entropyDecrease ≤ ErasureProcess.dissipatedEntropy proc
machineTemperatureLandauerBound proc ΔS h = landauerBound proc ΔS h

machineTemperaturePhysicalSecondLaw :
  ∀ (proc : ErasureProcess) (entropyDecrease : ℕ) →
  PhysicalSecondLaw proc entropyDecrease
machineTemperaturePhysicalSecondLaw proc ΔS = physicalSecondLaw proc ΔS

machine-temperature-not-wall-clock :
  (repository-in-machine ≡ wall-clock-theater) → ⊥
machine-temperature-not-wall-clock ()

machine-temperature-not-dag-scalar :
  (repository-in-machine ≡ abstract-dag-scalar) → ⊥
machine-temperature-not-dag-scalar ()

machine-temperature-bath-field :
  ∀ (bath : HeatBath) → ℕ
machine-temperature-bath-field bath = HeatBath.temperature bath

production-not-wired : productionWired ≡ false
production-not-wired = refl

landauer-not-production-wired : landauerProductionWired ≡ false
landauer-not-production-wired = refl

machine-temperature-production-not-wired :
  machineTemperatureProductionWired ≡ false
machine-temperature-production-not-wired = refl

------------------------------------------------------------------------
-- Fixtures — 1 accept + 3 refuse (mirror Rust probe)
------------------------------------------------------------------------

fixtureM3Accept : MachineTemperatureCandidate
fixtureM3Accept = record
  { kelvinMilli = 310000
  ; nodeId = "node-m3-rapl"
  ; source = repository-in-machine
  ; erasureBits = 64
  ; availableEnergyMilliJoule = 50000000
  }

fixtureWallClockRefuse : MachineTemperatureCandidate
fixtureWallClockRefuse = record
  { kelvinMilli = zero
  ; nodeId = "wall-clock-theater"
  ; source = wall-clock-theater
  ; erasureBits = zero
  ; availableEnergyMilliJoule = zero
  }

fixtureDagScalarRefuse : MachineTemperatureCandidate
fixtureDagScalarRefuse = record
  { kelvinMilli = suc zero
  ; nodeId = "dag-scalar-theater"
  ; source = abstract-dag-scalar
  ; erasureBits = zero
  ; availableEnergyMilliJoule = 1000000
  }

fixtureThinkpadCrossNodeRefuse : MachineTemperatureCandidate
fixtureThinkpadCrossNodeRefuse = record
  { kelvinMilli = 320000
  ; nodeId = "node-thinkpad"
  ; source = repository-in-machine
  ; erasureBits = 64
  ; availableEnergyMilliJoule = suc zero
  }

m3-accepts : evaluateMachineTemperature fixtureM3Accept ≡ inj₁ _
m3-accepts = refl

wall-clock-refused :
  evaluateMachineTemperature fixtureWallClockRefuse ≡ inj₂ wall-clock-as-temperature
wall-clock-refused = refl

dag-scalar-refused :
  evaluateMachineTemperature fixtureDagScalarRefuse ≡
  inj₂ abstract-dag-scalar-as-temperature
dag-scalar-refused = refl

thinkpad-cross-node-refused :
  ∃ λ r → evaluateMachineTemperature fixtureThinkpadCrossNodeRefuse ≡ inj₂ r
thinkpad-cross-node-refused =
  cross-node-energy-witness-mismatch "node-thinkpad"
    (landauerFloorMilliJoule 320000 64) (suc zero)
  , refl

------------------------------------------------------------------------
-- One design axiom + authority cites (not a second optimizer fork)
------------------------------------------------------------------------

machineTemperatureAxiom :
  (productionWired ≡ false)
  × (landauerProductionWired ≡ false)
  × (machineTemperatureProductionWired ≡ false)
  × (∀ (proc : ErasureProcess) (entropyDecrease : ℕ) →
      PhysicalSecondLaw proc entropyDecrease →
      entropyDecrease ≤ ErasureProcess.dissipatedEntropy proc)
  × (∃ λ w → evaluateMachineTemperature fixtureM3Accept ≡ inj₁ w)
  × (evaluateMachineTemperature fixtureWallClockRefuse ≡
     inj₂ wall-clock-as-temperature)
  × (evaluateMachineTemperature fixtureDagScalarRefuse ≡
     inj₂ abstract-dag-scalar-as-temperature)
machineTemperatureAxiom =
  production-not-wired ,
  ( landauer-not-production-wired ,
  ( machine-temperature-production-not-wired ,
  ( machineTemperatureLandauerBound ,
  ( (_ , m3-accepts) ,
  ( wall-clock-refused ,
  dag-scalar-refused )))))

machineTemperatureNamed : String
machineTemperatureNamed =
  "machineTemperature: Excitement T repository-in-machine LandauerBound not wall clock not DAG scalar"

machineTemperatureCellId : String
machineTemperatureCellId = "URGE-FORMAL-Q-AGDA-MACHINE-TEMPERATURE"

machineTemperatureNonClaim : String
machineTemperatureNonClaim =
  "URGE-FORMAL-Q-AGDA-MACHINE-TEMPERATURE §17.2 Excitement T is machine temperature of coupled repository-in-machine not wall clock not abstract DAG scalar Landauer erasure floor cross-node energy witness may refuse sole postulate physicalSecondLaw no extra postulate modality Unwired not physics GREEN not production_wired"

machine-temperature-modality-unwired :
  machineTemperatureModalityCurrent ≡ machine-temperature-unwired
machine-temperature-modality-unwired = refl

machineTemperaturePhysicsGreenAuthorized : Set
machineTemperaturePhysicsGreenAuthorized = ⊥

machine-temperature-physics-green-false : ¬ machineTemperaturePhysicsGreenAuthorized
machine-temperature-physics-green-false ()

composeSurrogateFor : String
composeSurrogateFor = "UMST.Excitement.select"

machine-temperature-compose-surrogate-ok :
  composeSurrogateFor ≡ "UMST.Excitement.select"
machine-temperature-compose-surrogate-ok = refl

second-argmin-refused :
  refuseSecondArgminSelector ≡ second-argmin
second-argmin-refused = refl
