-- SPDX-FileCopyrightText: 2026 Santosh Prabhu Shenbagamoorthy and Santhosh Shyamsundar
-- SPDX-License-Identifier: MIT

{-|
Module      : UMST.ChemConstants.Eco02ConsumeNotFork
Description : ECO-02 consume-not-fork on the knowing fiber (Q lattice)
Copyright   : (c) UMST Project, 2026

Chem consumes manifold @liquid_ppo@ and semantics @MiObservation@ authorities — does **not**
fork a chem-local Burn liquid-PPO kernel. @bindAntichainUntilMeasured@ holds until BIND is
measured; @oneLearnerSpine@ = not @chemForksLiquidPpoKernel@ (one spine, not a second optimizer).

* @chemForksLiquidPpoKernel@, @burnKernelCopiedToChem@, @liquidPpoProductionWired@ = False.
* @bindAntichainUntilMeasured@ = True (antichain until measured — not liquid-PPO on chem).
* **One** design axiom (@eco02ConsumeNotForkAxiom@): second law + conservation consume-not-fork.
* @physics_green@ stays false.

Haskell mirror of Coq ECO-02 consume-not-fork on the quantum / knowing fiber.
Cell: @CHEM-FORMAL-Q-HS-ECO-02-CONSUME-NOT-FORK@.
-}
module UMST.ChemConstants.Eco02ConsumeNotFork
  ( Eco02ConsumeNotForkModality (..)
  , eco02ConsumeNotForkModalityCurrent
  , chemForksLiquidPpoKernel
  , burnKernelCopiedToChem
  , liquidPpoProductionWired
  , bindAntichainUntilMeasured
  , oneLearnerSpine
  , consumeNotForkWitness
  , eco02ConsumeNotForkNotSecondOptimizer
  , eco02ConsumeNotForkAxiom
  , eco02SecondLawConservationNamed
  , manifoldLiquidPpoAuthority
  , semanticsMiObservationAuthority
  , eco02ConsumeNotForkCellId
  , eco02ConsumeNotForkNonClaim
  , eco02ConsumeNotForkPhysicsGreenAuthorized
  , eco02ConsumeNotForkPhysicsGreenFalse
  , eco02ConsumeNotForkModalityUnwired
  ) where

-- | Design modality for ECO-02 consume-not-fork claims (TYPE-03 preview).
data Eco02ConsumeNotForkModality
  = Eco02ConsumeNotForkUnwired
  | Eco02ConsumeNotForkAssumed
  | Eco02ConsumeNotForkProved
  | Eco02ConsumeNotForkSurrogate
  deriving (Eq, Show)

-- | Current scaffold modality — always Unwired on this cell.
eco02ConsumeNotForkModalityCurrent :: Eco02ConsumeNotForkModality
eco02ConsumeNotForkModalityCurrent = Eco02ConsumeNotForkUnwired

-- | Chem does **not** fork the manifold Burn liquid-PPO kernel.
chemForksLiquidPpoKernel :: Bool
chemForksLiquidPpoKernel = False

-- | Burn kernel is **not** copied into chem (consume-not-fork).
burnKernelCopiedToChem :: Bool
burnKernelCopiedToChem = False

-- | liquid-PPO is **not** production-wired on chem.
liquidPpoProductionWired :: Bool
liquidPpoProductionWired = False

-- | Antichain allocation until BIND measured — no liquid-PPO on chem until then.
bindAntichainUntilMeasured :: Bool
bindAntichainUntilMeasured = True

-- | One learner spine — not a second optimizer (no chem liquid-PPO fork).
oneLearnerSpine :: Bool
oneLearnerSpine = not chemForksLiquidPpoKernel

-- | Consume-not-fork witness: cite manifold authority, refuse chem kernel fork.
consumeNotForkWitness :: Bool
consumeNotForkWitness =
  not chemForksLiquidPpoKernel
    && not burnKernelCopiedToChem
    && not liquidPpoProductionWired

-- | Not a second optimizer: one spine + antichain until BIND measured.
eco02ConsumeNotForkNotSecondOptimizer :: Bool
eco02ConsumeNotForkNotSecondOptimizer =
  oneLearnerSpine && bindAntichainUntilMeasured && not liquidPpoProductionWired

-- | Single design axiom: second law + conservation consume-not-fork (not second optimizer).
eco02ConsumeNotForkAxiom :: Bool
eco02ConsumeNotForkAxiom =
  consumeNotForkWitness
    && eco02ConsumeNotForkNotSecondOptimizer
    && bindAntichainUntilMeasured

eco02SecondLawConservationNamed :: String
eco02SecondLawConservationNamed =
  "eco02ConsumeNotFork: second law + conservation — consume manifold liquid_ppo MiObservation; chem_forks_liquid_ppo_kernel false; bind antichain until BIND measured; one learner spine not second optimizer"

-- | Manifold liquid_ppo consume-not-fork authority (cited, not forked).
manifoldLiquidPpoAuthority :: String
manifoldLiquidPpoAuthority = "umst-manifold/src/ai/liquid_ppo.rs"

-- | Semantics MI observation consume-not-fork authority (cited, not forked).
semanticsMiObservationAuthority :: String
semanticsMiObservationAuthority = "umst/umst-semantics/src/mi_gate.rs"

eco02ConsumeNotForkCellId :: String
eco02ConsumeNotForkCellId = "CHEM-FORMAL-Q-HS-ECO-02-CONSUME-NOT-FORK"

-- | Non-claim fence — consume-not-fork Unwired ≠ Proved GREEN.
eco02ConsumeNotForkNonClaim :: String
eco02ConsumeNotForkNonClaim =
  "CHEM-FORMAL-Q-HS-ECO-02-CONSUME-NOT-FORK ECO-02 consume-not-fork second law conservation; chemForksLiquidPpoKernel burnKernelCopiedToChem liquidPpoProductionWired false; bindAntichainUntilMeasured oneLearnerSpine not second optimizer; one design axiom not second axiom; not GREEN DFT; not physics GREEN; not production_wired"

-- | Physics GREEN is unauthorized on the knowing ECO-02 consume-not-fork scaffold.
eco02ConsumeNotForkPhysicsGreenAuthorized :: Bool
eco02ConsumeNotForkPhysicsGreenAuthorized = False

eco02ConsumeNotForkPhysicsGreenFalse :: Bool
eco02ConsumeNotForkPhysicsGreenFalse = not eco02ConsumeNotForkPhysicsGreenAuthorized

eco02ConsumeNotForkModalityUnwired :: Bool
eco02ConsumeNotForkModalityUnwired =
  eco02ConsumeNotForkModalityCurrent == Eco02ConsumeNotForkUnwired
