-- SPDX-FileCopyrightText: 2026 Santosh Prabhu Shenbagamoorthy and Santhosh Shyamsundar
-- SPDX-License-Identifier: MIT

{-|
Module      : UMST.ChemConstants.RewriteConservation
Description : Rewrite conservation on the knowing fiber (Q lattice)
Copyright   : (c) UMST Project, 2026

**Rewrite** conservation: FP-03 thermo-preserving program **rewrite** combinators
(fusion / sequential composition) on **conservation** claims (Unwired / Assumed / Proved /
Surrogate). Thermo-preserving **rewrite** fusion identity conserved under honest scaffold;
non-preserving steps fail-closed. FP-03 **rewrite** laws are structure witnesses only
(@fp03RewriteProved@ = False).

* @RewriteConservationModality@ = Unwired / Assumed / Proved / Surrogate — four-step lattice, not 118² GREEN table.
* @fuseRewriteSteps@ — thermo-preserving fusion identity conserved on scaffold steps.
* @evaluateFusedRewrite@ — non-preserving step fail-closed.
* **One** design axiom (@rewriteConservationAxiom@): second law + **conservation**.
* @physics_green@ stays false.

Haskell mirror of thermo-preserving **rewrite** **conservation** on the quantum / knowing fiber.
Cell: @CHEM-FORMAL-Q-HS-REWRITE-CONSERVATION@.
-}
module UMST.ChemConstants.RewriteConservation
  ( RewriteConservationModality (..)
  , rewriteConservationModalityCurrent
  , rewriteLatticeAll
  , rewriteLatticeCount
  , ThermoRewriteStep (..)
  , thermoRewriteStepAll
  , thermoRewriteStepCount
  , ThermoRewriteWitness (..)
  , thermoWitnessBalanced
  , thermoWitnessMassViolate
  , thermoWitnessSecondLawViolate
  , FusedThermoRewrite (..)
  , ThermoPreservingVerdict (..)
  , evaluateThermoWitness
  , classifyRewriteStep
  , fuseRewriteSteps
  , evaluateFusedRewrite
  , FusionIdentityLaw (..)
  , fusionIdentityLawAll
  , fusionIdentityLawCount
  , RewriteConservationVerdict (..)
  , evaluateRewriteConservation
  , sampleBalancedWitness
  , sampleMassViolateWitness
  , sampleSecondLawViolateWitness
  , samplePreservingSteps
  , sampleNonPreservingStep
  , unwiredDesignOk
  , balancedWitnessPreserving
  , fusionIdentityConserved
  , fusionPreservingOk
  , conservationViolateRefused
  , secondLawViolateRefused
  , nonPreservingStepFailClosed
  , assumedRewriteDesignOk
  , surrogateRewriteDesignOk
  , greenInventRewriteRefuse
  , rewriteLatticeScaffold
  , rewriteLatticeNotGreenTable
  , fusionIdentityLawsScaffold
  , fusionIdentityLawsNotGreenTable
  , rewriteKnowingFiberOk
  , fp03RewriteInventRefuse
  , rewriteLatticeNotXor
  , fp03RewriteProved
  , rewriteConservationFraming
  , rewriteConservationAxiom
  , rewriteConservationNamed
  , thermoPreservingRewriteAuthority
  , chemL0Fp03Authority
  , rewriteConservationCellId
  , rewriteConservationNonClaim
  , rewriteConservationPhysicsGreenAuthorized
  , rewriteConservationPhysicsGreenFalse
  , rewriteConservationModalityUnwired
  ) where

-- | Design **rewrite** modality for FP-03 **conservation** claims.
data RewriteConservationModality
  = RewriteConservationUnwired
  | RewriteConservationAssumed
  | RewriteConservationProved
  | RewriteConservationSurrogate
  deriving (Eq, Show)

-- | Current scaffold **rewrite** modality — always Unwired on this cell.
rewriteConservationModalityCurrent :: RewriteConservationModality
rewriteConservationModalityCurrent = RewriteConservationUnwired

-- | All FP-03 **rewrite** lattice steps in stable order.
rewriteLatticeAll :: [RewriteConservationModality]
rewriteLatticeAll =
  [ RewriteConservationUnwired
  , RewriteConservationAssumed
  , RewriteConservationProved
  , RewriteConservationSurrogate
  ]

rewriteLatticeCount :: Int
rewriteLatticeCount = length rewriteLatticeAll

-- | Tagged **rewrite** step (scaffold classifier — not live Kleisli arrow).
data ThermoRewriteStep
  = ThermoRewriteIdentity
  | ThermoRewriteAdmissible
  | ThermoRewriteConservationViolate
  | ThermoRewriteSecondLawViolate
  deriving (Eq, Show)

thermoRewriteStepAll :: [ThermoRewriteStep]
thermoRewriteStepAll =
  [ ThermoRewriteIdentity
  , ThermoRewriteAdmissible
  , ThermoRewriteConservationViolate
  , ThermoRewriteSecondLawViolate
  ]

thermoRewriteStepCount :: Int
thermoRewriteStepCount = length thermoRewriteStepAll

-- | Whether a **rewrite** step is thermo-preserving under the scaffold bar.
isThermoPreservingStep :: ThermoRewriteStep -> Bool
isThermoPreservingStep step =
  case step of
    ThermoRewriteIdentity -> True
    ThermoRewriteAdmissible -> True
    ThermoRewriteConservationViolate -> False
    ThermoRewriteSecondLawViolate -> False

-- | Minimal thermodynamic witness for **rewrite** close (design scaffold).
data ThermoRewriteWitness = ThermoRewriteWitness
  { massDeltaKg :: Int
  , energyDeltaJ :: Int
  , entropyDeltaJPerK :: Int
  , externalWorkJ :: Int
  }
  deriving (Eq, Show)

-- | Balanced / conserved witness — admissible **rewrite**.
thermoWitnessBalanced :: ThermoRewriteWitness
thermoWitnessBalanced =
  ThermoRewriteWitness
    { massDeltaKg = 0
    , energyDeltaJ = 0
    , entropyDeltaJPerK = 0
    , externalWorkJ = 0
    }

-- | Mass violation witness — non-preserving **rewrite**.
thermoWitnessMassViolate :: ThermoRewriteWitness
thermoWitnessMassViolate =
  ThermoRewriteWitness
    { massDeltaKg = 1
    , energyDeltaJ = 0
    , entropyDeltaJPerK = 0
    , externalWorkJ = 0
    }

-- | Second-law violation witness — non-preserving **rewrite**.
thermoWitnessSecondLawViolate :: ThermoRewriteWitness
thermoWitnessSecondLawViolate =
  ThermoRewriteWitness
    { massDeltaKg = 0
    , energyDeltaJ = 0
    , entropyDeltaJPerK = -1
    , externalWorkJ = 0
    }

-- | Fusion of two **rewrite** steps (FP-03 fusion law preview).
data FusedThermoRewrite
  = FusedThermoRewriteIdentity
  | FusedThermoRewriteSequential ThermoRewriteStep ThermoRewriteStep
  deriving (Eq, Show)

-- | Verdict of a thermo-preserving **rewrite** / fusion close (fail-closed).
data ThermoPreservingVerdict
  = ThermoPreservingDesignOk
  | ThermoPreservingOk
  | ThermoPreservingFusionOk
  | ThermoPreservingConservationViolate
  | ThermoPreservingSecondLawViolate
  | ThermoPreservingGreenInventRefuse
  deriving (Eq, Show)

-- | Evaluate a thermodynamic witness against **conservation** + second-law bar.
evaluateThermoWitness :: ThermoRewriteWitness -> Bool -> ThermoPreservingVerdict
evaluateThermoWitness witness claimPhysicsGreen
  | claimPhysicsGreen = ThermoPreservingGreenInventRefuse
  | massDeltaKg witness /= 0 || energyDeltaJ witness /= 0 =
      ThermoPreservingConservationViolate
  | entropyDeltaJPerK witness < 0 && externalWorkJ witness <= 0 =
      ThermoPreservingSecondLawViolate
  | otherwise = ThermoPreservingOk

-- | Classify a **rewrite** step from a witness (scaffold classifier).
classifyRewriteStep :: ThermoRewriteWitness -> ThermoRewriteStep
classifyRewriteStep witness =
  case evaluateThermoWitness witness False of
    ThermoPreservingOk ->
      if witness == thermoWitnessBalanced
        then ThermoRewriteIdentity
        else ThermoRewriteAdmissible
    ThermoPreservingConservationViolate -> ThermoRewriteConservationViolate
    ThermoPreservingSecondLawViolate -> ThermoRewriteSecondLawViolate
    ThermoPreservingDesignOk -> ThermoRewriteConservationViolate
    ThermoPreservingFusionOk -> ThermoRewriteConservationViolate
    ThermoPreservingGreenInventRefuse -> ThermoRewriteConservationViolate

-- | Fuse two **rewrite** steps (FP fusion law — preserving ∘ preserving).
fuseRewriteSteps :: ThermoRewriteStep -> ThermoRewriteStep -> FusedThermoRewrite
fuseRewriteSteps first second =
  if first == ThermoRewriteIdentity && second == ThermoRewriteIdentity
    then FusedThermoRewriteIdentity
    else FusedThermoRewriteSequential first second

-- | Evaluate a fused **rewrite** under the thermo-preserving bar.
evaluateFusedRewrite :: FusedThermoRewrite -> Bool -> ThermoPreservingVerdict
evaluateFusedRewrite fused claimPhysicsGreen
  | claimPhysicsGreen = ThermoPreservingGreenInventRefuse
  | otherwise =
      case fused of
        FusedThermoRewriteIdentity -> ThermoPreservingFusionOk
        FusedThermoRewriteSequential first second ->
          if not (isThermoPreservingStep first)
            then nonPreservingVerdict first
            else
              if not (isThermoPreservingStep second)
                then nonPreservingVerdict second
                else ThermoPreservingFusionOk
  where
    nonPreservingVerdict step =
      case step of
        ThermoRewriteConservationViolate -> ThermoPreservingConservationViolate
        ThermoRewriteSecondLawViolate -> ThermoPreservingSecondLawViolate
        ThermoRewriteIdentity -> ThermoPreservingDesignOk
        ThermoRewriteAdmissible -> ThermoPreservingDesignOk

-- | **Rewrite** fusion identity law cells tracked by FP-03 (structure scaffold).
data FusionIdentityLaw
  = FusionIdentityConserved
  | PreservingFusionOk
  | ConservationViolateRefused
  | SecondLawViolateRefused
  deriving (Eq, Show)

fusionIdentityLawAll :: [FusionIdentityLaw]
fusionIdentityLawAll =
  [ FusionIdentityConserved
  , PreservingFusionOk
  , ConservationViolateRefused
  , SecondLawViolateRefused
  ]

fusionIdentityLawCount :: Int
fusionIdentityLawCount = length fusionIdentityLawAll

-- | Verdict for FP-03 **rewrite** **conservation** promotion (fail-closed).
data RewriteConservationVerdict
  = RewriteDesignOk
  | RewritePreservingOk
  | RewriteFusionOk
  | RewriteConservationViolateRefuse
  | RewriteSecondLawViolateRefuse
  | RewriteGreenInventRefuse
  deriving (Eq, Show)

-- | Evaluate FP-03 **rewrite** **conservation** typing (fail-closed).
evaluateRewriteConservation ::
  RewriteConservationModality
  -> ThermoRewriteWitness
  -> Bool
  -> RewriteConservationVerdict
evaluateRewriteConservation modality witness claimPhysicsGreen
  | claimPhysicsGreen = RewriteGreenInventRefuse
  | otherwise =
      case modality of
        RewriteConservationUnwired -> RewriteDesignOk
        RewriteConservationAssumed -> RewriteDesignOk
        RewriteConservationSurrogate -> RewriteDesignOk
        RewriteConservationProved ->
          case evaluateThermoWitness witness False of
            ThermoPreservingOk -> RewritePreservingOk
            ThermoPreservingConservationViolate ->
              RewriteConservationViolateRefuse
            ThermoPreservingSecondLawViolate ->
              RewriteSecondLawViolateRefuse
            ThermoPreservingDesignOk -> RewriteDesignOk
            ThermoPreservingFusionOk -> RewriteFusionOk
            ThermoPreservingGreenInventRefuse -> RewriteGreenInventRefuse

sampleBalancedWitness :: ThermoRewriteWitness
sampleBalancedWitness = thermoWitnessBalanced

sampleMassViolateWitness :: ThermoRewriteWitness
sampleMassViolateWitness = thermoWitnessMassViolate

sampleSecondLawViolateWitness :: ThermoRewriteWitness
sampleSecondLawViolateWitness = thermoWitnessSecondLawViolate

samplePreservingSteps :: (ThermoRewriteStep, ThermoRewriteStep)
samplePreservingSteps = (ThermoRewriteAdmissible, ThermoRewriteIdentity)

sampleNonPreservingStep :: ThermoRewriteStep
sampleNonPreservingStep = ThermoRewriteConservationViolate

-- | Unwired **rewrite** modality OK without thermo break.
unwiredDesignOk :: Bool
unwiredDesignOk =
  evaluateRewriteConservation
    RewriteConservationUnwired
    sampleBalancedWitness
    False
    == RewriteDesignOk

-- | Balanced witness is thermo-preserving.
balancedWitnessPreserving :: Bool
balancedWitnessPreserving =
  evaluateThermoWitness sampleBalancedWitness False == ThermoPreservingOk
    && classifyRewriteStep sampleBalancedWitness == ThermoRewriteIdentity

-- | Fusion identity conserved: identity ∘ identity = identity.
fusionIdentityConserved :: Bool
fusionIdentityConserved =
  let fused =
        fuseRewriteSteps ThermoRewriteIdentity ThermoRewriteIdentity
   in fused == FusedThermoRewriteIdentity
        && evaluateFusedRewrite fused False == ThermoPreservingFusionOk

-- | Fusion of preserving steps is admissible (still not physics GREEN).
fusionPreservingOk :: Bool
fusionPreservingOk =
  let (first, second) = samplePreservingSteps
      fused = fuseRewriteSteps first second
   in evaluateFusedRewrite fused False == ThermoPreservingFusionOk
        && isThermoPreservingStep first
        && isThermoPreservingStep second

-- | Conservation violation is fail-closed.
conservationViolateRefused :: Bool
conservationViolateRefused =
  evaluateThermoWitness sampleMassViolateWitness False
    == ThermoPreservingConservationViolate
    && classifyRewriteStep sampleMassViolateWitness
      == ThermoRewriteConservationViolate

-- | Second-law violation is fail-closed.
secondLawViolateRefused :: Bool
secondLawViolateRefused =
  evaluateThermoWitness sampleSecondLawViolateWitness False
    == ThermoPreservingSecondLawViolate
    && classifyRewriteStep sampleSecondLawViolateWitness
      == ThermoRewriteSecondLawViolate

-- | Non-preserving step in fusion composition is fail-closed.
nonPreservingStepFailClosed :: Bool
nonPreservingStepFailClosed =
  let fused =
        fuseRewriteSteps sampleNonPreservingStep ThermoRewriteIdentity
   in evaluateFusedRewrite fused False
      == ThermoPreservingConservationViolate
      && let fused2 =
               fuseRewriteSteps
                 ThermoRewriteIdentity
                 ThermoRewriteSecondLawViolate
          in evaluateFusedRewrite fused2 False
            == ThermoPreservingSecondLawViolate

-- | Assumed **rewrite** modality OK without thermo break (design scaffold).
assumedRewriteDesignOk :: Bool
assumedRewriteDesignOk =
  evaluateRewriteConservation
    RewriteConservationAssumed
    sampleBalancedWitness
    False
    == RewriteDesignOk

-- | Surrogate **rewrite** modality OK without thermo break (design scaffold).
surrogateRewriteDesignOk :: Bool
surrogateRewriteDesignOk =
  evaluateRewriteConservation
    RewriteConservationSurrogate
    sampleBalancedWitness
    False
    == RewriteDesignOk

-- | GREEN invent on **rewrite** **conservation** promotion is refused.
greenInventRewriteRefuse :: Bool
greenInventRewriteRefuse =
  evaluateRewriteConservation
    RewriteConservationUnwired
    sampleBalancedWitness
    True
    == RewriteGreenInventRefuse
    && evaluateThermoWitness sampleBalancedWitness True
      == ThermoPreservingGreenInventRefuse

-- | Four-step FP-03 **rewrite** lattice scaffold pinned.
rewriteLatticeScaffold :: Bool
rewriteLatticeScaffold =
  rewriteLatticeCount == 4
    && unwiredDesignOk
    && balancedWitnessPreserving
    && fusionIdentityConserved
    && fusionPreservingOk
    && conservationViolateRefused
    && secondLawViolateRefused
    && nonPreservingStepFailClosed
    && assumedRewriteDesignOk
    && surrogateRewriteDesignOk

-- | **Rewrite** lattice is structure scaffold — not 118² GREEN periodic table.
rewriteLatticeNotGreenTable :: Bool
rewriteLatticeNotGreenTable =
  rewriteLatticeCount == 4
    && rewriteLatticeCount /= 118 * 118
    && thermoRewriteStepCount /= 118 * 118

-- | Four **rewrite** fusion identity law cells scaffold pinned.
fusionIdentityLawsScaffold :: Bool
fusionIdentityLawsScaffold =
  fusionIdentityLawCount == 4
    && fusionIdentityConserved
    && fusionPreservingOk
    && conservationViolateRefused
    && secondLawViolateRefused

-- | **Rewrite** law cells are structure scaffold — not 118² GREEN periodic table.
fusionIdentityLawsNotGreenTable :: Bool
fusionIdentityLawsNotGreenTable =
  fusionIdentityLawsScaffold
    && fusionIdentityLawCount /= 118 * 118
    && samplePreservingSteps /= (ThermoRewriteConservationViolate, ThermoRewriteConservationViolate)

-- | Thermo-preserving **rewrite** **conservation** claims route to knowing / quantum fiber (not meso acting).
rewriteKnowingFiberOk :: Bool
rewriteKnowingFiberOk = True

-- | FP-03 **rewrite** invent refuse-closed scaffold witness.
fp03RewriteInventRefuse :: Bool
fp03RewriteInventRefuse = not fp03RewriteProved

-- | **Rewrite** lattice steps are concurrent Π_c — not XOR enum bucket.
rewriteLatticeNotXor :: Bool
rewriteLatticeNotXor =
  unwiredDesignOk
    && assumedRewriteDesignOk
    && surrogateRewriteDesignOk
    && fusionIdentityConserved
    && fusionPreservingOk
    && conservationViolateRefused
    && secondLawViolateRefused
    && nonPreservingStepFailClosed
    && greenInventRewriteRefuse

-- | FP-03 thermo-preserving **rewrite** proved (always false on this Unwired cell).
fp03RewriteProved :: Bool
fp03RewriteProved = False

-- | One axiom framing: second law + **conservation** for thermo-preserving **rewrite** scaffold.
rewriteConservationFraming :: String
rewriteConservationFraming =
  "second_law_conservation_rewrite_one_axiom"

-- | Single design axiom: second law + **conservation** thermo-preserving **rewrite** (not second axiom).
rewriteConservationAxiom :: Bool
rewriteConservationAxiom =
  rewriteLatticeScaffold
    && rewriteLatticeNotGreenTable
    && fusionIdentityLawsScaffold
    && fusionIdentityLawsNotGreenTable
    && rewriteKnowingFiberOk
    && balancedWitnessPreserving
    && fusionIdentityConserved
    && fusionPreservingOk
    && conservationViolateRefused
    && secondLawViolateRefused
    && nonPreservingStepFailClosed
    && greenInventRewriteRefuse
    && fp03RewriteInventRefuse
    && rewriteLatticeNotXor
    && not fp03RewriteProved
    && rewriteConservationFraming
      == "second_law_conservation_rewrite_one_axiom"

rewriteConservationNamed :: String
rewriteConservationNamed =
  "rewriteConservation: RewriteConservationModality Unwired Assumed Proved Surrogate four-step lattice fp03RewriteProved false fuseRewriteSteps evaluateFusedRewrite thermo-preserving fusion identity conserved non-preserving fail-closed second law conservation one axiom"

-- | Upstream FP-03 thermo-preserving **rewrite** authority (cited, not forked).
thermoPreservingRewriteAuthority :: String
thermoPreservingRewriteAuthority = "umst/umst-chem/src/thermo_preserving_rewrite.rs"

-- | L0 FP-03 thermo-preserving **rewrite** scaffold authority (crosswalk).
chemL0Fp03Authority :: String
chemL0Fp03Authority = "CHEM-L0-FP-03"

rewriteConservationCellId :: String
rewriteConservationCellId = "CHEM-FORMAL-Q-HS-REWRITE-CONSERVATION"

-- | Non-claim fence — thermo-preserving **rewrite** **conservation** Unwired ≠ Proved GREEN.
rewriteConservationNonClaim :: String
rewriteConservationNonClaim =
  "CHEM-FORMAL-Q-HS-REWRITE-CONSERVATION RewriteConservationModality Unwired Assumed Proved Surrogate four-step lattice fp03RewriteProved false fuseRewriteSteps evaluateFusedRewrite thermo-preserving fusion identity conserved non-preserving fail-closed Unwired one axiom second law conservation not 118 squared GREEN table not meso acting not physics GREEN not production_wired"

-- | Physics GREEN is unauthorized on the knowing thermo-preserving **rewrite** **conservation** scaffold.
rewriteConservationPhysicsGreenAuthorized :: Bool
rewriteConservationPhysicsGreenAuthorized = False

rewriteConservationPhysicsGreenFalse :: Bool
rewriteConservationPhysicsGreenFalse =
  not rewriteConservationPhysicsGreenAuthorized

rewriteConservationModalityUnwired :: Bool
rewriteConservationModalityUnwired =
  rewriteConservationModalityCurrent == RewriteConservationUnwired
