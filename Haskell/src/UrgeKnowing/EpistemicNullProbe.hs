-- SPDX-FileCopyrightText: 2026 Santosh Prabhu Shenbagamoorthy and Santhosh Shyamsundar
-- SPDX-License-Identifier: MIT

{-|
Module      : UrgeKnowing.EpistemicNullProbe
Description : EpistemicMI null probe I=0 on the knowing fiber
Copyright   : (c) UMST Project, 2026

§22.4 @epistemic_null_probe@ — the null @PathProbe@ carries zero epistemic MI
on the quantum knowing fiber. Mirrors Lean @EpistemicMI.epistemicMI_null@,
@epistemicMIBits_null@, and @epistemicLandauerCost_null@.

* @epistemicMINull@ — @EpistemicMI PathProbeNull ρ = 0@ for every density matrix.
* @epistemicMIBitsNull@ — bit-equivalent MI is likewise zero.
* @epistemicLandauerCostNull@ — Landauer hook vanishes under null readout.
* **One** design axiom (@epistemicNullProbeAxiom@): @physicalSecondLaw@ framing only;
  null-probe I=0 is definitional, not a second axiom.
* @physics_green@ stays false; modality @EpistemicNullProbeUnwired@.

Not ChemConstants. Cell: @URGE-FORMAL-Q-HS-EPISTEMIC-NULL-PROBE@.
Identity: @epistemic_null_probe@.
-}
module UrgeKnowing.EpistemicNullProbe
  ( epistemicMINull
  , epistemicMIBitsNull
  , epistemicLandauerCostNull
  , epistemicMINullAllStates
  , epistemicMIBitsNullAllStates
  , epistemicLandauerCostNullAllTemps
  , epistemicNullProbePolicy
  , EpistemicNullProbeModality (..)
  , epistemicNullProbeModalityCurrent
  , physicalSecondLawAxiom
  , landauerNotSecondAxiom
  , epistemicNullProbeAxiom
  , epistemicNullProbeNamed
  , epistemicNullProbeCellId
  , epistemicNullProbeNonClaim
  , epistemicNullProbePhysicsGreenAuthorized
  , epistemicNullProbePhysicsGreenFalse
  , epistemicNullProbeModalityUnwired
  , epistemicNullProbeKnowingFiberOk
  ) where

import DensityState (Matrix2x2)
import UrgeKnowing.LandauerHistoryLook
  ( PathProbe (..)
  , epistemicMI
  , epistemicMIBits
  , epistemicLandauerCost
  , physicalSecondLawAxiom
  , landauerNotSecondAxiom
  )

-- | Null probe epistemic MI is exactly zero (nats).
epistemicMINull :: Matrix2x2 -> Bool
epistemicMINull rho = epistemicMI PathProbeNull rho == 0

-- | Null probe bit-equivalent MI is exactly zero.
epistemicMIBitsNull :: Matrix2x2 -> Bool
epistemicMIBitsNull rho = epistemicMIBits PathProbeNull rho == 0

-- | Null probe Landauer cost vanishes at any temperature.
epistemicLandauerCostNull :: Matrix2x2 -> Double -> Bool
epistemicLandauerCostNull rho t =
  epistemicLandauerCost PathProbeNull rho t == 0

-- | @EpistemicMI PathProbeNull ρ = 0@ holds for representative states.
epistemicMINullAllStates :: Bool
epistemicMINullAllStates =
  epistemicMINull ((1, 0), (0, 0))
    && epistemicMINull ((0.5, 0), (0, 0.5))
    && epistemicMINull ((0.25, 0), (0, 0.75))

-- | @epistemicMIBits PathProbeNull ρ = 0@ holds for representative states.
epistemicMIBitsNullAllStates :: Bool
epistemicMIBitsNullAllStates =
  epistemicMIBitsNull ((1, 0), (0, 0))
    && epistemicMIBitsNull ((0.5, 0), (0, 0.5))
    && epistemicMIBitsNull ((0.25, 0), (0, 0.75))

-- | @epistemicLandauerCost PathProbeNull ρ T = 0@ holds for representative temps.
epistemicLandauerCostNullAllTemps :: Bool
epistemicLandauerCostNullAllTemps =
  epistemicLandauerCostNull ((0.5, 0), (0, 0.5)) 0
    && epistemicLandauerCostNull ((0.5, 0), (0, 0.5)) 300
    && epistemicLandauerCostNull ((1, 0), (0, 0)) 4.2

-- | Null-probe policy: no readout implies zero epistemic MI and zero Landauer hook.
epistemicNullProbePolicy :: Bool
epistemicNullProbePolicy =
  epistemicMINullAllStates
    && epistemicMIBitsNullAllStates
    && epistemicLandauerCostNullAllTemps

-- | Design modality for epistemic-null-probe claims (TYPE-03 preview).
data EpistemicNullProbeModality
  = EpistemicNullProbeUnwired
  | EpistemicNullProbeAssumed
  | EpistemicNullProbeProved
  | EpistemicNullProbeSurrogate
  deriving (Eq, Show)

epistemicNullProbeModalityCurrent :: EpistemicNullProbeModality
epistemicNullProbeModalityCurrent = EpistemicNullProbeUnwired

epistemicNullProbeAxiom :: Bool
epistemicNullProbeAxiom =
  epistemicNullProbePolicy
    && landauerNotSecondAxiom
    && epistemicNullProbeModalityUnwired
    && epistemicNullProbePhysicsGreenFalse

epistemicNullProbeNamed :: String
epistemicNullProbeNamed =
  "epistemic_null_probe: EpistemicMI null probe I=0 on knowing fiber; Landauer hook zero; physicalSecondLaw sole axiom framing"

epistemicNullProbeCellId :: String
epistemicNullProbeCellId = "URGE-FORMAL-Q-HS-EPISTEMIC-NULL-PROBE"

epistemicNullProbeNonClaim :: String
epistemicNullProbeNonClaim =
  "URGE-FORMAL-Q-HS-EPISTEMIC-NULL-PROBE epistemic_null_probe Unwired not Proved not GREEN not production_wired knowing fiber only not ChemConstants"

epistemicNullProbePhysicsGreenAuthorized :: Bool
epistemicNullProbePhysicsGreenAuthorized = False

epistemicNullProbePhysicsGreenFalse :: Bool
epistemicNullProbePhysicsGreenFalse = not epistemicNullProbePhysicsGreenAuthorized

epistemicNullProbeModalityUnwired :: Bool
epistemicNullProbeModalityUnwired =
  epistemicNullProbeModalityCurrent == EpistemicNullProbeUnwired

epistemicNullProbeKnowingFiberOk :: Bool
epistemicNullProbeKnowingFiberOk =
  epistemicNullProbeModalityUnwired && epistemicNullProbePhysicsGreenFalse
