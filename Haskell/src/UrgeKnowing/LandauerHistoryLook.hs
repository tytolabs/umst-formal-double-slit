-- SPDX-FileCopyrightText: 2026 Santosh Prabhu Shenbagamoorthy and Santhosh Shyamsundar
-- SPDX-License-Identifier: MIT

{-|
Module      : UrgeKnowing.LandauerHistoryLook
Description : Landauer bound of a look at rollout history on the knowing fiber
Copyright   : (c) UMST Project, 2026

§5.2 / §22.4 @landauerHistoryLook@ — measurement / Landauer cost of a **look at history**
along a finite rollout horizon. Mirrors Lean @EpistemicTrajectoryMI@ and
@EpistemicMI@ epistemic-Landauer hooks on the quantum knowing fiber.

* @historyLookLandauerCost@ — cumulative Landauer hook for inspecting `n` history steps.
* @epistemicLandauerCost@ — per-step probe-indexed Landauer cost (≤ one bit-energy).
* **One** design axiom (@landauerHistoryLookAxiom@): @physicalSecondLaw@ framing only;
  Landauer cost is **not** a second axiom.
* @physics_green@ stays false; modality @LandauerHistoryLookUnwired@.

Cell: @URGE-FORMAL-Q-HS-LANDAUER-HISTORY-LOOK@.
Identity: @landauer_history_look@.
-}
module UrgeKnowing.LandauerHistoryLook
  ( PathProbe (..)
  , epistemicMI
  , epistemicMIBits
  , epistemicLandauerCost
  , historyLookLandauerCost
  , historyLookMIBits
  , epistemicMINonneg
  , epistemicMIBitsLeOne
  , epistemicLandauerCostNonneg
  , epistemicLandauerCostLeLandauerBitEnergy
  , historyLookLandauerCostNonneg
  , historyLookLandauerCostLeNBitEnergy
  , historyLookLandauerCostNullZero
  , historyLookMIBitsNonneg
  , historyLookMIBitsLeN
  , LandauerHistoryLookModality (..)
  , landauerHistoryLookModalityCurrent
  , physicalSecondLawAxiom
  , landauerNotSecondAxiom
  , landauerHistoryLookAxiom
  , landauerHistoryLookNamed
  , landauerHistoryLookCellId
  , landauerHistoryLookNonClaim
  , landauerHistoryLookPhysicsGreenAuthorized
  , landauerHistoryLookPhysicsGreenFalse
  , landauerHistoryLookModalityUnwired
  , landauerHistoryLookKnowingFiberOk
  ) where

import DensityState (Matrix2x2)
import DoubleSlit (ln2, vonNeumannDiagonal, landauerBitEnergy)
import MeasurementCost (infoEnergyLowerBound)

-- | Minimal probe kind for epistemic MI on the knowing fiber.
data PathProbe
  = PathProbeNull
  | PathProbeWhichPath
  deriving (Eq, Show)

-- | Epistemic mutual-information surrogate in nats, indexed by probe kind.
epistemicMI :: PathProbe -> Matrix2x2 -> Double
epistemicMI PathProbeNull _ = 0
epistemicMI PathProbeWhichPath rho = vonNeumannDiagonal rho

-- | Bit-equivalent epistemic MI.
epistemicMIBits :: PathProbe -> Matrix2x2 -> Double
epistemicMIBits p rho = epistemicMI p rho / ln2

-- | Per-step Landauer hook from probe-indexed epistemic MI bits.
epistemicLandauerCost :: PathProbe -> Matrix2x2 -> Double -> Double
epistemicLandauerCost p rho t =
  infoEnergyLowerBound (epistemicMIBits p rho) t

-- | Cumulative bit-equivalent MI for a look at `n` history steps (scaffold rollout).
historyLookMIBits :: Int -> PathProbe -> Matrix2x2 -> Double
historyLookMIBits n p rho = fromIntegral n * epistemicMIBits p rho

-- | Cumulative Landauer cost for a look at `n` rollout-history steps at temperature `t`.
historyLookLandauerCost :: Int -> PathProbe -> Matrix2x2 -> Double -> Double
historyLookLandauerCost n p rho t =
  fromIntegral n * epistemicLandauerCost p rho t

epistemicMINonneg :: PathProbe -> Matrix2x2 -> Bool
epistemicMINonneg p rho = epistemicMI p rho >= 0

epistemicMIBitsLeOne :: PathProbe -> Matrix2x2 -> Bool
epistemicMIBitsLeOne p rho = epistemicMIBits p rho <= 1 + 1e-12

epistemicLandauerCostNonneg :: PathProbe -> Matrix2x2 -> Double -> Bool
epistemicLandauerCostNonneg p rho t =
  if t >= 0 then epistemicLandauerCost p rho t >= 0 else True

epistemicLandauerCostLeLandauerBitEnergy :: PathProbe -> Matrix2x2 -> Double -> Bool
epistemicLandauerCostLeLandauerBitEnergy p rho t =
  if t >= 0
    then epistemicLandauerCost p rho t <= landauerBitEnergy t + 1e-18
    else True

historyLookLandauerCostNonneg :: Int -> PathProbe -> Matrix2x2 -> Double -> Bool
historyLookLandauerCostNonneg n p rho t =
  if t >= 0 && n >= 0
    then historyLookLandauerCost n p rho t >= 0
    else True

historyLookLandauerCostLeNBitEnergy :: Int -> PathProbe -> Matrix2x2 -> Double -> Bool
historyLookLandauerCostLeNBitEnergy n p rho t =
  if t >= 0 && n >= 0
    then historyLookLandauerCost n p rho t <= fromIntegral n * landauerBitEnergy t + 1e-15
    else True

historyLookLandauerCostNullZero :: Int -> Matrix2x2 -> Double -> Bool
historyLookLandauerCostNullZero n rho t =
  historyLookLandauerCost n PathProbeNull rho t == 0

historyLookMIBitsNonneg :: Int -> PathProbe -> Matrix2x2 -> Bool
historyLookMIBitsNonneg n p rho =
  if n >= 0 then historyLookMIBits n p rho >= 0 else True

historyLookMIBitsLeN :: Int -> PathProbe -> Matrix2x2 -> Bool
historyLookMIBitsLeN n p rho =
  if n >= 0 then historyLookMIBits n p rho <= fromIntegral n + 1e-12 else True

-- | Design modality for landauer-history-look claims (TYPE-03 preview).
data LandauerHistoryLookModality
  = LandauerHistoryLookUnwired
  | LandauerHistoryLookAssumed
  | LandauerHistoryLookProved
  | LandauerHistoryLookSurrogate
  deriving (Eq, Show)

landauerHistoryLookModalityCurrent :: LandauerHistoryLookModality
landauerHistoryLookModalityCurrent = LandauerHistoryLookUnwired

-- | Sole axiom framing: physical second law (design witness — not a new postulate here).
physicalSecondLawAxiom :: String
physicalSecondLawAxiom = "LandauerLaw.physicalSecondLaw"

landauerNotSecondAxiom :: Bool
landauerNotSecondAxiom = physicalSecondLawAxiom /= "landauer_second_axiom"

landauerHistoryLookAxiom :: Bool
landauerHistoryLookAxiom =
  epistemicLandauerCostNonneg PathProbeWhichPath ((1, 0), (0, 0)) 300
    && historyLookLandauerCostNullZero 3 ((1, 0), (0, 0)) 300
    && landauerNotSecondAxiom
    && historyLookLandauerCostLeNBitEnergy 2 PathProbeWhichPath ((0.5, 0), (0, 0.5)) 300

landauerHistoryLookNamed :: String
landauerHistoryLookNamed =
  "landauerHistoryLook: Landauer bound of a look at rollout history; cumulative epistemic MI bits; physicalSecondLaw sole axiom framing"

landauerHistoryLookCellId :: String
landauerHistoryLookCellId = "URGE-FORMAL-Q-HS-LANDAUER-HISTORY-LOOK"

landauerHistoryLookNonClaim :: String
landauerHistoryLookNonClaim =
  "URGE-FORMAL-Q-HS-LANDAUER-HISTORY-LOOK landauer_history_look Unwired not Proved not GREEN not production_wired knowing fiber only"

landauerHistoryLookPhysicsGreenAuthorized :: Bool
landauerHistoryLookPhysicsGreenAuthorized = False

landauerHistoryLookPhysicsGreenFalse :: Bool
landauerHistoryLookPhysicsGreenFalse = not landauerHistoryLookPhysicsGreenAuthorized

landauerHistoryLookModalityUnwired :: Bool
landauerHistoryLookModalityUnwired =
  landauerHistoryLookModalityCurrent == LandauerHistoryLookUnwired

landauerHistoryLookKnowingFiberOk :: Bool
landauerHistoryLookKnowingFiberOk =
  landauerHistoryLookModalityUnwired && landauerHistoryLookPhysicsGreenFalse
