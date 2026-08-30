-- SPDX-FileCopyrightText: 2026 Santosh Prabhu Shenbagamoorthy and Santhosh Shyamsundar
-- SPDX-License-Identifier: MIT
{-|
Module      : UrgeKnowing.PadmaObservationCost
Description : Knowing-fiber Padma observation / read-tax cost honesty pin.
Copyright   : (c) UMST Project, 2026

Formal bools stay false. Not meso Economic. Not physics GREEN.
Cell: PADMA-FORMAL-KNOW-HS-OBS-COST
-}
module UrgeKnowing.PadmaObservationCost
  ( ObsCostModality (..)
  , obsCostModalityCurrent
  , physicsGreenFormal
  , productionWiredFormal
  , observationCostProvedFormal
  , physicsGreenStaysFalse
  , productionWiredStaysFalse
  , observationCostNotProved
  , modalityUnwired
  ) where

data ObsCostModality
  = ObsCostUnwired
  | ObsCostAssumed
  | ObsCostProved
  | ObsCostSurrogate
  deriving (Eq, Show)

obsCostModalityCurrent :: ObsCostModality
obsCostModalityCurrent = ObsCostUnwired

physicsGreenFormal :: Bool
physicsGreenFormal = False

productionWiredFormal :: Bool
productionWiredFormal = False

observationCostProvedFormal :: Bool
observationCostProvedFormal = False

physicsGreenStaysFalse :: Bool
physicsGreenStaysFalse = not physicsGreenFormal

productionWiredStaysFalse :: Bool
productionWiredStaysFalse = not productionWiredFormal

observationCostNotProved :: Bool
observationCostNotProved = not observationCostProvedFormal

modalityUnwired :: Bool
modalityUnwired = obsCostModalityCurrent == ObsCostUnwired
