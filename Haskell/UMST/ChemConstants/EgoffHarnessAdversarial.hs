-- SPDX-FileCopyrightText: 2026 Santosh Prabhu Shenbagamoorthy and Santhosh Shyamsundar
-- SPDX-License-Identifier: MIT
-- |
-- Module      : UMST.ChemConstants.EgoffHarnessAdversarial
-- Description : Quantum knowing — adversarial egoff harness drift refusal witness.
module UMST.ChemConstants.EgoffHarnessAdversarial
  ( soleAxiomCount
  , physicsGreen
  , sidecarModelPin
  , refuseSecondAxiom
  ) where

soleAxiomCount :: Int
soleAxiomCount = 1

physicsGreen :: Bool
physicsGreen = False

sidecarModelPin :: String
sidecarModelPin = "EGOFF_SIDECAR_MODEL"

refuseSecondAxiom :: Bool
refuseSecondAxiom = soleAxiomCount /= 2
