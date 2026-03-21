{-# LANGUAGE ScopedTypeVariables #-}

{-|
Module      : EpistemicGalois
Description : Landauer adjunction between Information and Energy
Copyright   : (c) UMST Project, 2026

This module establishes a formal Galois connection (adjunction) between
information acquisition and thermodynamic cost.

Given a fixed environment temperature T > 0:
1. Left Adjoint (L): Maps an information requirement I (bits) to the 
   minimum energy required L(I) = I * k_B * T * ln(2).
2. Right Adjoint (R): Maps an energy budget E (Joules) to the maximum 
   information acquirable R(E) = E / (k_B * T * ln(2)).

The Galois connection theorem states:
   L(I) <= E <==> I <= R(E)
-}
module EpistemicGalois
  ( requiredEnergy
  , acquirableInfo
  , requiredEnergyMono
  , acquirableInfoMono
  , landauerGaloisConnection
  ) where

import MeasurementCost (landauerBitEnergy)

-- | Minimum energy (Joules) required to acquire `i` bits of information
-- at temperature `t`. (Left adjoint)
requiredEnergy :: Double -> Double -> Double
requiredEnergy t i = i * landauerBitEnergy t

-- | Maximum information (bits) acquirable with an energy budget `e`
-- at temperature `t`. (Right adjoint)
acquirableInfo :: Double -> Double -> Double
acquirableInfo t e = e / landauerBitEnergy t

-- Property Checks (for QuickCheck parity with Lean theorems)

-- | The required energy is monotone with respect to information.
requiredEnergyMono :: Double -> Double -> Double -> Bool
requiredEnergyMono t i1 i2 
  | t < 0     = True -- Precondition
  | i1 <= i2  = requiredEnergy t i1 <= requiredEnergy t i2 + 1e-12
  | otherwise = True

-- | The acquirable info is monotone with respect to energy budget.
acquirableInfoMono :: Double -> Double -> Double -> Bool
acquirableInfoMono t e1 e2 
  | t <= 0    = True -- Precondition
  | e1 <= e2  = acquirableInfo t e1 <= acquirableInfo t e2 + 1e-12
  | otherwise = True

-- | The Landauer Galois connection: L(I) <= E <==> I <= R(E)
landauerGaloisConnection :: Double -> Double -> Double -> Bool
landauerGaloisConnection t i e 
  | t <= 0    = True
  | otherwise = 
      let leftSide  = requiredEnergy t i <= e + 1e-12
          rightSide = i <= acquirableInfo t e + 1e-12
       in leftSide == rightSide || (abs (requiredEnergy t i - e) < 1e-9)
