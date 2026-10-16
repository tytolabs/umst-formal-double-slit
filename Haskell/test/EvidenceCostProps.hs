-- SPDX-FileCopyrightText: 2026 Santosh Prabhu Shenbagamoorthy and Santhosh Shyamsundar
-- SPDX-License-Identifier: Apache-2.0
-- |
-- A verification as an observation, twin of Lean/Learning/EvidenceCost.lean: each property evaluates umst-formal's
-- executable predicate 'secondLaw' (UMST.Process, at the Lake pin) on the reset of a verification's record and checks
-- the cost of its evidence bits. Floating point is the runtime edge: comparisons carry a relative tolerance of 1e-9.
module Main (main) where

import Test.QuickCheck
import System.Exit (exitFailure)

import UMSTFormal.Process
  ( HeatBath (..), ErasureProcess (..), ProbDist (..), ProbDist2 (..), Process (..), Prior (..), secondLaw, shannon2, kB )

leTol :: Double -> Double -> Bool
leTol a b = a <= b + 1e-9 * maximum [abs a, abs b, 1e-30]

landauerBitEnergy :: Double -> Double
landauerBitEnergy t = kB * t * log 2

genTemp :: Gen Double
genTemp = choose (1, 1000)

-- | The record of b evidence bits: the uniform distribution on 2^b states, reset to a point.
bitRecord :: Int -> Prior
bitRecord bits = Transformation (ProbDist (replicate n (1 / fromIntegral n))) (ProbDist (1 : replicate (n - 1) 0))
  where n = 2 ^ bits

-- | A reset work for b bits at temperature t: the Landauer work scaled by a factor in [1/2, 3] (some refused).
genWork :: Int -> Double -> Gen Double
genWork bits t = do
  s <- choose (0.5, 3)
  pure (t * fromIntegral bits * log 2 * s + 1e-3)

-- | Twin of evidenceBits_cost_ge: an admissible reset of b bits costs at least b k_B T ln 2.
prop_evidenceBits_cost_ge :: Property
prop_evidenceBits_cost_ge = forAll (choose (0, 6)) $ \bits -> forAll genTemp $ \t -> forAll (genWork bits t) $ \w ->
  let e = ErasureProcess (HeatBath t) w
  in secondLaw (Erase e) (bitRecord bits) ==> leTol (fromIntegral bits * landauerBitEnergy t) (kB * w)

-- | Twin of evidenceBitsPerJoule_le.
prop_evidenceBitsPerJoule_le :: Property
prop_evidenceBitsPerJoule_le = forAll (choose (0, 6)) $ \bits -> forAll genTemp $ \t -> forAll (genWork bits t) $ \w ->
  let e = ErasureProcess (HeatBath t) w
  in secondLaw (Erase e) (bitRecord bits) ==> leTol (fromIntegral bits / (kB * w)) (1 / landauerBitEnergy t)

-- | A path qubit by its Born weight and coherence magnitude |rho01| <= sqrt (p0 p1).
genPath :: Gen (Double, Double)
genPath = do
  p <- choose (0, 1)
  c <- choose (0, 1)
  pure (p, c * sqrt (p * (1 - p)))

-- | Twin of pathEvidencePerJoule_le and pathEvidence_cost_ge_max on admissible resets of the path record.
prop_pathEvidence_cost_ge_max :: Property
prop_pathEvidence_cost_ge_max = forAll genPath $ \(p, c) -> forAll genTemp $ \t -> forAll (choose (0.5, 3)) $ \s ->
  let sDiag = shannon2 (ProbDist2 p)
      w = t * sDiag * s + 1e-3
      e = ErasureProcess (HeatBath t) w
      bits = sDiag / log 2
      v = 2 * c
  in secondLaw (Erase e) (Erasure (ProbDist2 p)) ==>
       leTol (max (landauerBitEnergy t * bits) (kB * t * v * v / 2)) (kB * w)
         && leTol (bits / (kB * w)) (1 / landauerBitEnergy t)

main :: IO ()
main = do
  results <- mapM (quickCheckWithResult stdArgs { maxSuccess = 1000 })
    [prop_evidenceBits_cost_ge, prop_evidenceBitsPerJoule_le, prop_pathEvidence_cost_ge_max]
  if all isSuccess results then pure () else exitFailure
