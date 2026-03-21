module Main where

import Test.QuickCheck
import Data.Complex
import DensityState
import MeasurementChannel
import DoubleSlit
import MeasurementCost
import EpistemicGalois
import qualified LandauerExtension as LE
import MonoidalState
import System.Exit (exitFailure)

-- | Generator for random valid 2x2 Density Matrices
genDensityMatrix :: Gen Matrix2x2
genDensityMatrix = do
  uReal <- choose (-1, 1)
  uImag <- choose (-1, 1)
  vReal <- choose (-1, 1)
  vImag <- choose (-1, 1)
  let u = uReal :+ uImag
      v = vReal :+ vImag
      norm = magnitude u ** 2 + magnitude v ** 2
  if norm < 0.001 
    then return ((1, 0), (0, 0)) 
    else do
      let scaleFactor = 1.0 / sqrt norm
          u' = u * (scaleFactor :+ 0)
          v' = v * (scaleFactor :+ 0)
      return $ pureState (u', v')

-- | Property 1: Complementarity V^2 + I^2 <= 1
prop_complementarity :: Property
prop_complementarity = forAll genDensityMatrix $ \rho ->
  let v = fringeVisibility rho
      i = distinguishability rho
      sumSq = v*v + i*i
  in counterexample ("V^2 + I^2 = " ++ show sumSq) (sumSq <= 1.000001)

-- | Property 2: Which-path measurement forces V = 0 and preserves I
prop_whichPath_collapse :: Property
prop_whichPath_collapse = forAll genDensityMatrix $ \rho ->
  let rho' = applyKraus whichPathChannel rho
      v' = fringeVisibility rho'
      iOrig = distinguishability rho
      iNew = distinguishability rho'
  in v' < 1e-9 && abs (iOrig - iNew) < 1e-9

-- | Property 3: Landauer bound cost is non-negative and capped by one bit energy at 300K
prop_landauer_bounds :: Property
prop_landauer_bounds = forAll genDensityMatrix $ \rho ->
  let temp = 300.0
      cost = landauerCostDiagonal rho temp
      maxCost = landauerBitEnergy temp
  in cost >= -1e-25 && cost <= maxCost + 1e-25

------------------------------------------------------------------------
-- MeasurementCost properties (mirror of Lean/MeasurementCost.lean)
------------------------------------------------------------------------

-- | Property 4: Null probe cost is always exactly 0 (measurementCost_null)
prop_mc_null_zero :: Double -> Bool
prop_mc_null_zero t = measurementCostNull t == 0

-- | Property 5: Which-path cost is nonneg and ≤ one Landauer bit-energy
--   Mirrors measurementCost_nonneg + measurementCost_le_landauerBitEnergy
prop_mc_whichPath_bounds :: Property
prop_mc_whichPath_bounds =
  forAll (choose (0.0, 1.0)) $ \p0 ->
    let temp = 300.0
        cost = measurementCostWhichPath p0 temp
        cap  = landauerBitEnergy temp
    in counterexample ("cost=" ++ show cost ++ " cap=" ++ show cap)
         (cost >= -1e-25 && cost <= cap + 1e-25)

-- | Property 6: Which-path channel leaves cost unchanged
--   Mirrors measurementCost_whichPath_channel_invariant
prop_mc_channel_invariant :: Property
prop_mc_channel_invariant = forAll genDensityMatrix $ \rho ->
  let temp  = 300.0
      p0    = realPart (fst (fst rho))          -- top-left diagonal = path weight
      rho'  = applyKraus whichPathChannel rho
      p0'   = realPart (fst (fst rho'))
      cost  = measurementCostWhichPath p0  temp
      cost' = measurementCostWhichPath p0' temp
  in abs (cost - cost') < 1e-20

------------------------------------------------------------------------
-- EpistemicGalois properties (mirror of Lean/EpistemicGalois.lean)
------------------------------------------------------------------------

-- | requiredEnergy is monotonically increasing in bits
prop_eg_requiredEnergy_mono :: Property
prop_eg_requiredEnergy_mono =
  forAll (choose (1.0, 1000.0)) $ \t ->
    forAll (choose (0.0, 100.0)) $ \i1 ->
      forAll (choose (i1, i1 + 100.0)) $ \i2 ->
        requiredEnergyMono t i1 i2

-- | acquirableInfo is monotonically increasing in budget
prop_eg_acquirableInfo_mono :: Property
prop_eg_acquirableInfo_mono =
  forAll (choose (1.0, 1000.0)) $ \t ->
    forAll (choose (0.0, 100.0)) $ \e1 ->
      forAll (choose (e1, e1 + 100.0)) $ \e2 ->
        acquirableInfoMono t e1 e2

-- | L(I) <= E <=> I <= R(E)  (Galois Connection Adjunction)
prop_eg_landauer_galois :: Property
prop_eg_landauer_galois =
  forAll (choose (1.0, 1000.0)) $ \t ->
    forAll (choose (0.0, 10.0)) $ \i ->
      forAll (choose (0.0, 1e-19)) $ \e ->
        landauerGaloisConnection t i e

------------------------------------------------------------------------
-- LandauerExtension (upstream reference parity)
------------------------------------------------------------------------

prop_le_300k_pos :: Property
prop_le_300k_pos = property LE.landauerEnergy_300K_pos

prop_le_energy_mono :: Property
prop_le_energy_mono =
  forAll ((,) <$> choose (0.0, 800.0) <*> choose (0.0, 800.0)) $ \(a, b) ->
    let tLo = min a b
        tHi = max a b
     in counterexample ("E(" ++ show tLo ++ ") <= E(" ++ show tHi ++ ")")
          (LE.landauerEnergyMono tLo tHi)

------------------------------------------------------------------------
-- MonoidalState (upstream reference parity)
------------------------------------------------------------------------

genThermoState :: Gen ThermodynamicState
genThermoState =
  TS <$> choose (-1e4, 1e4) <*> choose (-1e6, 1e6) <*> choose (-1, 1) <*> choose (0, 1e3)

prop_ms_combine_one :: Property
prop_ms_combine_one =
  forAll genThermoState $ \s1 ->
    forAll genThermoState $ \s2 ->
      combine_one_check s1 s2

prop_ms_combine_zero :: Property
prop_ms_combine_zero =
  forAll genThermoState $ \s1 ->
    forAll genThermoState $ \s2 ->
      combine_zero_check s1 s2

prop_ms_density_between :: Property
prop_ms_density_between =
  forAll (choose (0.0, 1.0)) $ \w ->
    forAll genThermoState $ \s1 ->
      forAll genThermoState $ \s2 ->
        combine_density_between w s1 s2

main :: IO ()
main = do
  putStrLn "Running umst-formal-double-slit QuickCheck Properties..."
  putStrLn "\n--- Complementarity ---"
  r1 <- quickCheckResult prop_complementarity
  putStrLn "\n--- Which-Path Output ---"
  r2 <- quickCheckResult prop_whichPath_collapse
  putStrLn "\n--- Landauer Bounds ---"
  r3 <- quickCheckResult prop_landauer_bounds
  putStrLn "\n--- MeasurementCost: null = 0 ---"
  r4 <- quickCheckResult prop_mc_null_zero
  putStrLn "\n--- MeasurementCost: which-path nonneg + 1-bit cap ---"
  r5 <- quickCheckResult prop_mc_whichPath_bounds
  putStrLn "\n--- MeasurementCost: channel invariance ---"
  r6 <- quickCheckResult prop_mc_channel_invariant
  putStrLn "\n--- EpistemicGalois: requiredEnergy mono ---"
  r7 <- quickCheckResult prop_eg_requiredEnergy_mono
  putStrLn "\n--- EpistemicGalois: acquirableInfo mono ---"
  r8 <- quickCheckResult prop_eg_acquirableInfo_mono
  putStrLn "\n--- EpistemicGalois: L ⊣ R Adjunction ---"
  r9 <- quickCheckResult prop_eg_landauer_galois
  putStrLn "\n--- LandauerExtension: 300K positivity ---"
  r10 <- quickCheckResult prop_le_300k_pos
  putStrLn "\n--- LandauerExtension: energy monotone ---"
  r11 <- quickCheckResult prop_le_energy_mono
  putStrLn "\n--- MonoidalState: combine 1 ---"
  r12 <- quickCheckResult prop_ms_combine_one
  putStrLn "\n--- MonoidalState: combine 0 ---"
  r13 <- quickCheckResult prop_ms_combine_zero
  putStrLn "\n--- MonoidalState: density between ---"
  r14 <- quickCheckResult prop_ms_density_between

  if all isSuccess [r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14]
    then putStrLn "All properties passed!"
    else exitFailure
