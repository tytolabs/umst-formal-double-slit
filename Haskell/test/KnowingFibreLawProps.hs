-- SPDX-FileCopyrightText: 2026 Santosh Prabhu Shenbagamoorthy and Santhosh Shyamsundar
-- SPDX-License-Identifier: MIT
-- |
-- The knowing fibre against the one second law, twin of Lean/KnowingFibreInstance.lean and
-- Lean/KnowingFibreLaw.lean: each property evaluates umst-formal's executable predicate 'secondLaw'
-- (UMST.Process, imported from umst-formal at the Lake pin, only that module) on the knowing fibre's processes.
-- Floating point is the runtime edge: comparisons carry a relative tolerance of 1e-9.
module Main (main) where

import Test.QuickCheck
import System.Exit (exitFailure)

import qualified DoubleSlit as DS

import UMSTFormal.Process
  ( HeatBath (..), ErasureProcess (..), FeedbackProcess (..), ProbDist2 (..), Process (..), Prior (..)
  , JointDist2 (..), secondLaw, mutualInformation2, jointEntropy2, marginalX2, marginalY2, shannon2, kB )

-- | A path qubit by its Born weight p0 and the magnitude of its coherence |rho01| <= sqrt (p0 p1).
data PathQubit = PathQubit { weight0 :: Double, coherence :: Double }
  deriving (Show)

genPathQubit :: Gen PathQubit
genPathQubit = do
  p <- choose (0, 1)
  t <- choose (0, 1)
  pure (PathQubit p (t * sqrt (p * (1 - p))))

genTemp :: Gen Double
genTemp = choose (1, 1000)

-- | Joules are of order k_B T ~ 1e-21; tolerances are relative to the larger side.
leTol :: Double -> Double -> Bool
leTol a b = a <= b + 1e-9 * maximum [abs a, abs b, 1e-30]

eqTol :: Double -> Double -> Bool
eqTol a b = leTol a b && leTol b a

distinguishability, fringeVisibility :: PathQubit -> Double
distinguishability q = abs (weight0 q - (1 - weight0 q))
fringeVisibility q = 2 * coherence q

-- | The Born prior of the path (umst-formal's two-state distribution).
pathBornDist :: PathQubit -> ProbDist2
pathBornDist = ProbDist2 . weight0

-- | Diagonal (path) entropy in nats.
vonNeumannDiagonal :: PathQubit -> Double
vonNeumannDiagonal = shannon2 . pathBornDist

landauerBitEnergy :: Double -> Double
landauerBitEnergy t = kB * t * log 2

pathEntropyBits :: PathQubit -> Double
pathEntropyBits q = vonNeumannDiagonal q / log 2

data PathProbe = NullProbe | WhichPathProbe
  deriving (Show)

instance Arbitrary PathProbe where
  arbitrary = elements [NullProbe, WhichPathProbe]

epistemicMI :: PathProbe -> PathQubit -> Double
epistemicMI NullProbe _ = 0
epistemicMI WhichPathProbe q = vonNeumannDiagonal q

measurementCost :: PathProbe -> PathQubit -> Double -> Double
measurementCost p q t = landauerBitEnergy t * (epistemicMI p q / log 2)

-- | The erasure at work T * S of the path prior.
pathBornEraseProcess :: PathQubit -> Double -> ErasureProcess
pathBornEraseProcess q t = ErasureProcess (HeatBath t) (t * vonNeumannDiagonal q)

epistemicMeasureFeedback :: PathProbe -> PathQubit -> Double -> FeedbackProcess
epistemicMeasureFeedback p q t = FeedbackProcess (HeatBath t) (measurementCost p q t) 0

-- | The record of a Lüders which-path measurement: the record equals the path.
pathRecordJoint :: PathQubit -> JointDist2
pathRecordJoint q = JointDist2 (weight0 q) 0 0 (1 - weight0 q)

-- | An erasure of the path record that obeys the erase case: work T * S plus a nonnegative excess.
genAdmissibleErase :: PathQubit -> Double -> Gen ErasureProcess
genAdmissibleErase q t = do
  s <- choose (0, 2)
  pure (ErasureProcess (HeatBath t) (t * vonNeumannDiagonal q * (1 + s) + s))

-- | The erase hypothesis for the path qubit, held only when the erase case of the second law holds: the
-- constructor is the check, so an inadmissible erasure has no hypothesis (a typed refusal).
newtype PathEraseHypothesis = PathEraseHypothesis ErasureProcess

pathEraseHypothesis :: PathQubit -> ErasureProcess -> Maybe PathEraseHypothesis
pathEraseHypothesis q e
  | secondLaw (Erase e) (Erasure (pathBornDist q)) = Just (PathEraseHypothesis e)
  | otherwise = Nothing

-- | The measure-feedback hypothesis: a record information equal to the probe's and the measure-feedback case.
data MeasureFeedbackHypothesis = MeasureFeedbackHypothesis { hypMi :: Double, hypProcess :: FeedbackProcess }

measureFeedbackHypothesis :: PathProbe -> PathQubit -> FeedbackProcess -> Double -> Maybe MeasureFeedbackHypothesis
measureFeedbackHypothesis p q f mi
  | eqTol mi (epistemicMI p q) && secondLaw (MeasureFeedback f) (Feedback mi) = Just (MeasureFeedbackHypothesis mi f)
  | otherwise = Nothing

-- KnowingFibreInstance ---------------------------------------------------------------------------------------------

prop_shannonEntropy_pathBornDist :: Property
prop_shannonEntropy_pathBornDist = forAll genPathQubit $ \q ->
  eqTol (shannon2 (pathBornDist q)) (vonNeumannDiagonal q)

prop_pathBornErase_secondLaw :: Property
prop_pathBornErase_secondLaw = forAll genPathQubit $ \q -> forAll genTemp $ \t ->
  let e = pathBornEraseProcess q t
  in secondLaw (Erase e { work = work e * (1 + 1e-12) + 1e-300 }) (Erasure (pathBornDist q))

prop_pathBornErase_processFamily :: Property
prop_pathBornErase_processFamily = forAll genPathQubit $ \q -> forAll genTemp $ \t ->
  let e = pathBornEraseProcess q t
      prior = Erasure (pathBornDist q)
  in secondLaw (Erase e { work = work e * (1 + 1e-12) + 1e-300 }) prior
       && not (secondLaw (MeasureFeedback (epistemicMeasureFeedback WhichPathProbe q t)) prior)

prop_PathEraseHypothesis :: Property
prop_PathEraseHypothesis = forAll genPathQubit $ \q -> forAll genTemp $ \t -> forAll (choose (0, 2000)) $ \w ->
  let e = ErasureProcess (HeatBath t) w
  in case pathEraseHypothesis q e of
       Just _ -> leTol (vonNeumannDiagonal q * t) w
       Nothing -> not (leTol (vonNeumannDiagonal q * t) (w * (1 - 1e-9)))

prop_pathEraseHypothesis_default :: Property
prop_pathEraseHypothesis_default = forAll genPathQubit $ \q -> forAll genTemp $ \t ->
  let e = pathBornEraseProcess q t
  in case pathEraseHypothesis q e { work = work e * (1 + 1e-12) + 1e-300 } of
       Just _ -> True
       Nothing -> False

prop_MeasureFeedbackHypothesis :: PathProbe -> Property
prop_MeasureFeedbackHypothesis p = forAll genPathQubit $ \q -> forAll genTemp $ \t -> forAll (choose (0.5, 1.5)) $ \r ->
  let f = (epistemicMeasureFeedback p q t) { extWork = r * measurementCost p q t }
  in abs (r - 1) > 1e-6 ==>
       case measureFeedbackHypothesis p q f (epistemicMI p q) of
         Just h -> leTol (extWork (hypProcess h)) (kB * t * hypMi h)
         Nothing -> extWork f > kB * t * epistemicMI p q

prop_landauerCostDiagonal_eq_kB_eraseWork :: Property
prop_landauerCostDiagonal_eq_kB_eraseWork = forAll genPathQubit $ \q -> forAll genTemp $ \t ->
  eqTol (landauerBitEnergy t * pathEntropyBits q) (kB * work (pathBornEraseProcess q t))

prop_measurementCost_eq_kBT_epistemicMI :: PathProbe -> Property
prop_measurementCost_eq_kBT_epistemicMI p = forAll genPathQubit $ \q -> forAll genTemp $ \t ->
  eqTol (measurementCost p q t) (kB * t * epistemicMI p q)

prop_measureFeedback_admissible_iff :: PathProbe -> Property
prop_measureFeedback_admissible_iff p = forAll genPathQubit $ \q -> forAll genTemp $ \t ->
  forAll (choose (0.5, 1.5)) $ \r ->
    let f = (epistemicMeasureFeedback p q t) { extWork = r * measurementCost p q t }
        lhs = secondLaw (MeasureFeedback f) (Feedback (epistemicMI p q))
        rhs = extWork f <= kB * t * epistemicMI p q
    in abs (r - 1) > 1e-6 ==> lhs == rhs

prop_measureFeedback_null_instance :: Property
prop_measureFeedback_null_instance = forAll genPathQubit $ \q -> forAll genTemp $ \t ->
  secondLaw (MeasureFeedback (epistemicMeasureFeedback NullProbe q t)) (Feedback (mutualInformation2 (JointDist2 0.25 0.25 0.25 0.25)))

-- KnowingFibreLaw --------------------------------------------------------------------------------------------------

prop_pathRecordJoint_marginalX :: Property
prop_pathRecordJoint_marginalX = forAll genPathQubit $ \q -> eqTol (p0 (marginalX2 (pathRecordJoint q))) (weight0 q)

prop_pathRecordJoint_marginalY :: Property
prop_pathRecordJoint_marginalY = forAll genPathQubit $ \q -> eqTol (p0 (marginalY2 (pathRecordJoint q))) (weight0 q)

prop_pathRecordJoint_jointEntropy :: Property
prop_pathRecordJoint_jointEntropy = forAll genPathQubit $ \q ->
  eqTol (jointEntropy2 (pathRecordJoint q)) (vonNeumannDiagonal q)

prop_pathRecordJoint_mutualInformation :: Property
prop_pathRecordJoint_mutualInformation = forAll genPathQubit $ \q ->
  eqTol (mutualInformation2 (pathRecordJoint q)) (epistemicMI WhichPathProbe q)

prop_whichPath_measureFeedback_secondLaw :: Property
prop_whichPath_measureFeedback_secondLaw = forAll genPathQubit $ \q -> forAll genTemp $ \t ->
  let f = epistemicMeasureFeedback WhichPathProbe q t
  in secondLaw (MeasureFeedback f { extWork = extWork f * (1 - 1e-12) }) (Feedback (mutualInformation2 (pathRecordJoint q)))

prop_measureFeedback_extWork_le_landauerBitEnergy :: PathProbe -> Property
prop_measureFeedback_extWork_le_landauerBitEnergy p = forAll genPathQubit $ \q -> forAll genTemp $ \t ->
  forAll (choose (-2, 2)) $ \dF -> forAll (choose (-1, 1.2)) $ \r ->
    let mi = epistemicMI p q
        f = FeedbackProcess (HeatBath t) (r * (negate dF * 1e-21 + kB * t * mi)) (dF * 1e-21)
    in secondLaw (MeasureFeedback f) (Feedback mi) ==>
         leTol (extWork f) (negate (deltaFreeEnergy f) + landauerBitEnergy t)

-- | A readout (work r times its cost, no free-energy change) admitted by the measure-feedback case of the second law
-- against the probe's information costs at most k_B T ln 2; readouts above their cost are refused (discarded).
prop_readoutCost_le_landauerBitEnergy_of_secondLaw :: PathProbe -> Property
prop_readoutCost_le_landauerBitEnergy_of_secondLaw p = forAll genPathQubit $ \q -> forAll genTemp $ \t ->
  forAll (choose (0, 1.5)) $ \r ->
    let f = (epistemicMeasureFeedback p q t) { extWork = r * measurementCost p q t }
    in secondLaw (MeasureFeedback f) (Feedback (epistemicMI p q)) ==> leTol (extWork f) (landauerBitEnergy t)

prop_erase_pathRecord_cost_ge_bits :: Property
prop_erase_pathRecord_cost_ge_bits = forAll genPathQubit $ \q -> forAll genTemp $ \t ->
  forAll (genAdmissibleErase q t) $ \e ->
    secondLaw (Erase e) (Erasure (pathBornDist q)) && leTol (landauerBitEnergy t * pathEntropyBits q) (kB * work e)

prop_erase_pathRecord_work :: Property
prop_erase_pathRecord_work = forAll genPathQubit $ \q -> forAll genTemp $ \t ->
  forAll (choose (0, 2000)) $ \w ->
    let e = ErasureProcess (HeatBath t) w
    in secondLaw (Erase e) (Erasure (pathBornDist q)) ==> leTol (vonNeumannDiagonal q * t) w

prop_negMulLog_ge_mul_one_sub :: Property
prop_negMulLog_ge_mul_one_sub = forAll (choose (0, 3)) $ \x ->
  leTol (x * (1 - x)) (if x <= 0 then 0 else negate (x * log x))

prop_one_sub_distinguishability_sq_le_two_mul_entropy :: Property
prop_one_sub_distinguishability_sq_le_two_mul_entropy = forAll genPathQubit $ \q ->
  leTol (1 - distinguishability q ^ (2 :: Int)) (2 * vonNeumannDiagonal q)

prop_erase_pathRecord_cost_ge_complementarity :: Property
prop_erase_pathRecord_cost_ge_complementarity = forAll genPathQubit $ \q -> forAll genTemp $ \t ->
  forAll (genAdmissibleErase q t) $ \e ->
    secondLaw (Erase e) (Erasure (pathBornDist q))
      && leTol (kB * t * (1 - distinguishability q ^ (2 :: Int)) / 2) (kB * work e)

prop_erase_pathRecord_cost_ge_visibility_sq :: Property
prop_erase_pathRecord_cost_ge_visibility_sq = forAll genPathQubit $ \q -> forAll genTemp $ \t ->
  forAll (genAdmissibleErase q t) $ \e ->
    secondLaw (Erase e) (Erasure (pathBornDist q)) && leTol (kB * t * fringeVisibility q ^ (2 :: Int) / 2) (kB * work e)

prop_measure_then_erase_no_net_work :: Property
prop_measure_then_erase_no_net_work = forAll genPathQubit $ \q -> forAll genTemp $ \t ->
  forAll (genAdmissibleErase q t) $ \e -> forAll (choose (-1, 1)) $ \r ->
    let mi = mutualInformation2 (pathRecordJoint q)
        f = FeedbackProcess (HeatBath t) (r * kB * t * mi) 0
    in secondLaw (MeasureFeedback f) (Feedback mi) && secondLaw (Erase e) (Erasure (pathBornDist q))
         && leTol (extWork f) (kB * work e)

-- | The reset of LandauerBound: its bound landauerCostDiagonal <= dissipatedHeat, with the heat k_B W of an
-- erasure that obeys the erase case.
prop_resetProcess_of_secondLaw :: Property
prop_resetProcess_of_secondLaw = forAll genPathQubit $ \q -> forAll genTemp $ \t ->
  forAll (genAdmissibleErase q t) $ \e ->
    let dissipatedHeat = kB * work e
    in secondLaw (Erase e) (Erasure (pathBornDist q)) && leTol (landauerBitEnergy t * pathEntropyBits q) dissipatedHeat

-- | The double-slit library's bit energy (its k_B from its constants twin) equals k_B T ln 2 with umst-formal's k_B.
prop_landauerBitEnergy_eq_kB :: Property
prop_landauerBitEnergy_eq_kB = forAll genTemp $ \t -> eqTol (DS.landauerBitEnergy t) (kB * t * log 2)

prop_measurementCost_le_landauerBitEnergy :: PathProbe -> Property
prop_measurementCost_le_landauerBitEnergy p = forAll genPathQubit $ \q -> forAll genTemp $ \t ->
  leTol (measurementCost p q t) (landauerBitEnergy t)

checks :: [(String, Property)]
checks =
  [ ("shannonEntropy_pathBornDist", prop_shannonEntropy_pathBornDist)
  , ("pathBornErase_secondLaw", prop_pathBornErase_secondLaw)
  , ("pathBornErase_processFamily", prop_pathBornErase_processFamily)
  , ("landauerCostDiagonal_eq_kB_eraseWork", prop_landauerCostDiagonal_eq_kB_eraseWork)
  , ("PathEraseHypothesis", prop_PathEraseHypothesis)
  , ("pathEraseHypothesis_default", prop_pathEraseHypothesis_default)
  , ("MeasureFeedbackHypothesis", property prop_MeasureFeedbackHypothesis)
  , ("measurementCost_eq_kBT_epistemicMI", property prop_measurementCost_eq_kBT_epistemicMI)
  , ("measureFeedback_admissible_iff", property prop_measureFeedback_admissible_iff)
  , ("measureFeedback_null_instance", prop_measureFeedback_null_instance)
  , ("pathRecordJoint_marginalX", prop_pathRecordJoint_marginalX)
  , ("pathRecordJoint_marginalY", prop_pathRecordJoint_marginalY)
  , ("pathRecordJoint_jointEntropy", prop_pathRecordJoint_jointEntropy)
  , ("pathRecordJoint_mutualInformation", prop_pathRecordJoint_mutualInformation)
  , ("whichPath_measureFeedback_secondLaw", prop_whichPath_measureFeedback_secondLaw)
  , ("landauerBitEnergy_eq_kB", prop_landauerBitEnergy_eq_kB)
  , ("measureFeedback_extWork_le_landauerBitEnergy", property prop_measureFeedback_extWork_le_landauerBitEnergy)
  , ("readoutCost_le_landauerBitEnergy_of_secondLaw", property prop_readoutCost_le_landauerBitEnergy_of_secondLaw)
  , ("erase_pathRecord_work", prop_erase_pathRecord_work)
  , ("erase_pathRecord_cost_ge_bits", prop_erase_pathRecord_cost_ge_bits)
  , ("negMulLog_ge_mul_one_sub", prop_negMulLog_ge_mul_one_sub)
  , ("one_sub_distinguishability_sq_le_two_mul_entropy", prop_one_sub_distinguishability_sq_le_two_mul_entropy)
  , ("erase_pathRecord_cost_ge_complementarity", prop_erase_pathRecord_cost_ge_complementarity)
  , ("erase_pathRecord_cost_ge_visibility_sq", prop_erase_pathRecord_cost_ge_visibility_sq)
  , ("measure_then_erase_no_net_work", prop_measure_then_erase_no_net_work)
  , ("resetProcess_of_secondLaw", prop_resetProcess_of_secondLaw)
  , ("measurementCost_le_landauerBitEnergy", property prop_measurementCost_le_landauerBitEnergy)
  ]

main :: IO ()
main = do
  putStrLn "Knowing fibre against umst-formal's secondLaw"
  rs <- mapM (\(name, p) -> putStrLn ("--- " ++ name) >> quickCheckWithResult stdArgs { maxSuccess = 500 } p) checks
  if all isSuccess rs then putStrLn "All knowing-fibre properties passed." else exitFailure
