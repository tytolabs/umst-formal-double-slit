module DoubleSlit where

import Data.Complex
import DensityState

kB :: Double
kB = 1.380649e-23

ln2 :: Double
ln2 = 0.69314718056

pathWeight :: Matrix2x2 -> Int -> Double
pathWeight ((a, _), (_, _)) 0 = realPart a
pathWeight ((_, _), (_, d)) 1 = realPart d
pathWeight _ _ = 0

distinguishability :: Matrix2x2 -> Double
distinguishability rho = abs (pathWeight rho 0 - pathWeight rho 1)

fringeVisibility :: Matrix2x2 -> Double
fringeVisibility ((_, b), (_, _)) = 2 * magnitude b

shannonBinary :: Double -> Double
shannonBinary p 
  | p <= 0 || p >= 1 = 0
  | otherwise = - p * log p - (1-p) * log (1-p)

vonNeumannDiagonal :: Matrix2x2 -> Double
vonNeumannDiagonal rho = shannonBinary (pathWeight rho 0)

landauerCostDiagonal :: Matrix2x2 -> Double -> Double
landauerCostDiagonal rho temp = kB * temp * ln2 * (vonNeumannDiagonal rho / ln2)

landauerBitEnergy :: Double -> Double
landauerBitEnergy temp = kB * temp * ln2
