-- |
-- Module      : MeasurementCost
-- Description : Thermodynamic energy lower-bound for quantum path measurement
--               (Haskell parity of Lean/MeasurementCost.lean)
module MeasurementCost
  ( kBoltzmannSI
  , landauerBitEnergy
  , infoEnergyLowerBound
  , pathEntropyBits
  , measurementCostNull
  , measurementCostWhichPath
  , measurementCostLe_landauerBitEnergy
  ) where

import DoubleSlit (kB, ln2, shannonBinary, landauerBitEnergy)

-- | SI Boltzmann constant (J/K).
kBoltzmannSI :: Double
kBoltzmannSI = kB

-- | Minimum energy to acquire `miBits` bits at temperature `t`.
infoEnergyLowerBound :: Double -> Double -> Double
infoEnergyLowerBound miBits t = miBits * landauerBitEnergy t

-- | Path-qubit entropy in bit-equivalents (nats / ln 2), in [0,1].
pathEntropyBits :: Double -> Double
pathEntropyBits p0 = shannonBinary p0 / ln2

-- | Null probe: zero mandatory dissipation.
measurementCostNull :: Double -> Double
measurementCostNull _t = 0

-- | Which-path probe cost. p0 = path weight of |0>, t = temperature.
measurementCostWhichPath :: Double -> Double -> Double
measurementCostWhichPath p0 t = infoEnergyLowerBound (pathEntropyBits p0) t

-- | Cost is bounded by one Landauer bit-energy (pathEntropyBits ≤ 1).
measurementCostLe_landauerBitEnergy :: Double -> Double -> Bool
measurementCostLe_landauerBitEnergy p0 t =
  measurementCostWhichPath p0 t <= landauerBitEnergy t
