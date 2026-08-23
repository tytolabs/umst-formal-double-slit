-- SPDX-FileCopyrightText: 2026 Santosh Prabhu Shenbagamoorthy and Santhosh Shyamsundar
-- SPDX-License-Identifier: MIT

{-|
Module      : ChemGeometry
Description : Quantum-number Q-lattice types for the knowing fiber
Copyright   : (c) UMST Project, 2026

Discrete identity for chemistry formalization: occupied cells of the
hydrogenic quantum-number product @QLattice(n, ℓ, m_ℓ, m_s)@.

This module is the **quantum / knowing** fiber — not meso thermo (see
@umst-formal@ acting stack). Madelung @n+ℓ@ ordering assigns @Z@ to
occupied cells; chart projections are derived views, not primary identity.
-}
module ChemGeometry
  ( PrincipalN (..)
  , AzimuthalL (..)
  , MagneticMl (..)
  , SpinMs (..)
  , QLatticeCell (..)
  , mkPrincipalN
  , mkAzimuthalL
  , mkMagneticMl
  , validAzimuthal
  , validMagnetic
  , validQLatticeCell
  , madelungSum
  , spinMsHalf
  ) where

import Data.Ratio ((%))

-- | Principal quantum number @n@ (hydrogenic shell index, @n ≥ 1@).
newtype PrincipalN = PrincipalN {unPrincipalN :: Word}
  deriving (Eq, Ord, Show)

-- | Azimuthal quantum number @ℓ@ (@0 ≤ ℓ < n@).
newtype AzimuthalL = AzimuthalL {unAzimuthalL :: Word}
  deriving (Eq, Ord, Show)

-- | Magnetic quantum number @m_ℓ@ (@-ℓ ≤ m_ℓ ≤ ℓ@).
newtype MagneticMl = MagneticMl {unMagneticMl :: Int}
  deriving (Eq, Ord, Show)

-- | Spin projection @m_s ∈ {+½, -½}@ (two-valued for a single electron).
data SpinMs = SpinUp | SpinDown
  deriving (Eq, Ord, Show, Enum, Bounded)

-- | One occupied cell of the Q-lattice product space.
data QLatticeCell = QLatticeCell
  { qPrincipal :: !PrincipalN
  , qAzimuthal :: !AzimuthalL
  , qMagnetic :: !MagneticMl
  , qSpin :: !SpinMs
  }
  deriving (Eq, Show)

-- | Construct @n@ when @n ≥ 1@.
mkPrincipalN :: Word -> Maybe PrincipalN
mkPrincipalN 0 = Nothing
mkPrincipalN n = Just (PrincipalN n)

-- | Construct @ℓ@ as a raw azimuthal index (range checked against @n@ separately).
mkAzimuthalL :: Word -> AzimuthalL
mkAzimuthalL = AzimuthalL

-- | Construct @m_ℓ@ as a raw magnetic index (range checked against @ℓ@ separately).
mkMagneticMl :: Int -> MagneticMl
mkMagneticMl = MagneticMl

-- | @0 ≤ ℓ < n@.
validAzimuthal :: PrincipalN -> AzimuthalL -> Bool
validAzimuthal (PrincipalN n) (AzimuthalL ell) = ell < n

-- | @-ℓ ≤ m_ℓ ≤ ℓ@.
validMagnetic :: AzimuthalL -> MagneticMl -> Bool
validMagnetic (AzimuthalL ell) (MagneticMl m)
  | ell > fromIntegral (maxBound :: Int) = False
  | otherwise =
      let lell = fromIntegral ell
       in m >= negate lell && m <= lell

-- | Well-formed occupied Q-lattice cell.
validQLatticeCell :: QLatticeCell -> Bool
validQLatticeCell cell =
  validAzimuthal (qPrincipal cell) (qAzimuthal cell)
    && validMagnetic (qAzimuthal cell) (qMagnetic cell)

-- | Madelung ordering key @n + ℓ@ (canonical walk that assigns @Z@).
madelungSum :: PrincipalN -> AzimuthalL -> Word
madelungSum (PrincipalN n) (AzimuthalL ell) = n + ell

-- | Spin projection as a rational half (@±½@).
spinMsHalf :: SpinMs -> Rational
spinMsHalf SpinUp = 1 % 2
spinMsHalf SpinDown = (-1) % 2
