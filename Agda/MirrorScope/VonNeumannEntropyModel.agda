-- SPDX-FileCopyrightText: 2026 Santosh Prabhu Shenbagamoorthy and Santhosh Shyamsundar
-- SPDX-License-Identifier: MIT
------------------------------------------------------------------------
-- P0-13b: entropy carrier + spectral laws as scoped records (mirror Coq).
------------------------------------------------------------------------

module MirrorScope.VonNeumannEntropyModel where

open import VonNeumannEntropySpec

record VonNeumannEntropyScope : Set₁ where
  field
    carrier     : RealEntropyCarrier
    entropy     : VonNeumannEntropyProps carrier
    shannon     : ShannonBinaryProps carrier entropy
    measurement : MeasurementEntropyProps carrier entropy

module WithVonNeumannEntropy (S : VonNeumannEntropyScope) where
  open VonNeumannEntropyScope S
  open RealEntropyCarrier carrier public
  open VonNeumannEntropyProps entropy public
  open ShannonBinaryProps shannon public
  open MeasurementEntropyProps measurement public
