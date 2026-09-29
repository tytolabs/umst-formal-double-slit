-- SPDX-FileCopyrightText: 2026 Santosh Prabhu Shenbagamoorthy and Santhosh Shyamsundar
-- SPDX-License-Identifier: MIT
------------------------------------------------------------------------
-- P0-13b: scoped Englert assumptions (mirror Coq ComplementaritySpec.v).
------------------------------------------------------------------------

{-# OPTIONS --without-K #-}

module MirrorScope.ComplementarityModel where

open import ComplementaritySpec
open import DensityStateSpec

------------------------------------------------------------------------
-- Scoped bundle: density constraints + complementarity laws (no postulate)
------------------------------------------------------------------------

record ComplementarityScope : Set where
  field
    density-props         : DensityMatrixProps
    complementarity-props : ComplementarityProps

module WithComplementarityScope (S : ComplementarityScope) where
  open ComplementarityScope S
  open ComplementarityProps complementarity-props public
  open DensityMatrixProps density-props public
