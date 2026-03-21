-- SPDX-License-Identifier: MIT
-- Copyright (c) 2026 Santhosh Shyamsundar, Santosh Prabhu Shenbagamoorthy — Studio TYTO

module DensityState where

import Data.Complex

-- | A 2x2 Complex Matrix represented as ((00, 01), (10, 11))
type Matrix2x2 = ((Complex Double, Complex Double), (Complex Double, Complex Double))

trace :: Matrix2x2 -> Complex Double
trace ((a, _), (_, d)) = a + d

adjoint :: Matrix2x2 -> Matrix2x2
adjoint ((a, b), (c, d)) = ((conjugate a, conjugate c), (conjugate b, conjugate d))

isHermitian :: Matrix2x2 -> Bool
isHermitian m = 
  let ((a, b), (c, d)) = m
      ((a', b'), (c', d')) = adjoint m
      tol = 1e-9
      eqC x y = magnitude (x - y) < tol
  in eqC a a' && eqC b b' && eqC c c' && eqC d d'

-- | Check if hermitian matrix is Positive Semi-Definite (Trace >= 0, Det >= 0)
isPSD :: Matrix2x2 -> Bool
isPSD m@((a, b), (c, d)) = 
  isHermitian m && (realPart a >= -1e-9) && (realPart d >= -1e-9) && (realPart (a*d - b*c) >= -1e-9)

-- | Density Matrix: PSD and Trace = 1
isDensityMatrix :: Matrix2x2 -> Bool
isDensityMatrix m = isPSD m && magnitude (trace m - 1) < 1e-9

pureState :: (Complex Double, Complex Double) -> Matrix2x2
pureState (u, v) = ((u*conjugate u, u*conjugate v), (v*conjugate u, v*conjugate v))
