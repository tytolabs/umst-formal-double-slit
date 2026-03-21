module MeasurementChannel where

import DensityState

type KrausOp = Matrix2x2

mulM :: Matrix2x2 -> Matrix2x2 -> Matrix2x2
mulM ((a, b), (c, d)) ((e, f), (g, h)) = 
  ((a*e + b*g, a*f + b*h), (c*e + d*g, c*f + d*h))

addM :: Matrix2x2 -> Matrix2x2 -> Matrix2x2
addM ((a, b), (c, d)) ((e, f), (g, h)) = 
  ((a+e, b+f), (c+g, d+h))

applyKraus :: [KrausOp] -> Matrix2x2 -> Matrix2x2
applyKraus ops rho = foldl1 addM [ mulM (mulM k rho) (adjoint k) | k <- ops ]

identityChannel :: [KrausOp]
identityChannel = [((1, 0), (0, 1))]

whichPathChannel :: [KrausOp]
whichPathChannel = [ ((1, 0), (0, 0)), ((0, 0), (0, 1)) ]
