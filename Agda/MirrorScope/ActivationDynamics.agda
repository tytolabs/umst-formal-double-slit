-- SPDX-FileCopyrightText: 2026 Santosh Prabhu Shenbagamoorthy and Santhosh Shyamsundar
-- SPDX-License-Identifier: MIT
------------------------------------------------------------------------
-- P0-13b: activation → state transformer bundle (mirror GatePhysicalModel).
------------------------------------------------------------------------

module MirrorScope.ActivationDynamics where

open import Activation

record ActivationScope : Set where
  field
    dynamics : ActivationEngineDynamics

module WithActivationDynamics (S : ActivationScope) where
  open ActivationScope S
  open ActivationEngineDynamics dynamics public
