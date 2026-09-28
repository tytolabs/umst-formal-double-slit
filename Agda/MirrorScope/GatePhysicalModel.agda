-- SPDX-FileCopyrightText: 2026 Santosh Prabhu Shenbagamoorthy and Santhosh Shyamsundar
-- SPDX-License-Identifier: MIT
{-# OPTIONS --without-K --safe #-}

-- P0-13: physical laws as record fields (no postulate). Shapes align with Gate.agda.

module MirrorScope.GatePhysicalModel where

open import Data.Nat as Nat using (ℕ)
open import Data.Rational as ℚ using (ℚ; 0ℚ; 1ℚ; _+_; _*_; _-_; _≤_)
open import Data.Product using (_×_; _,_)

record ThermodynamicState : Set where
  constructor mkState
  field
    density     : ℚ
    free-energy : ℚ
    hydration   : ℚ
    strength    : ℚ

open ThermodynamicState

private
  natToℚ : ℕ → ℚ
  natToℚ Nat.zero    = 0ℚ
  natToℚ (Nat.suc k) = 1ℚ + natToℚ k

δ-mass : ℚ
δ-mass = natToℚ 100

record Admissible (old new : ThermodynamicState) : Set where
  constructor mkAdmissible
  field
    mass-conserved : ((density new) - (density old) ≤ δ-mass)
                   × ((density old) - (density new) ≤ δ-mass)
    dissipation-nonneg : free-energy new ≤ free-energy old
    hydration-monotone : hydration old ≤ hydration new
    strength-monotone : strength old ≤ strength new

record PhysicalLaws : Set where
  field
    ψ-antitone : ∀ (s₁ s₂ : ThermodynamicState) →
      hydration s₁ ≤ hydration s₂ →
      free-energy s₂ ≤ free-energy s₁
    fc-monotone : ∀ (s₁ s₂ : ThermodynamicState) →
      hydration s₁ ≤ hydration s₂ →
      strength s₁ ≤ strength s₂

module _ (laws : PhysicalLaws) (open PhysicalLaws laws) where

  forward-hydration-admissible-parameterized :
    ∀ (old new : ThermodynamicState) →
    hydration old ≤ hydration new →
    ((density new) - (density old) ≤ δ-mass) →
    ((density old) - (density new) ≤ δ-mass) →
    Admissible old new
  forward-hydration-admissible-parameterized old new α-adv mc₁ mc₂ =
    mkAdmissible
      (mc₁ , mc₂)
      (ψ-antitone old new α-adv)
      α-adv
      (fc-monotone old new α-adv)
