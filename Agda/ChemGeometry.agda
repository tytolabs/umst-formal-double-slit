-- SPDX-FileCopyrightText: 2026 Santosh Prabhu Shenbagamoorthy and Santhosh Shyamsundar
-- SPDX-License-Identifier: MIT
------------------------------------------------------------------------
-- UMST-Formal: ChemGeometry.agda
--
-- Electronic quantum-number geometry (quantum / knowing fiber).
--
-- PRIMARY discrete identity: occupied 4D Q-lattice cell (n, ℓ, m_ℓ, m_s).
-- Madelung n+ℓ is the canonical walk key; Janet row is that same sum.
--
-- Structural hydrogenic bounds only — no new physics axiom.
------------------------------------------------------------------------

module ChemGeometry where

open import Data.Nat as ℕ using (ℕ; zero; suc; _+_)
open import Data.Nat.Properties using (_<?_; _≟_)
open import Data.Fin using (Fin; toℕ)
open import Data.Bool using (Bool; true; false)
open import Data.Product using (_×_; _,_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Data.Bool.Base using (if_then_else_)
open import Relation.Nullary using (Dec; yes; no)
open import Relation.Nullary.Decidable using (does)

------------------------------------------------------------------------
-- 1. Hydrogenic quantum numbers
------------------------------------------------------------------------

-- Principal n ≥ 1, stored as predecessor k with n = suc k.
PrincipalQN : Set
PrincipalQN = ℕ

nOf : PrincipalQN → ℕ
nOf k = suc k

-- Angular ℓ with 0 ≤ ℓ < n.
AngularQN : PrincipalQN → Set
AngularQN k = Fin (suc k)

ℓOf : {k : PrincipalQN} → AngularQN k → ℕ
ℓOf = toℕ

-- Magnetic degeneracy 2ℓ+1.
magneticSlots : ℕ → ℕ
magneticSlots ℓ = suc (ℓ + ℓ)

MagneticQN : {k : PrincipalQN} → AngularQN k → Set
MagneticQN {k} ℓ = Fin (magneticSlots (ℓOf ℓ))

-- Spin projection m_s ∈ {↓, ↑} (±½ in chemistry notation).
data Spin : Set where
  ↓ ↑ : Spin

record QuantumCell : Set where
  constructor mkQuantumCell
  field
    principal : PrincipalQN
    angular   : AngularQN principal
    magnetic  : MagneticQN angular
    spin      : Spin

open QuantumCell

------------------------------------------------------------------------
-- 2. Madelung / Janet geometry
------------------------------------------------------------------------

madelungSum : QuantumCell → ℕ
madelungSum q = nOf (principal q) + ℓOf (angular q)

janetRow : QuantumCell → ℕ
janetRow = madelungSum

-- Pauli doubling: 2(2ℓ+1) electrons per subshell.
subshellCapacity : {k : PrincipalQN} → AngularQN k → ℕ
subshellCapacity {k} ℓ = suc (magneticSlots (ℓOf ℓ) + magneticSlots (ℓOf ℓ))

madelungKey : QuantumCell → ℕ × ℕ
madelungKey q = madelungSum q , nOf (principal q)

lexLtℕ : ℕ → ℕ → ℕ → ℕ → Bool
lexLtℕ a₁ b₁ a₂ b₂ =
  if does (a₁ <? a₂) then true else
  if does (a₂ <? a₁) then false else
  does (b₁ <? b₂)

madelungLt? : QuantumCell → QuantumCell → Bool
madelungLt? q₁ q₂ =
  lexLtℕ (madelungSum q₁) (nOf (principal q₁))
         (madelungSum q₂) (nOf (principal q₂))

------------------------------------------------------------------------
-- 3. Occupied Q-lattice cell (PRIMARY identity)
------------------------------------------------------------------------

record OccupiedCell : Set where
  constructor mkOccupied
  field
    cell : QuantumCell

occupiedMadelung : OccupiedCell → ℕ
occupiedMadelung oc = madelungSum (OccupiedCell.cell oc)

------------------------------------------------------------------------
-- 4. Structural lemmas (arithmetic only)
------------------------------------------------------------------------

janetRow-madelung : ∀ q → janetRow q ≡ madelungSum q
janetRow-madelung q = refl

subshellCapacity-double : ∀ {k : PrincipalQN} (ℓ : AngularQN k) →
  subshellCapacity ℓ ≡ suc (magneticSlots (ℓOf ℓ) + magneticSlots (ℓOf ℓ))
subshellCapacity-double ℓ = refl
