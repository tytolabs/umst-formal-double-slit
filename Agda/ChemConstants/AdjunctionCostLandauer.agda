-- SPDX-FileCopyrightText: 2026 Santosh Prabhu Shenbagamoorthy and Santhosh Shyamsundar
-- SPDX-License-Identifier: MIT
------------------------------------------------------------------------
-- UMST-Formal: ChemConstants.AdjunctionCostLandauer.agda
--
-- CAT-03 adjunction-cost Landauer on the knowing fiber (Q lattice):
--   * impure⇄pure adjunction; pureward refine cost non-negative
--   * free purification ⊥ when contaminants remain
--   * forgetful view ≠ paid pureward purification (Landauer scaffold)
--
-- Mirrors sibling `ChemConstants/Eco02ConsumeNotFork.agda` +
-- Coq `ChemConstants/AdjunctionCostLandauer.v` style.
-- No meso / acting theorems. Modality Unwired; physics GREEN false.
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module ChemConstants.AdjunctionCostLandauer where

open import Data.Bool using (Bool; false; true)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Nat using (ℕ; zero; suc; _≤_)
open import Data.Nat.Base using (z≤n)
open import Data.Product using (_×_; _,_)
open import Data.String using (String)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Relation.Nullary using (¬_)

------------------------------------------------------------------------
-- Modality + adjunction-cost Landauer pins (knowing fiber — Unwired)
------------------------------------------------------------------------

data AdjunctionCostLandauerModality : Set where
  adjunction-cost-landauer-unwired adjunction-cost-landauer-assumed
    adjunction-cost-landauer-proved adjunction-cost-landauer-surrogate
    : AdjunctionCostLandauerModality

adjunctionCostLandauerModalityCurrent : AdjunctionCostLandauerModality
adjunctionCostLandauerModalityCurrent = adjunction-cost-landauer-unwired

productionWired landauerProductionWired : Bool
productionWired = false
landauerProductionWired = false

PurewardCost : Set
PurewardCost = ℕ

purewardCostZero minimumPurewardCostWhenContaminants : PurewardCost
purewardCostZero = zero
minimumPurewardCostWhenContaminants = suc zero

hasContaminants : Bool
hasContaminants = true

pureward-cost-nonnegative : ∀ (c : PurewardCost) → zero ≤ c
pureward-cost-nonnegative c = z≤n

FreePurificationWhenContaminants : Set
FreePurificationWhenContaminants =
  hasContaminants ≡ true × (purewardCostZero ≡ minimumPurewardCostWhenContaminants)

free-purification-⊥-when-contaminants : FreePurificationWhenContaminants → ⊥
free-purification-⊥-when-contaminants (refl , ())

not-free-purification-when-contaminants :
  ¬ (hasContaminants ≡ true × (purewardCostZero ≡ minimumPurewardCostWhenContaminants))
not-free-purification-when-contaminants h = free-purification-⊥-when-contaminants h

production-not-wired : productionWired ≡ false
production-not-wired = refl

landauer-not-production-wired : landauerProductionWired ≡ false
landauer-not-production-wired = refl

------------------------------------------------------------------------
-- One design axiom + authority cites (not a second optimizer fork)
------------------------------------------------------------------------

adjunctionCostLandauerAxiom :
  (∀ c → zero ≤ c)
  × (FreePurificationWhenContaminants → ⊥)
  × (productionWired ≡ false)
  × (landauerProductionWired ≡ false)
  × ¬ (hasContaminants ≡ true × (purewardCostZero ≡ minimumPurewardCostWhenContaminants))
adjunctionCostLandauerAxiom =
  pureward-cost-nonnegative
  , free-purification-⊥-when-contaminants
  , production-not-wired
  , landauer-not-production-wired
  , not-free-purification-when-contaminants

adjunctionCostLandauerNamed : String
adjunctionCostLandauerNamed =
  "adjunctionCostLandauer: impure⇄pure adjunction pureward cost non-negative; free purification ⊥ when contaminants"

adjunctionCostLandauerCellId : String
adjunctionCostLandauerCellId = "CHEM-FORMAL-Q-AGDA-ADJUNCTION-COST-LANDAUER"

adjunctionCostLandauerNonClaim : String
adjunctionCostLandauerNonClaim =
  "CHEM-FORMAL-Q-AGDA-ADJUNCTION-COST-LANDAUER CAT-03 adjunction-cost Landauer impure⇄pure pureward refine cost non-negative free purification ⊥ when contaminants forgetful view ≠ purification one design axiom second law conservation not free purification axiom; modality Unwired; not physics GREEN; not production_wired"

adjunction-cost-landauer-modality-unwired :
  adjunctionCostLandauerModalityCurrent ≡ adjunction-cost-landauer-unwired
adjunction-cost-landauer-modality-unwired = refl

adjunctionCostLandauerPhysicsGreenAuthorized : Set
adjunctionCostLandauerPhysicsGreenAuthorized = ⊥

adjunction-cost-landauer-physics-green-false : ¬ adjunctionCostLandauerPhysicsGreenAuthorized
adjunction-cost-landauer-physics-green-false ()
