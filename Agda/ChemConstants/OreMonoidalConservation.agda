-- SPDX-FileCopyrightText: 2026 Santosh Prabhu Shenbagamoorthy and Santhosh Shyamsundar
-- SPDX-License-Identifier: MIT
------------------------------------------------------------------------
-- UMST-Formal: ChemConstants.OreMonoidalConservation.agda
--
-- CAT-01 ore-monoidal conservation on the knowing fiber (Q lattice):
--   * OreTree leaf/tensor; unit I; associator as identity conservation
--   * concurrent monoidal product Π_c — not XOR ore enum
--   * monoidal laws Unwired (monoidalLawsProved = false)
--
-- Mirrors sibling `ChemConstants/AdjunctionCostLandauer.agda` +
-- `ChemConstants/Eco02ConsumeNotFork.agda` style.
-- No meso / acting theorems. Modality Unwired; physics GREEN false.
-- Not 118² GREEN table.
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module ChemConstants.OreMonoidalConservation where

open import Data.Bool using (Bool; false; true)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Product using (_×_; _,_)
open import Data.String using (String)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl)
open import Relation.Nullary using (¬_)

------------------------------------------------------------------------
-- Modality + ore-monoidal conservation pins (knowing fiber — Unwired)
------------------------------------------------------------------------

data OreMonoidalConservationModality : Set where
  ore-monoidal-conservation-unwired ore-monoidal-conservation-assumed
    ore-monoidal-conservation-proved ore-monoidal-conservation-surrogate
    : OreMonoidalConservationModality

oreMonoidalConservationModalityCurrent : OreMonoidalConservationModality
oreMonoidalConservationModalityCurrent = ore-monoidal-conservation-unwired

monoidalLawsProved productionWired productNotXor associatorIdentityConservation : Bool
monoidalLawsProved = false
productionWired = false
productNotXor = true
associatorIdentityConservation = true

------------------------------------------------------------------------
-- OreTree leaf/tensor (binary product tree — not Vec list)
------------------------------------------------------------------------

data OreTag : Set where
  hematite-dominant bauxite-dominant calcareous-gangue : OreTag

data OreTree : Set where
  leaf : OreTag → OreTree
  tensor : OreTree → OreTree → OreTree

oreUnit : OreTree
oreUnit = leaf calcareous-gangue

oreMonoidalProduct : OreTree → OreTree → OreTree
oreMonoidalProduct = tensor

hematiteLeaf bauxiteLeaf : OreTree
hematiteLeaf = leaf hematite-dominant
bauxiteLeaf = leaf bauxite-dominant

isTensor : OreTree → Bool
isTensor (tensor _ _) = true
isTensor _ = false

isUnit : OreTree → Bool
isUnit (leaf calcareous-gangue) = true
isUnit _ = false

left-unit-scaffold : ∀ (a : OreTree) → isUnit oreUnit ≡ true × isTensor (oreMonoidalProduct oreUnit a) ≡ true
left-unit-scaffold a = refl , refl

right-unit-scaffold : ∀ (a : OreTree) → isTensor (oreMonoidalProduct a oreUnit) ≡ true × isUnit oreUnit ≡ true
right-unit-scaffold a = refl , refl

associatorLeft associatorRight : OreTree → OreTree → OreTree → OreTree
associatorLeft a b c = oreMonoidalProduct (oreMonoidalProduct a b) c
associatorRight a b c = oreMonoidalProduct a (oreMonoidalProduct b c)

associative-bracketings-both-tensor :
  ∀ (a b c : OreTree) →
  isTensor (associatorLeft a b c) ≡ true × isTensor (associatorRight a b c) ≡ true
associative-bracketings-both-tensor a b c = refl , refl

associator-not-identity :
  associatorLeft hematiteLeaf bauxiteLeaf oreUnit ≢ associatorRight hematiteLeaf bauxiteLeaf oreUnit
associator-not-identity ()

associator-identity-conservation :
  associatorIdentityConservation ≡ true ×
  (∀ a b c → isTensor (associatorLeft a b c) ≡ true × isTensor (associatorRight a b c) ≡ true)
associator-identity-conservation = refl , associative-bracketings-both-tensor

triple-ore-concurrent : OreTree
triple-ore-concurrent =
  oreMonoidalProduct
    (oreMonoidalProduct hematiteLeaf bauxiteLeaf)
    (leaf calcareous-gangue)

triple-ore-is-tensor : isTensor triple-ore-concurrent ≡ true
triple-ore-is-tensor = refl

product-not-xor : productNotXor ≡ true
product-not-xor = refl

monoidal-laws-not-proved : monoidalLawsProved ≡ false
monoidal-laws-not-proved = refl

production-not-wired : productionWired ≡ false
production-not-wired = refl

------------------------------------------------------------------------
-- One design axiom + authority cites (not a second optimizer fork)
------------------------------------------------------------------------

oreMonoidalConservationAxiom :
  (monoidalLawsProved ≡ false)
  × (productionWired ≡ false)
  × (productNotXor ≡ true)
  × (associatorIdentityConservation ≡ true)
  × (∀ a → isTensor (oreMonoidalProduct oreUnit a) ≡ true)
  × (∀ a b c → isTensor (associatorLeft a b c) ≡ true × isTensor (associatorRight a b c) ≡ true)
  × ¬ (associatorLeft hematiteLeaf bauxiteLeaf oreUnit ≡ associatorRight hematiteLeaf bauxiteLeaf oreUnit)
oreMonoidalConservationAxiom =
  monoidal-laws-not-proved
  , production-not-wired
  , product-not-xor
  , refl
  , (λ a → refl)
  , associative-bracketings-both-tensor
  , associator-not-identity

oreMonoidalConservationNamed : String
oreMonoidalConservationNamed =
  "oreMonoidalConservation: OreTree leaf/tensor unit I associator identity conservation product not XOR"

oreMonoidalConservationCellId : String
oreMonoidalConservationCellId = "CHEM-FORMAL-Q-AGDA-ORE-MONOIDAL-CONSERVATION"

oreMonoidalConservationNonClaim : String
oreMonoidalConservationNonClaim =
  "CHEM-FORMAL-Q-AGDA-ORE-MONOIDAL-CONSERVATION CAT-01 ore-monoidal conservation OreTree leaf tensor unit I associator identity conservation concurrent product Pi_c not XOR ore enum monoidalLawsProved false not 118 squared GREEN table one design axiom second law conservation not second optimizer axiom modality Unwired not physics GREEN not production_wired"

ore-monoidal-conservation-modality-unwired :
  oreMonoidalConservationModalityCurrent ≡ ore-monoidal-conservation-unwired
ore-monoidal-conservation-modality-unwired = refl

oreMonoidalConservationPhysicsGreenAuthorized : Set
oreMonoidalConservationPhysicsGreenAuthorized = ⊥

ore-monoidal-conservation-physics-green-false : ¬ oreMonoidalConservationPhysicsGreenAuthorized
ore-monoidal-conservation-physics-green-false ()
