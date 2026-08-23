-- SPDX-FileCopyrightText: 2026 Santosh Prabhu Shenbagamoorthy and Santhosh Shyamsundar
-- SPDX-License-Identifier: MIT
------------------------------------------------------------------------
-- UMST-Formal: ChemConstants.CoalgebraConservation.agda
--
-- CAT-04 coalgebra conservation on the knowing fiber (Q lattice):
--   * CoalgebraStep identity/unfold/fold; associator as ore identity conservation
--   * coalgebra laws Unwired (coalgebraLawsProved = false)
--   * not CAT-04 coalgebra Proved (cat04CoalgebraProved = false)
--
-- Mirrors sibling `ChemConstants/PullbackConservation.agda` +
-- `ChemConstants/OreMonoidalConservation.agda` style.
-- No meso / acting theorems. Modality Unwired; physics GREEN false.
-- Not 118² GREEN table.
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module ChemConstants.CoalgebraConservation where

open import Data.Bool using (Bool; false; true)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Product using (_×_; _,_)
open import Data.String using (String)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl)
open import Relation.Nullary using (¬_)

------------------------------------------------------------------------
-- Modality + coalgebra conservation pins (knowing fiber — Unwired)
------------------------------------------------------------------------

data CoalgebraConservationModality : Set where
  coalgebra-conservation-unwired coalgebra-conservation-assumed
    coalgebra-conservation-proved coalgebra-conservation-surrogate
    : CoalgebraConservationModality

coalgebraConservationModalityCurrent : CoalgebraConservationModality
coalgebraConservationModalityCurrent = coalgebra-conservation-unwired

coalgebraLawsProved productionWired cat04CoalgebraProved oreIdentityConservation : Bool
coalgebraLawsProved = false
productionWired = false
cat04CoalgebraProved = false
oreIdentityConservation = true

------------------------------------------------------------------------
-- CoalgebraStep identity/unfold/fold (coalgebra scaffold — not Vec list)
------------------------------------------------------------------------

data OreTag : Set where
  hematite-dominant bauxite-dominant calcareous-gangue : OreTag

data CoalgebraStep : Set where
  identity : CoalgebraStep
  ore : OreTag → CoalgebraStep
  unfold : CoalgebraStep → CoalgebraStep → CoalgebraStep
  fold : CoalgebraStep → CoalgebraStep → CoalgebraStep

coalgebraIdentity : CoalgebraStep
coalgebraIdentity = identity

coalgebraUnfold coalgebraFold : CoalgebraStep → CoalgebraStep → CoalgebraStep
coalgebraUnfold = unfold
coalgebraFold = fold

hematiteOre bauxiteOre : CoalgebraStep
hematiteOre = ore hematite-dominant
bauxiteOre = ore bauxite-dominant

isUnfold isFold : CoalgebraStep → Bool
isUnfold (unfold _ _) = true
isUnfold _ = false

isFold (fold _ _) = true
isFold _ = false

isIdentity : CoalgebraStep → Bool
isIdentity identity = true
isIdentity _ = false

left-identity-scaffold :
  ∀ (a : CoalgebraStep) → isIdentity coalgebraIdentity ≡ true × isUnfold (coalgebraUnfold coalgebraIdentity a) ≡ true
left-identity-scaffold a = refl , refl

right-identity-scaffold :
  ∀ (a : CoalgebraStep) → isUnfold (coalgebraUnfold a coalgebraIdentity) ≡ true × isIdentity coalgebraIdentity ≡ true
right-identity-scaffold a = refl , refl

associatorLeft associatorRight : CoalgebraStep → CoalgebraStep → CoalgebraStep → CoalgebraStep
associatorLeft a b c = coalgebraUnfold (coalgebraUnfold a b) c
associatorRight a b c = coalgebraUnfold a (coalgebraUnfold b c)

associative-bracketings-both-unfold :
  ∀ (a b c : CoalgebraStep) →
  isUnfold (associatorLeft a b c) ≡ true × isUnfold (associatorRight a b c) ≡ true
associative-bracketings-both-unfold a b c = refl , refl

associator-not-identity :
  associatorLeft hematiteOre bauxiteOre coalgebraIdentity ≢ associatorRight hematiteOre bauxiteOre coalgebraIdentity
associator-not-identity ()

ore-identity-conservation :
  oreIdentityConservation ≡ true ×
  (∀ a b c → isUnfold (associatorLeft a b c) ≡ true × isUnfold (associatorRight a b c) ≡ true)
ore-identity-conservation = refl , associative-bracketings-both-unfold

triple-coalgebra-unfold : CoalgebraStep
triple-coalgebra-unfold =
  coalgebraUnfold
    (coalgebraUnfold hematiteOre bauxiteOre)
    (ore calcareous-gangue)

triple-coalgebra-is-unfold : isUnfold triple-coalgebra-unfold ≡ true
triple-coalgebra-is-unfold = refl

dual-coalgebra-fold : CoalgebraStep
dual-coalgebra-fold =
  coalgebraFold
    (coalgebraFold hematiteOre bauxiteOre)
    (ore calcareous-gangue)

dual-coalgebra-is-fold : isFold dual-coalgebra-fold ≡ true
dual-coalgebra-is-fold = refl

coalgebra-laws-not-proved : coalgebraLawsProved ≡ false
coalgebra-laws-not-proved = refl

cat04-coalgebra-not-proved : cat04CoalgebraProved ≡ false
cat04-coalgebra-not-proved = refl

production-not-wired : productionWired ≡ false
production-not-wired = refl

------------------------------------------------------------------------
-- One design axiom + authority cites (not a second optimizer fork)
------------------------------------------------------------------------

coalgebraConservationAxiom :
  (coalgebraLawsProved ≡ false)
  × (productionWired ≡ false)
  × (cat04CoalgebraProved ≡ false)
  × (oreIdentityConservation ≡ true)
  × (∀ a → isUnfold (coalgebraUnfold coalgebraIdentity a) ≡ true)
  × (∀ a b c → isUnfold (associatorLeft a b c) ≡ true × isUnfold (associatorRight a b c) ≡ true)
  × ¬ (associatorLeft hematiteOre bauxiteOre coalgebraIdentity ≡ associatorRight hematiteOre bauxiteOre coalgebraIdentity)
coalgebraConservationAxiom =
  coalgebra-laws-not-proved
  , production-not-wired
  , cat04-coalgebra-not-proved
  , refl
  , (λ a → refl)
  , associative-bracketings-both-unfold
  , associator-not-identity

coalgebraConservationNamed : String
coalgebraConservationNamed =
  "coalgebraConservation: CoalgebraStep identity unfold fold ore identity conservation"

coalgebraConservationCellId : String
coalgebraConservationCellId = "CHEM-FORMAL-Q-AGDA-COALGEBRA-CONSERVATION"

coalgebraConservationNonClaim : String
coalgebraConservationNonClaim =
  "CHEM-FORMAL-Q-AGDA-COALGEBRA-CONSERVATION CAT-04 coalgebra conservation CoalgebraStep identity unfold fold ore identity conservation coalgebraLawsProved false cat04CoalgebraProved false not CAT-04 coalgebra Proved not 118 squared GREEN table one design axiom second law conservation not second optimizer axiom modality Unwired not physics GREEN not production_wired"

coalgebra-conservation-modality-unwired :
  coalgebraConservationModalityCurrent ≡ coalgebra-conservation-unwired
coalgebra-conservation-modality-unwired = refl

coalgebraConservationPhysicsGreenAuthorized : Set
coalgebraConservationPhysicsGreenAuthorized = ⊥

coalgebra-conservation-physics-green-false : ¬ coalgebraConservationPhysicsGreenAuthorized
coalgebra-conservation-physics-green-false ()
