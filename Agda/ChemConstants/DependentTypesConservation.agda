-- SPDX-FileCopyrightText: 2026 Santosh Prabhu Shenbagamoorthy and Santhosh Shyamsundar
-- SPDX-License-Identifier: MIT
------------------------------------------------------------------------
-- UMST-Formal: ChemConstants.DependentTypesConservation.agda
--
-- TYPE-01 dependent-types conservation on the knowing fiber (Q lattice):
--   * DependentStep identity/at/geometry/thermo/compose; associator as
--     ElementId-indexed geometry/thermo identity conservation
--   * dependent-type laws Unwired (dependentTypesLawsProved = false)
--   * not TYPE-01 Proved (type01DepProved = false)
--   * SpeciesId is L1 not L0 (speciesIsL1 = true)
--
-- Mirrors sibling `ChemConstants/CoalgebraConservation.agda` +
-- `ChemConstants/PullbackConservation.agda` style.
-- No meso / acting theorems. Modality Unwired; physics GREEN false.
-- Not 118² GREEN table.
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module ChemConstants.DependentTypesConservation where

open import Data.Bool using (Bool; false; true)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Product using (_×_; _,_)
open import Data.String using (String)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl)
open import Relation.Nullary using (¬_)

------------------------------------------------------------------------
-- Modality + dependent-types conservation pins (knowing fiber — Unwired)
------------------------------------------------------------------------

data DependentTypesConservationModality : Set where
  dependent-types-conservation-unwired dependent-types-conservation-assumed
    dependent-types-conservation-proved dependent-types-conservation-surrogate
    : DependentTypesConservationModality

dependentTypesConservationModalityCurrent : DependentTypesConservationModality
dependentTypesConservationModalityCurrent = dependent-types-conservation-unwired

dependentTypesLawsProved productionWired type01DepProved speciesIsL1 geometryThermoIdentityConservation : Bool
dependentTypesLawsProved = false
productionWired = false
type01DepProved = false
speciesIsL1 = true
geometryThermoIdentityConservation = true

------------------------------------------------------------------------
-- DependentStep identity/at/geometry/thermo/compose (TYPE-01 scaffold)
------------------------------------------------------------------------

data ElementTag : Set where
  hematite-dominant bauxite-dominant calcareous-gangue : ElementTag

data DependentStep : Set where
  identity : DependentStep
  at : ElementTag → DependentStep
  geometry : DependentStep → DependentStep → DependentStep
  thermo : DependentStep → DependentStep → DependentStep
  compose : DependentStep → DependentStep → DependentStep

dependentIdentity : DependentStep
dependentIdentity = identity

dependentGeometry dependentThermo dependentCompose : DependentStep → DependentStep → DependentStep
dependentGeometry = geometry
dependentThermo = thermo
dependentCompose = compose

hematiteAt bauxiteAt : DependentStep
hematiteAt = at hematite-dominant
bauxiteAt = at bauxite-dominant

isAt isGeometry isThermo isCompose : DependentStep → Bool
isAt (at _) = true
isAt _ = false

isGeometry (geometry _ _) = true
isGeometry _ = false

isThermo (thermo _ _) = true
isThermo _ = false

isCompose (compose _ _) = true
isCompose _ = false

isIdentity : DependentStep → Bool
isIdentity identity = true
isIdentity _ = false

left-identity-scaffold :
  ∀ (a : DependentStep) → isIdentity dependentIdentity ≡ true × isCompose (dependentCompose dependentIdentity a) ≡ true
left-identity-scaffold a = refl , refl

right-identity-scaffold :
  ∀ (a : DependentStep) → isCompose (dependentCompose a dependentIdentity) ≡ true × isIdentity dependentIdentity ≡ true
right-identity-scaffold a = refl , refl

associatorLeft associatorRight : DependentStep → DependentStep → DependentStep → DependentStep
associatorLeft a b c = dependentCompose (dependentCompose a b) c
associatorRight a b c = dependentCompose a (dependentCompose b c)

associative-bracketings-both-compose :
  ∀ (a b c : DependentStep) →
  isCompose (associatorLeft a b c) ≡ true × isCompose (associatorRight a b c) ≡ true
associative-bracketings-both-compose a b c = refl , refl

associator-not-identity :
  associatorLeft hematiteAt bauxiteAt dependentIdentity ≢ associatorRight hematiteAt bauxiteAt dependentIdentity
associator-not-identity ()

geometry-thermo-identity-conservation :
  geometryThermoIdentityConservation ≡ true ×
  (∀ a b c → isCompose (associatorLeft a b c) ≡ true × isCompose (associatorRight a b c) ≡ true)
geometry-thermo-identity-conservation = refl , associative-bracketings-both-compose

triple-dependent-compose : DependentStep
triple-dependent-compose =
  dependentCompose
    (dependentCompose hematiteAt bauxiteAt)
    (at calcareous-gangue)

triple-dependent-is-compose : isCompose triple-dependent-compose ≡ true
triple-dependent-is-compose = refl

dual-geometry-thermo : DependentStep
dual-geometry-thermo =
  dependentGeometry
    (dependentThermo hematiteAt bauxiteAt)
    (at calcareous-gangue)

dual-geometry-is-geometry : isGeometry dual-geometry-thermo ≡ true
dual-geometry-is-geometry = refl

element-id-indexed-at : isAt hematiteAt ≡ true × isAt bauxiteAt ≡ true
element-id-indexed-at = refl , refl

species-is-l1 : speciesIsL1 ≡ true
species-is-l1 = refl

dependent-types-laws-not-proved : dependentTypesLawsProved ≡ false
dependent-types-laws-not-proved = refl

type01-dep-not-proved : type01DepProved ≡ false
type01-dep-not-proved = refl

production-not-wired : productionWired ≡ false
production-not-wired = refl

------------------------------------------------------------------------
-- One design axiom + authority cites (not a second optimizer fork)
------------------------------------------------------------------------

dependentTypesConservationAxiom :
  (dependentTypesLawsProved ≡ false)
  × (productionWired ≡ false)
  × (type01DepProved ≡ false)
  × (speciesIsL1 ≡ true)
  × (geometryThermoIdentityConservation ≡ true)
  × (∀ a → isCompose (dependentCompose dependentIdentity a) ≡ true)
  × (∀ a b c → isCompose (associatorLeft a b c) ≡ true × isCompose (associatorRight a b c) ≡ true)
  × ¬ (associatorLeft hematiteAt bauxiteAt dependentIdentity ≡ associatorRight hematiteAt bauxiteAt dependentIdentity)
dependentTypesConservationAxiom =
  dependent-types-laws-not-proved
  , production-not-wired
  , type01-dep-not-proved
  , species-is-l1
  , refl
  , (λ a → refl)
  , associative-bracketings-both-compose
  , associator-not-identity

dependentTypesConservationNamed : String
dependentTypesConservationNamed =
  "dependentTypesConservation: DependentStep ElementId-indexed geometry thermo identity conservation"

dependentTypesConservationCellId : String
dependentTypesConservationCellId = "CHEM-FORMAL-Q-AGDA-DEPENDENT-TYPES-CONSERVATION"

dependentTypesConservationNonClaim : String
dependentTypesConservationNonClaim =
  "CHEM-FORMAL-Q-AGDA-DEPENDENT-TYPES-CONSERVATION TYPE-01 dependent-types conservation DependentStep ElementId-indexed geometry thermo identity conservation dependentTypesLawsProved false type01DepProved false speciesIsL1 true not TYPE-01 Proved not 118 squared GREEN table one design axiom second law conservation not second optimizer axiom modality Unwired not physics GREEN not production_wired"

dependent-types-conservation-modality-unwired :
  dependentTypesConservationModalityCurrent ≡ dependent-types-conservation-unwired
dependent-types-conservation-modality-unwired = refl

dependentTypesConservationPhysicsGreenAuthorized : Set
dependentTypesConservationPhysicsGreenAuthorized = ⊥

dependent-types-conservation-physics-green-false : ¬ dependentTypesConservationPhysicsGreenAuthorized
dependent-types-conservation-physics-green-false ()
