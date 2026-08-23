-- SPDX-FileCopyrightText: 2026 Santosh Prabhu Shenbagamoorthy and Santhosh Shyamsundar
-- SPDX-License-Identifier: MIT
------------------------------------------------------------------------
-- UMST-Formal: ChemConstants.PullbackConservation.agda
--
-- CAT-02 pullback/pushout conservation on the knowing fiber (Q lattice):
--   * SpanStep identity/pullback/pushout; associator as shared-substructure identity conservation
--   * universal properties Unwired (universalPropertiesProved = false)
--   * not CAT-02 pullback Proved (cat02PullbackProved = false)
--
-- Mirrors sibling `ChemConstants/KleisliInteractConservation.agda` +
-- `ChemConstants/OreMonoidalConservation.agda` style.
-- No meso / acting theorems. Modality Unwired; physics GREEN false.
-- Not 118² GREEN table.
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module ChemConstants.PullbackConservation where

open import Data.Bool using (Bool; false; true)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Product using (_×_; _,_)
open import Data.String using (String)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl)
open import Relation.Nullary using (¬_)

------------------------------------------------------------------------
-- Modality + pullback conservation pins (knowing fiber — Unwired)
------------------------------------------------------------------------

data PullbackConservationModality : Set where
  pullback-conservation-unwired pullback-conservation-assumed
    pullback-conservation-proved pullback-conservation-surrogate
    : PullbackConservationModality

pullbackConservationModalityCurrent : PullbackConservationModality
pullbackConservationModalityCurrent = pullback-conservation-unwired

universalPropertiesProved productionWired cat02PullbackProved sharedSubstructureIdentityConservation : Bool
universalPropertiesProved = false
productionWired = false
cat02PullbackProved = false
sharedSubstructureIdentityConservation = true

------------------------------------------------------------------------
-- SpanStep identity/pullback/pushout (span scaffold — not Vec list)
------------------------------------------------------------------------

data SubstructureTag : Set where
  hematite-dominant bauxite-dominant calcareous-gangue : SubstructureTag

data SpanStep : Set where
  identity : SpanStep
  leg : SubstructureTag → SpanStep
  pullback : SpanStep → SpanStep → SpanStep
  pushout : SpanStep → SpanStep → SpanStep

spanIdentity : SpanStep
spanIdentity = identity

spanPullback spanPushout : SpanStep → SpanStep → SpanStep
spanPullback = pullback
spanPushout = pushout

hematiteLeg bauxiteLeg : SpanStep
hematiteLeg = leg hematite-dominant
bauxiteLeg = leg bauxite-dominant

isPullback isPushout : SpanStep → Bool
isPullback (pullback _ _) = true
isPullback _ = false

isPushout (pushout _ _) = true
isPushout _ = false

isIdentity : SpanStep → Bool
isIdentity identity = true
isIdentity _ = false

left-identity-scaffold :
  ∀ (a : SpanStep) → isIdentity spanIdentity ≡ true × isPullback (spanPullback spanIdentity a) ≡ true
left-identity-scaffold a = refl , refl

right-identity-scaffold :
  ∀ (a : SpanStep) → isPullback (spanPullback a spanIdentity) ≡ true × isIdentity spanIdentity ≡ true
right-identity-scaffold a = refl , refl

associatorLeft associatorRight : SpanStep → SpanStep → SpanStep → SpanStep
associatorLeft a b c = spanPullback (spanPullback a b) c
associatorRight a b c = spanPullback a (spanPullback b c)

associative-bracketings-both-pullback :
  ∀ (a b c : SpanStep) →
  isPullback (associatorLeft a b c) ≡ true × isPullback (associatorRight a b c) ≡ true
associative-bracketings-both-pullback a b c = refl , refl

associator-not-identity :
  associatorLeft hematiteLeg bauxiteLeg spanIdentity ≢ associatorRight hematiteLeg bauxiteLeg spanIdentity
associator-not-identity ()

shared-substructure-identity-conservation :
  sharedSubstructureIdentityConservation ≡ true ×
  (∀ a b c → isPullback (associatorLeft a b c) ≡ true × isPullback (associatorRight a b c) ≡ true)
shared-substructure-identity-conservation = refl , associative-bracketings-both-pullback

triple-span-pullback : SpanStep
triple-span-pullback =
  spanPullback
    (spanPullback hematiteLeg bauxiteLeg)
    (leg calcareous-gangue)

triple-span-is-pullback : isPullback triple-span-pullback ≡ true
triple-span-is-pullback = refl

dual-span-pushout : SpanStep
dual-span-pushout =
  spanPushout
    (spanPushout hematiteLeg bauxiteLeg)
    (leg calcareous-gangue)

dual-span-is-pushout : isPushout dual-span-pushout ≡ true
dual-span-is-pushout = refl

universal-properties-not-proved : universalPropertiesProved ≡ false
universal-properties-not-proved = refl

cat02-pullback-not-proved : cat02PullbackProved ≡ false
cat02-pullback-not-proved = refl

production-not-wired : productionWired ≡ false
production-not-wired = refl

------------------------------------------------------------------------
-- One design axiom + authority cites (not a second optimizer fork)
------------------------------------------------------------------------

pullbackConservationAxiom :
  (universalPropertiesProved ≡ false)
  × (productionWired ≡ false)
  × (cat02PullbackProved ≡ false)
  × (sharedSubstructureIdentityConservation ≡ true)
  × (∀ a → isPullback (spanPullback spanIdentity a) ≡ true)
  × (∀ a b c → isPullback (associatorLeft a b c) ≡ true × isPullback (associatorRight a b c) ≡ true)
  × ¬ (associatorLeft hematiteLeg bauxiteLeg spanIdentity ≡ associatorRight hematiteLeg bauxiteLeg spanIdentity)
pullbackConservationAxiom =
  universal-properties-not-proved
  , production-not-wired
  , cat02-pullback-not-proved
  , refl
  , (λ a → refl)
  , associative-bracketings-both-pullback
  , associator-not-identity

pullbackConservationNamed : String
pullbackConservationNamed =
  "pullbackConservation: SpanStep identity pullback pushout shared substructure identity conservation"

pullbackConservationCellId : String
pullbackConservationCellId = "CHEM-FORMAL-Q-AGDA-PULLBACK-CONSERVATION"

pullbackConservationNonClaim : String
pullbackConservationNonClaim =
  "CHEM-FORMAL-Q-AGDA-PULLBACK-CONSERVATION CAT-02 pullback pushout conservation SpanStep identity pullback pushout shared substructure identity conservation universalPropertiesProved false cat02PullbackProved false not CAT-02 pullback Proved not 118 squared GREEN table one design axiom second law conservation not second optimizer axiom modality Unwired not physics GREEN not production_wired"

pullback-conservation-modality-unwired :
  pullbackConservationModalityCurrent ≡ pullback-conservation-unwired
pullback-conservation-modality-unwired = refl

pullbackConservationPhysicsGreenAuthorized : Set
pullbackConservationPhysicsGreenAuthorized = ⊥

pullback-conservation-physics-green-false : ¬ pullbackConservationPhysicsGreenAuthorized
pullback-conservation-physics-green-false ()
