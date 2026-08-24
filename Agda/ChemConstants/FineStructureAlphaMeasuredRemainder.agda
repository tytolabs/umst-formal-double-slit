-- SPDX-FileCopyrightText: 2026 Santosh Prabhu Shenbagamoorthy and Santhosh Shyamsundar
-- SPDX-License-Identifier: MIT
------------------------------------------------------------------------
-- UMST-Formal: ChemConstants.FineStructureAlphaMeasuredRemainder.agda
--
-- Fine-structure **α** measured remainder conservation on the knowing fiber (Q lattice):
--   * CODATA MeasuredCited α deferred composition on second law + conservation
--   * Consume sibling vacuum_permittivity_si_derived (cite, no fork)
--   * Landauer kT ln 2 α derive refused — not Landauer-fake
--   * fineStructureAlphaMeasuredRemainderProved = false; modality Unwired; physics GREEN false
--
-- Mirrors sibling `ChemConstants/OccupancyEngineSort.agda` +
-- `Haskell/UMST/ChemConstants/FineStructureAlphaMeasuredRemainder.hs` style.
-- INT: umst/umst-chem/src/x_rows/fine_structure_alpha_measured_remainder.rs
-- No meso / acting theorems. WAVE100: not wired in lib.rs / eos.rs.
-- Zero postulates that invent physics. Remainder deferred composition on second law.
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module ChemConstants.FineStructureAlphaMeasuredRemainder where

open import Data.Bool.Base using (Bool; false; true; not; _∧_; if_then_else_)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Nat using (ℕ; zero; suc)
open import Data.Product using (_×_; _,_)
open import Data.String using (String)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl)
open import Relation.Nullary using (¬_)

------------------------------------------------------------------------
-- Modality + fine-structure α measured remainder pins (knowing fiber — Unwired)
------------------------------------------------------------------------

data FineStructureAlphaMeasuredRemainderModality : Set where
  fine-structure-alpha-measured-remainder-unwired
    fine-structure-alpha-measured-remainder-assumed
    fine-structure-alpha-measured-remainder-proved
    fine-structure-alpha-measured-remainder-surrogate
    : FineStructureAlphaMeasuredRemainderModality

fineStructureAlphaMeasuredRemainderModalityCurrent : FineStructureAlphaMeasuredRemainderModality
fineStructureAlphaMeasuredRemainderModalityCurrent =
  fine-structure-alpha-measured-remainder-unwired

fineStructureAlphaMeasuredRemainderModalityLatticeCardinality : ℕ
fineStructureAlphaMeasuredRemainderModalityLatticeCardinality = 4

fine-structure-alpha-measured-remainder-modality-lattice-cardinality-four :
  fineStructureAlphaMeasuredRemainderModalityLatticeCardinality ≡ 4
fine-structure-alpha-measured-remainder-modality-lattice-cardinality-four = refl

fineStructureAlphaMeasuredRemainderProved productionWired wave100LibRsWired
  wave100EosRsWired alphaDerivedFromLandauerKtLn2 alphaIsImpossibilityRest
  fineStructureAlphaIsNewAxiom alphaMeasuredRemainderSecondAxiomMinted
  pinDistinctFromLandauerTheater : Bool
fineStructureAlphaMeasuredRemainderProved = false
productionWired = false
wave100LibRsWired = false
wave100EosRsWired = false
alphaDerivedFromLandauerKtLn2 = false
alphaIsImpossibilityRest = false
fineStructureAlphaIsNewAxiom = false
alphaMeasuredRemainderSecondAxiomMinted = false
pinDistinctFromLandauerTheater = true

------------------------------------------------------------------------
-- North-star §0c pin kind — MeasuredCited vs refused theater channels
------------------------------------------------------------------------

data FineStructureAlphaPinKind : Set where
  measured-cited-pin landauer-kt-ln2-theater-pin impossibility-rest-theater-pin
    : FineStructureAlphaPinKind

isMeasuredCitedPin isLandauerKtLn2TheaterPin isImpossibilityRestTheaterPin
  : FineStructureAlphaPinKind → Bool
isMeasuredCitedPin measured-cited-pin = true
isMeasuredCitedPin _ = false

isLandauerKtLn2TheaterPin landauer-kt-ln2-theater-pin = true
isLandauerKtLn2TheaterPin _ = false

isImpossibilityRestTheaterPin impossibility-rest-theater-pin = true
isImpossibilityRestTheaterPin _ = false

measured-cited-pin-named :
  isMeasuredCitedPin measured-cited-pin ≡ true ×
  isLandauerKtLn2TheaterPin measured-cited-pin ≡ false ×
  isImpossibilityRestTheaterPin measured-cited-pin ≡ false
measured-cited-pin-named = refl , refl , refl

landauer-kt-ln2-theater-pin-named :
  isLandauerKtLn2TheaterPin landauer-kt-ln2-theater-pin ≡ true ×
  isMeasuredCitedPin landauer-kt-ln2-theater-pin ≡ false
landauer-kt-ln2-theater-pin-named = refl , refl

impossibility-rest-theater-pin-named :
  isImpossibilityRestTheaterPin impossibility-rest-theater-pin ≡ true ×
  isMeasuredCitedPin impossibility-rest-theater-pin ≡ false
impossibility-rest-theater-pin-named = refl , refl

measured-cited-distinct-from-landauer-theater :
  measured-cited-pin ≢ landauer-kt-ln2-theater-pin
measured-cited-distinct-from-landauer-theater ()

measured-cited-distinct-from-impossibility-rest :
  measured-cited-pin ≢ impossibility-rest-theater-pin
measured-cited-distinct-from-impossibility-rest ()

------------------------------------------------------------------------
-- Tag strings — CODATA MeasuredCited vs Landauer / impossibility theater
------------------------------------------------------------------------

codataAlphaCitationTag landauerKtLn2AlphaDeriveTheaterTag
  impossibilityRestTheaterTag measuredCitedPinTag : String
codataAlphaCitationTag = "CODATA-2018 recommended α"
landauerKtLn2AlphaDeriveTheaterTag = "landauer_kt_ln2_alpha_derive_theater"
impossibilityRestTheaterTag = "fine_structure_alpha_impossibility_rest_theater"
measuredCitedPinTag = "MeasuredCited"

codata-citation-named :
  codataAlphaCitationTag ≡ "CODATA-2018 recommended α"
codata-citation-named = refl

landauer-theater-tag-named :
  landauerKtLn2AlphaDeriveTheaterTag ≡ "landauer_kt_ln2_alpha_derive_theater"
landauer-theater-tag-named = refl

impossibility-rest-theater-tag-named :
  impossibilityRestTheaterTag ≡ "fine_structure_alpha_impossibility_rest_theater"
impossibility-rest-theater-tag-named = refl

measured-cited-pin-tag-named :
  measuredCitedPinTag ≡ "MeasuredCited"
measured-cited-pin-tag-named = refl

constStrNe : String → String → Bool
constStrNe a b with a | b
... | "MeasuredCited" | "landauer_kt_ln2_alpha_derive_theater" = true
... | "MeasuredCited" | "fine_structure_alpha_impossibility_rest_theater" = true
... | "CODATA-2018 recommended α" | "landauer_kt_ln2_alpha_derive_theater" = true
... | _ | _ = false

measured-cited-ne-landauer-theater :
  constStrNe measuredCitedPinTag landauerKtLn2AlphaDeriveTheaterTag ≡ true
measured-cited-ne-landauer-theater = refl

measured-cited-ne-impossibility-rest :
  constStrNe measuredCitedPinTag impossibilityRestTheaterTag ≡ true
measured-cited-ne-impossibility-rest = refl

codata-ne-landauer-theater :
  constStrNe codataAlphaCitationTag landauerKtLn2AlphaDeriveTheaterTag ≡ true
codata-ne-landauer-theater = refl

------------------------------------------------------------------------
-- Deferred composition scaffold — α MeasuredCited remainder on second law
------------------------------------------------------------------------

data DerivedSiCartridgeTag : Set where
  vacuum-permittivity-si-derived-cartridge : DerivedSiCartridgeTag

data AlphaRemainderPinStep : Set where
  pin-identity : AlphaRemainderPinStep
  pin-leaf : FineStructureAlphaPinKind → DerivedSiCartridgeTag → AlphaRemainderPinStep
  pin-compose : AlphaRemainderPinStep → AlphaRemainderPinStep → AlphaRemainderPinStep

alphaRemainderPinIdentity : AlphaRemainderPinStep
alphaRemainderPinIdentity = pin-identity

pinComposeOp : AlphaRemainderPinStep → AlphaRemainderPinStep → AlphaRemainderPinStep
pinComposeOp = pin-compose

measuredCitedVacuumPermittivityLeaf landauerTheaterVacuumLeaf
  impossibilityRestVacuumLeaf : AlphaRemainderPinStep
measuredCitedVacuumPermittivityLeaf =
  pin-leaf measured-cited-pin vacuum-permittivity-si-derived-cartridge
landauerTheaterVacuumLeaf =
  pin-leaf landauer-kt-ln2-theater-pin vacuum-permittivity-si-derived-cartridge
impossibilityRestVacuumLeaf =
  pin-leaf impossibility-rest-theater-pin vacuum-permittivity-si-derived-cartridge

isPinCompose isPinIdentity : AlphaRemainderPinStep → Bool
isPinCompose (pin-compose _ _) = true
isPinCompose _ = false

isPinIdentity pin-identity = true
isPinIdentity _ = false

left-identity-scaffold :
  ∀ (a : AlphaRemainderPinStep) →
  isPinIdentity alphaRemainderPinIdentity ≡ true ×
  isPinCompose (pinComposeOp alphaRemainderPinIdentity a) ≡ true
left-identity-scaffold a = refl , refl

right-identity-scaffold :
  ∀ (a : AlphaRemainderPinStep) →
  isPinCompose (pinComposeOp a alphaRemainderPinIdentity) ≡ true ×
  isPinIdentity alphaRemainderPinIdentity ≡ true
right-identity-scaffold a = refl , refl

associatorLeft associatorRight :
  AlphaRemainderPinStep → AlphaRemainderPinStep → AlphaRemainderPinStep → AlphaRemainderPinStep
associatorLeft a b c = pinComposeOp (pinComposeOp a b) c
associatorRight a b c = pinComposeOp a (pinComposeOp b c)

associative-bracketings-both-pin-compose :
  ∀ (a b c : AlphaRemainderPinStep) →
  isPinCompose (associatorLeft a b c) ≡ true × isPinCompose (associatorRight a b c) ≡ true
associative-bracketings-both-pin-compose a b c = refl , refl

associator-not-identity :
  associatorLeft measuredCitedVacuumPermittivityLeaf landauerTheaterVacuumLeaf alphaRemainderPinIdentity ≢
  associatorRight measuredCitedVacuumPermittivityLeaf landauerTheaterVacuumLeaf alphaRemainderPinIdentity
associator-not-identity ()

triple-pin-compose : AlphaRemainderPinStep
triple-pin-compose =
  pinComposeOp
    (pinComposeOp measuredCitedVacuumPermittivityLeaf landauerTheaterVacuumLeaf)
    alphaRemainderPinIdentity

triple-pin-compose-is-compose : isPinCompose triple-pin-compose ≡ true
triple-pin-compose-is-compose = refl

------------------------------------------------------------------------
-- Refusal pins — Landauer-fake and impossibility rest not authorized
------------------------------------------------------------------------

alpha-not-derived-from-landauer-kt-ln2 : alphaDerivedFromLandauerKtLn2 ≡ false
alpha-not-derived-from-landauer-kt-ln2 = refl

alpha-not-impossibility-rest : alphaIsImpossibilityRest ≡ false
alpha-not-impossibility-rest = refl

fine-structure-alpha-not-new-axiom : fineStructureAlphaIsNewAxiom ≡ false
fine-structure-alpha-not-new-axiom = refl

alpha-measured-remainder-not-second-axiom :
  alphaMeasuredRemainderSecondAxiomMinted ≡ false
alpha-measured-remainder-not-second-axiom = refl

pin-distinct-from-landauer-theater-bool : pinDistinctFromLandauerTheater ≡ true
pin-distinct-from-landauer-theater-bool = refl

fine-structure-alpha-measured-remainder-not-proved :
  fineStructureAlphaMeasuredRemainderProved ≡ false
fine-structure-alpha-measured-remainder-not-proved = refl

production-not-wired : productionWired ≡ false
production-not-wired = refl

wave100-lib-rs-not-wired : wave100LibRsWired ≡ false
wave100-lib-rs-not-wired = refl

wave100-eos-rs-not-wired : wave100EosRsWired ≡ false
wave100-eos-rs-not-wired = refl

------------------------------------------------------------------------
-- Authority cites — vacuum_permittivity_si_derived sibling (read-only, no fork)
------------------------------------------------------------------------

vacuumPermittivitySiDerivedAuthority : String
vacuumPermittivitySiDerivedAuthority =
  "umst/umst-chem/src/vacuum_permittivity_si_derived.rs"

vacuumPermittivitySiDerivedCrossCellId : String
vacuumPermittivitySiDerivedCrossCellId =
  "CHEM-INT-VACUUM-PERMITTIVITY-SI-DERIVED"

vacuumPermittivitySiDerivedMarker : String
vacuumPermittivitySiDerivedMarker =
  "chem_int_vacuum_permittivity_si_derived_v1"

vacuum-permittivity-si-derived-authority-named :
  vacuumPermittivitySiDerivedAuthority ≡
  "umst/umst-chem/src/vacuum_permittivity_si_derived.rs"
vacuum-permittivity-si-derived-authority-named = refl

vacuum-permittivity-si-derived-cross-cell-id-named :
  vacuumPermittivitySiDerivedCrossCellId ≡ "CHEM-INT-VACUUM-PERMITTIVITY-SI-DERIVED"
vacuum-permittivity-si-derived-cross-cell-id-named = refl

secondLawConservationAxiomPin : String
secondLawConservationAxiomPin =
  "second law conservation — fine-structure alpha CODATA measured remainder deferred composition; measured remainder witness not second axiom; sole axiom"

alphaNotLandauerOrImpossibilityOr26thAxiom : String
alphaNotLandauerOrImpossibilityOr26thAxiom =
  "fine-structure alpha is CODATA measured remainder deferred composition — not Landauer kT ln 2 derive not impossibility rest not 26th axiom"

------------------------------------------------------------------------
-- Honest conjunct — deferred composition, not Landauer-fake
------------------------------------------------------------------------

fineStructureAlphaMeasuredRemainderHonestConjunct : Bool
fineStructureAlphaMeasuredRemainderHonestConjunct =
  not fineStructureAlphaIsNewAxiom ∧
  not alphaMeasuredRemainderSecondAxiomMinted ∧
  not alphaDerivedFromLandauerKtLn2 ∧
  not alphaIsImpossibilityRest ∧
  pinDistinctFromLandauerTheater ∧
  isMeasuredCitedPin measured-cited-pin ∧
  isPinCompose triple-pin-compose

fine-structure-alpha-measured-remainder-honest-conjunct-true :
  fineStructureAlphaMeasuredRemainderHonestConjunct ≡ true
fine-structure-alpha-measured-remainder-honest-conjunct-true = refl

------------------------------------------------------------------------
-- Conservation close verdict — fail-closed lattice
------------------------------------------------------------------------

data FineStructureAlphaMeasuredRemainderVerdict : Set where
  verdict-unwired-ok verdict-deferred-composition-ok verdict-green-invent-refuse
    verdict-production-wired-refuse verdict-landauer-fake-refuse
    verdict-impossibility-rest-refuse verdict-new-axiom-refuse
    : FineStructureAlphaMeasuredRemainderVerdict

fineStructureAlphaMeasuredRemainderVerdictOk :
  FineStructureAlphaMeasuredRemainderVerdict → Bool
fineStructureAlphaMeasuredRemainderVerdictOk verdict-unwired-ok = true
fineStructureAlphaMeasuredRemainderVerdictOk verdict-deferred-composition-ok = true
fineStructureAlphaMeasuredRemainderVerdictOk _ = false

evaluateFineStructureAlphaMeasuredRemainder :
  FineStructureAlphaMeasuredRemainderModality →
  Bool → Bool → Bool → Bool → Bool →
  FineStructureAlphaMeasuredRemainderVerdict
evaluateFineStructureAlphaMeasuredRemainder m claimPhysicsGreen claimProved
  claimProductionWired claimLandauerDerive claimImpossibilityRest =
  if claimPhysicsGreen then verdict-green-invent-refuse else
  if claimProductionWired then verdict-production-wired-refuse else
  if claimLandauerDerive then verdict-landauer-fake-refuse else
  if claimImpossibilityRest then verdict-impossibility-rest-refuse else
  if claimProved then verdict-deferred-composition-ok else
  if fineStructureAlphaMeasuredRemainderHonestConjunct then pickModality m
  else verdict-new-axiom-refuse
  where
  pickModality : FineStructureAlphaMeasuredRemainderModality → FineStructureAlphaMeasuredRemainderVerdict
  pickModality fine-structure-alpha-measured-remainder-unwired = verdict-unwired-ok
  pickModality _ = verdict-deferred-composition-ok

fine-structure-alpha-measured-remainder-unwired-ok :
  evaluateFineStructureAlphaMeasuredRemainder
    fine-structure-alpha-measured-remainder-unwired false false false false false
    ≡ verdict-unwired-ok
fine-structure-alpha-measured-remainder-unwired-ok = refl

fine-structure-alpha-measured-remainder-green-invent-refuse :
  evaluateFineStructureAlphaMeasuredRemainder
    fine-structure-alpha-measured-remainder-unwired true false false false false
    ≡ verdict-green-invent-refuse
fine-structure-alpha-measured-remainder-green-invent-refuse = refl

fine-structure-alpha-measured-remainder-production-wired-refuse :
  evaluateFineStructureAlphaMeasuredRemainder
    fine-structure-alpha-measured-remainder-unwired false false true false false
    ≡ verdict-production-wired-refuse
fine-structure-alpha-measured-remainder-production-wired-refuse = refl

fine-structure-alpha-measured-remainder-landauer-fake-refuse :
  evaluateFineStructureAlphaMeasuredRemainder
    fine-structure-alpha-measured-remainder-unwired false false false true false
    ≡ verdict-landauer-fake-refuse
fine-structure-alpha-measured-remainder-landauer-fake-refuse = refl

fine-structure-alpha-measured-remainder-green-refuse-verdict-false :
  fineStructureAlphaMeasuredRemainderVerdictOk
    (evaluateFineStructureAlphaMeasuredRemainder
       fine-structure-alpha-measured-remainder-unwired true false false false false)
    ≡ false
fine-structure-alpha-measured-remainder-green-refuse-verdict-false = refl

------------------------------------------------------------------------
-- One design axiom + authority cites (not a 26th axiom fork)
------------------------------------------------------------------------

soleAxiomCount : ℕ
soleAxiomCount = 1

sole-axiom-count-is-one : soleAxiomCount ≡ 1
sole-axiom-count-is-one = refl

fineStructureAlphaMeasuredRemainderAxiom :
  (fineStructureAlphaMeasuredRemainderProved ≡ false)
  × (productionWired ≡ false)
  × (wave100LibRsWired ≡ false)
  × (wave100EosRsWired ≡ false)
  × (alphaDerivedFromLandauerKtLn2 ≡ false)
  × (alphaIsImpossibilityRest ≡ false)
  × (fineStructureAlphaIsNewAxiom ≡ false)
  × (alphaMeasuredRemainderSecondAxiomMinted ≡ false)
  × (pinDistinctFromLandauerTheater ≡ true)
  × (constStrNe measuredCitedPinTag landauerKtLn2AlphaDeriveTheaterTag ≡ true)
  × (constStrNe codataAlphaCitationTag landauerKtLn2AlphaDeriveTheaterTag ≡ true)
  × (∀ a → isPinCompose (pinComposeOp alphaRemainderPinIdentity a) ≡ true)
  × (∀ a b c →
      isPinCompose (associatorLeft a b c) ≡ true × isPinCompose (associatorRight a b c) ≡ true)
  × ¬ (measured-cited-pin ≡ landauer-kt-ln2-theater-pin)
  × (fineStructureAlphaMeasuredRemainderHonestConjunct ≡ true)
  × (evaluateFineStructureAlphaMeasuredRemainder
       fine-structure-alpha-measured-remainder-unwired false false false false false
       ≡ verdict-unwired-ok)
  × (fineStructureAlphaMeasuredRemainderVerdictOk
       (evaluateFineStructureAlphaMeasuredRemainder
          fine-structure-alpha-measured-remainder-unwired true false false false false)
     ≡ false)
  × (soleAxiomCount ≡ 1)
fineStructureAlphaMeasuredRemainderAxiom =
  fine-structure-alpha-measured-remainder-not-proved
  , production-not-wired
  , wave100-lib-rs-not-wired
  , wave100-eos-rs-not-wired
  , alpha-not-derived-from-landauer-kt-ln2
  , alpha-not-impossibility-rest
  , fine-structure-alpha-not-new-axiom
  , alpha-measured-remainder-not-second-axiom
  , pin-distinct-from-landauer-theater-bool
  , measured-cited-ne-landauer-theater
  , codata-ne-landauer-theater
  , (λ a → refl)
  , associative-bracketings-both-pin-compose
  , measured-cited-distinct-from-landauer-theater
  , fine-structure-alpha-measured-remainder-honest-conjunct-true
  , fine-structure-alpha-measured-remainder-unwired-ok
  , fine-structure-alpha-measured-remainder-green-refuse-verdict-false
  , sole-axiom-count-is-one

fineStructureAlphaMeasuredRemainderNamed : String
fineStructureAlphaMeasuredRemainderNamed =
  "fineStructureAlphaMeasuredRemainder: CODATA MeasuredCited alpha deferred composition on second law conservation cite vacuum_permittivity_si_derived not fork Landauer kT ln 2 derive refused not Landauer-fake not impossibility rest not 26th axiom sole axiom"

fineStructureAlphaMeasuredRemainderCrossWitnessAuthority : String
fineStructureAlphaMeasuredRemainderCrossWitnessAuthority =
  "umst/umst-chem/src/x_rows/fine_structure_alpha_measured_remainder.rs"

chemIntCrossFineStructureAlphaMeasuredRemainderAuthority : String
chemIntCrossFineStructureAlphaMeasuredRemainderAuthority =
  "CHEM-INT-CROSS-FINE-STRUCTURE-ALPHA-MEASURED-REMAINDER-CONSERVATION"

fineStructureAlphaMeasuredRemainderCellId : String
fineStructureAlphaMeasuredRemainderCellId =
  "CHEM-FORMAL-Q-AGDA-FINE-STRUCTURE-ALPHA-MEASURED-REMAINDER-CONSERVATION"

fineStructureAlphaMeasuredRemainderNonClaim : String
fineStructureAlphaMeasuredRemainderNonClaim =
  "CHEM-FORMAL-Q-AGDA-FINE-STRUCTURE-ALPHA-MEASURED-REMAINDER-CONSERVATION fine-structure alpha measured remainder Unwired — CODATA MeasuredCited α deferred composition on second law conservation; consume vacuum_permittivity_si_derived measured_cited not fork; Landauer kT ln 2 alpha derive refused not Landauer-fake; not impossibility rest; not 26th axiom; not physics GREEN; not production_wired"

fine-structure-alpha-measured-remainder-cell-id :
  fineStructureAlphaMeasuredRemainderCellId ≡
  "CHEM-FORMAL-Q-AGDA-FINE-STRUCTURE-ALPHA-MEASURED-REMAINDER-CONSERVATION"
fine-structure-alpha-measured-remainder-cell-id = refl

fine-structure-alpha-measured-remainder-cites-cross-witness-rs :
  fineStructureAlphaMeasuredRemainderCrossWitnessAuthority ≡
  "umst/umst-chem/src/x_rows/fine_structure_alpha_measured_remainder.rs"
fine-structure-alpha-measured-remainder-cites-cross-witness-rs = refl

fine-structure-alpha-measured-remainder-modality-unwired :
  fineStructureAlphaMeasuredRemainderModalityCurrent ≡
  fine-structure-alpha-measured-remainder-unwired
fine-structure-alpha-measured-remainder-modality-unwired = refl

fineStructureAlphaMeasuredRemainderPhysicsGreenAuthorized : Set
fineStructureAlphaMeasuredRemainderPhysicsGreenAuthorized = ⊥

fine-structure-alpha-measured-remainder-physics-green-false :
  ¬ fineStructureAlphaMeasuredRemainderPhysicsGreenAuthorized
fine-structure-alpha-measured-remainder-physics-green-false ()

fineStructureAlphaMeasuredRemainderMarker : String
fineStructureAlphaMeasuredRemainderMarker =
  "chem_int_cross_fine_structure_alpha_measured_remainder_v1"

fineStructureAlphaMeasuredRemainderSurface : String
fineStructureAlphaMeasuredRemainderSurface =
  "fine_structure_alpha_measured_remainder_surface"
