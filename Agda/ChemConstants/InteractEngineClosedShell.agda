-- SPDX-FileCopyrightText: 2026 Santosh Prabhu Shenbagamoorthy and Santhosh Shyamsundar
-- SPDX-License-Identifier: MIT
------------------------------------------------------------------------
-- UMST-Formal: ChemConstants.InteractEngineClosedShell.agda
--
-- Interact-engine closed-shell conservation on the knowing fiber (Q lattice):
--   * Closed-shell noble-gas Z (He … Og): 2, 10, 18, 36, 54, 86, 118
--   * He no-ore = missing Interact class 5 (structure_blocking_inertness), not atmophile GREEN
--   * InteractKind::StructureBlocking partiality typed — not nobility magic
--   * catalysis priced under sole axiom — not a 26th axiom
--   * interactEngineClosedShellProved false; modality Unwired; physics GREEN false
--
-- Mirrors sibling `ChemConstants/CartridgeOreConsultMonoid.agda` style.
-- INT: umst/umst-chem/src/x_rows/interact_engine_closed_shell.rs
-- No meso / acting theorems. WAVE100: not wired in lib.rs / eos.rs.
-- Zero postulates that invent physics. Remainder deferred composition on second law.
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module ChemConstants.InteractEngineClosedShell where

open import Data.Bool.Base using (Bool; false; true; not; _∧_; if_then_else_)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Nat using (ℕ; zero; suc; _*_)
open import Data.Nat.Properties as ℕ-Props using (_≟_)
open import Data.Product using (_×_; _,_)
open import Data.String using (String)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl)
open import Relation.Nullary using (¬_)
open import Relation.Nullary.Decidable using (does)

------------------------------------------------------------------------
-- Modality + interact-engine closed-shell pins (knowing fiber — Unwired)
------------------------------------------------------------------------

data InteractEngineClosedShellModality : Set where
  interact-engine-closed-shell-unwired interact-engine-closed-shell-assumed
    interact-engine-closed-shell-proved interact-engine-closed-shell-surrogate
    : InteractEngineClosedShellModality

interactEngineClosedShellModalityCurrent : InteractEngineClosedShellModality
interactEngineClosedShellModalityCurrent = interact-engine-closed-shell-unwired

interactEngineClosedShellModalityLatticeCardinality : ℕ
interactEngineClosedShellModalityLatticeCardinality = 4

interact-engine-closed-shell-modality-lattice-cardinality-four :
  interactEngineClosedShellModalityLatticeCardinality ≡ 4
interact-engine-closed-shell-modality-lattice-cardinality-four = refl

interactEngineClosedShellProved productionWired wave100LibRsWired wave100EosRsWired
  catalysisIsExtraAxiom heNoOreMissingInteract structureBlockingKindPinned
  oganessonInBarNotXeCopy : Bool
interactEngineClosedShellProved = false
productionWired = false
wave100LibRsWired = false
wave100EosRsWired = false
catalysisIsExtraAxiom = false
heNoOreMissingInteract = true
structureBlockingKindPinned = true
oganessonInBarNotXeCopy = true

------------------------------------------------------------------------
-- Closed-shell noble-gas Z table (He … Og)
------------------------------------------------------------------------

closedShellZ0 closedShellZ1 closedShellZ2 closedShellZ3
  closedShellZ4 closedShellZ5 closedShellZ6 : ℕ
closedShellZ0 = 2
closedShellZ1 = 10
closedShellZ2 = 18
closedShellZ3 = 36
closedShellZ4 = 54
closedShellZ5 = 86
closedShellZ6 = 118

closedShellZCount : ℕ
closedShellZCount = 7

closed-shell-z-count-seven : closedShellZCount ≡ 7
closed-shell-z-count-seven = refl

helium-z-is-two : closedShellZ0 ≡ 2
helium-z-is-two = refl

oganesson-z-is-118 : closedShellZ6 ≡ 118
oganesson-z-is-118 = refl

xenon-z-is-86 : closedShellZ5 ≡ 86
xenon-z-is-86 = refl

oganesson-in-bar-not-xe-copy :
  (closedShellZ6 ≡ 118) × (closedShellZ5 ≡ 86)
oganesson-in-bar-not-xe-copy = oganesson-z-is-118 , xenon-z-is-86

------------------------------------------------------------------------
-- Interact class 5 — structure-blocking / inertness authority
------------------------------------------------------------------------

class5StructureBlockingPatternIndex : ℕ
class5StructureBlockingPatternIndex = 5

class-5-structure-blocking-index-five :
  class5StructureBlockingPatternIndex ≡ 5
class-5-structure-blocking-index-five = refl

interactKindStructureBlockingTag patternBundleStructureBlockingFactorTag : String
interactKindStructureBlockingTag = "InteractKind::StructureBlocking"
patternBundleStructureBlockingFactorTag = "structure_blocking_inertness"

structure-blocking-kind-pinned-bool : structureBlockingKindPinned ≡ true
structure-blocking-kind-pinned-bool = refl

------------------------------------------------------------------------
-- He no-ore = missing Interact class 5, not atmophile nobility GREEN
------------------------------------------------------------------------

heNoOreMissingInteractClass5 : Bool
heNoOreMissingInteractClass5 = true

he-no-ore-missing-interact-class5 :
  heNoOreMissingInteractClass5 ≡ true
he-no-ore-missing-interact-class5 = refl

he-no-ore-missing-interact-class5-pinned :
  (closedShellZ0 ≡ 2) × (class5StructureBlockingPatternIndex ≡ 5)
he-no-ore-missing-interact-class5-pinned = helium-z-is-two , class-5-structure-blocking-index-five

he-no-ore-not-atmophile-green :
  heNoOreMissingInteract ≡ true
he-no-ore-not-atmophile-green = refl

------------------------------------------------------------------------
-- Catalysis not a 26th axiom — priced under sole axiom
------------------------------------------------------------------------

catalysis-not-extra-axiom : catalysisIsExtraAxiom ≡ false
catalysis-not-extra-axiom = refl

------------------------------------------------------------------------
-- InteractKind partiality scaffold — structure-blocking vs bond-forming folklore
------------------------------------------------------------------------

data InteractKind : Set where
  structure-blocking-kind bond-forming-folklore-kind : InteractKind

isStructureBlockingKind isBondFormingFolkloreKind : InteractKind → Bool
isStructureBlockingKind structure-blocking-kind = true
isStructureBlockingKind _ = false

isBondFormingFolkloreKind bond-forming-folklore-kind = true
isBondFormingFolkloreKind _ = false

structure-blocking-kind-pinned :
  isStructureBlockingKind structure-blocking-kind ≡ true ×
  isBondFormingFolkloreKind structure-blocking-kind ≡ false
structure-blocking-kind-pinned = refl , refl

structure-blocking-distinct-from-folklore :
  structure-blocking-kind ≢ bond-forming-folklore-kind
structure-blocking-distinct-from-folklore ()

------------------------------------------------------------------------
-- InteractPartialRefuse tree — Kleisli Interact is partial, not total
------------------------------------------------------------------------

data InteractPartialRefuse : Set where
  interact-refuse-leaf : InteractKind → InteractPartialRefuse
  interact-refuse-compose : InteractPartialRefuse → InteractPartialRefuse → InteractPartialRefuse

interactRefuseUnit : InteractPartialRefuse
interactRefuseUnit = interact-refuse-leaf structure-blocking-kind

heliumClosedShellRefuse nobleGasRefuse : InteractPartialRefuse
heliumClosedShellRefuse = interact-refuse-leaf structure-blocking-kind
nobleGasRefuse = interact-refuse-leaf structure-blocking-kind

isInteractRefuseCompose : InteractPartialRefuse → Bool
isInteractRefuseCompose (interact-refuse-compose _ _) = true
isInteractRefuseCompose _ = false

isInteractRefuseLeaf : InteractPartialRefuse → Bool
isInteractRefuseLeaf (interact-refuse-leaf _) = true
isInteractRefuseLeaf _ = false

left-refuse-scaffold :
  ∀ (a : InteractPartialRefuse) →
  isInteractRefuseLeaf interactRefuseUnit ≡ true ×
  isInteractRefuseCompose (interact-refuse-compose interactRefuseUnit a) ≡ true
left-refuse-scaffold a = refl , refl

right-refuse-scaffold :
  ∀ (a : InteractPartialRefuse) →
  isInteractRefuseCompose (interact-refuse-compose a interactRefuseUnit) ≡ true ×
  isInteractRefuseLeaf interactRefuseUnit ≡ true
right-refuse-scaffold a = refl , refl

refuseAssociatorLeft refuseAssociatorRight :
  InteractPartialRefuse → InteractPartialRefuse → InteractPartialRefuse → InteractPartialRefuse
refuseAssociatorLeft a b c = interact-refuse-compose (interact-refuse-compose a b) c
refuseAssociatorRight a b c = interact-refuse-compose a (interact-refuse-compose b c)

associative-refuse-bracketings-both-compose :
  ∀ (a b c : InteractPartialRefuse) →
  isInteractRefuseCompose (refuseAssociatorLeft a b c) ≡ true ×
  isInteractRefuseCompose (refuseAssociatorRight a b c) ≡ true
associative-refuse-bracketings-both-compose a b c = refl , refl

refuse-associator-not-identity :
  refuseAssociatorLeft heliumClosedShellRefuse nobleGasRefuse interactRefuseUnit ≢
  refuseAssociatorRight heliumClosedShellRefuse nobleGasRefuse interactRefuseUnit
refuse-associator-not-identity ()

triple-interact-refuse-compose : InteractPartialRefuse
triple-interact-refuse-compose =
  interact-refuse-compose
    (interact-refuse-compose heliumClosedShellRefuse nobleGasRefuse)
    interactRefuseUnit

triple-interact-refuse-is-compose : isInteractRefuseCompose triple-interact-refuse-compose ≡ true
triple-interact-refuse-is-compose = refl

interactEngineClosedShellHonestConjunct : Bool
interactEngineClosedShellHonestConjunct =
  not catalysisIsExtraAxiom ∧
  heNoOreMissingInteract ∧
  structureBlockingKindPinned ∧
  oganessonInBarNotXeCopy ∧
  true

interact-engine-closed-shell-honest-conjunct-true :
  interactEngineClosedShellHonestConjunct ≡ true
interact-engine-closed-shell-honest-conjunct-true = refl

interact-engine-closed-shell-not-proved : interactEngineClosedShellProved ≡ false
interact-engine-closed-shell-not-proved = refl

production-not-wired : productionWired ≡ false
production-not-wired = refl

wave100-lib-rs-not-wired : wave100LibRsWired ≡ false
wave100-lib-rs-not-wired = refl

wave100-eos-rs-not-wired : wave100EosRsWired ≡ false
wave100-eos-rs-not-wired = refl

oganesson-in-bar-not-xe-copy-bool : oganessonInBarNotXeCopy ≡ true
oganesson-in-bar-not-xe-copy-bool = refl

------------------------------------------------------------------------
-- Conservation close verdict — fail-closed lattice
------------------------------------------------------------------------

data InteractEngineClosedShellVerdict : Set where
  verdict-unwired-ok verdict-closed-shell-ok verdict-atmophile-green-refuse
    verdict-green-invent-refuse verdict-production-wired-refuse
    : InteractEngineClosedShellVerdict

interactEngineClosedShellVerdictOk : InteractEngineClosedShellVerdict → Bool
interactEngineClosedShellVerdictOk verdict-unwired-ok = true
interactEngineClosedShellVerdictOk verdict-closed-shell-ok = true
interactEngineClosedShellVerdictOk _ = false

evaluateInteractEngineClosedShell :
  InteractEngineClosedShellModality →
  Bool → Bool → Bool →
  InteractEngineClosedShellVerdict
evaluateInteractEngineClosedShell m claimPhysicsGreen claimProved claimProductionWired =
  if claimPhysicsGreen then verdict-green-invent-refuse else
  if claimProductionWired then verdict-production-wired-refuse else
  if claimProved then verdict-closed-shell-ok else
  if interactEngineClosedShellHonestConjunct then pickModality m else verdict-atmophile-green-refuse
  where
  pickModality : InteractEngineClosedShellModality → InteractEngineClosedShellVerdict
  pickModality interact-engine-closed-shell-unwired = verdict-unwired-ok
  pickModality _ = verdict-closed-shell-ok

interact-engine-closed-shell-unwired-ok :
  evaluateInteractEngineClosedShell
    interact-engine-closed-shell-unwired false false false
    ≡ verdict-unwired-ok
interact-engine-closed-shell-unwired-ok = refl

interact-engine-closed-shell-green-invent-refuse :
  evaluateInteractEngineClosedShell
    interact-engine-closed-shell-unwired true false false
    ≡ verdict-green-invent-refuse
interact-engine-closed-shell-green-invent-refuse = refl

interact-engine-closed-shell-production-wired-refuse :
  evaluateInteractEngineClosedShell
    interact-engine-closed-shell-unwired false false true
    ≡ verdict-production-wired-refuse
interact-engine-closed-shell-production-wired-refuse = refl

interact-engine-closed-shell-atmophile-green-refuse :
  interactEngineClosedShellVerdictOk
    (evaluateInteractEngineClosedShell
       interact-engine-closed-shell-unwired true false false)
    ≡ false
interact-engine-closed-shell-atmophile-green-refuse = refl

------------------------------------------------------------------------
-- One design axiom + authority cites (not a 26th axiom fork)
------------------------------------------------------------------------

soleAxiomCount : ℕ
soleAxiomCount = 1

sole-axiom-count-is-one : soleAxiomCount ≡ 1
sole-axiom-count-is-one = refl

interactEngineClosedShellAxiom :
  (interactEngineClosedShellProved ≡ false)
  × (productionWired ≡ false)
  × (wave100LibRsWired ≡ false)
  × (wave100EosRsWired ≡ false)
  × (catalysisIsExtraAxiom ≡ false)
  × (heNoOreMissingInteract ≡ true)
  × (structureBlockingKindPinned ≡ true)
  × (oganessonInBarNotXeCopy ≡ true)
  × (closedShellZCount ≡ 7)
  × (interactEngineClosedShellHonestConjunct ≡ true)
  × (heNoOreMissingInteractClass5 ≡ true)
  × (∀ a → isInteractRefuseCompose (interact-refuse-compose interactRefuseUnit a) ≡ true)
  × (∀ a b c →
      isInteractRefuseCompose (refuseAssociatorLeft a b c) ≡ true ×
      isInteractRefuseCompose (refuseAssociatorRight a b c) ≡ true)
  × ¬ (refuseAssociatorLeft heliumClosedShellRefuse nobleGasRefuse interactRefuseUnit ≡
       refuseAssociatorRight heliumClosedShellRefuse nobleGasRefuse interactRefuseUnit)
  × (evaluateInteractEngineClosedShell
       interact-engine-closed-shell-unwired false false false
       ≡ verdict-unwired-ok)
  × (interactEngineClosedShellVerdictOk
       (evaluateInteractEngineClosedShell
          interact-engine-closed-shell-unwired true false false)
     ≡ false)
  × (soleAxiomCount ≡ 1)
  × (structure-blocking-kind ≢ bond-forming-folklore-kind)
interactEngineClosedShellAxiom =
  interact-engine-closed-shell-not-proved
  , production-not-wired
  , wave100-lib-rs-not-wired
  , wave100-eos-rs-not-wired
  , catalysis-not-extra-axiom
  , he-no-ore-not-atmophile-green
  , structure-blocking-kind-pinned-bool
  , oganesson-in-bar-not-xe-copy-bool
  , closed-shell-z-count-seven
  , interact-engine-closed-shell-honest-conjunct-true
  , he-no-ore-missing-interact-class5
  , (λ a → refl)
  , associative-refuse-bracketings-both-compose
  , refuse-associator-not-identity
  , interact-engine-closed-shell-unwired-ok
  , interact-engine-closed-shell-atmophile-green-refuse
  , sole-axiom-count-is-one
  , structure-blocking-distinct-from-folklore

interactEngineClosedShellConservationNamed : String
interactEngineClosedShellConservationNamed =
  "interactEngineClosedShell: closed-shell noble-gas Z He Og InteractKind StructureBlocking class 5 He no-ore missing Interact catalysis not 26th axiom partial refuse conservation"

interactEngineClosedShellCrossWitnessAuthority : String
interactEngineClosedShellCrossWitnessAuthority =
  "umst/umst-chem/src/x_rows/interact_engine_closed_shell.rs"

chemIntCrossInteractEngineClosedShellAuthority : String
chemIntCrossInteractEngineClosedShellAuthority =
  "CHEM-INT-CROSS-INTERACT-ENGINE-CLOSED-SHELL-CONSERVATION"

interactEngineClosedShellCellId : String
interactEngineClosedShellCellId =
  "CHEM-FORMAL-Q-AGDA-INTERACT-ENGINE-CLOSED-SHELL-CONSERVATION"

interactEngineClosedShellNonClaim : String
interactEngineClosedShellNonClaim =
  "CHEM-FORMAL-Q-AGDA-INTERACT-ENGINE-CLOSED-SHELL-CONSERVATION Interact-engine closed-shell blocking partial Interact refuse He no-ore missing Interact class 5 structure_blocking_inertness not atmophile GREEN catalysis not 26th axiom interactEngineClosedShellProved false Unwired WAVE100 lib.rs eos.rs not wired one axiom second law conservation remainder deferred composition on second law not impossibility modality Unwired not physics GREEN not production_wired"

interact-engine-closed-shell-cell-id :
  interactEngineClosedShellCellId ≡
  "CHEM-FORMAL-Q-AGDA-INTERACT-ENGINE-CLOSED-SHELL-CONSERVATION"
interact-engine-closed-shell-cell-id = refl

interact-engine-closed-shell-cites-cross-witness-rs :
  interactEngineClosedShellCrossWitnessAuthority ≡
  "umst/umst-chem/src/x_rows/interact_engine_closed_shell.rs"
interact-engine-closed-shell-cites-cross-witness-rs = refl

interact-engine-closed-shell-modality-unwired :
  interactEngineClosedShellModalityCurrent ≡ interact-engine-closed-shell-unwired
interact-engine-closed-shell-modality-unwired = refl

interactEngineClosedShellPhysicsGreenAuthorized : Set
interactEngineClosedShellPhysicsGreenAuthorized = ⊥

interact-engine-closed-shell-physics-green-false :
  ¬ interactEngineClosedShellPhysicsGreenAuthorized
interact-engine-closed-shell-physics-green-false ()
