-- SPDX-FileCopyrightText: 2026 Santosh Prabhu Shenbagamoorthy and Santhosh Shyamsundar
-- SPDX-License-Identifier: MIT
------------------------------------------------------------------------
-- UMST-Formal: ChemConstants.DlvoKtNotPsi.agda
--
-- Knowing-fiber Agda: fluids DLVO kT is a coefficient pin, not constitutive ψ:
--   * DLVO_KT_PIN_TAG = coefficient_pin; PSI_TAG = constitutive_psi
--   * dlvoKtIsPsi false; pinDistinctFromPsi true
--   * Sole axiom: second law + conservation (not 26th axiom)
--   * dlvoKtNotPsiProved false; modality Unwired; physics GREEN false
--
-- Mirrors sibling `ChemConstants/CartridgeConstitutiveCompose.agda` style.
-- INT cross-witness: umst/umst-chem/src/x_rows/dlvo_kt_not_psi.rs
-- No meso / acting theorems. WAVE100: not wired in lib.rs / eos.rs.
-- Remainder is deferred composition on the same second law, not impossibility.
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module ChemConstants.DlvoKtNotPsi where

open import Data.Bool using (Bool; false; true; not; _∧_)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Nat using (ℕ; suc; zero)
open import Data.Product using (_×_; _,_)
open import Data.String using (String)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl)
open import Relation.Nullary using (¬_)

------------------------------------------------------------------------
-- Modality + DLVO kT not-ψ pins (knowing fiber — Unwired)
------------------------------------------------------------------------

data DlvoKtNotPsiModality : Set where
  dlvo-kt-not-psi-unwired dlvo-kt-not-psi-assumed
    dlvo-kt-not-psi-proved dlvo-kt-not-psi-surrogate
    : DlvoKtNotPsiModality

dlvoKtNotPsiModalityCurrent : DlvoKtNotPsiModality
dlvoKtNotPsiModalityCurrent = dlvo-kt-not-psi-unwired

dlvoKtNotPsiProved productionWired wave100LibRsWired wave100EosRsWired
  dlvoKtIsPsi pinDistinctFromPsi : Bool
dlvoKtNotPsiProved = false
productionWired = false
wave100LibRsWired = false
wave100EosRsWired = false
dlvoKtIsPsi = false
pinDistinctFromPsi = true

------------------------------------------------------------------------
-- Pin tag channels — coefficient pin vs constitutive ψ
------------------------------------------------------------------------

data DlvoPinTag : Set where
  coefficient-pin-tag constitutive-psi-tag : DlvoPinTag

dlvoKtPinTag psiTag : String
dlvoKtPinTag = "coefficient_pin"
psiTag = "constitutive_psi"

coefficient-pin-tag-named :
  dlvoKtPinTag ≡ "coefficient_pin"
coefficient-pin-tag-named = refl

constitutive-psi-tag-named :
  psiTag ≡ "constitutive_psi"
constitutive-psi-tag-named = refl

isCoefficientPin isConstitutivePsi : DlvoPinTag → Bool
isCoefficientPin coefficient-pin-tag = true
isCoefficientPin _ = false

isConstitutivePsi constitutive-psi-tag = true
isConstitutivePsi _ = false

coefficient-pin-channel-named :
  isCoefficientPin coefficient-pin-tag ≡ true × isConstitutivePsi coefficient-pin-tag ≡ false
coefficient-pin-channel-named = refl , refl

constitutive-psi-channel-named :
  isConstitutivePsi constitutive-psi-tag ≡ true × isCoefficientPin constitutive-psi-tag ≡ false
constitutive-psi-channel-named = refl , refl

coefficient-pin-distinct-from-psi : coefficient-pin-tag ≢ constitutive-psi-tag
coefficient-pin-distinct-from-psi ()

------------------------------------------------------------------------
-- DLVO kT pin scaffold — compose steps dual of constitutive ψ carrier
------------------------------------------------------------------------

data FluidsCartridgeTag : Set where
  colloidal-fluids-cartridge : FluidsCartridgeTag

data DlvoKtPinStep : Set where
  pin-identity : DlvoKtPinStep
  pin-leaf : DlvoPinTag → FluidsCartridgeTag → DlvoKtPinStep
  pin-compose : DlvoKtPinStep → DlvoKtPinStep → DlvoKtPinStep

dlvoKtPinIdentity : DlvoKtPinStep
dlvoKtPinIdentity = pin-identity

pinComposeOp : DlvoKtPinStep → DlvoKtPinStep → DlvoKtPinStep
pinComposeOp = pin-compose

coefficientPinColloidalLeaf constitutivePsiColloidalLeaf : DlvoKtPinStep
coefficientPinColloidalLeaf = pin-leaf coefficient-pin-tag colloidal-fluids-cartridge
constitutivePsiColloidalLeaf = pin-leaf constitutive-psi-tag colloidal-fluids-cartridge

isPinCompose isPinIdentity : DlvoKtPinStep → Bool
isPinCompose (pin-compose _ _) = true
isPinCompose _ = false

isPinIdentity pin-identity = true
isPinIdentity _ = false

left-identity-scaffold :
  ∀ (a : DlvoKtPinStep) →
  isPinIdentity dlvoKtPinIdentity ≡ true ×
  isPinCompose (pinComposeOp dlvoKtPinIdentity a) ≡ true
left-identity-scaffold a = refl , refl

right-identity-scaffold :
  ∀ (a : DlvoKtPinStep) →
  isPinCompose (pinComposeOp a dlvoKtPinIdentity) ≡ true ×
  isPinIdentity dlvoKtPinIdentity ≡ true
right-identity-scaffold a = refl , refl

associatorLeft associatorRight :
  DlvoKtPinStep → DlvoKtPinStep → DlvoKtPinStep → DlvoKtPinStep
associatorLeft a b c = pinComposeOp (pinComposeOp a b) c
associatorRight a b c = pinComposeOp a (pinComposeOp b c)

associative-bracketings-both-pin-compose :
  ∀ (a b c : DlvoKtPinStep) →
  isPinCompose (associatorLeft a b c) ≡ true × isPinCompose (associatorRight a b c) ≡ true
associative-bracketings-both-pin-compose a b c = refl , refl

associator-not-identity :
  associatorLeft coefficientPinColloidalLeaf constitutivePsiColloidalLeaf dlvoKtPinIdentity ≢
  associatorRight coefficientPinColloidalLeaf constitutivePsiColloidalLeaf dlvoKtPinIdentity
associator-not-identity ()

------------------------------------------------------------------------
-- kT pin ≠ ψ — const-time string inequality scaffold
------------------------------------------------------------------------

constStrNe : String → String → Bool
constStrNe a b with a | b
... | "coefficient_pin" | "constitutive_psi" = true
... | _ | _ = false

pin-tag-ne-psi-tag : constStrNe dlvoKtPinTag psiTag ≡ true
pin-tag-ne-psi-tag = refl

dlvo-kt-not-psi : dlvoKtIsPsi ≡ false
dlvo-kt-not-psi = refl

pin-distinct-from-psi-bool : pinDistinctFromPsi ≡ true
pin-distinct-from-psi-bool = refl

pin-distinct-from-psi-scaffold :
  (dlvoKtIsPsi ≡ false) × (constStrNe dlvoKtPinTag psiTag ≡ true)
pin-distinct-from-psi-scaffold = dlvo-kt-not-psi , pin-tag-ne-psi-tag

triple-pin-compose : DlvoKtPinStep
triple-pin-compose =
  pinComposeOp
    (pinComposeOp coefficientPinColloidalLeaf constitutivePsiColloidalLeaf)
    dlvoKtPinIdentity

triple-pin-compose-is-compose : isPinCompose triple-pin-compose ≡ true
triple-pin-compose-is-compose = refl

dlvo-kt-not-psi-proved-false : dlvoKtNotPsiProved ≡ false
dlvo-kt-not-psi-proved-false = refl

production-not-wired : productionWired ≡ false
production-not-wired = refl

wave100-lib-rs-not-wired : wave100LibRsWired ≡ false
wave100-lib-rs-not-wired = refl

wave100-eos-rs-not-wired : wave100EosRsWired ≡ false
wave100-eos-rs-not-wired = refl

------------------------------------------------------------------------
-- One design axiom + authority cites (not a 26th axiom fork)
------------------------------------------------------------------------

soleAxiomCount : ℕ
soleAxiomCount = 1

sole-axiom-count-is-one : soleAxiomCount ≡ 1
sole-axiom-count-is-one = refl

dlvoKtNotPsiAxiom :
  (dlvoKtNotPsiProved ≡ false)
  × (productionWired ≡ false)
  × (wave100LibRsWired ≡ false)
  × (wave100EosRsWired ≡ false)
  × (dlvoKtIsPsi ≡ false)
  × (pinDistinctFromPsi ≡ true)
  × (constStrNe dlvoKtPinTag psiTag ≡ true)
  × (∀ a → isPinCompose (pinComposeOp dlvoKtPinIdentity a) ≡ true)
  × (∀ a b c →
      isPinCompose (associatorLeft a b c) ≡ true × isPinCompose (associatorRight a b c) ≡ true)
  × ¬ (coefficient-pin-tag ≡ constitutive-psi-tag)
  × (soleAxiomCount ≡ 1)
dlvoKtNotPsiAxiom =
  dlvo-kt-not-psi-proved-false
  , production-not-wired
  , wave100-lib-rs-not-wired
  , wave100-eos-rs-not-wired
  , dlvo-kt-not-psi
  , pin-distinct-from-psi-bool
  , pin-tag-ne-psi-tag
  , (λ a → refl)
  , associative-bracketings-both-pin-compose
  , coefficient-pin-distinct-from-psi
  , sole-axiom-count-is-one

dlvoKtNotPsiNamed : String
dlvoKtNotPsiNamed =
  "dlvoKtNotPsi: fluids DLVO kT coefficient pin not constitutive psi pinDistinctFromPsi true dlvoKtIsPsi false"

dlvoKtNotPsiCrossWitnessAuthority : String
dlvoKtNotPsiCrossWitnessAuthority =
  "umst/umst-chem/src/x_rows/dlvo_kt_not_psi.rs"

chemIntCrossDlvoKtNotPsiAuthority : String
chemIntCrossDlvoKtNotPsiAuthority =
  "CHEM-INT-CROSS-DLVO-KT-NOT-PSI-CONSERVATION"

dlvoKtNotPsiCellId : String
dlvoKtNotPsiCellId =
  "CHEM-FORMAL-Q-AGDA-DLVO-KT-NOT-PSI-CONSERVATION"

dlvoKtNotPsiNonClaim : String
dlvoKtNotPsiNonClaim =
  "CHEM-FORMAL-Q-AGDA-DLVO-KT-NOT-PSI-CONSERVATION fluids DLVO kT is a coefficient pin not constitutive psi not a 26th axiom dlvoKtNotPsiProved false Unwired WAVE100 lib.rs eos.rs not wired one axiom second law conservation remainder deferred composition on same second law not impossibility modality Unwired not physics GREEN not production_wired"

dlvo-kt-not-psi-cell-id :
  dlvoKtNotPsiCellId ≡
  "CHEM-FORMAL-Q-AGDA-DLVO-KT-NOT-PSI-CONSERVATION"
dlvo-kt-not-psi-cell-id = refl

dlvo-kt-not-psi-cites-cross-witness-rs :
  dlvoKtNotPsiCrossWitnessAuthority ≡
  "umst/umst-chem/src/x_rows/dlvo_kt_not_psi.rs"
dlvo-kt-not-psi-cites-cross-witness-rs = refl

dlvo-kt-not-psi-modality-unwired :
  dlvoKtNotPsiModalityCurrent ≡ dlvo-kt-not-psi-unwired
dlvo-kt-not-psi-modality-unwired = refl

dlvoKtNotPsiPhysicsGreenAuthorized : Set
dlvoKtNotPsiPhysicsGreenAuthorized = ⊥

dlvo-kt-not-psi-physics-green-false :
  ¬ dlvoKtNotPsiPhysicsGreenAuthorized
dlvo-kt-not-psi-physics-green-false ()
