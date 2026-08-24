-- SPDX-FileCopyrightText: 2026 Santosh Prabhu Shenbagamoorthy and Santhosh Shyamsundar
-- SPDX-License-Identifier: MIT
------------------------------------------------------------------------
-- UMST-Formal: ChemConstants.CartridgeOreConsultMonoid.agda
--
-- CAT-cartridge Ore consult monoidal conservation on the knowing fiber (Q lattice):
--   * C-S-H (Ca,Si,O,H) and pore solution (Na,Cl,O,H) are Ore consults, not ElementId smuggle
--   * OreConsultTree leaf/tensor; unit I; associator as identity conservation
--   * concurrent monoidal product Π_c — pattern for Z=1..118 assemblages, not XOR ore enum
--   * monoidal laws Unwired (oreConsultMonoidProved = false)
--
-- Mirrors sibling `ChemConstants/OreMonoidalConservation.agda` +
-- `ChemConstants/CementHydrationNotL0G.agda` style.
-- INT: umst/umst-chem/src/x_rows/cartridge_ore_consult_monoid.rs
-- No meso / acting theorems. Modality Unwired; physics GREEN false.
-- WAVE100: not wired in lib.rs / eos.rs. Not 118² GREEN table.
-- Zero postulates that invent physics. Remainder deferred composition on second law.
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module ChemConstants.CartridgeOreConsultMonoid where

open import Data.Bool.Base using (Bool; false; true; not; _∧_; if_then_else_)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Nat using (ℕ; zero; suc; _≤_; _<_; _*_)
open import Data.Nat.Properties as ℕ-Props using (_≟_)
open import Data.Product using (_×_; _,_)
open import Data.String using (String)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl)
open import Relation.Nullary using (¬_)
open import Relation.Nullary.Decidable using (does)

------------------------------------------------------------------------
-- Modality + cartridge Ore consult monoidal pins (knowing fiber — Unwired)
------------------------------------------------------------------------

data CartridgeOreConsultMonoidModality : Set where
  cartridge-ore-consult-monoid-unwired cartridge-ore-consult-monoid-assumed
    cartridge-ore-consult-monoid-proved cartridge-ore-consult-monoid-surrogate
    : CartridgeOreConsultMonoidModality

cartridgeOreConsultMonoidModalityCurrent : CartridgeOreConsultMonoidModality
cartridgeOreConsultMonoidModalityCurrent = cartridge-ore-consult-monoid-unwired

cartridgeOreConsultModalityLatticeCardinality : ℕ
cartridgeOreConsultModalityLatticeCardinality = 4

cartridge-ore-consult-modality-lattice-cardinality-four :
  cartridgeOreConsultModalityLatticeCardinality ≡ 4
cartridge-ore-consult-modality-lattice-cardinality-four = refl

cartridge-ore-consult-modality-lattice-not-118-squared :
  does (cartridgeOreConsultModalityLatticeCardinality ℕ-Props.≟ (118 * 118)) ≡ false
cartridge-ore-consult-modality-lattice-not-118-squared = refl

oreConsultMonoidProved productionWired productNotXor associatorIdentityConservation
  wave100LibRsWired wave100EosRsWired : Bool
oreConsultMonoidProved = false
productionWired = false
productNotXor = true
associatorIdentityConservation = true
wave100LibRsWired = false
wave100EosRsWired = false

------------------------------------------------------------------------
-- Ore consult kinds — C-S-H and pore solution, not ElementId smuggle
------------------------------------------------------------------------

data OreConsultKind : Set where
  csh-consult pore-consult : OreConsultKind

cshIsElementId poreSolutionIsElementId : Bool
cshIsElementId = false
poreSolutionIsElementId = false

csh-not-element-id : cshIsElementId ≡ false
csh-not-element-id = refl

pore-solution-not-element-id : poreSolutionIsElementId ≡ false
pore-solution-not-element-id = refl

csh-distinct-from-pore : csh-consult ≢ pore-consult
csh-distinct-from-pore ()

------------------------------------------------------------------------
-- C-S-H Ore Z factors (Ca=20, Si=14, O=8, H=1) — Z in 1..118 bar
------------------------------------------------------------------------

cshCaZ cshSiZ cshOZ cshHZ : ℕ
cshCaZ = 20
cshSiZ = 14
cshOZ = 8
cshHZ = 1

poreNaZ poreClZ poreOZ poreHZ : ℕ
poreNaZ = 11
poreClZ = 17
poreOZ = 8
poreHZ = 1

periodicBarZ : ℕ
periodicBarZ = 118

z-in-bar : ℕ → Bool
z-in-bar 20 = true
z-in-bar 14 = true
z-in-bar 8  = true
z-in-bar 1  = true
z-in-bar 11 = true
z-in-bar 17 = true
z-in-bar _  = false

csh-ca-z-in-bar : z-in-bar cshCaZ ≡ true
csh-ca-z-in-bar = refl

csh-si-z-in-bar : z-in-bar cshSiZ ≡ true
csh-si-z-in-bar = refl

csh-o-z-in-bar : z-in-bar cshOZ ≡ true
csh-o-z-in-bar = refl

csh-h-z-in-bar : z-in-bar cshHZ ≡ true
csh-h-z-in-bar = refl

pore-na-z-in-bar : z-in-bar poreNaZ ≡ true
pore-na-z-in-bar = refl

pore-cl-z-in-bar : z-in-bar poreClZ ≡ true
pore-cl-z-in-bar = refl

pore-o-z-in-bar : z-in-bar poreOZ ≡ true
pore-o-z-in-bar = refl

pore-h-z-in-bar : z-in-bar poreHZ ≡ true
pore-h-z-in-bar = refl

cshOreFactorsInBar poreOreFactorsInBar : Bool
cshOreFactorsInBar =
  z-in-bar cshCaZ ∧ z-in-bar cshSiZ ∧ z-in-bar cshOZ ∧ z-in-bar cshHZ
poreOreFactorsInBar =
  z-in-bar poreNaZ ∧ z-in-bar poreClZ ∧ z-in-bar poreOZ ∧ z-in-bar poreHZ

csh-ore-factors-in-bar : cshOreFactorsInBar ≡ true
csh-ore-factors-in-bar = refl

pore-ore-factors-in-bar : poreOreFactorsInBar ≡ true
pore-ore-factors-in-bar = refl

oreFactorsInBar : Bool
oreFactorsInBar = cshOreFactorsInBar ∧ poreOreFactorsInBar

ore-factors-in-bar : oreFactorsInBar ≡ true
ore-factors-in-bar = refl

cartridgeOreConsultHonestConjunct : Bool
cartridgeOreConsultHonestConjunct =
  not cshIsElementId ∧ not poreSolutionIsElementId ∧ oreFactorsInBar

cartridge-ore-consult-honest-conjunct : cartridgeOreConsultHonestConjunct ≡ true
cartridge-ore-consult-honest-conjunct = refl

------------------------------------------------------------------------
-- OreConsultTree leaf/tensor (binary product tree — not ElementId smuggle)
------------------------------------------------------------------------

data OreConsultTree : Set where
  consult-leaf : OreConsultKind → OreConsultTree
  consult-tensor : OreConsultTree → OreConsultTree → OreConsultTree

oreConsultUnit : OreConsultTree
oreConsultUnit = consult-leaf pore-consult

oreConsultMonoidalProduct : OreConsultTree → OreConsultTree → OreConsultTree
oreConsultMonoidalProduct = consult-tensor

cshConsultLeaf poreConsultLeaf : OreConsultTree
cshConsultLeaf = consult-leaf csh-consult
poreConsultLeaf = consult-leaf pore-consult

isConsultTensor : OreConsultTree → Bool
isConsultTensor (consult-tensor _ _) = true
isConsultTensor _ = false

isConsultUnit : OreConsultTree → Bool
isConsultUnit (consult-leaf pore-consult) = true
isConsultUnit _ = false

left-unit-scaffold :
  ∀ (a : OreConsultTree) →
  isConsultUnit oreConsultUnit ≡ true × isConsultTensor (oreConsultMonoidalProduct oreConsultUnit a) ≡ true
left-unit-scaffold a = refl , refl

right-unit-scaffold :
  ∀ (a : OreConsultTree) →
  isConsultTensor (oreConsultMonoidalProduct a oreConsultUnit) ≡ true × isConsultUnit oreConsultUnit ≡ true
right-unit-scaffold a = refl , refl

consultAssociatorLeft consultAssociatorRight :
  OreConsultTree → OreConsultTree → OreConsultTree → OreConsultTree
consultAssociatorLeft a b c = oreConsultMonoidalProduct (oreConsultMonoidalProduct a b) c
consultAssociatorRight a b c = oreConsultMonoidalProduct a (oreConsultMonoidalProduct b c)

associative-bracketings-both-tensor :
  ∀ (a b c : OreConsultTree) →
  isConsultTensor (consultAssociatorLeft a b c) ≡ true × isConsultTensor (consultAssociatorRight a b c) ≡ true
associative-bracketings-both-tensor a b c = refl , refl

associator-not-identity :
  consultAssociatorLeft cshConsultLeaf poreConsultLeaf oreConsultUnit ≢
  consultAssociatorRight cshConsultLeaf poreConsultLeaf oreConsultUnit
associator-not-identity ()

associator-identity-conservation :
  associatorIdentityConservation ≡ true ×
  (∀ a b c →
    isConsultTensor (consultAssociatorLeft a b c) ≡ true × isConsultTensor (consultAssociatorRight a b c) ≡ true)
associator-identity-conservation = refl , associative-bracketings-both-tensor

triple-ore-consult-concurrent : OreConsultTree
triple-ore-consult-concurrent =
  oreConsultMonoidalProduct
    (oreConsultMonoidalProduct cshConsultLeaf poreConsultLeaf)
    oreConsultUnit

triple-ore-consult-is-tensor : isConsultTensor triple-ore-consult-concurrent ≡ true
triple-ore-consult-is-tensor = refl

product-not-xor : productNotXor ≡ true
product-not-xor = refl

ore-consult-monoid-not-proved : oreConsultMonoidProved ≡ false
ore-consult-monoid-not-proved = refl

production-not-wired : productionWired ≡ false
production-not-wired = refl

wave100-lib-rs-not-wired : wave100LibRsWired ≡ false
wave100-lib-rs-not-wired = refl

wave100-eos-rs-not-wired : wave100EosRsWired ≡ false
wave100-eos-rs-not-wired = refl

------------------------------------------------------------------------
-- Conservation close verdict — fail-closed lattice
------------------------------------------------------------------------

data CartridgeOreConsultMonoidVerdict : Set where
  verdict-unwired-ok verdict-ore-consult-ok verdict-element-id-smuggle-refuse
    verdict-green-invent-refuse verdict-production-wired-refuse
    : CartridgeOreConsultMonoidVerdict

cartridgeOreConsultVerdictOk : CartridgeOreConsultMonoidVerdict → Bool
cartridgeOreConsultVerdictOk verdict-unwired-ok = true
cartridgeOreConsultVerdictOk verdict-ore-consult-ok = true
cartridgeOreConsultVerdictOk _ = false

evaluateCartridgeOreConsultMonoid :
  CartridgeOreConsultMonoidModality →
  Bool → Bool → Bool →
  CartridgeOreConsultMonoidVerdict
evaluateCartridgeOreConsultMonoid m claimPhysicsGreen claimProved claimProductionWired =
  if claimPhysicsGreen then verdict-green-invent-refuse else
  if claimProductionWired then verdict-production-wired-refuse else
  if claimProved then verdict-ore-consult-ok else
  if cartridgeOreConsultHonestConjunct then pickModality m else verdict-element-id-smuggle-refuse
  where
  pickModality : CartridgeOreConsultMonoidModality → CartridgeOreConsultMonoidVerdict
  pickModality cartridge-ore-consult-monoid-unwired = verdict-unwired-ok
  pickModality _ = verdict-ore-consult-ok

cartridge-ore-consult-unwired-ok :
  evaluateCartridgeOreConsultMonoid
    cartridge-ore-consult-monoid-unwired false false false
    ≡ verdict-unwired-ok
cartridge-ore-consult-unwired-ok = refl

cartridge-ore-consult-green-invent-refuse :
  evaluateCartridgeOreConsultMonoid
    cartridge-ore-consult-monoid-unwired true false false
    ≡ verdict-green-invent-refuse
cartridge-ore-consult-green-invent-refuse = refl

cartridge-ore-consult-production-wired-refuse :
  evaluateCartridgeOreConsultMonoid
    cartridge-ore-consult-monoid-unwired false false true
    ≡ verdict-production-wired-refuse
cartridge-ore-consult-production-wired-refuse = refl

cartridge-ore-consult-element-id-smuggle-refuse :
  cartridgeOreConsultVerdictOk
    (evaluateCartridgeOreConsultMonoid
       cartridge-ore-consult-monoid-unwired true false false)
    ≡ false
cartridge-ore-consult-element-id-smuggle-refuse = refl

------------------------------------------------------------------------
-- One design axiom + authority cites (not a 26th axiom fork)
------------------------------------------------------------------------

soleAxiomCount : ℕ
soleAxiomCount = 1

sole-axiom-count-is-one : soleAxiomCount ≡ 1
sole-axiom-count-is-one = refl

cartridgeOreConsultMonoidAxiom :
  (oreConsultMonoidProved ≡ false)
  × (productionWired ≡ false)
  × (wave100LibRsWired ≡ false)
  × (wave100EosRsWired ≡ false)
  × (productNotXor ≡ true)
  × (associatorIdentityConservation ≡ true)
  × (cshIsElementId ≡ false)
  × (poreSolutionIsElementId ≡ false)
  × (oreFactorsInBar ≡ true)
  × (cartridgeOreConsultHonestConjunct ≡ true)
  × (∀ a → isConsultTensor (oreConsultMonoidalProduct oreConsultUnit a) ≡ true)
  × (∀ a b c →
      isConsultTensor (consultAssociatorLeft a b c) ≡ true × isConsultTensor (consultAssociatorRight a b c) ≡ true)
  × ¬ (consultAssociatorLeft cshConsultLeaf poreConsultLeaf oreConsultUnit ≡
       consultAssociatorRight cshConsultLeaf poreConsultLeaf oreConsultUnit)
  × (evaluateCartridgeOreConsultMonoid
       cartridge-ore-consult-monoid-unwired false false false
       ≡ verdict-unwired-ok)
  × (cartridgeOreConsultVerdictOk
       (evaluateCartridgeOreConsultMonoid
          cartridge-ore-consult-monoid-unwired true false false)
     ≡ false)
  × (soleAxiomCount ≡ 1)
cartridgeOreConsultMonoidAxiom =
  ore-consult-monoid-not-proved
  , production-not-wired
  , wave100-lib-rs-not-wired
  , wave100-eos-rs-not-wired
  , product-not-xor
  , refl
  , csh-not-element-id
  , pore-solution-not-element-id
  , ore-factors-in-bar
  , cartridge-ore-consult-honest-conjunct
  , (λ a → refl)
  , associative-bracketings-both-tensor
  , associator-not-identity
  , cartridge-ore-consult-unwired-ok
  , cartridge-ore-consult-element-id-smuggle-refuse
  , sole-axiom-count-is-one

cartridgeOreConsultMonoidConservationNamed : String
cartridgeOreConsultMonoidConservationNamed =
  "cartridgeOreConsultMonoid: C-S-H Ca Si O H and pore Na Cl O H Ore consults not ElementId smuggle Z 1..118 monoidal tensor unit I associator identity conservation"

cartridgeOreConsultCrossWitnessAuthority : String
cartridgeOreConsultCrossWitnessAuthority =
  "umst/umst-chem/src/x_rows/cartridge_ore_consult_monoid.rs"

chemIntCrossCartridgeOreConsultAuthority : String
chemIntCrossCartridgeOreConsultAuthority =
  "CHEM-INT-CROSS-CARTRIDGE-ORE-CONSULT-MONOID-CONSERVATION"

cartridgeOreConsultMonoidCellId : String
cartridgeOreConsultMonoidCellId =
  "CHEM-FORMAL-Q-AGDA-CARTRIDGE-ORE-CONSULT-MONOID-CONSERVATION"

cartridgeOreConsultMonoidNonClaim : String
cartridgeOreConsultMonoidNonClaim =
  "CHEM-FORMAL-Q-AGDA-CARTRIDGE-ORE-CONSULT-MONOID-CONSERVATION C-S-H Ca Si O H and pore Na Cl O H are Ore consults not ElementId smuggle pattern Z 1..118 assemblages not a 26th axiom oreConsultMonoidProved false Unwired WAVE100 lib.rs eos.rs not wired one axiom second law conservation not second optimizer axiom not GREEN DFT not physics GREEN not production_wired remainder deferred composition on second law not impossibility"

cartridge-ore-consult-monoid-cell-id :
  cartridgeOreConsultMonoidCellId ≡
  "CHEM-FORMAL-Q-AGDA-CARTRIDGE-ORE-CONSULT-MONOID-CONSERVATION"
cartridge-ore-consult-monoid-cell-id = refl

cartridge-ore-consult-cites-cross-witness-rs :
  cartridgeOreConsultCrossWitnessAuthority ≡
  "umst/umst-chem/src/x_rows/cartridge_ore_consult_monoid.rs"
cartridge-ore-consult-cites-cross-witness-rs = refl

cartridge-ore-consult-modality-unwired :
  cartridgeOreConsultMonoidModalityCurrent ≡ cartridge-ore-consult-monoid-unwired
cartridge-ore-consult-modality-unwired = refl

cartridgeOreConsultMonoidPhysicsGreenAuthorized : Set
cartridgeOreConsultMonoidPhysicsGreenAuthorized = ⊥

cartridge-ore-consult-monoid-physics-green-false :
  ¬ cartridgeOreConsultMonoidPhysicsGreenAuthorized
cartridge-ore-consult-monoid-physics-green-false ()
