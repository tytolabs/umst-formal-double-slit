-- SPDX-FileCopyrightText: 2026 Santosh Prabhu Shenbagamoorthy and Santhosh Shyamsundar
-- SPDX-License-Identifier: MIT
------------------------------------------------------------------------
-- UMST-Formal: ChemConstants.LinearConservation.agda
--
-- TYPE-02 linear conservation on the knowing fiber (Q lattice):
--   * ConservationAxis Mass/Charge/AtomCount/Enthalpy — structure not 118² GREEN
--   * LinearCoeffRow signed coeffs; linear exact-balance sum 0 balanced / imbalanced refuse
--   * Affine weakening only with DissipativeWitness; without witness refuse
--   * linear laws Unwired (type02LinearProved = false)
--
-- Mirrors sibling `ChemConstants/DependentTypesConservation.agda` +
-- `ChemConstants/OreMonoidalConservation.agda` style.
-- No meso / acting theorems. Modality Unwired; physics GREEN false.
-- Not 118² GREEN table. Second-law + conservation framing (not wired).
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module ChemConstants.LinearConservation where

open import Data.Bool.Base using (Bool; false; true; _∧_)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Integer.Base using (ℤ; +_; -[1+_]; _+_; +0)
open import Data.Integer.Properties as ℤ-Props using (_≟_)
open import Data.Maybe using (Maybe; nothing; just)
open import Data.Nat using (ℕ; zero; suc; _*_)
open import Data.Nat.Properties as ℕ-Props using (_≤?_; _≟_)
open import Data.Product using (_×_; _,_)
open import Data.String using (String)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Relation.Nullary using (Dec; yes; no; ¬_)
open import Relation.Nullary.Decidable using (does)

------------------------------------------------------------------------
-- Modality + linear conservation pins (knowing fiber — Unwired)
------------------------------------------------------------------------

data LinearConservationModality : Set where
  linear-conservation-unwired linear-conservation-assumed
    linear-conservation-proved linear-conservation-surrogate
    : LinearConservationModality

linearConservationModalityCurrent : LinearConservationModality
linearConservationModalityCurrent = linear-conservation-unwired

type02LinearProved productionWired linearAlgebraNotSpeciesBacked
  conservationAxesNot118GreenTable linearConservationSecondLawFramed : Bool
type02LinearProved = false
productionWired = false
linearAlgebraNotSpeciesBacked = true
conservationAxesNot118GreenTable = true
linearConservationSecondLawFramed = true

------------------------------------------------------------------------
-- ConservationAxis Mass/Charge/AtomCount/Enthalpy (structure — not 118²)
------------------------------------------------------------------------

data ConservationAxis : Set where
  mass-axis charge-axis atom-count-axis enthalpy-axis : ConservationAxis

conservationAxisCardinality : ℕ
conservationAxisCardinality = 4

conservation-axis-cardinality-four : conservationAxisCardinality ≡ 4
conservation-axis-cardinality-four = refl

------------------------------------------------------------------------
-- LinearCoeffRow — signed coeffs; linear exact-balance on an axis
------------------------------------------------------------------------

record LinearCoeffRow : Set where
  constructor mkLinearCoeffRow
  field
    axis : ConservationAxis
    reactantA reactantB productC productD : ℤ

linearCoeffSum : LinearCoeffRow → ℤ
linearCoeffSum row =
  LinearCoeffRow.reactantA row
  + LinearCoeffRow.reactantB row
  + LinearCoeffRow.productC row
  + LinearCoeffRow.productD row

linearAxisBalanced : LinearCoeffRow → Bool
linearAxisBalanced row = does (linearCoeffSum row ℤ-Props.≟ +0)

massBalancedRow : LinearCoeffRow
massBalancedRow = mkLinearCoeffRow mass-axis (+ 1) (+ 1) (-[1+ 0 ]) (-[1+ 0 ])

chargeBalancedRow : LinearCoeffRow
chargeBalancedRow = mkLinearCoeffRow charge-axis (+ 2) (-[1+ 0 ]) (-[1+ 0 ]) +0

massImbalancedRow : LinearCoeffRow
massImbalancedRow = mkLinearCoeffRow mass-axis (+ 1) (+ 1) (-[1+ 0 ]) +0

atomCountImbalancedRow : LinearCoeffRow
atomCountImbalancedRow = mkLinearCoeffRow atom-count-axis (+ 3) +0 (-[1+ 0 ]) (-[1+ 0 ])

enthalpyZeroRow : LinearCoeffRow
enthalpyZeroRow = mkLinearCoeffRow enthalpy-axis +0 +0 +0 +0

mass-balanced-linear-conservation : linearAxisBalanced massBalancedRow ≡ true
mass-balanced-linear-conservation = refl

charge-balanced-linear-conservation : linearAxisBalanced chargeBalancedRow ≡ true
charge-balanced-linear-conservation = refl

mass-imbalanced-linear-refuse : linearAxisBalanced massImbalancedRow ≡ false
mass-imbalanced-linear-refuse = refl

atom-count-imbalanced-linear-refuse : linearAxisBalanced atomCountImbalancedRow ≡ false
atom-count-imbalanced-linear-refuse = refl

enthalpy-zero-linear-conservation : linearAxisBalanced enthalpyZeroRow ≡ true
enthalpy-zero-linear-conservation = refl

axisEq : ConservationAxis → ConservationAxis → Bool
axisEq mass-axis mass-axis = true
axisEq charge-axis charge-axis = true
axisEq atom-count-axis atom-count-axis = true
axisEq enthalpy-axis enthalpy-axis = true
axisEq _ _ = false

linearRowOnAxis : LinearCoeffRow → ConservationAxis → Bool
linearRowOnAxis row axis = axisEq (LinearCoeffRow.axis row) axis

mass-balanced-on-mass-axis : linearRowOnAxis massBalancedRow mass-axis ≡ true
mass-balanced-on-mass-axis = refl

------------------------------------------------------------------------
-- Affine slack + dissipative witness — weakening only with witness
------------------------------------------------------------------------

record AffineSlackRow : Set where
  constructor mkAffineSlackRow
  field
    linear : LinearCoeffRow
    slack : ℕ

affineConservationClosed : AffineSlackRow → Bool
affineConservationClosed row =
  does (linearCoeffSum (AffineSlackRow.linear row) + + (AffineSlackRow.slack row) ℤ-Props.≟ +0)

record DissipativeWitness : Set where
  constructor mkDissipativeWitness
  field
    slack bathTempScaffold dissipatedWorkScaffold : ℕ

dissipativeWitnessOk : DissipativeWitness → Bool
dissipativeWitnessOk w =
  does
    ( DissipativeWitness.slack w * DissipativeWitness.bathTempScaffold w
      ℕ-Props.≤? DissipativeWitness.dissipatedWorkScaffold w
    )

affineWeakeningAdmitted : AffineSlackRow → Maybe DissipativeWitness → Bool
affineWeakeningAdmitted row nothing = false
affineWeakeningAdmitted row (just w) =
  affineConservationClosed row
  ∧ does (DissipativeWitness.slack w ℕ-Props.≟ AffineSlackRow.slack row)
  ∧ dissipativeWitnessOk w

massAffineLinearRow : LinearCoeffRow
massAffineLinearRow = mkLinearCoeffRow mass-axis (-[1+ 1 ]) (+ 1) +0 +0

mass-affine-linear-row-imbalanced : linearAxisBalanced massAffineLinearRow ≡ false
mass-affine-linear-row-imbalanced = refl

massAffineSlackRow : AffineSlackRow
massAffineSlackRow = mkAffineSlackRow massAffineLinearRow 1

massAffineConservationClosed : affineConservationClosed massAffineSlackRow ≡ true
massAffineConservationClosed = refl

massDissipativeWitness : DissipativeWitness
massDissipativeWitness = mkDissipativeWitness 1 2 3

mass-dissipative-witness-ok : dissipativeWitnessOk massDissipativeWitness ≡ true
mass-dissipative-witness-ok = refl

mass-affine-weakening-admitted-with-witness :
  affineWeakeningAdmitted massAffineSlackRow (just massDissipativeWitness) ≡ true
mass-affine-weakening-admitted-with-witness = refl

mass-affine-weakening-refuse-without-witness :
  affineWeakeningAdmitted massAffineSlackRow nothing ≡ false
mass-affine-weakening-refuse-without-witness = refl

massWrongSlackWitness : DissipativeWitness
massWrongSlackWitness = mkDissipativeWitness 2 2 10

mass-affine-weakening-refuse-wrong-witness :
  affineWeakeningAdmitted massAffineSlackRow (just massWrongSlackWitness) ≡ false
mass-affine-weakening-refuse-wrong-witness = refl

------------------------------------------------------------------------
-- Honest pins — not TYPE-02 Proved, not physics GREEN
------------------------------------------------------------------------

type02-linear-not-proved : type02LinearProved ≡ false
type02-linear-not-proved = refl

production-not-wired : productionWired ≡ false
production-not-wired = refl

linear-algebra-not-species-backed : linearAlgebraNotSpeciesBacked ≡ true
linear-algebra-not-species-backed = refl

conservation-axes-not-118-green-table : conservationAxesNot118GreenTable ≡ true
conservation-axes-not-118-green-table = refl

linear-conservation-second-law-framed : linearConservationSecondLawFramed ≡ true
linear-conservation-second-law-framed = refl

------------------------------------------------------------------------
-- One design axiom + authority cites (not a second optimizer fork)
------------------------------------------------------------------------

linearConservationAxiom :
  (type02LinearProved ≡ false)
  × (productionWired ≡ false)
  × (linearAlgebraNotSpeciesBacked ≡ true)
  × (conservationAxesNot118GreenTable ≡ true)
  × (linearConservationSecondLawFramed ≡ true)
  × (linearAxisBalanced massBalancedRow ≡ true)
  × (linearAxisBalanced chargeBalancedRow ≡ true)
  × (linearAxisBalanced massImbalancedRow ≡ false)
  × (linearAxisBalanced massAffineLinearRow ≡ false)
  × (linearAxisBalanced atomCountImbalancedRow ≡ false)
  × (affineWeakeningAdmitted massAffineSlackRow (just massDissipativeWitness) ≡ true)
  × (affineWeakeningAdmitted massAffineSlackRow nothing ≡ false)
  × (affineWeakeningAdmitted massAffineSlackRow (just massWrongSlackWitness) ≡ false)
linearConservationAxiom =
  type02-linear-not-proved
  , production-not-wired
  , linear-algebra-not-species-backed
  , conservation-axes-not-118-green-table
  , linear-conservation-second-law-framed
  , mass-balanced-linear-conservation
  , charge-balanced-linear-conservation
  , mass-imbalanced-linear-refuse
  , mass-affine-linear-row-imbalanced
  , atom-count-imbalanced-linear-refuse
  , mass-affine-weakening-admitted-with-witness
  , mass-affine-weakening-refuse-without-witness
  , mass-affine-weakening-refuse-wrong-witness

linearConservationNamed : String
linearConservationNamed =
  "linearConservation: ConservationAxis Mass Charge AtomCount Enthalpy linear exact-balance affine slack dissipative witness"

linearConservationCellId : String
linearConservationCellId = "CHEM-FORMAL-Q-AGDA-LINEAR-CONSERVATION"

linearConservationNonClaim : String
linearConservationNonClaim =
  "CHEM-FORMAL-Q-AGDA-LINEAR-CONSERVATION TYPE-02 linear conservation ConservationAxis Mass Charge AtomCount Enthalpy linear exact-balance affine slack dissipative witness type02LinearProved false not TYPE-02 Proved not 118 squared GREEN table one design axiom second law conservation not second optimizer axiom modality Unwired not physics GREEN not production_wired"

linear-conservation-modality-unwired :
  linearConservationModalityCurrent ≡ linear-conservation-unwired
linear-conservation-modality-unwired = refl

linearConservationPhysicsGreenAuthorized : Set
linearConservationPhysicsGreenAuthorized = ⊥

linear-conservation-physics-green-false : ¬ linearConservationPhysicsGreenAuthorized
linear-conservation-physics-green-false ()
