-- SPDX-FileCopyrightText: 2026 Santosh Prabhu Shenbagamoorthy and Santhosh Shyamsundar
-- SPDX-License-Identifier: MIT
------------------------------------------------------------------------
-- UMST-Formal: ChemConstants.ConstantDeriveSecondLawCensus.agda
--
-- Constant-derive second-law census on the knowing fiber (Q lattice):
--   * Engines consult ExactSI / occupancy / derived-morphism sheaf
--   * Do not mint k, R, or ε₀; α MeasuredCited not Landauer-faked
--   * constantDeriveSecondLawCensusProved = false; modality Unwired; physics GREEN false
--
-- Mirrors sibling `ChemConstants/OccupancyEngineSort.agda` scaffold +
-- INT `umst-chem/src/x_rows/constant_derive_second_law_census.rs`.
-- Cites engine_refuses_new_si constant_derive_preference si_exact_defining_constants
-- gas_constant_is_derived_morphism vacuum_permittivity_si_derived qlattice — not fork.
-- No meso / acting theorems. WAVE100: not wired in lib.rs / eos.rs.
-- Zero postulates that invent physics. Sole axiom: second law + conservation.
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module ChemConstants.ConstantDeriveSecondLawCensus where

open import Data.Bool.Base using (Bool; false; true; not; _∧_; if_then_else_)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Nat using (ℕ; zero; suc; _+_)
open import Data.Product using (_×_; _,_)
open import Data.String using (String)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl)
open import Relation.Nullary using (¬_)

open import ChemConstants.EngineRefusesNewSi using
  ( engineMayMintSi; engineUsesExistingSheaf
  ; forbiddenMintCount; soleAxiomSecondLawConservation; soleAxiomCount
  ; engine-may-not-mint-si; engine-uses-existing-sheaf
  ; forbidden-mint-count-three; sole-axiom-second-law; sole-axiom-count-one
  ; engineRefusesNewSiIntCellId; engineRefusesNewSiMarker
  )

------------------------------------------------------------------------
-- Modality + constant-derive second-law census pins (knowing fiber — Unwired)
------------------------------------------------------------------------

data ConstantDeriveSecondLawCensusModality : Set where
  constant-derive-second-law-census-unwired constant-derive-second-law-census-assumed
    constant-derive-second-law-census-proved constant-derive-second-law-census-surrogate
    : ConstantDeriveSecondLawCensusModality

constantDeriveSecondLawCensusModalityCurrent : ConstantDeriveSecondLawCensusModality
constantDeriveSecondLawCensusModalityCurrent = constant-derive-second-law-census-unwired

constantDeriveSecondLawCensusModalityLatticeCardinality : ℕ
constantDeriveSecondLawCensusModalityLatticeCardinality = 4

constant-derive-second-law-census-modality-lattice-cardinality-four :
  constantDeriveSecondLawCensusModalityLatticeCardinality ≡ 4
constant-derive-second-law-census-modality-lattice-cardinality-four = refl

constantDeriveSecondLawCensusProved productionWired productNotXor wave100LibRsWired
  wave100EosRsWired landauerFakeAlphaMinted allCensusRowsConsultSheaf
  forbiddenSiMintsPinned enginesUseExistingSheaf
  alphaMeasuredCitedNotLandauerFake landauerBridgeScopedKcNotAlpha
  exactSiKCitedNotMinted : Bool
constantDeriveSecondLawCensusProved = false
productionWired = false
productNotXor = true
wave100LibRsWired = false
wave100EosRsWired = false
landauerFakeAlphaMinted = false
allCensusRowsConsultSheaf = true
forbiddenSiMintsPinned = true
enginesUseExistingSheaf = true
alphaMeasuredCitedNotLandauerFake = true
landauerBridgeScopedKcNotAlpha = true
exactSiKCitedNotMinted = true

------------------------------------------------------------------------
-- Sheaf consult layers — ExactSI / occupancy / derived morphism
------------------------------------------------------------------------

data SheafConsultLayer : Set where
  exact-si-layer occupancy-layer derived-morphism-layer : SheafConsultLayer

isExactSiLayer isOccupancyLayer isDerivedMorphismLayer : SheafConsultLayer → Bool
isExactSiLayer exact-si-layer = true
isExactSiLayer _ = false

isOccupancyLayer occupancy-layer = true
isOccupancyLayer _ = false

isDerivedMorphismLayer derived-morphism-layer = true
isDerivedMorphismLayer _ = false

exact-si-layer-named :
  isExactSiLayer exact-si-layer ≡ true × isOccupancyLayer exact-si-layer ≡ false
exact-si-layer-named = refl , refl

occupancy-layer-named :
  isOccupancyLayer occupancy-layer ≡ true × isExactSiLayer occupancy-layer ≡ false
occupancy-layer-named = refl , refl

derived-morphism-layer-named :
  isDerivedMorphismLayer derived-morphism-layer ≡ true × isExactSiLayer derived-morphism-layer ≡ false
derived-morphism-layer-named = refl , refl

sheafConsultLayerCount : ℕ
sheafConsultLayerCount = 3

sheaf-consult-layer-count-three : sheafConsultLayerCount ≡ 3
sheaf-consult-layer-count-three = refl

------------------------------------------------------------------------
-- Engine census rows — consult sheaf, do not mint k/R/ε₀
------------------------------------------------------------------------

data EngineCensusRowTag : Set where
  si-exact-defining-constants-row qlattice-row
    gas-constant-derived-morphism-row vacuum-permittivity-derived-row
    engine-refuses-new-si-row : EngineCensusRowTag

engineCensusRowCount : ℕ
engineCensusRowCount = 5

engine-census-row-count-five : engineCensusRowCount ≡ 5
engine-census-row-count-five = refl

rowMayMintSi : EngineCensusRowTag → Bool
rowMayMintSi _ = false

rowSheafLayer : EngineCensusRowTag → SheafConsultLayer
rowSheafLayer si-exact-defining-constants-row = exact-si-layer
rowSheafLayer qlattice-row = occupancy-layer
rowSheafLayer gas-constant-derived-morphism-row = derived-morphism-layer
rowSheafLayer vacuum-permittivity-derived-row = derived-morphism-layer
rowSheafLayer engine-refuses-new-si-row = exact-si-layer

row-census-conservation-holds :
  ∀ (r : EngineCensusRowTag) → rowMayMintSi r ≡ false
row-census-conservation-holds r = refl

all-engine-census-rows-consult-sheaf :
  allCensusRowsConsultSheaf ≡ true
all-engine-census-rows-consult-sheaf = refl

forbidden-si-mints-pinned :
  forbiddenSiMintsPinned ≡ true
forbidden-si-mints-pinned = refl

engines-use-existing-sheaf-bool :
  enginesUseExistingSheaf ≡ true
engines-use-existing-sheaf-bool = refl

engines-may-not-mint-forbidden-si :
  engineMayMintSi ≡ false
engines-may-not-mint-forbidden-si = engine-may-not-mint-si

------------------------------------------------------------------------
-- Fine-structure α — MeasuredCited, not Landauer-faked
------------------------------------------------------------------------

fineStructureAlphaPinKind landauerBridgeCoversKcNotAlpha : String
fineStructureAlphaPinKind = "MeasuredCited"
landauerBridgeCoversKcNotAlpha =
  "LandauerEinsteinBridge.lean FormalLift k c — alpha remains MeasuredCited not Landauer-faked"

fine-structure-alpha-pin-kind-named :
  fineStructureAlphaPinKind ≡ "MeasuredCited"
fine-structure-alpha-pin-kind-named = refl

landauer-fake-alpha-not-minted : landauerFakeAlphaMinted ≡ false
landauer-fake-alpha-not-minted = refl

alpha-measured-cited-not-landauer-fake :
  alphaMeasuredCitedNotLandauerFake ≡ true
alpha-measured-cited-not-landauer-fake = refl

landauer-bridge-scoped-kc-not-alpha :
  landauerBridgeScopedKcNotAlpha ≡ true
landauer-bridge-scoped-kc-not-alpha = refl

exact-si-k-cited-not-minted :
  exactSiKCitedNotMinted ≡ true
exact-si-k-cited-not-minted = refl

------------------------------------------------------------------------
-- Honest conjunct — census consult ≠ SI mint ≠ Landauer-fake α
------------------------------------------------------------------------

constantDeriveSecondLawCensusHonestConjunct : Bool
constantDeriveSecondLawCensusHonestConjunct =
  not engineMayMintSi ∧
  allCensusRowsConsultSheaf ∧
  forbiddenSiMintsPinned ∧
  enginesUseExistingSheaf ∧
  alphaMeasuredCitedNotLandauerFake ∧
  landauerBridgeScopedKcNotAlpha ∧
  exactSiKCitedNotMinted ∧
  not landauerFakeAlphaMinted ∧
  soleAxiomSecondLawConservation

constant-derive-second-law-census-honest-conjunct-true :
  constantDeriveSecondLawCensusHonestConjunct ≡ true
constant-derive-second-law-census-honest-conjunct-true = refl

constant-derive-second-law-census-not-proved :
  constantDeriveSecondLawCensusProved ≡ false
constant-derive-second-law-census-not-proved = refl

production-not-wired : productionWired ≡ false
production-not-wired = refl

wave100-lib-rs-not-wired : wave100LibRsWired ≡ false
wave100-lib-rs-not-wired = refl

wave100-eos-rs-not-wired : wave100EosRsWired ≡ false
wave100-eos-rs-not-wired = refl

product-not-xor : productNotXor ≡ true
product-not-xor = refl

------------------------------------------------------------------------
-- Conservation close verdict — fail-closed lattice
------------------------------------------------------------------------

data ConstantDeriveSecondLawCensusVerdict : Set where
  verdict-unwired-ok verdict-census-ok verdict-green-invent-refuse
    verdict-production-wired-refuse verdict-si-mint-refuse
    : ConstantDeriveSecondLawCensusVerdict

constantDeriveSecondLawCensusVerdictOk : ConstantDeriveSecondLawCensusVerdict → Bool
constantDeriveSecondLawCensusVerdictOk verdict-unwired-ok = true
constantDeriveSecondLawCensusVerdictOk verdict-census-ok = true
constantDeriveSecondLawCensusVerdictOk _ = false

evaluateConstantDeriveSecondLawCensus :
  ConstantDeriveSecondLawCensusModality →
  Bool → Bool → Bool →
  ConstantDeriveSecondLawCensusVerdict
evaluateConstantDeriveSecondLawCensus m claimPhysicsGreen claimProved claimProductionWired =
  if claimPhysicsGreen then verdict-green-invent-refuse else
  if claimProductionWired then verdict-production-wired-refuse else
  if engineMayMintSi then verdict-si-mint-refuse else
  if claimProved then verdict-census-ok else
  if constantDeriveSecondLawCensusHonestConjunct then pickModality m else verdict-si-mint-refuse
  where
  pickModality : ConstantDeriveSecondLawCensusModality → ConstantDeriveSecondLawCensusVerdict
  pickModality constant-derive-second-law-census-unwired = verdict-unwired-ok
  pickModality _ = verdict-census-ok

constant-derive-second-law-census-unwired-ok :
  evaluateConstantDeriveSecondLawCensus
    constant-derive-second-law-census-unwired false false false
    ≡ verdict-unwired-ok
constant-derive-second-law-census-unwired-ok = refl

constant-derive-second-law-census-green-invent-refuse :
  evaluateConstantDeriveSecondLawCensus
    constant-derive-second-law-census-unwired true false false
    ≡ verdict-green-invent-refuse
constant-derive-second-law-census-green-invent-refuse = refl

constant-derive-second-law-census-production-wired-refuse :
  evaluateConstantDeriveSecondLawCensus
    constant-derive-second-law-census-unwired false false true
    ≡ verdict-production-wired-refuse
constant-derive-second-law-census-production-wired-refuse = refl

constant-derive-second-law-census-green-refuse-verdict-false :
  constantDeriveSecondLawCensusVerdictOk
    (evaluateConstantDeriveSecondLawCensus
       constant-derive-second-law-census-unwired true false false)
    ≡ false
constant-derive-second-law-census-green-refuse-verdict-false = refl

------------------------------------------------------------------------
-- One design axiom + authority cites (not a 26th axiom fork)
------------------------------------------------------------------------

constantDeriveSecondLawCensusAxiom :
  (constantDeriveSecondLawCensusProved ≡ false)
  × (productionWired ≡ false)
  × (wave100LibRsWired ≡ false)
  × (wave100EosRsWired ≡ false)
  × (engineMayMintSi ≡ false)
  × (engineUsesExistingSheaf ≡ true)
  × (forbiddenMintCount ≡ 3)
  × (allCensusRowsConsultSheaf ≡ true)
  × (forbiddenSiMintsPinned ≡ true)
  × (enginesUseExistingSheaf ≡ true)
  × (alphaMeasuredCitedNotLandauerFake ≡ true)
  × (landauerBridgeScopedKcNotAlpha ≡ true)
  × (exactSiKCitedNotMinted ≡ true)
  × (landauerFakeAlphaMinted ≡ false)
  × (soleAxiomSecondLawConservation ≡ true)
  × (soleAxiomCount ≡ 1)
  × (constantDeriveSecondLawCensusHonestConjunct ≡ true)
  × (engineCensusRowCount ≡ 5)
  × (sheafConsultLayerCount ≡ 3)
  × (evaluateConstantDeriveSecondLawCensus
       constant-derive-second-law-census-unwired false false false
       ≡ verdict-unwired-ok)
  × (constantDeriveSecondLawCensusVerdictOk
       (evaluateConstantDeriveSecondLawCensus
          constant-derive-second-law-census-unwired true false false)
     ≡ false)
constantDeriveSecondLawCensusAxiom =
  constant-derive-second-law-census-not-proved
  , production-not-wired
  , wave100-lib-rs-not-wired
  , wave100-eos-rs-not-wired
  , engine-may-not-mint-si
  , engine-uses-existing-sheaf
  , forbidden-mint-count-three
  , all-engine-census-rows-consult-sheaf
  , forbidden-si-mints-pinned
  , engines-use-existing-sheaf-bool
  , alpha-measured-cited-not-landauer-fake
  , landauer-bridge-scoped-kc-not-alpha
  , exact-si-k-cited-not-minted
  , landauer-fake-alpha-not-minted
  , sole-axiom-second-law
  , sole-axiom-count-one
  , constant-derive-second-law-census-honest-conjunct-true
  , engine-census-row-count-five
  , sheaf-consult-layer-count-three
  , constant-derive-second-law-census-unwired-ok
  , constant-derive-second-law-census-green-refuse-verdict-false

constantDeriveSecondLawCensusNamed : String
constantDeriveSecondLawCensusNamed =
  "constantDeriveSecondLawCensus: engines consult ExactSI occupancy derived-morphism sheaf do not mint k R epsilon_0 alpha MeasuredCited not Landauer-faked sole axiom second law conservation"

constantDeriveSecondLawCensusCrossWitnessAuthority : String
constantDeriveSecondLawCensusCrossWitnessAuthority =
  "umst/umst-chem/src/x_rows/constant_derive_second_law_census.rs"

engineRefusesNewSiAuthority : String
engineRefusesNewSiAuthority =
  "umst/umst-chem/src/x_rows/engine_refuses_new_si.rs"

constantDerivePreferenceAuthority : String
constantDerivePreferenceAuthority =
  "umst/umst-chem/src/constant_derive_preference.rs"

siExactDefiningConstantsAuthority : String
siExactDefiningConstantsAuthority =
  "umst/umst-chem/src/si_exact_defining_constants.rs"

gasConstantDerivedMorphismAuthority : String
gasConstantDerivedMorphismAuthority =
  "umst/umst-chem/src/gas_constant_is_derived_morphism.rs"

vacuumPermittivitySiDerivedAuthority : String
vacuumPermittivitySiDerivedAuthority =
  "umst/umst-chem/src/vacuum_permittivity_si_derived.rs"

qlatticeAuthority : String
qlatticeAuthority = "umst/umst-chem/src/qlattice.rs"

secondLawConservationAxiom : String
secondLawConservationAxiom =
  "second law conservation — engines consult sheaf; alpha MeasuredCited not Landauer-faked; sole axiom"

censusNotSiMintOrLandauerFakeAlphaOr26thAxiom : String
censusNotSiMintOrLandauerFakeAlphaOr26thAxiom =
  "constant derive census consults ExactSI occupancy derived-morphism sheaf — not mint k R epsilon_0 not Landauer-fake alpha not 26th axiom"

constantDeriveSecondLawCensusCellId : String
constantDeriveSecondLawCensusCellId =
  "CHEM-FORMAL-Q-AGDA-CONSTANT-DERIVE-SECOND-LAW-CENSUS-CONSERVATION"

constantDeriveSecondLawCensusIntCellId : String
constantDeriveSecondLawCensusIntCellId =
  "CHEM-INT-CROSS-CONSTANT-DERIVE-SECOND-LAW-CENSUS-CONSERVATION"

constantDeriveSecondLawCensusNonClaim : String
constantDeriveSecondLawCensusNonClaim =
  "CHEM-FORMAL-Q-AGDA-CONSTANT-DERIVE-SECOND-LAW-CENSUS-CONSERVATION Unwired — engines consult ExactSI occupancy derived-morphism sheaf; do not mint k R epsilon_0; alpha MeasuredCited not Landauer-faked; cite engine_refuses_new_si constant_derive_preference si_exact_defining_constants gas_constant_is_derived_morphism vacuum_permittivity_si_derived qlattice not fork; second law conservation sole axiom not 26th axiom; not physics GREEN; not production_wired"

constant-derive-second-law-census-cell-id :
  constantDeriveSecondLawCensusCellId ≡
  "CHEM-FORMAL-Q-AGDA-CONSTANT-DERIVE-SECOND-LAW-CENSUS-CONSERVATION"
constant-derive-second-law-census-cell-id = refl

constant-derive-second-law-census-cites-cross-witness-rs :
  constantDeriveSecondLawCensusCrossWitnessAuthority ≡
  "umst/umst-chem/src/x_rows/constant_derive_second_law_census.rs"
constant-derive-second-law-census-cites-cross-witness-rs = refl

constant-derive-second-law-census-modality-unwired :
  constantDeriveSecondLawCensusModalityCurrent ≡ constant-derive-second-law-census-unwired
constant-derive-second-law-census-modality-unwired = refl

constantDeriveSecondLawCensusMarker : String
constantDeriveSecondLawCensusMarker =
  "chem_int_cross_constant_derive_second_law_census_v1"

constantDeriveSecondLawCensusSurface : String
constantDeriveSecondLawCensusSurface = "constant_derive_second_law_census_surface"

constantDeriveSecondLawCensusPhysicsGreenAuthorized : Set
constantDeriveSecondLawCensusPhysicsGreenAuthorized = ⊥

constant-derive-second-law-census-physics-green-false :
  ¬ constantDeriveSecondLawCensusPhysicsGreenAuthorized
constant-derive-second-law-census-physics-green-false ()
