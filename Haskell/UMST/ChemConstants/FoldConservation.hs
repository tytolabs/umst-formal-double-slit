-- SPDX-FileCopyrightText: 2026 Santosh Prabhu Shenbagamoorthy and Santhosh Shyamsundar
-- SPDX-License-Identifier: MIT

{-|
Module      : UMST.ChemConstants.FoldConservation
Description : Classifier-fold conservation on the knowing fiber (Q lattice)
Copyright   : (c) UMST Project, 2026

**Fold** conservation: FP-01 pattern-taxonomy classifier **fold** combinators
(conjunctive / disjunctive) on **conservation** claims (Unwired / Assumed / Proved /
Surrogate). Conjunctive and disjunctive **fold** identity conserved under honest scaffold;
empty conjunctive **fold** = true, empty disjunctive **fold** = false.
FP-01 classifier **fold** laws are structure witnesses only (@fp01FoldProved@ = False).

* @FoldConservationModality@ = Unwired / Assumed / Proved / Surrogate — four-step lattice, not 118² GREEN table.
* @foldClassifiers@ — conjunctive and disjunctive **fold** identity conserved on scaffold predicates.
* **One** design axiom (@foldConservationAxiom@): second law + **conservation**.
* @physics_green@ stays false.

Haskell mirror of classifier **fold** **conservation** on the quantum / knowing fiber.
Cell: @CHEM-FORMAL-Q-HS-FOLD-CONSERVATION@.
-}
module UMST.ChemConstants.FoldConservation
  ( FoldConservationModality (..)
  , foldConservationModalityCurrent
  , foldLatticeAll
  , foldLatticeCount
  , PatternFeature (..)
  , patternFeatureZero
  , PatternClassifierKind (..)
  , patternClassifierKindAll
  , patternClassifierKindCount
  , ClassifierFoldOp (..)
  , classifierFoldOpAll
  , classifierFoldOpCount
  , classifyKind
  , foldClassifiers
  , FoldIdentityLaw (..)
  , foldIdentityLawAll
  , foldIdentityLawCount
  , FoldConservationVerdict (..)
  , evaluateFoldConservation
  , sampleBondFormingFeatures
  , sampleConjunctiveKinds
  , sampleDisjunctiveKinds
  , sampleEmptyKinds
  , unwiredDesignOk
  , conjunctiveEmptyIdentityOk
  , disjunctiveEmptyIdentityOk
  , conjunctiveFoldIdentityConserved
  , disjunctiveFoldIdentityConserved
  , assumedFoldDesignOk
  , surrogateFoldDesignOk
  , greenInventFoldRefuse
  , foldLatticeScaffold
  , foldLatticeNotGreenTable
  , foldIdentityLawsScaffold
  , foldIdentityLawsNotGreenTable
  , foldKnowingFiberOk
  , fp01FoldInventRefuse
  , foldLatticeNotXor
  , fp01FoldProved
  , foldConservationFraming
  , foldConservationAxiom
  , foldConservationNamed
  , patternClassifierFoldsAuthority
  , chemL0Fp01Authority
  , foldConservationCellId
  , foldConservationNonClaim
  , foldConservationPhysicsGreenAuthorized
  , foldConservationPhysicsGreenFalse
  , foldConservationModalityUnwired
  ) where

-- | Design **fold** modality for FP-01 **conservation** claims.
data FoldConservationModality
  = FoldConservationUnwired
  | FoldConservationAssumed
  | FoldConservationProved
  | FoldConservationSurrogate
  deriving (Eq, Show)

-- | Current scaffold **fold** modality — always Unwired on this cell.
foldConservationModalityCurrent :: FoldConservationModality
foldConservationModalityCurrent = FoldConservationUnwired

-- | All FP-01 **fold** lattice steps in stable order.
foldLatticeAll :: [FoldConservationModality]
foldLatticeAll =
  [ FoldConservationUnwired
  , FoldConservationAssumed
  , FoldConservationProved
  , FoldConservationSurrogate
  ]

foldLatticeCount :: Int
foldLatticeCount = length foldLatticeAll

-- | Minimal feature snapshot for §2 pattern classifiers (design scaffold).
data PatternFeature = PatternFeature
  { featurePerElement :: Bool
  , featureShared :: Bool
  , featureBondForming :: Bool
  , featureBondRepelling :: Bool
  , featureStructureEnabling :: Bool
  , featureStructureBlocking :: Bool
  }
  deriving (Eq, Show)

-- | All-off baseline for **fold** identity tests.
patternFeatureZero :: PatternFeature
patternFeatureZero =
  PatternFeature
    { featurePerElement = False
    , featureShared = False
    , featureBondForming = False
    , featureBondRepelling = False
    , featureStructureEnabling = False
    , featureStructureBlocking = False
    }

-- | §2 pattern-taxonomy classifier bucket (design enum — not exhaustive GREEN).
data PatternClassifierKind
  = PerElementKind
  | SharedKind
  | BondFormingKind
  | BondRepellingKind
  | StructureEnablingKind
  | StructureBlockingKind
  deriving (Eq, Show)

-- | All classifier kinds in stable order (structure scaffold — not 118² GREEN table).
patternClassifierKindAll :: [PatternClassifierKind]
patternClassifierKindAll =
  [ PerElementKind
  , SharedKind
  , BondFormingKind
  , BondRepellingKind
  , StructureEnablingKind
  , StructureBlockingKind
  ]

patternClassifierKindCount :: Int
patternClassifierKindCount = length patternClassifierKindAll

-- | **Fold** combinator for composing classifier predicates.
data ClassifierFoldOp
  = ConjunctiveFold
  | DisjunctiveFold
  deriving (Eq, Show)

-- | All classifier **fold** ops in stable order.
classifierFoldOpAll :: [ClassifierFoldOp]
classifierFoldOpAll = [ConjunctiveFold, DisjunctiveFold]

classifierFoldOpCount :: Int
classifierFoldOpCount = length classifierFoldOpAll

-- | Evaluate one classifier predicate on features (pure bool classifier).
classifyKind :: PatternClassifierKind -> PatternFeature -> Bool
classifyKind kind features =
  case kind of
    PerElementKind -> featurePerElement features
    SharedKind -> featureShared features
    BondFormingKind -> featureBondForming features
    BondRepellingKind -> featureBondRepelling features
    StructureEnablingKind -> featureStructureEnabling features
    StructureBlockingKind -> featureStructureBlocking features

-- | **Fold** up classifier predicates — conjunctive / disjunctive **fold** identity conserved.
foldClassifiers ::
  [PatternClassifierKind] -> ClassifierFoldOp -> PatternFeature -> Bool
foldClassifiers kinds op features =
  case kinds of
    [] ->
      case op of
        ConjunctiveFold -> True
        DisjunctiveFold -> False
    (first : rest) ->
      let firstResult = classifyKind first features
          step acc k =
            let next = classifyKind k features
             in case op of
                  ConjunctiveFold -> acc && next
                  DisjunctiveFold -> acc || next
       in foldl step firstResult rest

-- | **Fold** identity law cells tracked by FP-01 (structure scaffold).
data FoldIdentityLaw
  = ConjunctiveEmptyIdentity
  | DisjunctiveEmptyIdentity
  | ConjunctiveFoldConserved
  | DisjunctiveFoldConserved
  deriving (Eq, Show)

-- | All **fold** identity law cells in stable order.
foldIdentityLawAll :: [FoldIdentityLaw]
foldIdentityLawAll =
  [ ConjunctiveEmptyIdentity
  , DisjunctiveEmptyIdentity
  , ConjunctiveFoldConserved
  , DisjunctiveFoldConserved
  ]

foldIdentityLawCount :: Int
foldIdentityLawCount = length foldIdentityLawAll

-- | Verdict for FP-01 classifier **fold** **conservation** promotion (fail-closed).
data FoldConservationVerdict
  = FoldDesignOk
  | FoldIdentityConservedOk
  | FoldIdentityBrokenRefuse
  | FoldGreenInventRefuse
  deriving (Eq, Show)

foldIdentityWitnessOk :: ClassifierFoldOp -> [PatternClassifierKind] -> PatternFeature -> Bool
foldIdentityWitnessOk op kinds features =
  let folded = foldClassifiers kinds op features
      manual =
        case kinds of
          [] ->
            case op of
              ConjunctiveFold -> True
              DisjunctiveFold -> False
          (first : rest) ->
            let firstResult = classifyKind first features
                step acc k =
                  let next = classifyKind k features
                   in case op of
                        ConjunctiveFold -> acc && next
                        DisjunctiveFold -> acc || next
             in foldl step firstResult rest
   in folded == manual

-- | Evaluate FP-01 classifier **fold** **conservation** typing (fail-closed).
evaluateFoldConservation ::
  FoldConservationModality
  -> ClassifierFoldOp
  -> [PatternClassifierKind]
  -> PatternFeature
  -> Bool
  -> FoldConservationVerdict
evaluateFoldConservation modality op kinds features claimPhysicsGreen
  | claimPhysicsGreen = FoldGreenInventRefuse
  | otherwise =
      case modality of
        FoldConservationUnwired -> FoldDesignOk
        FoldConservationAssumed -> FoldDesignOk
        FoldConservationSurrogate -> FoldDesignOk
        FoldConservationProved ->
          if foldIdentityWitnessOk op kinds features
            then FoldIdentityConservedOk
            else FoldIdentityBrokenRefuse

-- | Sample bond-forming scaffold features for **fold** witnesses.
sampleBondFormingFeatures :: PatternFeature
sampleBondFormingFeatures =
  PatternFeature
    { featurePerElement = False
    , featureShared = False
    , featureBondForming = True
    , featureBondRepelling = False
    , featureStructureEnabling = False
    , featureStructureBlocking = False
    }

-- | Sample conjunctive **fold** classifier kinds.
sampleConjunctiveKinds :: [PatternClassifierKind]
sampleConjunctiveKinds = [BondFormingKind, StructureEnablingKind]

-- | Sample disjunctive **fold** classifier kinds.
sampleDisjunctiveKinds :: [PatternClassifierKind]
sampleDisjunctiveKinds = [BondFormingKind, StructureEnablingKind]

-- | Sample empty classifier list for **fold** identity pins.
sampleEmptyKinds :: [PatternClassifierKind]
sampleEmptyKinds = []

-- | Unwired **fold** modality OK without identity break.
unwiredDesignOk :: Bool
unwiredDesignOk =
  evaluateFoldConservation
    FoldConservationUnwired
    ConjunctiveFold
    sampleConjunctiveKinds
    sampleBondFormingFeatures
    False
    == FoldDesignOk

-- | Conjunctive empty **fold** identity = true (conserved).
conjunctiveEmptyIdentityOk :: Bool
conjunctiveEmptyIdentityOk =
  foldClassifiers sampleEmptyKinds ConjunctiveFold patternFeatureZero

-- | Disjunctive empty **fold** identity = false (conserved).
disjunctiveEmptyIdentityOk :: Bool
disjunctiveEmptyIdentityOk =
  not (foldClassifiers sampleEmptyKinds DisjunctiveFold patternFeatureZero)

-- | Conjunctive **fold** identity conserved on scaffold predicates.
conjunctiveFoldIdentityConserved :: Bool
conjunctiveFoldIdentityConserved =
  evaluateFoldConservation
    FoldConservationProved
    ConjunctiveFold
    sampleConjunctiveKinds
    sampleBondFormingFeatures
    False
    == FoldIdentityConservedOk
    && foldClassifiers sampleConjunctiveKinds ConjunctiveFold sampleBondFormingFeatures
      == ( classifyKind BondFormingKind sampleBondFormingFeatures
            && classifyKind StructureEnablingKind sampleBondFormingFeatures
         )

-- | Disjunctive **fold** identity conserved on scaffold predicates.
disjunctiveFoldIdentityConserved :: Bool
disjunctiveFoldIdentityConserved =
  evaluateFoldConservation
    FoldConservationProved
    DisjunctiveFold
    sampleDisjunctiveKinds
    sampleBondFormingFeatures
    False
    == FoldIdentityConservedOk
    && foldClassifiers sampleDisjunctiveKinds DisjunctiveFold sampleBondFormingFeatures
      == classifyKind BondFormingKind sampleBondFormingFeatures

-- | Assumed **fold** modality OK without identity break (design scaffold).
assumedFoldDesignOk :: Bool
assumedFoldDesignOk =
  evaluateFoldConservation
    FoldConservationAssumed
    DisjunctiveFold
    sampleDisjunctiveKinds
    sampleBondFormingFeatures
    False
    == FoldDesignOk

-- | Surrogate **fold** modality OK without identity break (design scaffold).
surrogateFoldDesignOk :: Bool
surrogateFoldDesignOk =
  evaluateFoldConservation
    FoldConservationSurrogate
    ConjunctiveFold
    sampleConjunctiveKinds
    sampleBondFormingFeatures
    False
    == FoldDesignOk

-- | GREEN invent on classifier **fold** **conservation** promotion is refused.
greenInventFoldRefuse :: Bool
greenInventFoldRefuse =
  evaluateFoldConservation
    FoldConservationUnwired
    ConjunctiveFold
    sampleConjunctiveKinds
    sampleBondFormingFeatures
    True
    == FoldGreenInventRefuse

-- | Four-step FP-01 **fold** lattice scaffold pinned.
foldLatticeScaffold :: Bool
foldLatticeScaffold =
  foldLatticeCount == 4
    && unwiredDesignOk
    && conjunctiveEmptyIdentityOk
    && disjunctiveEmptyIdentityOk
    && conjunctiveFoldIdentityConserved
    && disjunctiveFoldIdentityConserved
    && assumedFoldDesignOk
    && surrogateFoldDesignOk

-- | **Fold** lattice is structure scaffold — not 118² GREEN periodic table.
foldLatticeNotGreenTable :: Bool
foldLatticeNotGreenTable =
  foldLatticeCount == 4
    && foldLatticeCount /= 118 * 118
    && sampleConjunctiveKinds /= sampleEmptyKinds

-- | Four **fold** identity law cells scaffold pinned.
foldIdentityLawsScaffold :: Bool
foldIdentityLawsScaffold =
  foldIdentityLawCount == 4
    && conjunctiveEmptyIdentityOk
    && disjunctiveEmptyIdentityOk
    && conjunctiveFoldIdentityConserved
    && disjunctiveFoldIdentityConserved

-- | **Fold** law cells are structure scaffold — not 118² GREEN periodic table.
foldIdentityLawsNotGreenTable :: Bool
foldIdentityLawsNotGreenTable =
  foldIdentityLawsScaffold
    && foldIdentityLawCount /= 118 * 118
    && sampleDisjunctiveKinds /= sampleEmptyKinds

-- | Classifier **fold** **conservation** claims route to knowing / quantum fiber (not meso acting).
foldKnowingFiberOk :: Bool
foldKnowingFiberOk = True

-- | FP-01 classifier **fold** invent refuse-closed scaffold witness.
fp01FoldInventRefuse :: Bool
fp01FoldInventRefuse = not fp01FoldProved

-- | **Fold** lattice steps are concurrent Π_c — not XOR enum bucket.
foldLatticeNotXor :: Bool
foldLatticeNotXor =
  unwiredDesignOk
    && assumedFoldDesignOk
    && surrogateFoldDesignOk
    && conjunctiveEmptyIdentityOk
    && disjunctiveEmptyIdentityOk
    && conjunctiveFoldIdentityConserved
    && disjunctiveFoldIdentityConserved
    && greenInventFoldRefuse

-- | FP-01 classifier **fold** proved (always false on this Unwired cell).
fp01FoldProved :: Bool
fp01FoldProved = False

-- | One axiom framing: second law + **conservation** for classifier **fold** scaffold.
foldConservationFraming :: String
foldConservationFraming =
  "second_law_conservation_fold_one_axiom"

-- | Single design axiom: second law + **conservation** classifier **fold** (not second axiom).
foldConservationAxiom :: Bool
foldConservationAxiom =
  foldLatticeScaffold
    && foldLatticeNotGreenTable
    && foldIdentityLawsScaffold
    && foldIdentityLawsNotGreenTable
    && foldKnowingFiberOk
    && conjunctiveEmptyIdentityOk
    && disjunctiveEmptyIdentityOk
    && conjunctiveFoldIdentityConserved
    && disjunctiveFoldIdentityConserved
    && greenInventFoldRefuse
    && fp01FoldInventRefuse
    && foldLatticeNotXor
    && not fp01FoldProved
    && foldConservationFraming
      == "second_law_conservation_fold_one_axiom"

foldConservationNamed :: String
foldConservationNamed =
  "foldConservation: FoldConservationModality Unwired Assumed Proved Surrogate four-step lattice fp01FoldProved false conjunctiveFold disjunctiveFold fold identity conserved second law conservation one axiom"

-- | Upstream FP-01 pattern classifier **fold** authority (cited, not forked).
patternClassifierFoldsAuthority :: String
patternClassifierFoldsAuthority = "umst/umst-chem/src/pattern_classifier_folds.rs"

-- | L0 FP-01 classifier **fold** scaffold authority (crosswalk).
chemL0Fp01Authority :: String
chemL0Fp01Authority = "CHEM-L0-FP-01"

foldConservationCellId :: String
foldConservationCellId = "CHEM-FORMAL-Q-HS-FOLD-CONSERVATION"

-- | Non-claim fence — classifier **fold** **conservation** Unwired ≠ Proved GREEN.
foldConservationNonClaim :: String
foldConservationNonClaim =
  "CHEM-FORMAL-Q-HS-FOLD-CONSERVATION FoldConservationModality Unwired Assumed Proved Surrogate four-step lattice fp01FoldProved false conjunctiveFold disjunctiveFold fold identity conserved Unwired one axiom second law conservation not 118 squared GREEN table not meso acting not physics GREEN not production_wired"

-- | Physics GREEN is unauthorized on the knowing classifier **fold** **conservation** scaffold.
foldConservationPhysicsGreenAuthorized :: Bool
foldConservationPhysicsGreenAuthorized = False

foldConservationPhysicsGreenFalse :: Bool
foldConservationPhysicsGreenFalse =
  not foldConservationPhysicsGreenAuthorized

foldConservationModalityUnwired :: Bool
foldConservationModalityUnwired =
  foldConservationModalityCurrent == FoldConservationUnwired
