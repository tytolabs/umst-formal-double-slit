-- SPDX-FileCopyrightText: 2026 Santosh Prabhu Shenbagamoorthy and Santhosh Shyamsundar
-- SPDX-License-Identifier: MIT

{-|
Module      : UMST.ChemConstants.AdjunctionCostLandauer
Description : CAT-03 adjunction-cost Landauer on the knowing fiber (Q lattice)
Copyright   : (c) UMST Project, 2026

CAT-03 adjunction-cost Landauer: impure⇄pure adjunction; pureward refine cost
non-negative; free purification forbidden when contaminants remain. Forgetful view
≠ paid pureward purification (Landauer scaffold).

* @purewardCost@ ≥ 0; @freePurificationAdmitted@ = False when contaminants.
* @purificationImpliesPositiveCost@ when contaminants present.
* **One** design axiom (@adjunctionCostLandauerAxiom@): second law + conservation;
  Landauer cost is **not** a second axiom.
* @physics_green@ stays false.

Haskell mirror of Coq @ChemConstants/AdjunctionCostLandauer.v@ on the quantum / knowing fiber.
Cell: @CHEM-FORMAL-Q-HS-ADJUNCTION-COST-LANDAUER@.
-}
module UMST.ChemConstants.AdjunctionCostLandauer
  ( AdjunctionCostLandauerModality (..)
  , adjunctionCostLandauerModalityCurrent
  , purewardCost
  , contaminantsPresent
  , minPurewardCost
  , purewardCostNonneg
  , purewardCostPositive
  , minPurewardCostNonneg
  , minPurewardCostZeroWhenPure
  , freePurificationAdmitted
  , attemptZeroCostPurification
  , freePurificationAdmittedFalseWhenImpure
  , freePurificationForbidden
  , freePurificationAdmittedTrueWhenPure
  , purificationImpliesPositiveCost
  , paidPurewardCostAdmitsPurification
  , adjunctionCostPaidPurewardAdmits
  , impurePureAdjunctionAuthority
  , chemL0Cat03Authority
  , refineCostAuthority
  , adjunctionSecondLawConservationFraming
  , adjunctionNotSecondLandauerAxiom
  , adjunctionCostLandauerAxiom
  , adjunctionCostLandauerNamed
  , adjunctionCostLandauerCellId
  , adjunctionCostLandauerNonClaim
  , adjunctionCostLandauerPhysicsGreenAuthorized
  , adjunctionCostLandauerPhysicsGreenFalse
  , adjunctionCostLandauerModalityUnwired
  ) where

-- | Design modality for CAT-03 adjunction-cost Landauer claims (TYPE-03 preview).
data AdjunctionCostLandauerModality
  = AdjunctionCostLandauerUnwired
  | AdjunctionCostLandauerAssumed
  | AdjunctionCostLandauerProved
  | AdjunctionCostLandauerSurrogate
  deriving (Eq, Show)

-- | Current scaffold modality — always Unwired on this cell.
adjunctionCostLandauerModalityCurrent :: AdjunctionCostLandauerModality
adjunctionCostLandauerModalityCurrent = AdjunctionCostLandauerUnwired

-- | Pureward refine cost pin (knowing fiber — Unwired).
purewardCost :: Int
purewardCost = 1

-- | Contaminants remain on the knowing scaffold (design witness).
contaminantsPresent :: Bool
contaminantsPresent = True

-- | Minimum pureward cost given contaminant presence.
minPurewardCost :: Bool -> Int
minPurewardCost hasContaminants =
  if hasContaminants then purewardCost else 0

purewardCostNonneg :: Bool
purewardCostNonneg = purewardCost >= 0

purewardCostPositive :: Bool
purewardCostPositive = purewardCost > 0

minPurewardCostNonneg :: Bool -> Bool
minPurewardCostNonneg hasContaminants = minPurewardCost hasContaminants >= 0

minPurewardCostZeroWhenPure :: Bool
minPurewardCostZeroWhenPure = minPurewardCost False == 0

-- | Free purification admitted only when paid cost meets minimum (or no contaminants).
freePurificationAdmitted :: Int -> Int -> Bool -> Bool
freePurificationAdmitted paidCost minCost hasContaminants =
  if hasContaminants then minCost <= paidCost else True

attemptZeroCostPurification :: Bool -> Bool
attemptZeroCostPurification hasContaminants =
  freePurificationAdmitted 0 (minPurewardCost hasContaminants) hasContaminants

-- | Zero-cost purification is **not** admitted when contaminants remain.
freePurificationAdmittedFalseWhenImpure :: Bool
freePurificationAdmittedFalseWhenImpure =
  not (attemptZeroCostPurification True)

freePurificationForbidden :: Bool
freePurificationForbidden = attemptZeroCostPurification True == False

freePurificationAdmittedTrueWhenPure :: Bool
freePurificationAdmittedTrueWhenPure = attemptZeroCostPurification False

-- | Purification with contaminants implies positive minimum cost.
purificationImpliesPositiveCost :: Bool
purificationImpliesPositiveCost = minPurewardCost True > 0

paidPurewardCostAdmitsPurification :: Bool
paidPurewardCostAdmitsPurification =
  freePurificationAdmitted purewardCost (minPurewardCost True) True

adjunctionCostPaidPurewardAdmits :: Bool
adjunctionCostPaidPurewardAdmits =
  paidPurewardCostAdmitsPurification && freePurificationForbidden

-- | Cited upstream authority strings (views only — adjunction cost).
impurePureAdjunctionAuthority :: String
impurePureAdjunctionAuthority = "umst/umst-chem/src/impure_pure_adjunction.rs"

chemL0Cat03Authority :: String
chemL0Cat03Authority = "CHEM-L0-CAT-03"

refineCostAuthority :: String
refineCostAuthority = "umst/umst-formal/Lean/Chem/RefineCost.lean"

-- | One axiom framing: second law + conservation; Landauer cost is not a second axiom.
adjunctionSecondLawConservationFraming :: String
adjunctionSecondLawConservationFraming =
  "second_law_conservation_adjunction_cost_one_axiom_landauer_not_second_axiom"

adjunctionNotSecondLandauerAxiom :: Bool
adjunctionNotSecondLandauerAxiom =
  adjunctionSecondLawConservationFraming /= "landauer_second_axiom"

-- | Single design axiom: second law + conservation adjunction-cost (not second Landauer axiom).
adjunctionCostLandauerAxiom :: Bool
adjunctionCostLandauerAxiom =
  purewardCostNonneg
    && purificationImpliesPositiveCost
    && freePurificationForbidden
    && adjunctionCostPaidPurewardAdmits
    && adjunctionNotSecondLandauerAxiom

adjunctionCostLandauerNamed :: String
adjunctionCostLandauerNamed =
  "adjunctionCostLandauer: CAT-03 impure⇄pure adjunction pureward cost non-negative; free purification forbidden when contaminants; second law + conservation one axiom Landauer cost not second axiom"

adjunctionCostLandauerCellId :: String
adjunctionCostLandauerCellId = "CHEM-FORMAL-Q-HS-ADJUNCTION-COST-LANDAUER"

-- | Non-claim fence — adjunction-cost Landauer Unwired ≠ Proved GREEN.
adjunctionCostLandauerNonClaim :: String
adjunctionCostLandauerNonClaim =
  "CHEM-FORMAL-Q-HS-ADJUNCTION-COST-LANDAUER CAT-03 adjunction-cost Landauer purewardCost mandatory freePurificationForbidden contaminantsPresent Unwired one axiom second law conservation Landauer cost not second axiom not GREEN DFT not physics GREEN not production_wired"

-- | Physics GREEN is unauthorized on the knowing adjunction-cost Landauer scaffold.
adjunctionCostLandauerPhysicsGreenAuthorized :: Bool
adjunctionCostLandauerPhysicsGreenAuthorized = False

adjunctionCostLandauerPhysicsGreenFalse :: Bool
adjunctionCostLandauerPhysicsGreenFalse =
  not adjunctionCostLandauerPhysicsGreenAuthorized

adjunctionCostLandauerModalityUnwired :: Bool
adjunctionCostLandauerModalityUnwired =
  adjunctionCostLandauerModalityCurrent == AdjunctionCostLandauerUnwired
