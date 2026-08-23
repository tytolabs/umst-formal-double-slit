-- SPDX-FileCopyrightText: 2026 Santosh Prabhu Shenbagamoorthy and Santhosh Shyamsundar
-- SPDX-License-Identifier: MIT

{-|
Module      : UMST.ChemConstants.PullbackConservation
Description : Pullback conservation on the knowing fiber (Q lattice)
Copyright   : (c) UMST Project, 2026

Pullback conservation: @SubstructureDiagram@ pullback/pushout scaffold for shared ore
substructure — limit/colimit legs, overlap identity conserved. Universal properties and
CAT-02 pullback are structure witnesses only (@universalPropertiesProved@ = False,
@cat02PullbackProved@ = False).

* @SubstructureDiagram@ = kind/overlap/leftLeg/rightLeg — diagram carrier, not @Vec@ list.
* @pullbackPushoutScaffold@ — pullback + pushout legs distinct, overlap conserved.
* **One** design axiom (@pullbackConservationAxiom@): second law + conservation.
* Shared-substructure overlap identity conserved under pullback/pushout scaffold.
* @physics_green@ stays false.

Haskell mirror of pullback conservation on the quantum / knowing fiber.
Cell: @CHEM-FORMAL-Q-HS-PULLBACK-CONSERVATION@.
-}
module UMST.ChemConstants.PullbackConservation
  ( PullbackConservationModality (..)
  , pullbackConservationModalityCurrent
  , SubstructureOverlapTag (..)
  , SharedSubstructureDiagramKind (..)
  , SubstructureDiagram (..)
  , substructureDiagramKind
  , substructureDiagramOverlap
  , substructureDiagramLeftLeg
  , substructureDiagramRightLeg
  , substructureDiagramLegsDistinct
  , pullbackDiagramScaffold
  , pushoutDiagramScaffold
  , degenerateLegsDiagram
  , sharedSubstructureOverlapConserved
  , sharedSubstructureIdentityConservedUnderPullback
  , sharedSubstructureIdentityConservedUnderPushout
  , sharedSubstructureIdentityConserved
  , pullbackPushoutScaffold
  , degenerateLegsRefuse
  , universalPropertiesInventRefuse
  , substructureDiagramNotListBacked
  , pullbackComposeNotXor
  , universalPropertiesProved
  , cat02PullbackProved
  , pullbackConservationFraming
  , pullbackConservationAxiom
  , pullbackConservationNamed
  , sharedSubstructureLimitsAuthority
  , chemL0Cat02Authority
  , pullbackConservationCellId
  , pullbackConservationNonClaim
  , pullbackConservationPhysicsGreenAuthorized
  , pullbackConservationPhysicsGreenFalse
  , pullbackConservationModalityUnwired
  ) where

-- | Design modality for pullback conservation claims (TYPE-03 preview).
data PullbackConservationModality
  = PullbackConservationUnwired
  | PullbackConservationAssumed
  | PullbackConservationProved
  | PullbackConservationSurrogate
  deriving (Eq, Show)

-- | Current scaffold modality — always Unwired on this cell.
pullbackConservationModalityCurrent :: PullbackConservationModality
pullbackConservationModalityCurrent = PullbackConservationUnwired

-- | Shared ore overlap tags (bounded scaffold — not XOR enum).
data SubstructureOverlapTag
  = QuartzVeinScaffold
  | SulfideMatrixScaffold
  | CarbonateGangueScaffold
  deriving (Eq, Show)

-- | Categorical diagram kind for shared substructure (limit vs colimit).
data SharedSubstructureDiagramKind
  = PullbackKind
  | PushoutKind
  deriving (Eq, Show)

-- | Minimal two-leg diagram scaffold into shared substructure (design carrier).
data SubstructureDiagram
  = SubstructureDiagram SharedSubstructureDiagramKind SubstructureOverlapTag Int Int
  deriving (Eq, Show)

substructureDiagramKind :: SubstructureDiagram -> SharedSubstructureDiagramKind
substructureDiagramKind (SubstructureDiagram kind _ _ _) = kind

substructureDiagramOverlap :: SubstructureDiagram -> SubstructureOverlapTag
substructureDiagramOverlap (SubstructureDiagram _ overlap _ _) = overlap

substructureDiagramLeftLeg :: SubstructureDiagram -> Int
substructureDiagramLeftLeg (SubstructureDiagram _ _ left _) = left

substructureDiagramRightLeg :: SubstructureDiagram -> Int
substructureDiagramRightLeg (SubstructureDiagram _ _ _ right) = right

substructureDiagramLegsDistinct :: SubstructureDiagram -> Bool
substructureDiagramLegsDistinct diagram =
  substructureDiagramLeftLeg diagram /= substructureDiagramRightLeg diagram

-- | Example pullback scaffold — limit along shared quartz vein overlap.
pullbackDiagramScaffold :: SubstructureDiagram
pullbackDiagramScaffold =
  SubstructureDiagram PullbackKind QuartzVeinScaffold 0 1

-- | Example pushout scaffold — colimit gluing along sulfide matrix overlap.
pushoutDiagramScaffold :: SubstructureDiagram
pushoutDiagramScaffold =
  SubstructureDiagram PushoutKind SulfideMatrixScaffold 0 1

-- | Degenerate diagram — identical legs (refuse-closed witness).
degenerateLegsDiagram :: SubstructureDiagram
degenerateLegsDiagram =
  SubstructureDiagram PullbackKind CarbonateGangueScaffold 2 2

-- | Overlap tag conserved on admissible pullback/pushout scaffolds.
sharedSubstructureOverlapConserved :: SubstructureDiagram -> SubstructureOverlapTag -> Bool
sharedSubstructureOverlapConserved diagram expectedOverlap =
  substructureDiagramOverlap diagram == expectedOverlap

-- | Pullback scaffold preserves shared overlap identity with distinct legs.
sharedSubstructureIdentityConservedUnderPullback :: Bool
sharedSubstructureIdentityConservedUnderPullback =
  substructureDiagramKind pullbackDiagramScaffold == PullbackKind
    && sharedSubstructureOverlapConserved pullbackDiagramScaffold QuartzVeinScaffold
    && substructureDiagramLegsDistinct pullbackDiagramScaffold

-- | Pushout scaffold preserves shared overlap identity with distinct legs.
sharedSubstructureIdentityConservedUnderPushout :: Bool
sharedSubstructureIdentityConservedUnderPushout =
  substructureDiagramKind pushoutDiagramScaffold == PushoutKind
    && sharedSubstructureOverlapConserved pushoutDiagramScaffold SulfideMatrixScaffold
    && substructureDiagramLegsDistinct pushoutDiagramScaffold

-- | Shared-substructure overlap identity conserved under pullback + pushout scaffold.
sharedSubstructureIdentityConserved :: Bool
sharedSubstructureIdentityConserved =
  sharedSubstructureIdentityConservedUnderPullback
    && sharedSubstructureIdentityConservedUnderPushout

-- | Both pullback and pushout scaffolds admissible under Unwired design rules.
pullbackPushoutScaffold :: Bool
pullbackPushoutScaffold =
  sharedSubstructureIdentityConserved
    && substructureDiagramLegsDistinct pullbackDiagramScaffold
    && substructureDiagramLegsDistinct pushoutDiagramScaffold

-- | Degenerate legs refuse-closed — identical legs not admissible.
degenerateLegsRefuse :: Bool
degenerateLegsRefuse = not (substructureDiagramLegsDistinct degenerateLegsDiagram)

-- | Universal property invent refuse-closed scaffold witness.
universalPropertiesInventRefuse :: Bool
universalPropertiesInventRefuse = not universalPropertiesProved

-- | SubstructureDiagram algebra is not list-backed (two-leg diagram scaffold).
substructureDiagramNotListBacked :: Bool
substructureDiagramNotListBacked =
  pullbackDiagramScaffold /= pushoutDiagramScaffold
    && substructureDiagramKind pullbackDiagramScaffold /= substructureDiagramKind pushoutDiagramScaffold

-- | Diagram legs are concurrent Π_c — not XOR enum bucket.
pullbackComposeNotXor :: Bool
pullbackComposeNotXor =
  substructureDiagramLegsDistinct pullbackDiagramScaffold
    && substructureDiagramLegsDistinct pushoutDiagramScaffold
    && substructureDiagramLeftLeg pullbackDiagramScaffold
      /= substructureDiagramRightLeg pushoutDiagramScaffold

-- | Universal properties proved (always false on this Unwired cell).
universalPropertiesProved :: Bool
universalPropertiesProved = False

-- | CAT-02 pullback proved (always false on this Unwired cell).
cat02PullbackProved :: Bool
cat02PullbackProved = False

-- | One axiom framing: second law + conservation for pullback scaffold.
pullbackConservationFraming :: String
pullbackConservationFraming =
  "second_law_conservation_pullback_one_axiom"

-- | Single design axiom: second law + conservation pullback (not second axiom).
pullbackConservationAxiom :: Bool
pullbackConservationAxiom =
  substructureDiagramNotListBacked
    && pullbackPushoutScaffold
    && sharedSubstructureIdentityConserved
    && degenerateLegsRefuse
    && universalPropertiesInventRefuse
    && pullbackComposeNotXor
    && not universalPropertiesProved
    && not cat02PullbackProved
    && pullbackConservationFraming
      == "second_law_conservation_pullback_one_axiom"

pullbackConservationNamed :: String
pullbackConservationNamed =
  "pullbackConservation: SubstructureDiagram pullback/pushout scaffold; shared overlap identity conserved; universalPropertiesProved false cat02PullbackProved false; second law + conservation one axiom"

-- | Upstream shared-substructure limits authority (cited, not forked).
sharedSubstructureLimitsAuthority :: String
sharedSubstructureLimitsAuthority = "umst/umst-chem/src/shared_substructure_limits.rs"

-- | L0 CAT-02 pullback scaffold authority (crosswalk).
chemL0Cat02Authority :: String
chemL0Cat02Authority = "umst/umst-chem/src/l0_tables/shared.rs"

pullbackConservationCellId :: String
pullbackConservationCellId = "CHEM-FORMAL-Q-HS-PULLBACK-CONSERVATION"

-- | Non-claim fence — pullback conservation Unwired ≠ Proved GREEN.
pullbackConservationNonClaim :: String
pullbackConservationNonClaim =
  "CHEM-FORMAL-Q-HS-PULLBACK-CONSERVATION SubstructureDiagram pullback pushout scaffold sharedSubstructureIdentityConserved universalPropertiesProved false cat02PullbackProved false Unwired one axiom second law conservation not XOR enum not Vec list not GREEN DFT not physics GREEN not production_wired"

-- | Physics GREEN is unauthorized on the knowing pullback conservation scaffold.
pullbackConservationPhysicsGreenAuthorized :: Bool
pullbackConservationPhysicsGreenAuthorized = False

pullbackConservationPhysicsGreenFalse :: Bool
pullbackConservationPhysicsGreenFalse =
  not pullbackConservationPhysicsGreenAuthorized

pullbackConservationModalityUnwired :: Bool
pullbackConservationModalityUnwired =
  pullbackConservationModalityCurrent == PullbackConservationUnwired
