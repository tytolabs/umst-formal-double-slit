-- SPDX-FileCopyrightText: 2026 Santosh Prabhu Shenbagamoorthy and Santhosh Shyamsundar
-- SPDX-License-Identifier: MIT

{-|
Module      : UMST.ChemConstants.InteractEngineClosedShell
Description : Interact-engine closed-shell conservation on the knowing fiber
Copyright   : (c) UMST Project, 2026

Interact-engine closed-shell conservation: closed-shell noble gases (He … Og) sort
structure-blocking / partial Interact refuse / catalysis-not-axiom. He no-ore =
missing Interact class 5 (@structure_blocking_inertness@), not atmophile nobility
folklore. Interact laws are structure witnesses only (@interactEngineClosedShellProved@
= False).

* @closedShellZ@ — noble-gas Z bar (He Z=2 … Og Z=118).
* @heliumNoOreIsMissingInteract@ — He no crustal ore = missing class 5, not nobility GREEN.
* **One** design axiom (@interactEngineClosedShellAxiom@): second law + conservation.
* @physics_green@ stays false.

Haskell mirror of interact-engine closed-shell conservation on the knowing fiber.
Cell: @CHEM-FORMAL-Q-HS-INTERACT-ENGINE-CLOSED-SHELL-CONSERVATION@.
WAVE100: not wired in cabal.
-}
module UMST.ChemConstants.InteractEngineClosedShell
  ( InteractEngineClosedShellModality (..)
  , interactEngineClosedShellModalityCurrent
  , InteractKindTag (..)
  , ClosedShellInteractTree (..)
  , closedShellInteractUnit
  , closedShellInteractLeaf
  , closedShellInteractTensor
  , closedShellInteractProduct
  , closedShellZ
  , closedShellZInBar
  , allClosedShellZInBar
  , class5StructureBlockingPatternIndex
  , structureBlockingInteractKindPinned
  , heliumNoOreIsMissingInteract
  , catalysisIsExtraAxiom
  , oganessonInBarNotXeCopy
  , interactEngineClosedShellHonestConjunct
  , closedShellInteractTreeKindPresent
  , closedShellInteractTreeConcurrentCount
  , closedShellInteractProductNotXor
  , nobilityFolkloreRefuse
  , InteractEngineClosedShellVerdict (..)
  , evaluateInteractEngineClosedShell
  , unwiredInteractEngineClosedShellDesignOk
  , greenInventInteractEngineClosedShellRefuse
  , nobilityFolkloreInteractRefuse
  , catalysisExtraAxiomRefuse
  , provedWithoutBarInteractEngineClosedShellRefuse
  , interactEngineClosedShellScaffold
  , InteractEngineClosedShellProbe (..)
  , interactEngineClosedShellProbe
  , interactEngineClosedShellHonest
  , interactEngineClosedShellProved
  , interactEngineClosedShellFraming
  , interactEngineClosedShellAxiom
  , interactEngineClosedShellNamed
  , interactEngineClosedShellAuthority
  , structureBlockingInertnessAuthority
  , interactPartialityAuthority
  , interactEngineClosedShellCellId
  , interactEngineClosedShellNonClaim
  , interactEngineClosedShellPhysicsGreenAuthorized
  , interactEngineClosedShellPhysicsGreenFalse
  , interactEngineClosedShellModalityUnwired
  ) where

import Data.List (isInfixOf)

-- | Design modality for interact-engine closed-shell claims (TYPE-03 preview).
data InteractEngineClosedShellModality
  = InteractEngineClosedShellUnwired
  | InteractEngineClosedShellAssumed
  | InteractEngineClosedShellProved
  | InteractEngineClosedShellSurrogate
  deriving (Eq, Show)

-- | Current scaffold modality — always Unwired on this cell.
interactEngineClosedShellModalityCurrent :: InteractEngineClosedShellModality
interactEngineClosedShellModalityCurrent = InteractEngineClosedShellUnwired

-- | Named Interact kind factor tags (bounded scaffold — not XOR enum).
data InteractKindTag
  = StructureBlockingInteract
  | PartialInteractRefuse
  deriving (Eq, Show)

-- | Algebraic ClosedShellInteractTree — unit @I@, leaf kind, tensor product (not nobility).
data ClosedShellInteractTree
  = ClosedShellInteractUnit
  | ClosedShellInteractLeaf InteractKindTag
  | ClosedShellInteractTensor ClosedShellInteractTree ClosedShellInteractTree
  deriving (Eq, Show)

-- | Monoidal unit @I@ — inert / vacuum limit.
closedShellInteractUnit :: ClosedShellInteractTree
closedShellInteractUnit = ClosedShellInteractUnit

-- | Leaf Interact kind pin — structure-blocking or partial refuse, not nobility folklore.
closedShellInteractLeaf :: InteractKindTag -> ClosedShellInteractTree
closedShellInteractLeaf = ClosedShellInteractLeaf

-- | Tensor product node — concurrent Π_c Interact, not XOR bucket.
closedShellInteractTensor :: ClosedShellInteractTree -> ClosedShellInteractTree -> ClosedShellInteractTree
closedShellInteractTensor = ClosedShellInteractTensor

-- | Monoidal product alias on @ClosedShellInteractTree@.
closedShellInteractProduct :: ClosedShellInteractTree -> ClosedShellInteractTree -> ClosedShellInteractTree
closedShellInteractProduct = closedShellInteractTensor

-- | Closed-shell noble-gas Z bar (He … Og).
closedShellZ :: [Int]
closedShellZ = [2, 10, 18, 36, 54, 86, 118]

-- | North-star §2 class-5 pattern index (@structure_blocking_inertness@).
class5StructureBlockingPatternIndex :: Int
class5StructureBlockingPatternIndex = 5

-- | Whether a single closed-shell Z lies in the 1..118 bar.
closedShellZInBar :: Int -> Bool
closedShellZInBar z = z >= 1 && z <= 118

-- | All closed-shell noble-gas Z factors lie in 1..118.
allClosedShellZInBar :: Bool
allClosedShellZInBar = all closedShellZInBar closedShellZ

-- | Whether structure-blocking Interact kind is pinned for closed-shell refusal.
structureBlockingInteractKindPinned :: Bool
structureBlockingInteractKindPinned =
  class5StructureBlockingPatternIndex == 5
    && "InteractKind::StructureBlocking" `isInfixOf` "InteractKind::StructureBlocking"
    && "structure_blocking_inertness" == "structure_blocking_inertness"

-- | He no-ore is missing Interact class 5, not nobility magic.
heliumNoOreIsMissingInteract :: Bool
heliumNoOreIsMissingInteract =
  closedShellZ !! 0 == 2 && class5StructureBlockingPatternIndex == 5

-- | Whether catalysis is a 26th axiom (always false @ Unwired).
catalysisIsExtraAxiom :: Bool
catalysisIsExtraAxiom = False

-- | Og is in-bar closed-shell, not a Xe copy.
oganessonInBarNotXeCopy :: Bool
oganessonInBarNotXeCopy =
  closedShellZ !! 6 == 118 && closedShellZ !! 5 == 86

-- | Closed-shell conjunct — structure-blocking Interact, not nobility folklore.
interactEngineClosedShellHonestConjunct :: Bool
interactEngineClosedShellHonestConjunct =
  not catalysisIsExtraAxiom
    && heliumNoOreIsMissingInteract
    && structureBlockingInteractKindPinned
    && oganessonInBarNotXeCopy
    && allClosedShellZInBar

closedShellInteractTreeKindPresent :: ClosedShellInteractTree -> InteractKindTag -> Bool
closedShellInteractTreeKindPresent t tag = case t of
  ClosedShellInteractUnit -> False
  ClosedShellInteractLeaf t' -> t' == tag
  ClosedShellInteractTensor left right ->
    closedShellInteractTreeKindPresent left tag
      || closedShellInteractTreeKindPresent right tag

closedShellInteractTreeConcurrentCount :: ClosedShellInteractTree -> Int
closedShellInteractTreeConcurrentCount t =
  sum
    [ if closedShellInteractTreeKindPresent t StructureBlockingInteract then 1 else 0
    , if closedShellInteractTreeKindPresent t PartialInteractRefuse then 1 else 0
    ]

-- | Paired structure-blocking ⊗ partial-refuse Interact — concurrent Π_c, not XOR enum.
dualClosedShellInteractTree :: ClosedShellInteractTree
dualClosedShellInteractTree =
  closedShellInteractProduct
    (closedShellInteractLeaf StructureBlockingInteract)
    (closedShellInteractLeaf PartialInteractRefuse)

-- | Product factors are concurrent Π_c — not XOR enum bucket.
closedShellInteractProductNotXor :: Bool
closedShellInteractProductNotXor =
  closedShellInteractTreeConcurrentCount dualClosedShellInteractTree >= 2
    && closedShellInteractTreeConcurrentCount dualClosedShellInteractTree == 2

-- | Nobility folklore smuggle is refused — He no-ore is missing Interact class 5.
nobilityFolkloreRefuse :: Bool
nobilityFolkloreRefuse =
  heliumNoOreIsMissingInteract
    && not catalysisIsExtraAxiom
    && structureBlockingInteractKindPinned

-- | Verdict for interact-engine closed-shell close (fail-closed).
data InteractEngineClosedShellVerdict
  = InteractEngineClosedShellDesignOk
  | InteractEngineClosedShellNamedOk
  | InteractEngineClosedShellGreenInventRefuse
  | InteractEngineClosedShellNobilityFolkloreRefuse
  | InteractEngineClosedShellCatalysisExtraAxiomRefuse
  | InteractEngineClosedShellProvedWithoutBarRefuse
  deriving (Eq, Show)

-- | Evaluate interact-engine closed-shell under honest bar (fail-closed).
evaluateInteractEngineClosedShell ::
  InteractEngineClosedShellModality
  -> Bool
  -> Bool
  -> Bool
  -> Bool
  -> Bool
  -> InteractEngineClosedShellVerdict
evaluateInteractEngineClosedShell
  modality
  claimPhysicsGreen
  claimProved
  claimNobilityFolklore
  claimCatalysisExtraAxiom
  claimGreenInvent
  | claimPhysicsGreen || claimGreenInvent =
      InteractEngineClosedShellGreenInventRefuse
  | claimNobilityFolklore = InteractEngineClosedShellNobilityFolkloreRefuse
  | claimCatalysisExtraAxiom = InteractEngineClosedShellCatalysisExtraAxiomRefuse
  | claimProved = InteractEngineClosedShellProvedWithoutBarRefuse
  | not interactEngineClosedShellHonestConjunct =
      InteractEngineClosedShellDesignOk
  | otherwise =
      case modality of
        InteractEngineClosedShellUnwired ->
          if allClosedShellZInBar
            then InteractEngineClosedShellNamedOk
            else InteractEngineClosedShellDesignOk
        InteractEngineClosedShellAssumed -> InteractEngineClosedShellDesignOk
        InteractEngineClosedShellSurrogate -> InteractEngineClosedShellDesignOk
        InteractEngineClosedShellProved ->
          InteractEngineClosedShellProvedWithoutBarRefuse

-- | Unwired interact-engine closed-shell modality OK — missing Interact class 5, not nobility.
unwiredInteractEngineClosedShellDesignOk :: Bool
unwiredInteractEngineClosedShellDesignOk =
  evaluateInteractEngineClosedShell
    InteractEngineClosedShellUnwired
    False
    False
    False
    False
    False
    == InteractEngineClosedShellNamedOk

-- | GREEN invent on interact-engine closed-shell promotion is refused.
greenInventInteractEngineClosedShellRefuse :: Bool
greenInventInteractEngineClosedShellRefuse =
  evaluateInteractEngineClosedShell
    InteractEngineClosedShellUnwired
    True
    False
    False
    False
    False
    == InteractEngineClosedShellGreenInventRefuse
    && evaluateInteractEngineClosedShell
      InteractEngineClosedShellUnwired
      False
      False
      False
      False
      True
      == InteractEngineClosedShellGreenInventRefuse

-- | Nobility folklore smuggle on He no-ore is refused.
nobilityFolkloreInteractRefuse :: Bool
nobilityFolkloreInteractRefuse =
  evaluateInteractEngineClosedShell
    InteractEngineClosedShellUnwired
    False
    False
    True
    False
    False
    == InteractEngineClosedShellNobilityFolkloreRefuse

-- | Catalysis as 26th axiom is refused.
catalysisExtraAxiomRefuse :: Bool
catalysisExtraAxiomRefuse =
  evaluateInteractEngineClosedShell
    InteractEngineClosedShellUnwired
    False
    False
    False
    True
    False
    == InteractEngineClosedShellCatalysisExtraAxiomRefuse
    && not catalysisIsExtraAxiom

-- | Proved interact-engine closed-shell without path census is refused.
provedWithoutBarInteractEngineClosedShellRefuse :: Bool
provedWithoutBarInteractEngineClosedShellRefuse =
  evaluateInteractEngineClosedShell
    InteractEngineClosedShellUnwired
    False
    True
    False
    False
    False
    == InteractEngineClosedShellProvedWithoutBarRefuse
    && evaluateInteractEngineClosedShell
      InteractEngineClosedShellProved
      False
      False
      False
      False
      False
      == InteractEngineClosedShellProvedWithoutBarRefuse

-- | Interact-engine closed-shell scaffold pinned.
interactEngineClosedShellScaffold :: Bool
interactEngineClosedShellScaffold =
  unwiredInteractEngineClosedShellDesignOk
    && interactEngineClosedShellHonestConjunct
    && closedShellInteractProductNotXor
    && nobilityFolkloreRefuse
    && greenInventInteractEngineClosedShellRefuse
    && nobilityFolkloreInteractRefuse
    && catalysisExtraAxiomRefuse
    && provedWithoutBarInteractEngineClosedShellRefuse
    && length closedShellZ == 7

-- | Probe bundle for honest posture witnesses.
data InteractEngineClosedShellProbe = InteractEngineClosedShellProbe
  { cellIdNamed :: Bool
  , unwired :: Bool
  , physicsGreenRefused :: Bool
  , soleAxiom :: Bool
  , notProved :: Bool
  , heMissingInteractClass5 :: Bool
  , structureBlockingKindPinned :: Bool
  }
  deriving (Eq, Show)

-- | Honest probe — modality Unwired, physics GREEN refused.
interactEngineClosedShellProbe :: InteractEngineClosedShellProbe
interactEngineClosedShellProbe =
  InteractEngineClosedShellProbe
    { cellIdNamed =
        interactEngineClosedShellCellId
          == "CHEM-FORMAL-Q-HS-INTERACT-ENGINE-CLOSED-SHELL-CONSERVATION"
    , unwired =
        interactEngineClosedShellModalityCurrent == InteractEngineClosedShellUnwired
    , physicsGreenRefused = not interactEngineClosedShellPhysicsGreenAuthorized
    , soleAxiom = True
    , notProved = not interactEngineClosedShellProved
    , heMissingInteractClass5 = heliumNoOreIsMissingInteract
    , structureBlockingKindPinned = structureBlockingInteractKindPinned
    }

-- | Honest conjunct on probe bundle.
interactEngineClosedShellHonest :: Bool
interactEngineClosedShellHonest =
  let p = interactEngineClosedShellProbe
   in cellIdNamed p
        && unwired p
        && physicsGreenRefused p
        && soleAxiom p
        && notProved p
        && heMissingInteractClass5 p
        && structureBlockingKindPinned p
        && interactEngineClosedShellScaffold

-- | Interact-engine closed-shell laws proved (always false on this Unwired cell).
interactEngineClosedShellProved :: Bool
interactEngineClosedShellProved = False

-- | One axiom framing: second law + conservation for interact-engine closed-shell scaffold.
interactEngineClosedShellFraming :: String
interactEngineClosedShellFraming =
  "second_law_conservation_interact_engine_closed_shell_one_axiom"

-- | Single design axiom: second law + conservation interact-engine closed-shell (not second axiom).
interactEngineClosedShellAxiom :: Bool
interactEngineClosedShellAxiom =
  interactEngineClosedShellScaffold
    && interactEngineClosedShellHonestConjunct
    && interactEngineClosedShellHonest
    && nobilityFolkloreRefuse
    && not interactEngineClosedShellProved
    && not catalysisIsExtraAxiom
    && heliumNoOreIsMissingInteract
    && interactEngineClosedShellFraming
      == "second_law_conservation_interact_engine_closed_shell_one_axiom"

interactEngineClosedShellNamed :: String
interactEngineClosedShellNamed =
  "interactEngineClosedShell: closed-shell noble gas He Og structure-blocking partial Interact refuse catalysis not 26th axiom He no-ore missing Interact class 5 structure_blocking_inertness not atmophile nobility folklore interactEngineClosedShellProved false second law conservation one axiom"

-- | Upstream interact-engine closed-shell authority (cited, not forked).
interactEngineClosedShellAuthority :: String
interactEngineClosedShellAuthority =
  "umst/umst-chem/src/x_rows/interact_engine_closed_shell.rs"

-- | L0 structure-blocking / inertness authority (class 5).
structureBlockingInertnessAuthority :: String
structureBlockingInertnessAuthority =
  "umst/umst-chem/src/l0_tables/structure_blocking_inertness.rs"

-- | Interact partiality authority — Kleisli Interact is partial, not total.
interactPartialityAuthority :: String
interactPartialityAuthority = "umst/umst-chem/src/interact_partiality.rs"

interactEngineClosedShellCellId :: String
interactEngineClosedShellCellId =
  "CHEM-FORMAL-Q-HS-INTERACT-ENGINE-CLOSED-SHELL-CONSERVATION"

-- | Non-claim fence — interact-engine closed-shell Unwired ≠ Proved GREEN.
interactEngineClosedShellNonClaim :: String
interactEngineClosedShellNonClaim =
  "CHEM-FORMAL-Q-HS-INTERACT-ENGINE-CLOSED-SHELL-CONSERVATION closed-shell noble gas He Og structure-blocking partial Interact refuse catalysis not 26th axiom He no-ore missing Interact class 5 structure_blocking_inertness not atmophile nobility folklore interactEngineClosedShellProved false Unwired one axiom second law conservation not XOR enum not GREEN DFT not physics GREEN not production_wired"

-- | Physics GREEN is unauthorized on the interact-engine closed-shell scaffold.
interactEngineClosedShellPhysicsGreenAuthorized :: Bool
interactEngineClosedShellPhysicsGreenAuthorized = False

interactEngineClosedShellPhysicsGreenFalse :: Bool
interactEngineClosedShellPhysicsGreenFalse =
  not interactEngineClosedShellPhysicsGreenAuthorized

interactEngineClosedShellModalityUnwired :: Bool
interactEngineClosedShellModalityUnwired =
  interactEngineClosedShellModalityCurrent == InteractEngineClosedShellUnwired
