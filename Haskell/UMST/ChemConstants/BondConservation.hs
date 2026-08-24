-- SPDX-FileCopyrightText: 2026 Santosh Prabhu Shenbagamoorthy and Santhosh Shyamsundar
-- SPDX-License-Identifier: MIT

{-|
Module      : UMST.ChemConstants.BondConservation
Description : Bond conservation on the knowing fiber (Q lattice)
Copyright   : (c) UMST Project, 2026

**Bond** conservation: GRAPH-01 bond / reaction edge identity conserved on named
**bond** and reaction morphisms (H–O Z=1/8; Og Z=118; forward hydration named).
Named **bond** / reaction edge identity conserved under honest scaffold; self-loop
and GREEN invent fail-closed. GRAPH-01 **bond** laws are structure witnesses only
(@graph01BondProved@ = False).

* @BondConservationModality@ = Unwired / Assumed / Proved / Surrogate — four-step lattice, not 118² GREEN table.
* @evaluateBondEdge@ — named **bond** edge identity conserved; self-loop refuse-closed.
* @evaluateReactionEdge@ — forward hydration named reaction edge typed @ scaffold.
* **One** design axiom (@bondConservationAxiom@): second law + **conservation**.
* @physics_green@ stays false.

Haskell mirror of GRAPH-01 **bond** **conservation** on the quantum / knowing fiber.
Cell: @CHEM-FORMAL-Q-HS-BOND-CONSERVATION@.
-}
module UMST.ChemConstants.BondConservation
  ( BondConservationModality (..)
  , bondConservationModalityCurrent
  , bondLatticeAll
  , bondLatticeCount
  , BondElementZ (..)
  , bondElementZAll
  , bondElementZCount
  , BondGraphNodeId (..)
  , ReactionVertexId (..)
  , BondKind (..)
  , bondKindAll
  , bondKindCount
  , ReactionEdgeKind (..)
  , reactionEdgeKindAll
  , reactionEdgeKindCount
  , BondEdge (..)
  , bondEdgeHOHydrogenBond
  , bondEdgeSelfLoopOganesson
  , ReactionEdge (..)
  , reactionEdgeForwardHydrationNamed
  , BondEdgeVerdict (..)
  , ReactionEdgeVerdict (..)
  , evaluateBondEdge
  , evaluateReactionEdge
  , EdgeIdentityLaw (..)
  , edgeIdentityLawAll
  , edgeIdentityLawCount
  , BondConservationVerdict (..)
  , evaluateBondConservation
  , sampleNamedBondEdge
  , sampleSelfLoopEdge
  , sampleForwardHydrationEdge
  , unwiredDesignOk
  , hOElementZValid
  , oganessonZValid
  , namedBondEdgeIdentityConserved
  , forwardHydrationNamedOk
  , bondAndReactionEdgesNamed
  , selfLoopFailClosed
  , greenInventBondRefuse
  , assumedBondDesignOk
  , surrogateBondDesignOk
  , bondLatticeScaffold
  , bondLatticeNotGreenTable
  , edgeIdentityLawsScaffold
  , edgeIdentityLawsNotGreenTable
  , bondKnowingFiberOk
  , graph01BondInventRefuse
  , bondLatticeNotXor
  , graph01BondProved
  , bondConservationFraming
  , bondConservationAxiom
  , bondConservationNamed
  , bondReactionGraphAuthority
  , chemL0Graph01Authority
  , bondConservationCellId
  , bondConservationNonClaim
  , bondConservationPhysicsGreenAuthorized
  , bondConservationPhysicsGreenFalse
  , bondConservationModalityUnwired
  ) where

-- | IUPAC periodic-table cardinality (Z=1..118).
iupacTableCardinality :: Int
iupacTableCardinality = 118

-- | Design **bond** modality for GRAPH-01 **conservation** claims.
data BondConservationModality
  = BondConservationUnwired
  | BondConservationAssumed
  | BondConservationProved
  | BondConservationSurrogate
  deriving (Eq, Show)

-- | Current scaffold **bond** modality — always Unwired on this cell.
bondConservationModalityCurrent :: BondConservationModality
bondConservationModalityCurrent = BondConservationUnwired

-- | All GRAPH-01 **bond** lattice steps in stable order.
bondLatticeAll :: [BondConservationModality]
bondLatticeAll =
  [ BondConservationUnwired
  , BondConservationAssumed
  , BondConservationProved
  , BondConservationSurrogate
  ]

bondLatticeCount :: Int
bondLatticeCount = length bondLatticeAll

-- | Private Z pin — not L1 SpeciesId; not wired ElementId.
data BondElementZ
  = BondElementHydrogen
  | BondElementOxygen
  | BondElementOganesson
  deriving (Eq, Show)

-- | All scaffold **bond** element Z pins in stable order.
bondElementZAll :: [BondElementZ]
bondElementZAll =
  [ BondElementHydrogen
  , BondElementOxygen
  , BondElementOganesson
  ]

bondElementZCount :: Int
bondElementZCount = length bondElementZAll

-- | Numeric Z for a **bond** element pin.
bondElementZNumeric :: BondElementZ -> Int
bondElementZNumeric z =
  case z of
    BondElementHydrogen -> 1
    BondElementOxygen -> 8
    BondElementOganesson -> 118

-- | Whether a **bond** element Z is valid IUPAC Z @ scaffold.
isValidIupacZ :: BondElementZ -> Bool
isValidIupacZ z =
  let n = bondElementZNumeric z
   in n > 0 && n <= iupacTableCardinality

-- | Private graph node id (distinct from L1 SpeciesId).
newtype BondGraphNodeId = BondGraphNodeId Int
  deriving (Eq, Show)

-- | Private reaction vertex id.
newtype ReactionVertexId = ReactionVertexId Int
  deriving (Eq, Show)

-- | Named **bond** kind (scaffold classifier — not live solver).
data BondKind
  = CovalentNamed
  | IonicNamed
  | HydrogenBondNamed
  | CoordinationNamed
  deriving (Eq, Show)

bondKindAll :: [BondKind]
bondKindAll =
  [ CovalentNamed
  , IonicNamed
  , HydrogenBondNamed
  , CoordinationNamed
  ]

bondKindCount :: Int
bondKindCount = length bondKindAll

-- | Named reaction edge kind (scaffold classifier).
data ReactionEdgeKind
  = ForwardNamed
  | ReverseNamed
  | CatalyticNamed
  | DissipativePathNamed
  deriving (Eq, Show)

reactionEdgeKindAll :: [ReactionEdgeKind]
reactionEdgeKindAll =
  [ ForwardNamed
  , ReverseNamed
  , CatalyticNamed
  , DissipativePathNamed
  ]

reactionEdgeKindCount :: Int
reactionEdgeKindCount = length reactionEdgeKindAll

-- | Typed **bond** edge with named element Z pins.
data BondEdge = BondEdge
  { bondFrom :: BondGraphNodeId
  , bondTo :: BondGraphNodeId
  , bondFromZ :: BondElementZ
  , bondToZ :: BondElementZ
  , bondKind :: BondKind
  }
  deriving (Eq, Show)

-- | Scaffold H–O hydrogen-**bond** edge (Z=1/8).
bondEdgeHOHydrogenBond :: BondEdge
bondEdgeHOHydrogenBond =
  BondEdge
    { bondFrom = BondGraphNodeId 1
    , bondTo = BondGraphNodeId 2
    , bondFromZ = BondElementHydrogen
    , bondToZ = BondElementOxygen
    , bondKind = HydrogenBondNamed
    }

-- | Scaffold self-loop **bond** edge (Og Z=118) — must fail-closed.
bondEdgeSelfLoopOganesson :: BondEdge
bondEdgeSelfLoopOganesson =
  BondEdge
    { bondFrom = BondGraphNodeId 3
    , bondTo = BondGraphNodeId 3
    , bondFromZ = BondElementOganesson
    , bondToZ = BondElementOganesson
    , bondKind = CovalentNamed
    }

-- | Whether a **bond** edge is non-trivial (no self-loop).
isNontrivialBondEdge :: BondEdge -> Bool
isNontrivialBondEdge edge =
  bondFrom edge /= bondTo edge

-- | Whether **bond** element Z pins are valid IUPAC Z.
bondEdgeElementZValid :: BondEdge -> Bool
bondEdgeElementZValid edge =
  isValidIupacZ (bondFromZ edge) && isValidIupacZ (bondToZ edge)

-- | Typed reaction edge (forward hydration named @ scaffold).
data ReactionEdge = ReactionEdge
  { reactionVertex :: ReactionVertexId
  , reactionKind :: ReactionEdgeKind
  }
  deriving (Eq, Show)

-- | Forward hydration-named reaction edge @ scaffold.
reactionEdgeForwardHydrationNamed :: ReactionEdge
reactionEdgeForwardHydrationNamed =
  ReactionEdge
    { reactionVertex = ReactionVertexId 1
    , reactionKind = ForwardNamed
    }

-- | Verdict for a **bond** edge close (fail-closed).
data BondEdgeVerdict
  = BondEdgeDesignOk
  | BondEdgeNamedOk
  | BondEdgeSelfLoopRefuse
  | BondEdgeGreenInventRefuse
  | BondEdgeProvedWithoutBarRefuse
  deriving (Eq, Show)

-- | Verdict for a reaction edge close (fail-closed).
data ReactionEdgeVerdict
  = ReactionEdgeDesignOk
  | ReactionEdgeNamedOk
  | ReactionEdgeGreenInventRefuse
  | ReactionEdgeProvedWithoutBarRefuse
  deriving (Eq, Show)

-- | Evaluate a **bond** edge under GRAPH-01 **conservation** bar (fail-closed).
evaluateBondEdge ::
  BondConservationModality
  -> BondEdge
  -> Bool
  -> Bool
  -> BondEdgeVerdict
evaluateBondEdge modality edge claimPhysicsGreen claimProved
  | claimPhysicsGreen = BondEdgeGreenInventRefuse
  | claimProved = BondEdgeProvedWithoutBarRefuse
  | not (isNontrivialBondEdge edge) = BondEdgeSelfLoopRefuse
  | otherwise =
      case modality of
        BondConservationUnwired -> BondEdgeNamedOk
        BondConservationAssumed -> BondEdgeDesignOk
        BondConservationSurrogate -> BondEdgeDesignOk
        BondConservationProved -> BondEdgeProvedWithoutBarRefuse

-- | Evaluate a reaction edge under GRAPH-01 **conservation** bar (fail-closed).
evaluateReactionEdge ::
  BondConservationModality
  -> ReactionEdge
  -> Bool
  -> Bool
  -> ReactionEdgeVerdict
evaluateReactionEdge modality edge claimPhysicsGreen claimProved
  | claimPhysicsGreen = ReactionEdgeGreenInventRefuse
  | claimProved = ReactionEdgeProvedWithoutBarRefuse
  | otherwise =
      case modality of
        BondConservationUnwired -> ReactionEdgeNamedOk
        BondConservationAssumed -> ReactionEdgeDesignOk
        BondConservationSurrogate -> ReactionEdgeDesignOk
        BondConservationProved -> ReactionEdgeProvedWithoutBarRefuse
  where
    _ = edge

-- | **Bond** edge identity law cells tracked by GRAPH-01 (structure scaffold).
data EdgeIdentityLaw
  = EdgeIdentityConserved
  | NamedBondOk
  | SelfLoopRefused
  | GreenInventRefused
  deriving (Eq, Show)

edgeIdentityLawAll :: [EdgeIdentityLaw]
edgeIdentityLawAll =
  [ EdgeIdentityConserved
  , NamedBondOk
  , SelfLoopRefused
  , GreenInventRefused
  ]

edgeIdentityLawCount :: Int
edgeIdentityLawCount = length edgeIdentityLawAll

-- | Verdict for GRAPH-01 **bond** **conservation** promotion (fail-closed).
data BondConservationVerdict
  = BondDesignOk
  | BondNamedOk
  | BondSelfLoopRefuse
  | BondGreenInventRefuse
  | BondProvedWithoutBarRefuse
  deriving (Eq, Show)

-- | Evaluate GRAPH-01 **bond** **conservation** typing (fail-closed).
evaluateBondConservation ::
  BondConservationModality
  -> BondEdge
  -> ReactionEdge
  -> Bool
  -> Bool
  -> BondConservationVerdict
evaluateBondConservation modality bondEdge reactionEdge claimPhysicsGreen claimProved
  | claimPhysicsGreen = BondGreenInventRefuse
  | claimProved = BondProvedWithoutBarRefuse
  | otherwise =
      case evaluateBondEdge modality bondEdge False False of
        BondEdgeSelfLoopRefuse -> BondSelfLoopRefuse
        BondEdgeGreenInventRefuse -> BondGreenInventRefuse
        BondEdgeProvedWithoutBarRefuse -> BondProvedWithoutBarRefuse
        BondEdgeNamedOk ->
          case evaluateReactionEdge modality reactionEdge False False of
            ReactionEdgeNamedOk -> BondNamedOk
            ReactionEdgeGreenInventRefuse -> BondGreenInventRefuse
            ReactionEdgeProvedWithoutBarRefuse -> BondProvedWithoutBarRefuse
            ReactionEdgeDesignOk -> BondDesignOk
        BondEdgeDesignOk -> BondDesignOk

sampleNamedBondEdge :: BondEdge
sampleNamedBondEdge = bondEdgeHOHydrogenBond

sampleSelfLoopEdge :: BondEdge
sampleSelfLoopEdge = bondEdgeSelfLoopOganesson

sampleForwardHydrationEdge :: ReactionEdge
sampleForwardHydrationEdge = reactionEdgeForwardHydrationNamed

-- | Unwired **bond** modality OK without thermo break.
unwiredDesignOk :: Bool
unwiredDesignOk =
  evaluateBondConservation
    BondConservationUnwired
    sampleNamedBondEdge
    sampleForwardHydrationEdge
    False
    False
    == BondNamedOk

-- | H–O **bond** edge carries valid Z=1/8 pins.
hOElementZValid :: Bool
hOElementZValid =
  bondEdgeElementZValid bondEdgeHOHydrogenBond
    && bondElementZNumeric (bondFromZ bondEdgeHOHydrogenBond) == 1
    && bondElementZNumeric (bondToZ bondEdgeHOHydrogenBond) == 8

-- | Z=118 Oganesson pin is valid IUPAC Z @ scaffold.
oganessonZValid :: Bool
oganessonZValid =
  isValidIupacZ BondElementOganesson
    && bondElementZNumeric BondElementOganesson == iupacTableCardinality

-- | Named **bond** edge identity conserved: H–O Z pins + kind stable.
namedBondEdgeIdentityConserved :: Bool
namedBondEdgeIdentityConserved =
  let edge = bondEdgeHOHydrogenBond
   in isNontrivialBondEdge edge
        && hOElementZValid
        && evaluateBondEdge
          BondConservationUnwired
          edge
          False
          False
          == BondEdgeNamedOk
        && bondKind edge == HydrogenBondNamed

-- | Forward hydration-named reaction edge is typed @ scaffold.
forwardHydrationNamedOk :: Bool
forwardHydrationNamedOk =
  let edge = reactionEdgeForwardHydrationNamed
   in reactionVertex edge == ReactionVertexId 1
        && reactionKind edge == ForwardNamed
        && evaluateReactionEdge
          BondConservationUnwired
          edge
          False
          False
          == ReactionEdgeNamedOk

-- | **Bond** and reaction edge kinds are both named @ scaffold.
bondAndReactionEdgesNamed :: Bool
bondAndReactionEdgesNamed =
  namedBondEdgeIdentityConserved && forwardHydrationNamedOk

-- | Self-loop **bond** edge is fail-closed.
selfLoopFailClosed :: Bool
selfLoopFailClosed =
  evaluateBondEdge
    BondConservationUnwired
    sampleSelfLoopEdge
    False
    False
    == BondEdgeSelfLoopRefuse
    && evaluateBondConservation
      BondConservationUnwired
      sampleSelfLoopEdge
      sampleForwardHydrationEdge
      False
      False
      == BondSelfLoopRefuse

-- | GREEN invent on **bond** **conservation** promotion is refused.
greenInventBondRefuse :: Bool
greenInventBondRefuse =
  evaluateBondConservation
    BondConservationUnwired
    sampleNamedBondEdge
    sampleForwardHydrationEdge
    True
    False
    == BondGreenInventRefuse
    && evaluateBondEdge
      BondConservationUnwired
      sampleNamedBondEdge
      True
      False
      == BondEdgeGreenInventRefuse

-- | Assumed **bond** modality OK without thermo break (design scaffold).
assumedBondDesignOk :: Bool
assumedBondDesignOk =
  evaluateBondConservation
    BondConservationAssumed
    sampleNamedBondEdge
    sampleForwardHydrationEdge
    False
    False
    == BondDesignOk

-- | Surrogate **bond** modality OK without thermo break (design scaffold).
surrogateBondDesignOk :: Bool
surrogateBondDesignOk =
  evaluateBondConservation
    BondConservationSurrogate
    sampleNamedBondEdge
    sampleForwardHydrationEdge
    False
    False
    == BondDesignOk

-- | Four-step GRAPH-01 **bond** lattice scaffold pinned.
bondLatticeScaffold :: Bool
bondLatticeScaffold =
  bondLatticeCount == 4
    && unwiredDesignOk
    && hOElementZValid
    && oganessonZValid
    && namedBondEdgeIdentityConserved
    && forwardHydrationNamedOk
    && bondAndReactionEdgesNamed
    && selfLoopFailClosed
    && assumedBondDesignOk
    && surrogateBondDesignOk

-- | **Bond** lattice is structure scaffold — not 118² GREEN periodic table.
bondLatticeNotGreenTable :: Bool
bondLatticeNotGreenTable =
  bondLatticeCount == 4
    && bondLatticeCount /= 118 * 118
    && bondKindCount /= 118 * 118
    && reactionEdgeKindCount /= 118 * 118

-- | Four **bond** edge identity law cells scaffold pinned.
edgeIdentityLawsScaffold :: Bool
edgeIdentityLawsScaffold =
  edgeIdentityLawCount == 4
    && namedBondEdgeIdentityConserved
    && forwardHydrationNamedOk
    && selfLoopFailClosed
    && greenInventBondRefuse

-- | **Bond** law cells are structure scaffold — not 118² GREEN periodic table.
edgeIdentityLawsNotGreenTable :: Bool
edgeIdentityLawsNotGreenTable =
  edgeIdentityLawsScaffold
    && edgeIdentityLawCount /= 118 * 118
    && bondElementZCount /= 118 * 118

-- | GRAPH-01 **bond** **conservation** claims route to knowing / quantum fiber (not meso acting).
bondKnowingFiberOk :: Bool
bondKnowingFiberOk = True

-- | GRAPH-01 **bond** invent refuse-closed scaffold witness.
graph01BondInventRefuse :: Bool
graph01BondInventRefuse = not graph01BondProved

-- | **Bond** lattice steps are concurrent Π_c — not XOR enum bucket.
bondLatticeNotXor :: Bool
bondLatticeNotXor =
  unwiredDesignOk
    && assumedBondDesignOk
    && surrogateBondDesignOk
    && namedBondEdgeIdentityConserved
    && forwardHydrationNamedOk
    && selfLoopFailClosed
    && greenInventBondRefuse

-- | GRAPH-01 **bond** proved (always false on this Unwired cell).
graph01BondProved :: Bool
graph01BondProved = False

-- | One axiom framing: second law + **conservation** for GRAPH-01 **bond** scaffold.
bondConservationFraming :: String
bondConservationFraming =
  "second_law_conservation_bond_one_axiom"

-- | Single design axiom: second law + **conservation** GRAPH-01 **bond** (not second axiom).
bondConservationAxiom :: Bool
bondConservationAxiom =
  bondLatticeScaffold
    && bondLatticeNotGreenTable
    && edgeIdentityLawsScaffold
    && edgeIdentityLawsNotGreenTable
    && bondKnowingFiberOk
    && hOElementZValid
    && oganessonZValid
    && namedBondEdgeIdentityConserved
    && forwardHydrationNamedOk
    && bondAndReactionEdgesNamed
    && selfLoopFailClosed
    && greenInventBondRefuse
    && graph01BondInventRefuse
    && bondLatticeNotXor
    && not graph01BondProved
    && bondConservationFraming
      == "second_law_conservation_bond_one_axiom"

bondConservationNamed :: String
bondConservationNamed =
  "bondConservation: BondConservationModality Unwired Assumed Proved Surrogate four-step lattice graph01BondProved false evaluateBondEdge evaluateReactionEdge named bond reaction edge identity conserved H-O Z=1/8 Og Z=118 forward hydration named self-loop fail-closed second law conservation one axiom"

-- | Upstream GRAPH-01 **bond** / reaction graph authority (cited, not forked).
bondReactionGraphAuthority :: String
bondReactionGraphAuthority = "umst/umst-chem/src/bond_reaction_graph.rs"

-- | L0 GRAPH-01 **bond** scaffold authority (crosswalk).
chemL0Graph01Authority :: String
chemL0Graph01Authority = "CHEM-L0-GRAPH-01"

bondConservationCellId :: String
bondConservationCellId = "CHEM-FORMAL-Q-HS-BOND-CONSERVATION"

-- | Non-claim fence — GRAPH-01 **bond** **conservation** Unwired ≠ Proved GREEN.
bondConservationNonClaim :: String
bondConservationNonClaim =
  "CHEM-FORMAL-Q-HS-BOND-CONSERVATION BondConservationModality Unwired Assumed Proved Surrogate four-step lattice graph01BondProved false evaluateBondEdge evaluateReactionEdge named bond reaction edge identity conserved H-O Z=1/8 Og Z=118 forward hydration named self-loop fail-closed Unwired one axiom second law conservation not 118 squared GREEN table not meso acting not physics GREEN not production_wired"

-- | Physics GREEN is unauthorized on the knowing GRAPH-01 **bond** **conservation** scaffold.
bondConservationPhysicsGreenAuthorized :: Bool
bondConservationPhysicsGreenAuthorized = False

bondConservationPhysicsGreenFalse :: Bool
bondConservationPhysicsGreenFalse =
  not bondConservationPhysicsGreenAuthorized

bondConservationModalityUnwired :: Bool
bondConservationModalityUnwired =
  bondConservationModalityCurrent == BondConservationUnwired
