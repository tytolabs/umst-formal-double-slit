-- SPDX-FileCopyrightText: 2026 Santosh Prabhu Shenbagamoorthy and Santhosh Shyamsundar
-- SPDX-License-Identifier: MIT

{-|
Module      : UMST.ChemConstants.HyperConservation
Description : Hyper conservation on the knowing fiber (Q lattice)
Copyright   : (c) UMST Project, 2026

**Hyper** conservation: GRAPH-03 multi-constituent ore incidence via **hyper**edges
conserved on named ternary arity pins (hematite; magnetite; silicate gangue; Fe Z=26).
Named **hyper** incidence identity conserved under honest scaffold; trivial **hyper**
and GREEN invent fail-closed. GRAPH-03 **hyper** laws are structure witnesses only
(@graph03HyperProved@ = False). **Hyper** ≠ bond. No @petgraph@ kernel fork.

* @HyperConservationModality@ = Unwired / Assumed / Proved / Surrogate — four-step lattice, not 118² GREEN table.
* @evaluateHyperedge@ — named **hyper** multi-constituent incidence identity conserved; trivial **hyper** refuse-closed.
* @evaluateTernaryIncidence@ — ternary arity **hyper**edge typed @ scaffold; hematite ≠ gangue.
* **One** design axiom (@hyperConservationAxiom@): second law + **conservation**.
* @physics_green@ stays false.

Haskell mirror of GRAPH-03 **hyper** **conservation** on the quantum / knowing fiber.
Cell: @CHEM-FORMAL-Q-HS-HYPER-CONSERVATION@.
-}
module UMST.ChemConstants.HyperConservation
  ( HyperConservationModality (..)
  , hyperConservationModalityCurrent
  , hyperLatticeAll
  , hyperLatticeCount
  , HyperElementZ (..)
  , hyperElementZAll
  , hyperElementZCount
  , HyperGraphNodeId (..)
  , OreConstituentId (..)
  , oreConstituentIdAll
  , oreConstituentIdCount
  , GraphTopologyKind (..)
  , graphTopologyKindAll
  , graphTopologyKindCount
  , HyperedgeArity (..)
  , hyperedgeArityAll
  , hyperedgeArityCount
  , HyperRole (..)
  , hyperRoleAll
  , hyperRoleCount
  , HyperKind (..)
  , hyperKindAll
  , hyperKindCount
  , Hyperedge (..)
  , hyperedgeTernaryOre
  , hyperedgeTrivialOganesson
  , HyperIncidence (..)
  , hyperIncidenceTernaryL3
  , hyperIncidenceTrivialL0
  , Hypergraph (..)
  , hypergraphScaffoldTernary
  , HyperedgeVerdict (..)
  , TernaryIncidenceVerdict (..)
  , evaluateHyperedge
  , evaluateTernaryIncidence
  , IncidenceIdentityLaw (..)
  , incidenceIdentityLawAll
  , incidenceIdentityLawCount
  , HyperConservationVerdict (..)
  , evaluateHyperConservation
  , sampleNamedHyperedge
  , sampleTrivialHyperedge
  , sampleTernaryIncidence
  , unwiredDesignOk
  , feElementZValid
  , hematiteConstituentValid
  , oganessonZValid
  , namedHyperIncidenceIdentityConserved
  , ternaryIncidenceNamedOk
  , hyperAndTernaryIncidenceNamed
  , hematiteNeGangue
  , ternaryArityConsistent
  , multiConstituentNamed
  , trivialHyperFailClosed
  , greenInventHyperRefuse
  , assumedHyperDesignOk
  , surrogateHyperDesignOk
  , hyperLatticeScaffold
  , hyperLatticeNotGreenTable
  , incidenceIdentityLawsScaffold
  , incidenceIdentityLawsNotGreenTable
  , hyperKnowingFiberOk
  , graph03HyperInventRefuse
  , hyperLatticeNotXor
  , graph03HyperProved
  , hyperNeBond
  , petgraphKernelForked
  , hyperConservationFraming
  , hyperConservationAxiom
  , hyperConservationNamed
  , oreHypergraphAuthority
  , chemL0Graph03Authority
  , hyperConservationCellId
  , hyperConservationNonClaim
  , hyperConservationPhysicsGreenAuthorized
  , hyperConservationPhysicsGreenFalse
  , hyperConservationModalityUnwired
  ) where

-- | IUPAC periodic-table cardinality (Z=1..118).
iupacTableCardinality :: Int
iupacTableCardinality = 118

-- | Design **hyper** modality for GRAPH-03 **conservation** claims.
data HyperConservationModality
  = HyperConservationUnwired
  | HyperConservationAssumed
  | HyperConservationProved
  | HyperConservationSurrogate
  deriving (Eq, Show)

-- | Current scaffold **hyper** modality — always Unwired on this cell.
hyperConservationModalityCurrent :: HyperConservationModality
hyperConservationModalityCurrent = HyperConservationUnwired

-- | All GRAPH-03 **hyper** lattice steps in stable order.
hyperLatticeAll :: [HyperConservationModality]
hyperLatticeAll =
  [ HyperConservationUnwired
  , HyperConservationAssumed
  , HyperConservationProved
  , HyperConservationSurrogate
  ]

hyperLatticeCount :: Int
hyperLatticeCount = length hyperLatticeAll

-- | Private Z pin — not L1 SpeciesId; not wired ElementId.
data HyperElementZ
  = HyperElementIron
  | HyperElementMagnetite
  | HyperElementOganesson
  deriving (Eq, Show)

-- | All scaffold **hyper** element Z pins in stable order.
hyperElementZAll :: [HyperElementZ]
hyperElementZAll =
  [ HyperElementIron
  , HyperElementMagnetite
  , HyperElementOganesson
  ]

hyperElementZCount :: Int
hyperElementZCount = length hyperElementZAll

-- | Numeric Z for a **hyper** element pin.
hyperElementZNumeric :: HyperElementZ -> Int
hyperElementZNumeric z =
  case z of
    HyperElementIron -> 26
    HyperElementMagnetite -> 26
    HyperElementOganesson -> 118

-- | Whether a **hyper** element Z is valid IUPAC Z @ scaffold.
isValidIupacZ :: HyperElementZ -> Bool
isValidIupacZ z =
  let n = hyperElementZNumeric z
   in n > 0 && n <= iupacTableCardinality

-- | Private graph node id (distinct from L1 SpeciesId).
newtype HyperGraphNodeId = HyperGraphNodeId Int
  deriving (Eq, Show)

-- | Named ore constituent pins for **hyper** incidence (not SpeciesId).
data OreConstituentId
  = HematiteNamed
  | MagnetiteNamed
  | SilicateGangueNamed
  | CalciteGangueNamed
  deriving (Eq, Show)

-- | All scaffold ore constituent pins in stable order.
oreConstituentIdAll :: [OreConstituentId]
oreConstituentIdAll =
  [ HematiteNamed
  , MagnetiteNamed
  , SilicateGangueNamed
  , CalciteGangueNamed
  ]

oreConstituentIdCount :: Int
oreConstituentIdCount = length oreConstituentIdAll

-- | GRAPH-03 topology kind — **hyper**graph vs pairwise bond (distinct SSOT).
data GraphTopologyKind
  = PairwiseBondTopology
  | MultiHeadHyperedgeTopology
  deriving (Eq, Show)

graphTopologyKindAll :: [GraphTopologyKind]
graphTopologyKindAll =
  [ PairwiseBondTopology
  , MultiHeadHyperedgeTopology
  ]

graphTopologyKindCount :: Int
graphTopologyKindCount = length graphTopologyKindAll

-- | **Hyper**edge arity scaffold (ternary multi-constituent **conservation**).
data HyperedgeArity
  = HyperArityBinary
  | HyperArityTernary
  | HyperArityMultiConstituent
  deriving (Eq, Show)

hyperedgeArityAll :: [HyperedgeArity]
hyperedgeArityAll =
  [ HyperArityBinary
  , HyperArityTernary
  , HyperArityMultiConstituent
  ]

hyperedgeArityCount :: Int
hyperedgeArityCount = length hyperedgeArityAll

-- | Minimum constituent count for a **hyper**edge arity.
hyperedgeArityMinConstituentCount :: HyperedgeArity -> Int
hyperedgeArityMinConstituentCount arity =
  case arity of
    HyperArityBinary -> 2
    HyperArityTernary -> 3
    HyperArityMultiConstituent -> 4

-- | Whether arity is multi-constituent (ternary or above).
hyperedgeArityIsMultiConstituent :: HyperedgeArity -> Bool
hyperedgeArityIsMultiConstituent arity =
  case arity of
    HyperArityBinary -> False
    HyperArityTernary -> True
    HyperArityMultiConstituent -> True

-- | Named **hyper** role (scaffold classifier — not live hypergraph solver).
data HyperRole
  = OreIncidenceNamed
  | GangueTailNamed
  | MultiHeadNamed
  deriving (Eq, Show)

hyperRoleAll :: [HyperRole]
hyperRoleAll =
  [ OreIncidenceNamed
  , GangueTailNamed
  , MultiHeadNamed
  ]

hyperRoleCount :: Int
hyperRoleCount = length hyperRoleAll

-- | Named **hyper** kind (scaffold classifier — distinct from bond kind).
data HyperKind
  = IncidenceNamed
  | TernaryNamed
  | MultiConstituentNamed
  | HypergraphNamed
  deriving (Eq, Show)

hyperKindAll :: [HyperKind]
hyperKindAll =
  [ IncidenceNamed
  , TernaryNamed
  , MultiConstituentNamed
  , HypergraphNamed
  ]

hyperKindCount :: Int
hyperKindCount = length hyperKindAll

-- | Typed **hyper**edge with named ore constituent pins and ternary arity.
data Hyperedge = Hyperedge
  { hyperTopology :: GraphTopologyKind
  , hyperArity :: HyperedgeArity
  , hyperConstituentCount :: Int
  , hyperHeads :: [OreConstituentId]
  , hyperAnchorZ :: HyperElementZ
  , hyperRole :: HyperRole
  , hyperKind :: HyperKind
  }
  deriving (Eq, Show)

-- | Scaffold ternary ore **hyper**edge (hematite; magnetite; silicate gangue).
hyperedgeTernaryOre :: Hyperedge
hyperedgeTernaryOre =
  Hyperedge
    { hyperTopology = MultiHeadHyperedgeTopology
    , hyperArity = HyperArityTernary
    , hyperConstituentCount = 3
    , hyperHeads =
        [ HematiteNamed
        , MagnetiteNamed
        , SilicateGangueNamed
        ]
    , hyperAnchorZ = HyperElementIron
    , hyperRole = OreIncidenceNamed
    , hyperKind = TernaryNamed
    }

-- | Scaffold trivial **hyper**edge (Og Z=118) — must fail-closed.
hyperedgeTrivialOganesson :: Hyperedge
hyperedgeTrivialOganesson =
  Hyperedge
    { hyperTopology = MultiHeadHyperedgeTopology
    , hyperArity = HyperArityBinary
    , hyperConstituentCount = 1
    , hyperHeads = []
    , hyperAnchorZ = HyperElementOganesson
    , hyperRole = GangueTailNamed
    , hyperKind = IncidenceNamed
    }

-- | **Hyper** incidence with level (level 0 = trivial **hyper**).
data HyperIncidence = HyperIncidence
  { hyperIncEdge :: Hyperedge
  , hyperIncLevel :: Int
  }
  deriving (Eq, Show)

-- | Named ternary L3 **hyper** incidence @ scaffold.
hyperIncidenceTernaryL3 :: HyperIncidence
hyperIncidenceTernaryL3 =
  HyperIncidence
    { hyperIncEdge = hyperedgeTernaryOre
    , hyperIncLevel = 3
    }

-- | Trivial L0 **hyper** incidence — must fail-closed.
hyperIncidenceTrivialL0 :: HyperIncidence
hyperIncidenceTrivialL0 =
  HyperIncidence
    { hyperIncEdge = hyperedgeTrivialOganesson
    , hyperIncLevel = 0
    }

-- | Whether a **hyper** incidence is non-trivial (level > 0, arity consistent).
isNontrivialHyperIncidence :: HyperIncidence -> Bool
isNontrivialHyperIncidence inc =
  hyperIncLevel inc > 0
    && hyperedgeArityConsistent (hyperIncEdge inc)

-- | Whether **hyper** element Z pins are valid IUPAC Z.
hyperIncElementZValid :: HyperIncidence -> Bool
hyperIncElementZValid inc =
  isValidIupacZ (hyperAnchorZ (hyperIncEdge inc))

-- | Occupied head count for a **hyper**edge.
hyperedgeOccupiedHeadCount :: Hyperedge -> Int
hyperedgeOccupiedHeadCount edge = length (hyperHeads edge)

-- | Whether **hyper**edge arity is consistent (multi-constituent **conservation**).
hyperedgeArityConsistent :: Hyperedge -> Bool
hyperedgeArityConsistent edge =
  let occupied = hyperedgeOccupiedHeadCount edge
      minCount = hyperedgeArityMinConstituentCount (hyperArity edge)
   in hyperConstituentCount edge >= minCount
        && occupied == hyperConstituentCount edge
        && hyperTopology edge == MultiHeadHyperedgeTopology

-- | Whether topology is **hyper**graph (not pairwise bond).
topologyIsHypergraph :: GraphTopologyKind -> Bool
topologyIsHypergraph topo =
  case topo of
    MultiHeadHyperedgeTopology -> True
    PairwiseBondTopology -> False

-- | **Hyper**graph scaffold wrapper.
data Hypergraph = Hypergraph
  { hypergraphTopology :: GraphTopologyKind
  , hypergraphEdge :: Hyperedge
  }
  deriving (Eq, Show)

-- | Scaffold ternary **hyper**graph @ GRAPH-03.
hypergraphScaffoldTernary :: Hypergraph
hypergraphScaffoldTernary =
  Hypergraph
    { hypergraphTopology = MultiHeadHyperedgeTopology
    , hypergraphEdge = hyperedgeTernaryOre
    }

-- | Whether **hyper**graph is **hyper** not bond @ scaffold.
isHypergraphNotBond :: Hypergraph -> Bool
isHypergraphNotBond hg =
  topologyIsHypergraph (hypergraphTopology hg)
    && hypergraphTopology hg /= PairwiseBondTopology
    && hyperedgeArityConsistent (hypergraphEdge hg)

-- | Verdict for a **hyper**edge close (fail-closed).
data HyperedgeVerdict
  = HyperedgeDesignOk
  | HyperedgeNamedOk
  | HyperedgeTrivialRefuse
  | HyperedgeGreenInventRefuse
  | HyperedgeProvedWithoutBarRefuse
  | HyperedgeArityInconsistentRefuse
  deriving (Eq, Show)

-- | Verdict for ternary incidence close (fail-closed).
data TernaryIncidenceVerdict
  = TernaryIncidenceDesignOk
  | TernaryIncidenceNamedOk
  | TernaryIncidenceGreenInventRefuse
  | TernaryIncidenceProvedWithoutBarRefuse
  deriving (Eq, Show)

-- | Evaluate a **hyper**edge under GRAPH-03 **conservation** bar (fail-closed).
evaluateHyperedge ::
  HyperConservationModality
  -> Hyperedge
  -> Bool
  -> Bool
  -> HyperedgeVerdict
evaluateHyperedge modality edge claimPhysicsGreen claimProved
  | claimPhysicsGreen = HyperedgeGreenInventRefuse
  | claimProved = HyperedgeProvedWithoutBarRefuse
  | not (hyperedgeArityConsistent edge) = HyperedgeArityInconsistentRefuse
  | hyperConstituentCount edge < hyperedgeArityMinConstituentCount (hyperArity edge) =
      HyperedgeTrivialRefuse
  | otherwise =
      case modality of
        HyperConservationUnwired -> HyperedgeNamedOk
        HyperConservationAssumed -> HyperedgeDesignOk
        HyperConservationSurrogate -> HyperedgeDesignOk
        HyperConservationProved -> HyperedgeProvedWithoutBarRefuse

-- | Evaluate ternary incidence under GRAPH-03 **conservation** bar (fail-closed).
evaluateTernaryIncidence ::
  HyperConservationModality
  -> HyperIncidence
  -> Bool
  -> Bool
  -> TernaryIncidenceVerdict
evaluateTernaryIncidence modality inc claimPhysicsGreen claimProved
  | claimPhysicsGreen = TernaryIncidenceGreenInventRefuse
  | claimProved = TernaryIncidenceProvedWithoutBarRefuse
  | not (isNontrivialHyperIncidence inc) = TernaryIncidenceDesignOk
  | otherwise =
      case modality of
        HyperConservationUnwired -> TernaryIncidenceNamedOk
        HyperConservationAssumed -> TernaryIncidenceDesignOk
        HyperConservationSurrogate -> TernaryIncidenceDesignOk
        HyperConservationProved -> TernaryIncidenceProvedWithoutBarRefuse
  where
    _ = inc

-- | **Hyper** incidence identity law cells tracked by GRAPH-03 (structure scaffold).
data IncidenceIdentityLaw
  = IncidenceIdentityConserved
  | NamedHyperOk
  | TrivialHyperRefused
  | GreenInventRefused
  deriving (Eq, Show)

incidenceIdentityLawAll :: [IncidenceIdentityLaw]
incidenceIdentityLawAll =
  [ IncidenceIdentityConserved
  , NamedHyperOk
  , TrivialHyperRefused
  , GreenInventRefused
  ]

incidenceIdentityLawCount :: Int
incidenceIdentityLawCount = length incidenceIdentityLawAll

-- | Verdict for GRAPH-03 **hyper** **conservation** promotion (fail-closed).
data HyperConservationVerdict
  = HyperDesignOk
  | HyperNamedOk
  | HyperTrivialRefuse
  | HyperGreenInventRefuse
  | HyperProvedWithoutBarRefuse
  | HyperArityInconsistentRefuse
  deriving (Eq, Show)

-- | Evaluate GRAPH-03 **hyper** **conservation** typing (fail-closed).
evaluateHyperConservation ::
  HyperConservationModality
  -> Hyperedge
  -> HyperIncidence
  -> Bool
  -> Bool
  -> HyperConservationVerdict
evaluateHyperConservation modality edge inc claimPhysicsGreen claimProved
  | claimPhysicsGreen = HyperGreenInventRefuse
  | claimProved = HyperProvedWithoutBarRefuse
  | otherwise =
      case evaluateHyperedge modality edge False False of
        HyperedgeArityInconsistentRefuse -> HyperArityInconsistentRefuse
        HyperedgeTrivialRefuse -> HyperTrivialRefuse
        HyperedgeGreenInventRefuse -> HyperGreenInventRefuse
        HyperedgeProvedWithoutBarRefuse -> HyperProvedWithoutBarRefuse
        HyperedgeNamedOk ->
          case evaluateTernaryIncidence modality inc False False of
            TernaryIncidenceNamedOk -> HyperNamedOk
            TernaryIncidenceGreenInventRefuse -> HyperGreenInventRefuse
            TernaryIncidenceProvedWithoutBarRefuse -> HyperProvedWithoutBarRefuse
            TernaryIncidenceDesignOk -> HyperDesignOk
        HyperedgeDesignOk -> HyperDesignOk

sampleNamedHyperedge :: Hyperedge
sampleNamedHyperedge = hyperedgeTernaryOre

sampleTrivialHyperedge :: Hyperedge
sampleTrivialHyperedge = hyperedgeTrivialOganesson

sampleTernaryIncidence :: HyperIncidence
sampleTernaryIncidence = hyperIncidenceTernaryL3

-- | Unwired **hyper** modality OK without thermo break.
unwiredDesignOk :: Bool
unwiredDesignOk =
  evaluateHyperConservation
    HyperConservationUnwired
    sampleNamedHyperedge
    sampleTernaryIncidence
    False
    False
    == HyperNamedOk

-- | Fe **hyper** anchor carries valid Z=26 pin.
feElementZValid :: Bool
feElementZValid =
  hyperIncElementZValid hyperIncidenceTernaryL3
    && hyperElementZNumeric (hyperAnchorZ (hyperIncEdge hyperIncidenceTernaryL3)) == 26

-- | Hematite constituent pin is named @ scaffold.
hematiteConstituentValid :: Bool
hematiteConstituentValid =
  HematiteNamed `elem` hyperHeads hyperedgeTernaryOre
    && hematiteNeGangue

-- | Z=118 Oganesson pin is valid IUPAC Z @ scaffold.
oganessonZValid :: Bool
oganessonZValid =
  isValidIupacZ HyperElementOganesson
    && hyperElementZNumeric HyperElementOganesson == iupacTableCardinality

-- | Hematite and silicate gangue are distinct @ scaffold (**conservation** identity).
hematiteNeGangue :: Bool
hematiteNeGangue = HematiteNamed /= SilicateGangueNamed

-- | Ternary **hyper**edge arity is consistent @ scaffold.
ternaryArityConsistent :: Bool
ternaryArityConsistent =
  hyperedgeArityConsistent hyperedgeTernaryOre
    && hyperArity hyperedgeTernaryOre == HyperArityTernary
    && hyperConstituentCount hyperedgeTernaryOre == 3
    && hyperedgeOccupiedHeadCount hyperedgeTernaryOre == 3

-- | Multi-constituent arity is named (ternary ≥ 3 heads).
multiConstituentNamed :: Bool
multiConstituentNamed =
  hyperedgeArityIsMultiConstituent HyperArityTernary
    && hyperedgeArityIsMultiConstituent HyperArityMultiConstituent
    && not (hyperedgeArityIsMultiConstituent HyperArityBinary)

-- | Named **hyper** incidence identity conserved: ternary heads + Fe Z pins stable.
namedHyperIncidenceIdentityConserved :: Bool
namedHyperIncidenceIdentityConserved =
  let inc = hyperIncidenceTernaryL3
      edge = hyperIncEdge inc
   in isNontrivialHyperIncidence inc
        && feElementZValid
        && hematiteConstituentValid
        && hematiteNeGangue
        && ternaryArityConsistent
        && evaluateHyperedge
          HyperConservationUnwired
          edge
          False
          False
          == HyperedgeNamedOk
        && hyperKind edge == TernaryNamed

-- | Ternary incidence named **hyper** edge is typed @ scaffold.
ternaryIncidenceNamedOk :: Bool
ternaryIncidenceNamedOk =
  let inc = hyperIncidenceTernaryL3
   in hyperIncLevel inc == 3
        && ternaryArityConsistent
        && evaluateTernaryIncidence
          HyperConservationUnwired
          inc
          False
          False
          == TernaryIncidenceNamedOk

-- | **Hyper** and ternary incidence roles are both named @ scaffold.
hyperAndTernaryIncidenceNamed :: Bool
hyperAndTernaryIncidenceNamed =
  namedHyperIncidenceIdentityConserved && ternaryIncidenceNamedOk

-- | Trivial **hyper** incidence is fail-closed.
trivialHyperFailClosed :: Bool
trivialHyperFailClosed =
  evaluateHyperedge
    HyperConservationUnwired
    sampleTrivialHyperedge
    False
    False
    == HyperedgeArityInconsistentRefuse
    && evaluateHyperConservation
      HyperConservationUnwired
      sampleTrivialHyperedge
      hyperIncidenceTrivialL0
      False
      False
      == HyperArityInconsistentRefuse

-- | GREEN invent on **hyper** **conservation** promotion is refused.
greenInventHyperRefuse :: Bool
greenInventHyperRefuse =
  evaluateHyperConservation
    HyperConservationUnwired
    sampleNamedHyperedge
    sampleTernaryIncidence
    True
    False
    == HyperGreenInventRefuse
    && evaluateHyperedge
      HyperConservationUnwired
      sampleNamedHyperedge
      True
      False
      == HyperedgeGreenInventRefuse

-- | Assumed **hyper** modality OK without thermo break (design scaffold).
assumedHyperDesignOk :: Bool
assumedHyperDesignOk =
  evaluateHyperConservation
    HyperConservationAssumed
    sampleNamedHyperedge
    sampleTernaryIncidence
    False
    False
    == HyperDesignOk

-- | Surrogate **hyper** modality OK without thermo break (design scaffold).
surrogateHyperDesignOk :: Bool
surrogateHyperDesignOk =
  evaluateHyperConservation
    HyperConservationSurrogate
    sampleNamedHyperedge
    sampleTernaryIncidence
    False
    False
    == HyperDesignOk

-- | Four-step GRAPH-03 **hyper** lattice scaffold pinned.
hyperLatticeScaffold :: Bool
hyperLatticeScaffold =
  hyperLatticeCount == 4
    && unwiredDesignOk
    && feElementZValid
    && hematiteConstituentValid
    && oganessonZValid
    && namedHyperIncidenceIdentityConserved
    && ternaryIncidenceNamedOk
    && hyperAndTernaryIncidenceNamed
    && hematiteNeGangue
    && ternaryArityConsistent
    && multiConstituentNamed
    && trivialHyperFailClosed
    && assumedHyperDesignOk
    && surrogateHyperDesignOk

-- | **Hyper** lattice is structure scaffold — not 118² GREEN periodic table.
hyperLatticeNotGreenTable :: Bool
hyperLatticeNotGreenTable =
  hyperLatticeCount == 4
    && hyperLatticeCount /= 118 * 118
    && hyperKindCount /= 118 * 118
    && hyperRoleCount /= 118 * 118

-- | Four **hyper** incidence identity law cells scaffold pinned.
incidenceIdentityLawsScaffold :: Bool
incidenceIdentityLawsScaffold =
  incidenceIdentityLawCount == 4
    && namedHyperIncidenceIdentityConserved
    && ternaryIncidenceNamedOk
    && hematiteNeGangue
    && ternaryArityConsistent
    && trivialHyperFailClosed
    && greenInventHyperRefuse

-- | **Hyper** law cells are structure scaffold — not 118² GREEN periodic table.
incidenceIdentityLawsNotGreenTable :: Bool
incidenceIdentityLawsNotGreenTable =
  incidenceIdentityLawsScaffold
    && incidenceIdentityLawCount /= 118 * 118
    && hyperElementZCount /= 118 * 118

-- | GRAPH-03 **hyper** **conservation** claims route to knowing / quantum fiber (not meso acting).
hyperKnowingFiberOk :: Bool
hyperKnowingFiberOk = True

-- | GRAPH-03 **hyper** invent refuse-closed scaffold witness.
graph03HyperInventRefuse :: Bool
graph03HyperInventRefuse = not graph03HyperProved

-- | **Hyper** lattice steps are concurrent Π_c — not XOR enum bucket.
hyperLatticeNotXor :: Bool
hyperLatticeNotXor =
  unwiredDesignOk
    && assumedHyperDesignOk
    && surrogateHyperDesignOk
    && namedHyperIncidenceIdentityConserved
    && ternaryIncidenceNamedOk
    && hematiteNeGangue
    && ternaryArityConsistent
    && trivialHyperFailClosed
    && greenInventHyperRefuse

-- | `petgraph` kernel is **not** forked into this cell.
petgraphKernelForked :: Bool
petgraphKernelForked = False

-- | **Hyper** morphisms are multi-head incidence — not bond/reaction GRAPH-01 edges.
hyperNeBond :: Bool
hyperNeBond =
  oreHypergraphAuthority
    /= "umst/umst-chem/src/bond_reaction_graph.rs"
    && hyperKindAll /= []
    && hyperRoleAll /= []
    && isHypergraphNotBond hypergraphScaffoldTernary
    && not (topologyIsHypergraph PairwiseBondTopology)
    && not petgraphKernelForked

-- | GRAPH-03 **hyper** proved (always false on this Unwired cell).
graph03HyperProved :: Bool
graph03HyperProved = False

-- | One axiom framing: second law + **conservation** for GRAPH-03 **hyper** scaffold.
hyperConservationFraming :: String
hyperConservationFraming =
  "second_law_conservation_hyper_one_axiom"

-- | Single design axiom: second law + **conservation** GRAPH-03 **hyper** (not second axiom).
hyperConservationAxiom :: Bool
hyperConservationAxiom =
  hyperLatticeScaffold
    && hyperLatticeNotGreenTable
    && incidenceIdentityLawsScaffold
    && incidenceIdentityLawsNotGreenTable
    && hyperKnowingFiberOk
    && feElementZValid
    && hematiteConstituentValid
    && oganessonZValid
    && namedHyperIncidenceIdentityConserved
    && ternaryIncidenceNamedOk
    && hyperAndTernaryIncidenceNamed
    && hematiteNeGangue
    && ternaryArityConsistent
    && multiConstituentNamed
    && trivialHyperFailClosed
    && greenInventHyperRefuse
    && graph03HyperInventRefuse
    && hyperLatticeNotXor
    && hyperNeBond
    && not graph03HyperProved
    && not petgraphKernelForked
    && hyperConservationFraming
      == "second_law_conservation_hyper_one_axiom"

hyperConservationNamed :: String
hyperConservationNamed =
  "hyperConservation: HyperConservationModality Unwired Assumed Proved Surrogate four-step lattice graph03HyperProved false evaluateHyperedge evaluateTernaryIncidence named hyper multi-constituent incidence identity conserved ternary arity hematite ne gangue Fe Z=26 Og Z=118 trivial hyper fail-closed hyper ne bond no petgraph fork second law conservation one axiom"

-- | Upstream GRAPH-03 ore **hyper**graph authority (cited, not forked).
oreHypergraphAuthority :: String
oreHypergraphAuthority = "umst/umst-chem/src/ore_hypergraph.rs"

-- | L0 GRAPH-03 **hyper** scaffold authority (crosswalk).
chemL0Graph03Authority :: String
chemL0Graph03Authority = "CHEM-L0-GRAPH-03"

hyperConservationCellId :: String
hyperConservationCellId = "CHEM-FORMAL-Q-HS-HYPER-CONSERVATION"

-- | Non-claim fence — GRAPH-03 **hyper** **conservation** Unwired ≠ Proved GREEN.
hyperConservationNonClaim :: String
hyperConservationNonClaim =
  "CHEM-FORMAL-Q-HS-HYPER-CONSERVATION HyperConservationModality Unwired Assumed Proved Surrogate four-step lattice graph03HyperProved false evaluateHyperedge evaluateTernaryIncidence named hyper multi-constituent incidence identity conserved ternary arity hematite ne gangue Fe Z=26 Og Z=118 trivial hyper fail-closed hyper ne bond no petgraph fork Unwired one axiom second law conservation not 118 squared GREEN table not meso acting not physics GREEN not production_wired"

-- | Physics GREEN is unauthorized on the knowing GRAPH-03 **hyper** **conservation** scaffold.
hyperConservationPhysicsGreenAuthorized :: Bool
hyperConservationPhysicsGreenAuthorized = False

hyperConservationPhysicsGreenFalse :: Bool
hyperConservationPhysicsGreenFalse =
  not hyperConservationPhysicsGreenAuthorized

hyperConservationModalityUnwired :: Bool
hyperConservationModalityUnwired =
  hyperConservationModalityCurrent == HyperConservationUnwired
