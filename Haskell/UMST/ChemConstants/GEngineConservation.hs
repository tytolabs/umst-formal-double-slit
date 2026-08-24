-- SPDX-FileCopyrightText: 2026 Santosh Prabhu Shenbagamoorthy and Santhosh Shyamsundar
-- SPDX-License-Identifier: MIT

{-|
Module      : UMST.ChemConstants.GEngineConservation
Description : **G-engine** **conservation** on the knowing fiber (Q lattice)
Copyright   : (c) UMST Project, 2026

**G-engine** **conservation**: constitutive G-engine may **sort** not **mint** constants —
sorts using the existing SI/occupancy/derived-morphism sheaf and Thermo_n G(T,P,x) type;
refuses k, R, ε₀ mint and live measured G invent. Named G-engine identity conserved under
honest scaffold; trivial XOR, parallel G axiom, constants mint, formation-zero ≠ G, T/P
float-pin smuggle, and GREEN invent fail-closed. G-engine **conservation** laws are
structure witnesses only (@gEngineConservationProved@ = False). No SpeciesId fork.

* @GEngineConservationModality@ = Unwired / Assumed / Proved / Surrogate — four-step lattice, not 118² GREEN table.
* @evaluateGEngineBundle@ — named G-engine identity conserved; XOR mutual-exclusivity refuse-closed.
* @evaluateGEngineConservation@ — concurrent Π_c **conservation** typed @ scaffold; Present ≥2 is **product** not XOR.
* **One** design axiom (@gEngineConservationAxiom@): second law + **conservation** (not 26th axiom).
* @physics_green@ stays false.

Haskell mirror of **G-engine** **conservation** on the quantum / knowing fiber.
Cell: @CHEM-FORMAL-Q-HS-G-ENGINE-CONSERVATION@.
INT: umst/umst-chem/src/thermo_g.rs (read-only cite).
L0: umst/umst-chem/src/l0_tables/shared.rs (read-only cite).
WAVE100: not wired in cabal / lib.rs / eos.rs / nano.
-}
module UMST.ChemConstants.GEngineConservation
  ( GEngineConservationModality (..)
  , gEngineConservationModalityCurrent
  , gEngineLatticeAll
  , gEngineLatticeCount
  , class13GEnginePatternIndex
  , GEngineChannelSlot (..)
  , gEngineChannelSlotAll
  , gEngineChannelSlotCount
  , GEngineProductChannel (..)
  , gEngineProductChannelAll
  , gEngineProductChannelCount
  , gEngineProductChannelIndex
  , GEngineConcurrentBundle (..)
  , gEngineConcurrentBundleUnwired
  , gEngineConcurrentBundleWithChannel
  , gEngineConcurrentBundleWithPresent
  , gEngineConcurrentBundleChannelAt
  , gEngineConcurrentBundleHolds
  , gEngineConcurrentBundlePresentCount
  , gEngineConcurrentBundleIsConcurrentProduct
  , gEngineSortNotMintWitness
  , GEngineXorPosture (..)
  , gEngineXorPostureExclusive
  , gEngineXorPostureConcurrent
  , GEngineConservationVerdict (..)
  , GEngineXorVerdict (..)
  , evaluateGEngineBundle
  , evaluateGEngineXor
  , evaluateGEngineConservation
  , GEngineConservationLaw (..)
  , gEngineConservationLawAll
  , gEngineConservationLawCount
  , sampleGEngineSortNotMintBundle
  , sampleXorExclusiveBundle
  , sampleTrivialUnwiredBundle
  , unwiredDesignOk
  , gEngineSortNotMintConcurrentOk
  , class13GEnginePatternIndexOk
  , concurrentProductNotXorOk
  , xorMutuallyExclusiveRefuse
  , greenInventGEngineRefuse
  , parallelGEngineAxiomRefuse
  , constantsMintRefuse
  , sortNotMintNotAxiomRefuse
  , tpFloatPinRefuse
  , assumedGEngineDesignOk
  , surrogateGEngineDesignOk
  , gEngineLatticeScaffold
  , gEngineLatticeNotGreenTable
  , gEngineConservationLawsScaffold
  , gEngineConservationLawsNotGreenTable
  , gEngineKnowingFiberOk
  , gEngineConservationInventRefuse
  , gEngineLatticeNotXor
  , gEngineConservationProved
  , gEngineConservationNeSpeciesId
  , speciesIdForked
  , ironAtomicNumberZWitness
  , copperAtomicNumberZWitness
  , gEngineConservationFraming
  , gEngineConservationAxiom
  , gEngineConservationNamed
  , gEngineConservationAuthority
  , chemL0GEngineAuthority
  , thermoConservationAuthority
  , engineRefusesNewSiAuthority
  , siSheafAuthority
  , edgeGEngineAuthority
  , temperatureGraphFunctionAuthority
  , pressureGraphFunctionAuthority
  , gEngineConservationCellId
  , gEngineConservationNonClaim
  , gEngineConservationPhysicsGreenAuthorized
  , gEngineConservationPhysicsGreenFalse
  , gEngineConservationModalityUnwired
  ) where

-- | IUPAC periodic-table cardinality (Z=1..118) — not g-engine GREEN table.
iupacTableCardinality :: Int
iupacTableCardinality = 118

-- | North-star class-13 (`g_engine`) constitutive chart pattern index.
class13GEnginePatternIndex :: Int
class13GEnginePatternIndex = 13

-- | Iron Z=26 — thermo witness element pin.
ironAtomicNumberZWitness :: Int
ironAtomicNumberZWitness = 26

-- | Copper Z=29 — thermo witness element pin.
copperAtomicNumberZWitness :: Int
copperAtomicNumberZWitness = 29

-- | Design **G-engine** modality for class-14 **conservation** claims.
data GEngineConservationModality
  = GEngineConservationUnwired
  | GEngineConservationAssumed
  | GEngineConservationProved
  | GEngineConservationSurrogate
  deriving (Eq, Show)

-- | Current scaffold **G-engine** modality — always Unwired on this cell.
gEngineConservationModalityCurrent :: GEngineConservationModality
gEngineConservationModalityCurrent =
  GEngineConservationUnwired

-- | All G-engine **conservation** lattice steps in stable order.
gEngineLatticeAll :: [GEngineConservationModality]
gEngineLatticeAll =
  [ GEngineConservationUnwired
  , GEngineConservationAssumed
  , GEngineConservationProved
  , GEngineConservationSurrogate
  ]

gEngineLatticeCount :: Int
gEngineLatticeCount = length gEngineLatticeAll

-- | Catalysis product channel slot — concurrent **product** factor, not XOR bucket.
data GEngineChannelSlot
  = GEngineSlotUnwired
  | GEngineSlotAbsent
  | GEngineSlotPresent
  deriving (Eq, Show)

-- | All g-engine channel slots in stable order.
gEngineChannelSlotAll :: [GEngineChannelSlot]
gEngineChannelSlotAll =
  [ GEngineSlotUnwired
  , GEngineSlotAbsent
  , GEngineSlotPresent
  ]

gEngineChannelSlotCount :: Int
gEngineChannelSlotCount = length gEngineChannelSlotAll

-- | Named Interact restriction / barrier↓ / catalyst-not-consumed product channels.
data GEngineProductChannel
  = GEngineSortExistingSheaf
  | ConstantsNotMinted
  | ThermoGTypeConserved
  deriving (Eq, Show)

-- | All g-engine product channels in north-star stable order.
gEngineProductChannelAll :: [GEngineProductChannel]
gEngineProductChannelAll =
  [ GEngineSortExistingSheaf
  , ConstantsNotMinted
  , ThermoGTypeConserved
  ]

gEngineProductChannelCount :: Int
gEngineProductChannelCount = length gEngineProductChannelAll

-- | Stable channel index for a g-engine product channel (0..2).
gEngineProductChannelIndex :: GEngineProductChannel -> Int
gEngineProductChannelIndex channel =
  case channel of
    GEngineSortExistingSheaf -> 0
    ConstantsNotMinted -> 1
    ThermoGTypeConserved -> 2

-- | G-engine g-engine concurrent **product** bundle (north-star §3).
data GEngineConcurrentBundle = GEngineConcurrentBundle
  { gEngineClassPresent :: Bool
  , gEngineChannelSlots :: [GEngineChannelSlot]
  }
  deriving (Eq, Show)

-- | All channels Unwired — honest scaffold baseline.
gEngineConcurrentBundleUnwired :: GEngineConcurrentBundle
gEngineConcurrentBundleUnwired =
  GEngineConcurrentBundle
    False
    (replicate gEngineProductChannelCount GEngineSlotUnwired)

-- | Set one channel at index; leaves others unchanged.
gEngineConcurrentBundleWithChannel ::
  Int -> GEngineChannelSlot -> GEngineConcurrentBundle -> GEngineConcurrentBundle
gEngineConcurrentBundleWithChannel idx slot bundle =
  let slots = gEngineChannelSlots bundle
      before = take idx slots
      after = drop (idx + 1) slots
      current = if idx >= 0 && idx < length slots then slot else slots !! idx
   in GEngineConcurrentBundle
        (gEngineClassPresent bundle)
        (before ++ [current] ++ after)

-- | Mark channel index Present on the g-engine **product**.
gEngineConcurrentBundleWithPresent ::
  Int -> GEngineConcurrentBundle -> GEngineConcurrentBundle
gEngineConcurrentBundleWithPresent idx bundle =
  gEngineConcurrentBundleWithChannel idx GEngineSlotPresent bundle

-- | Read channel slot at index (0..2).
gEngineConcurrentBundleChannelAt ::
  Int -> GEngineConcurrentBundle -> Maybe GEngineChannelSlot
gEngineConcurrentBundleChannelAt idx bundle =
  let slots = gEngineChannelSlots bundle
   in if idx >= 0 && idx < length slots
        then Just (slots !! idx)
        else Nothing

-- | Whether channel index is Present on the concurrent **product**.
gEngineConcurrentBundleHolds :: Int -> GEngineConcurrentBundle -> Bool
gEngineConcurrentBundleHolds idx bundle =
  case gEngineConcurrentBundleChannelAt idx bundle of
    Just GEngineSlotPresent -> True
    _ -> False

-- | Count of Present channels (may exceed 1 — concurrent **product**).
gEngineConcurrentBundlePresentCount :: GEngineConcurrentBundle -> Int
gEngineConcurrentBundlePresentCount bundle =
  length (filter (== GEngineSlotPresent) (gEngineChannelSlots bundle))

-- | Whether bundle demonstrates concurrent **product** (≥2 Present channels).
gEngineConcurrentBundleIsConcurrentProduct :: GEngineConcurrentBundle -> Bool
gEngineConcurrentBundleIsConcurrentProduct bundle =
  gEngineConcurrentBundlePresentCount bundle >= 2

-- | Catalysis witness: Interact restriction (0) + barrier↓ (1) + not consumed (2) concurrent on G-engine.
gEngineSortNotMintWitness :: GEngineConcurrentBundle
gEngineSortNotMintWitness =
  gEngineConcurrentBundleWithPresent 2
    (gEngineConcurrentBundleWithPresent 1
      (gEngineConcurrentBundleWithPresent 0
        (GEngineConcurrentBundle True
          (replicate gEngineProductChannelCount GEngineSlotUnwired))))

-- | XOR posture — mutual exclusivity scaffold defect (must refuse).
data GEngineXorPosture
  = GEngineXorExclusive
  | GEngineXorConcurrent
  deriving (Eq, Show)

-- | XOR mutual-exclusivity posture — must fail-closed.
gEngineXorPostureExclusive :: GEngineXorPosture
gEngineXorPostureExclusive = GEngineXorExclusive

-- | Concurrent Π_c posture — honest **product** scaffold.
gEngineXorPostureConcurrent :: GEngineXorPosture
gEngineXorPostureConcurrent = GEngineXorConcurrent

-- | Verdict for g-engine **conservation** close (fail-closed).
data GEngineConservationVerdict
  = GEngineConservationDesignOk
  | GEngineConservationNamedOk
  | GEngineConservationTrivialRefuse
  | GEngineConservationGreenInventRefuse
  | GEngineConservationProvedWithoutBarRefuse
  | GEngineConservationXorRefuse
  deriving (Eq, Show)

-- | Verdict for XOR posture close (fail-closed).
data GEngineXorVerdict
  = GEngineXorDesignOk
  | GEngineXorNamedOk
  | GEngineXorGreenInventRefuse
  | GEngineXorProvedWithoutBarRefuse
  | GEngineXorMutuallyExclusiveRefuse
  deriving (Eq, Show)

-- | Evaluate a g-engine bundle under class-14 **conservation** bar (fail-closed).
evaluateGEngineBundle ::
  GEngineConservationModality
  -> GEngineConcurrentBundle
  -> Bool
  -> Bool
  -> GEngineConservationVerdict
evaluateGEngineBundle modality bundle claimPhysicsGreen claimProved
  | claimPhysicsGreen = GEngineConservationGreenInventRefuse
  | claimProved = GEngineConservationProvedWithoutBarRefuse
  | length (gEngineChannelSlots bundle) /= gEngineProductChannelCount =
      GEngineConservationTrivialRefuse
  | otherwise =
      case modality of
        GEngineConservationUnwired ->
          if gEngineConcurrentBundleIsConcurrentProduct bundle
            then GEngineConservationNamedOk
            else GEngineConservationDesignOk
        GEngineConservationAssumed -> GEngineConservationDesignOk
        GEngineConservationSurrogate -> GEngineConservationDesignOk
        GEngineConservationProved -> GEngineConservationProvedWithoutBarRefuse

-- | Evaluate XOR posture under class-14 **conservation** bar (fail-closed).
evaluateGEngineXor ::
  GEngineConservationModality
  -> GEngineXorPosture
  -> Bool
  -> Bool
  -> GEngineXorVerdict
evaluateGEngineXor modality posture claimPhysicsGreen claimProved
  | claimPhysicsGreen = GEngineXorGreenInventRefuse
  | claimProved = GEngineXorProvedWithoutBarRefuse
  | posture == GEngineXorExclusive = GEngineXorMutuallyExclusiveRefuse
  | otherwise =
      case modality of
        GEngineConservationUnwired -> GEngineXorNamedOk
        GEngineConservationAssumed -> GEngineXorDesignOk
        GEngineConservationSurrogate -> GEngineXorDesignOk
        GEngineConservationProved -> GEngineXorProvedWithoutBarRefuse

-- | **Catalysis** identity law cells tracked by class-14 **conservation** (structure scaffold).
data GEngineConservationLaw
  = GEngineConservationConserved
  | NamedGEngineConservationOk
  | TrivialGEngineRefused
  | GreenInventGEngineRefused
  deriving (Eq, Show)

gEngineConservationLawAll :: [GEngineConservationLaw]
gEngineConservationLawAll =
  [ GEngineConservationConserved
  , NamedGEngineConservationOk
  , TrivialGEngineRefused
  , GreenInventGEngineRefused
  ]

gEngineConservationLawCount :: Int
gEngineConservationLawCount = length gEngineConservationLawAll

-- | Evaluate G-engine **conservation** **conservation** typing (fail-closed).
evaluateGEngineConservation ::
  GEngineConservationModality
  -> GEngineConcurrentBundle
  -> GEngineXorPosture
  -> Bool
  -> Bool
  -> GEngineConservationVerdict
evaluateGEngineConservation modality bundle posture claimPhysicsGreen claimProved
  | claimPhysicsGreen = GEngineConservationGreenInventRefuse
  | claimProved = GEngineConservationProvedWithoutBarRefuse
  | otherwise =
      case evaluateGEngineXor modality posture False False of
        GEngineXorMutuallyExclusiveRefuse -> GEngineConservationXorRefuse
        GEngineXorGreenInventRefuse -> GEngineConservationGreenInventRefuse
        GEngineXorProvedWithoutBarRefuse -> GEngineConservationProvedWithoutBarRefuse
        _ ->
          case evaluateGEngineBundle modality bundle False False of
            GEngineConservationNamedOk -> GEngineConservationNamedOk
            GEngineConservationGreenInventRefuse -> GEngineConservationGreenInventRefuse
            GEngineConservationProvedWithoutBarRefuse -> GEngineConservationProvedWithoutBarRefuse
            GEngineConservationTrivialRefuse -> GEngineConservationTrivialRefuse
            GEngineConservationXorRefuse -> GEngineConservationXorRefuse
            GEngineConservationDesignOk -> GEngineConservationDesignOk

sampleGEngineSortNotMintBundle :: GEngineConcurrentBundle
sampleGEngineSortNotMintBundle = gEngineSortNotMintWitness

sampleXorExclusiveBundle :: GEngineConcurrentBundle
sampleXorExclusiveBundle = gEngineConcurrentBundleUnwired

sampleTrivialUnwiredBundle :: GEngineConcurrentBundle
sampleTrivialUnwiredBundle = gEngineConcurrentBundleUnwired

-- | Unwired **G-engine** modality OK without thermo break.
unwiredDesignOk :: Bool
unwiredDesignOk =
  evaluateGEngineConservation
    GEngineConservationUnwired
    sampleGEngineSortNotMintBundle
    gEngineXorPostureConcurrent
    False
    False
    == GEngineConservationNamedOk

-- | Catalysis witness: Interact restriction + barrier↓ + catalyst-not-consumed concurrent Π_c on G-engine.
gEngineSortNotMintConcurrentOk :: Bool
gEngineSortNotMintConcurrentOk =
  let bundle = gEngineSortNotMintWitness
   in gEngineClassPresent bundle
        && gEngineConcurrentBundleHolds 0 bundle
        && gEngineConcurrentBundleHolds 1 bundle
        && gEngineConcurrentBundleHolds 2 bundle
        && gEngineConcurrentBundlePresentCount bundle == 3
        && gEngineConcurrentBundleIsConcurrentProduct bundle
        && ironAtomicNumberZWitness == 26
        && copperAtomicNumberZWitness == 29
        && class13GEnginePatternIndex == 13

-- | G-engine g-engine pattern index pinned @ scaffold.
class13GEnginePatternIndexOk :: Bool
class13GEnginePatternIndexOk =
  class13GEnginePatternIndex == 13
    && gEngineProductChannelCount == 3
    && length (gEngineChannelSlots gEngineConcurrentBundleUnwired) == 3

-- | Concurrent **product** Π_c — ≥2 Present is **product** not XOR.
concurrentProductNotXorOk :: Bool
concurrentProductNotXorOk =
  gEngineConcurrentBundleIsConcurrentProduct gEngineSortNotMintWitness
    && gEngineConcurrentBundlePresentCount gEngineSortNotMintWitness >= 2
    && gEngineConcurrentBundlePresentCount gEngineSortNotMintWitness == 3

-- | XOR mutually-exclusive posture is fail-closed.
xorMutuallyExclusiveRefuse :: Bool
xorMutuallyExclusiveRefuse =
  evaluateGEngineXor
    GEngineConservationUnwired
    gEngineXorPostureExclusive
    False
    False
    == GEngineXorMutuallyExclusiveRefuse
    && evaluateGEngineConservation
      GEngineConservationUnwired
      sampleGEngineSortNotMintBundle
      gEngineXorPostureExclusive
      False
      False
      == GEngineConservationXorRefuse

-- | GREEN invent on **G-engine** **conservation** promotion is refused.
greenInventGEngineRefuse :: Bool
greenInventGEngineRefuse =
  evaluateGEngineConservation
    GEngineConservationUnwired
    sampleGEngineSortNotMintBundle
    gEngineXorPostureConcurrent
    True
    False
    == GEngineConservationGreenInventRefuse
    && evaluateGEngineBundle
      GEngineConservationUnwired
      sampleGEngineSortNotMintBundle
      True
      False
      == GEngineConservationGreenInventRefuse

-- | Parallel g-engine axiom (26th law) mint is refused — second law + conservation only.
parallelGEngineAxiomRefuse :: Bool
parallelGEngineAxiomRefuse =
  gEngineConservationAuthority
    == "umst/umst-chem/src/thermo_g.rs"
    && gEngineConservationProved == False
    && not (gEngineConservationAuthority == "26th_g_engine_axiom")
    && gEngineConservationFraming
      /= "parallel_g_engine_axiom_not_second_law"
    && chemL0GEngineAuthority
      == "umst/umst-chem/src/l0_tables/shared.rs"

-- | Catalyst consumed in net reaction is refused — conservation posture mandatory.
constantsMintRefuse :: Bool
constantsMintRefuse =
  parallelGEngineAxiomRefuse
    && gEngineConservationFraming
      /= "g_engine_constants_mint_in_net_sort"
    && edgeGEngineAuthority
      == "umst/umst-chem/src/thermo_g.rs"
    && engineRefusesNewSiAuthority
      == "umst/umst-chem/src/x_rows/engine_refuses_new_si.rs"
    && siSheafAuthority
      == "umst/umst-chem/src/si_sheaf.rs"
    && class13GEnginePatternIndex == 13

-- | Catalysis is Interact restriction — not a parallel g-engine axiom.
sortNotMintNotAxiomRefuse :: Bool
sortNotMintNotAxiomRefuse =
  constantsMintRefuse
    && gEngineConservationFraming
      /= "g_engine_axiom_not_sort_not_mint"
    && class13GEnginePatternIndex == 13
    && gEngineConcurrentBundleIsConcurrentProduct gEngineSortNotMintWitness

-- | T/P graph functions on Interact graph — refuse bare float-pin smuggle on g-engine scaffold.
tpFloatPinRefuse :: Bool
tpFloatPinRefuse =
  sortNotMintNotAxiomRefuse
    && gEngineConservationFraming
      /= "tp_bare_float_pin_on_g_engine"
    && temperatureGraphFunctionAuthority
      == "umst/umst-chem/src/temperature_is_graph_function.rs"
    && pressureGraphFunctionAuthority
      == "umst/umst-chem/src/pressure_is_graph_function.rs"
    && class13GEnginePatternIndex == 13

-- | Assumed **G-engine** modality OK without thermo break (design scaffold).
assumedGEngineDesignOk :: Bool
assumedGEngineDesignOk =
  evaluateGEngineConservation
    GEngineConservationAssumed
    sampleGEngineSortNotMintBundle
    gEngineXorPostureConcurrent
    False
    False
    == GEngineConservationDesignOk

-- | Surrogate **G-engine** modality OK without thermo break (design scaffold).
surrogateGEngineDesignOk :: Bool
surrogateGEngineDesignOk =
  evaluateGEngineConservation
    GEngineConservationSurrogate
    sampleGEngineSortNotMintBundle
    gEngineXorPostureConcurrent
    False
    False
    == GEngineConservationDesignOk

-- | Four-step G-engine **conservation** lattice scaffold pinned.
gEngineLatticeScaffold :: Bool
gEngineLatticeScaffold =
  gEngineLatticeCount == 4
    && unwiredDesignOk
    && class13GEnginePatternIndexOk
    && gEngineSortNotMintConcurrentOk
    && concurrentProductNotXorOk
    && xorMutuallyExclusiveRefuse
    && assumedGEngineDesignOk
    && surrogateGEngineDesignOk
    && parallelGEngineAxiomRefuse
    && constantsMintRefuse
    && sortNotMintNotAxiomRefuse
    && tpFloatPinRefuse

-- | **Catalysis** lattice is structure scaffold — not 118² GREEN periodic table.
gEngineLatticeNotGreenTable :: Bool
gEngineLatticeNotGreenTable =
  gEngineLatticeCount == 4
    && gEngineLatticeCount /= iupacTableCardinality * iupacTableCardinality
    && gEngineProductChannelCount /= iupacTableCardinality * iupacTableCardinality
    && gEngineChannelSlotCount /= iupacTableCardinality * iupacTableCardinality

-- | Four **G-engine** identity law cells scaffold pinned.
gEngineConservationLawsScaffold :: Bool
gEngineConservationLawsScaffold =
  gEngineConservationLawCount == 4
    && gEngineSortNotMintConcurrentOk
    && concurrentProductNotXorOk
    && xorMutuallyExclusiveRefuse
    && greenInventGEngineRefuse
    && parallelGEngineAxiomRefuse
    && constantsMintRefuse
    && sortNotMintNotAxiomRefuse
    && tpFloatPinRefuse

-- | **Catalysis** law cells are structure scaffold — not 118² GREEN periodic table.
gEngineConservationLawsNotGreenTable :: Bool
gEngineConservationLawsNotGreenTable =
  gEngineConservationLawsScaffold
    && gEngineConservationLawCount /= 118 * 118
    && gEngineProductChannelCount /= 118 * 118

-- | G-engine **G-engine** **conservation** claims route to knowing / quantum fiber (not meso acting).
gEngineKnowingFiberOk :: Bool
gEngineKnowingFiberOk = True

-- | G-engine **G-engine** invent refuse-closed scaffold witness.
gEngineConservationInventRefuse :: Bool
gEngineConservationInventRefuse =
  not gEngineConservationProved

-- | **Catalysis** lattice steps are concurrent Π_c — not XOR enum bucket.
gEngineLatticeNotXor :: Bool
gEngineLatticeNotXor =
  unwiredDesignOk
    && assumedGEngineDesignOk
    && surrogateGEngineDesignOk
    && gEngineSortNotMintConcurrentOk
    && concurrentProductNotXorOk
    && xorMutuallyExclusiveRefuse
    && greenInventGEngineRefuse

-- | G-engine **G-engine** proved (always false on this Unwired cell).
gEngineConservationProved :: Bool
gEngineConservationProved = False

-- | `SpeciesId` is **not** forked into this cell.
speciesIdForked :: Bool
speciesIdForked = False

-- | **Catalysis** morphisms are class-14 neighbor channels — not SpeciesId tag mint.
gEngineConservationNeSpeciesId :: Bool
gEngineConservationNeSpeciesId =
  gEngineConservationAuthority
    /= "umst/umst-chem/src/species_id.rs"
    && gEngineProductChannelAll /= []
    && gEngineConcurrentBundleIsConcurrentProduct gEngineSortNotMintWitness
    && not speciesIdForked

-- | One axiom framing: second law + **conservation** for G-engine **conservation** scaffold.
gEngineConservationFraming :: String
gEngineConservationFraming =
  "second_law_conservation_g_engine_sort_not_mint_one_axiom"

-- | Single design axiom: second law + **conservation** class-14 g-engine (not 26th axiom).
gEngineConservationAxiom :: Bool
gEngineConservationAxiom =
  gEngineLatticeScaffold
    && gEngineLatticeNotGreenTable
    && gEngineConservationLawsScaffold
    && gEngineConservationLawsNotGreenTable
    && gEngineKnowingFiberOk
    && class13GEnginePatternIndexOk
    && gEngineSortNotMintConcurrentOk
    && concurrentProductNotXorOk
    && xorMutuallyExclusiveRefuse
    && greenInventGEngineRefuse
    && parallelGEngineAxiomRefuse
    && constantsMintRefuse
    && sortNotMintNotAxiomRefuse
    && tpFloatPinRefuse
    && gEngineConservationInventRefuse
    && gEngineLatticeNotXor
    && gEngineConservationNeSpeciesId
    && not gEngineConservationProved
    && not speciesIdForked
    && gEngineConservationFraming
      == "second_law_conservation_g_engine_sort_not_mint_one_axiom"

gEngineConservationNamed :: String
gEngineConservationNamed =
  "gEngineConservation: GEngineConservationModality Unwired Assumed Proved Surrogate four-step lattice gEngineConservationProved false evaluateGEngineBundle evaluateGEngineConservation named G-engine sort existing sheaf constants not minted Thermo_n G type concurrent product identity conserved present ge 2 product not XOR sort not mint witness concurrent xor mutually exclusive refuse parallel g engine axiom refuse constants mint refuse sort not mint not axiom refuse tp float pin refuse g engine ne SpeciesId fork second law conservation one axiom"

-- | Upstream INT g-engine **conservation** authority (cited read-only, not forked).
gEngineConservationAuthority :: String
gEngineConservationAuthority =
  "umst/umst-chem/src/thermo_g.rs"

-- | L0 class-14 g-engine table authority (crosswalk).
chemL0GEngineAuthority :: String
chemL0GEngineAuthority =
  "umst/umst-chem/src/l0_tables/shared.rs"

-- | PatternBundle product conservation authority (concurrent Π_c crosswalk).
thermoConservationAuthority :: String
thermoConservationAuthority =
  "umst/umst-formal-double-slit/Haskell/UMST/ChemConstants/ThermoConservation.hs"

-- | Interact restriction authority (g-engine as Interact restriction — not axiom).
engineRefusesNewSiAuthority :: String
engineRefusesNewSiAuthority = "umst/umst-chem/src/x_rows/engine_refuses_new_si.rs"

-- | Kleisli Interact authority (composition carrier — not folklore list).
siSheafAuthority :: String
siSheafAuthority = "umst/umst-chem/src/si_sheaf.rs"

-- | L0 edge g-engine authority (barrier↓ morphism — not proved on this cell).
edgeGEngineAuthority :: String
edgeGEngineAuthority = "umst/umst-chem/src/thermo_g.rs"

-- | Interact-graph temperature function authority (v14 T as graph function).
temperatureGraphFunctionAuthority :: String
temperatureGraphFunctionAuthority =
  "umst/umst-chem/src/temperature_is_graph_function.rs"

-- | Interact-graph pressure function authority (v14 P as graph function).
pressureGraphFunctionAuthority :: String
pressureGraphFunctionAuthority =
  "umst/umst-chem/src/pressure_is_graph_function.rs"

gEngineConservationCellId :: String
gEngineConservationCellId =
  "CHEM-FORMAL-Q-HS-G-ENGINE-CONSERVATION"

-- | Non-claim fence — G-engine **conservation** **conservation** Unwired ≠ Proved GREEN.
gEngineConservationNonClaim :: String
gEngineConservationNonClaim =
  "CHEM-FORMAL-Q-HS-G-ENGINE-CONSERVATION GEngineConservationModality Unwired Assumed Proved Surrogate four-step lattice gEngineConservationProved false evaluateGEngineBundle evaluateGEngineConservation named G-engine sort not mint constants existing SI occupancy derived morphism sheaf Thermo_n G type concurrent product identity conserved present ge 2 product not XOR sort not mint witness concurrent xor mutually exclusive refuse parallel g engine axiom refuse constants mint refuse sort not mint not axiom refuse tp float pin refuse g engine ne SpeciesId Unwired one axiom second law conservation not 118 squared GREEN table not meso acting not physics GREEN not production_wired"

-- | Physics GREEN is unauthorized on the knowing G-engine **conservation** **conservation** scaffold.
gEngineConservationPhysicsGreenAuthorized :: Bool
gEngineConservationPhysicsGreenAuthorized = False

gEngineConservationPhysicsGreenFalse :: Bool
gEngineConservationPhysicsGreenFalse =
  not gEngineConservationPhysicsGreenAuthorized

gEngineConservationModalityUnwired :: Bool
gEngineConservationModalityUnwired =
  gEngineConservationModalityCurrent == GEngineConservationUnwired
