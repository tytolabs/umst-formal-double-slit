-- SPDX-FileCopyrightText: 2026 Santosh Prabhu Shenbagamoorthy and Santhosh Shyamsundar
-- SPDX-License-Identifier: MIT

{-|
Module      : UrgeKnowing.PersistVsOccupancy
Description : PersistVsOccupancy — §12.7 persist Hilbert ≠ occupancy Hilbert
Copyright   : (c) UMST Project, 2026

§12.7 @persist_vs_occupancy@ — persist Hilbert (acting) distinct from occupancy
Hilbert (knowing). homolog relates fibers — homolog ≠ copy. Positive fuse refusal.
Mirrors Agda @UrgeKnowing.PersistVsOccupancy@, Coq @PersistVsOccupancy.v@, and
Rust @persist_vs_occupancy@.

* @persistHilbertIndex@ — egoff @hilbert_index(ucrs_seq, grid_hash)@ via @xy2d@.
* @occupancyHilbertIndex@ — ADK @cell_locality_hash@ FNV antichain sort surrogate.
* @homologNotCopy@ — homolog witness is restriction, not bitwise identity.
* Compose @selectExcitement@ — not a second ℚ argmin.
* **One** design axiom (@persistVsOccupancyAxiom@): @physicalSecondLaw@ framing only.
* @physics_green@ stays false; modality @PersistVsOccupancyUnwired@.

Not meso thermo G(T,P,x). Cell: @URGE-FORMAL-Q-HS-PERSIST-VS-OCCUPANCY@.
Identity: @persist_vs_occupancy@.
-}
module UrgeKnowing.PersistVsOccupancy
  ( ExcitementCand (..)
  , selectExcitement
  , composeSurrogateFor
  , metaExcitementModule
  , HilbertRole (..)
  , persistHilbertRole
  , occupancyHilbertRole
  , persistNeOccupancyRole
  , PersistHilbert (..)
  , OccupancyHilbert (..)
  , persistHilbertRoleOf
  , occupancyHilbertRoleOf
  , HilbertFuseRefused (..)
  , HilbertFuseResult (..)
  , fusePersistIntoOccupancyRefused
  , fuseOccupancyIntoPersistRefused
  , homologNotCopyRefused
  , refuseFusePersistIntoOccupancy
  , refuseFuseOccupancyIntoPersist
  , refuseSecondArgminSelector
  , persistHilbertBits
  , persistHilbertCoords
  , persistCurveIndex
  , persistHilbertIndex
  , occupancyHilbertIndex
  , HilbertHomologWitness (..)
  , homologClaimsIdentityCopy
  , homologPersistToOccupancy
  , homologNotCopy
  , FiberVerdict (..)
  , FiberFixtureStep (..)
  , evaluateFiberMorphism
  , persistVsOccupancyFixture
  , countFiberVerdict
  , persistVsOccupancyPositiveRefuseHonest
  , PersistVsOccupancyAttempt (..)
  , PersistVsOccupancyRefusal (..)
  , PersistVsOccupancyOutcome (..)
  , evaluatePersistVsOccupancy
  , urgePersistVsOccupancySelect
  , persistVsOccupancyModalityUnwired
  , persistVsOccupancyPhysicsGreen
  , persistVsOccupancyProductionWired
  , fixtureAcceptPersistVsOccupancy
  , fixtureRefuseFusePersistIntoOccupancy
  , fixtureRefuseHomologIdentityCopy
  , persistVsOccupancyPolicy
  , PersistVsOccupancyModality (..)
  , persistVsOccupancyModalityCurrent
  , physicalSecondLawAxiom
  , landauerNotSecondAxiom
  , persistVsOccupancyAxiom
  , persistVsOccupancyNamed
  , persistVsOccupancyCellId
  , persistVsOccupancyNonClaim
  , persistHilbertAuthority
  , occupancyHilbertAuthority
  , persistNotOccupancyCopyCollision
  , persistVsOccupancyPhysicsGreenAuthorized
  , persistVsOccupancyPhysicsGreenFalse
  , persistVsOccupancyModalityUnwiredWitness
  , persistVsOccupancyKnowingFiberOk
  ) where

import Data.Bits (shiftL, shiftR, xor, (.&.), (.|.))
import Data.List (sortOn)
import Data.Word (Word8, Word32, Word64)
import UrgeKnowing.EpistemicNullProbe
  ( landauerNotSecondAxiom
  , physicalSecondLawAxiom
  )

-- | Compose surrogate cites @UMST.Excitement.select@ (import pin — not local argmin).
composeSurrogateFor :: String
composeSurrogateFor = "UMST.Excitement.select"

-- | umst-meta excitement module authority path.
metaExcitementModule :: String
metaExcitementModule = "umst-meta/crates/umst-meta/src/excitement.rs"

-- | Minimal Excitement candidate for persist-vs-occupancy compose (fixture scale).
data ExcitementCand = ExcitementCand
  { excitementCandId :: String
  , excitementCandFreeEnergy :: Double
  , excitementCandProvenanceIntact :: Bool
  , excitementCandDropsProvenance :: Bool
  }
  deriving (Eq, Show)

-- | Whether candidate is admissible for Excitement selection.
excitementCandAdmissible :: ExcitementCand -> Bool
excitementCandAdmissible c =
  excitementCandProvenanceIntact c && not (excitementCandDropsProvenance c)

-- | Pure total Excitement on finite admissible set — compose pin, not second argmin.
selectExcitement :: Double -> [ExcitementCand] -> Maybe ExcitementCand
selectExcitement _ [] = Nothing
selectExcitement _ cands =
  let admissible = filter excitementCandAdmissible cands
   in case sortOn (\c -> (excitementCandFreeEnergy c, excitementCandId c)) admissible of
        [] -> Nothing
        (best : _) -> Just best

-- | Hilbert role tag — persist (acting) vs occupancy (knowing).
data HilbertRole
  = HilbertRolePersistActing
  | HilbertRoleOccupancyKnowing
  deriving (Eq, Show)

persistHilbertRole :: HilbertRole
persistHilbertRole = HilbertRolePersistActing

occupancyHilbertRole :: HilbertRole
occupancyHilbertRole = HilbertRoleOccupancyKnowing

persistNeOccupancyRole :: Bool
persistNeOccupancyRole = persistHilbertRole /= occupancyHilbertRole

-- | Persist Hilbert newtype (acting / sled persist morphism).
newtype PersistHilbert = PersistHilbert {persistRaw :: Word32}
  deriving (Eq, Show)

-- | Occupancy Hilbert newtype (knowing / ADK FNV locality sort).
newtype OccupancyHilbert = OccupancyHilbert {occupancyRaw :: Word32}
  deriving (Eq, Show)

persistHilbertRoleOf :: PersistHilbert -> HilbertRole
persistHilbertRoleOf _ = HilbertRolePersistActing

occupancyHilbertRoleOf :: OccupancyHilbert -> HilbertRole
occupancyHilbertRoleOf _ = HilbertRoleOccupancyKnowing

-- | Positive fuse refusal across Hilbert fibers.
data HilbertFuseRefused
  = FusePersistIntoOccupancy
  | FuseOccupancyIntoPersist
  | FuseHomologIsNotCopy
  | FuseSecondArgmin
  deriving (Eq, Show)

fusePersistIntoOccupancyRefused :: HilbertFuseRefused
fusePersistIntoOccupancyRefused = FusePersistIntoOccupancy

fuseOccupancyIntoPersistRefused :: HilbertFuseRefused
fuseOccupancyIntoPersistRefused = FuseOccupancyIntoPersist

homologNotCopyRefused :: HilbertFuseRefused
homologNotCopyRefused = FuseHomologIsNotCopy

data HilbertFuseResult a
  = FuseOk a
  | FuseRefused HilbertFuseRefused
  deriving (Eq, Show)

refuseFusePersistIntoOccupancy ::
  PersistHilbert -> HilbertFuseResult OccupancyHilbert
refuseFusePersistIntoOccupancy _ =
  FuseRefused FusePersistIntoOccupancy

refuseFuseOccupancyIntoPersist ::
  OccupancyHilbert -> HilbertFuseResult PersistHilbert
refuseFuseOccupancyIntoPersist _ =
  FuseRefused FuseOccupancyIntoPersist

refuseSecondArgminSelector :: Either HilbertFuseRefused a
refuseSecondArgminSelector = Left FuseSecondArgmin

persistHilbertBits :: Int
persistHilbertBits = 8

persistHilbertCoords :: Word64 -> Word64 -> (Word32, Word32)
persistHilbertCoords ucrs grid =
  let side = shiftL 1 persistHilbertBits
      mask = side - 1
      x = fromIntegral ucrs .&. mask
      y =
        fromIntegral grid .&. mask
          .|. shiftL (fromIntegral (grid `shiftR` 16) .&. mask) 16
   in (x, y)

rot2 :: Word32 -> Word32 -> Word32 -> Word32 -> Word32 -> (Word32, Word32)
rot2 s x y rx ry =
  let (x', y') =
        if ry == 0
          then
            if rx == 1
              then (s - 1 - x, s - 1 - y)
              else (x, y)
          else (x, y)
      (x'', y'') =
        if ry == 0 then (y', x') else (x', y')
   in (x'', y'')

d2xy :: Int -> Word32 -> (Word32, Word32)
d2xy n d =
  let limit = shiftL 1 n
      go t x y s =
        if s >= limit
          then (x, y)
          else
            let rx = (t `div` 2) .&. 1
                ry = (t `xor` rx) .&. 1
                (x', y') = rot2 s x y rx ry
                t' = t `div` 4
                s' = s `shiftL` 1
             in go t' (x' + s * rx) (y' + s * ry) s'
   in go d 0 0 1

xy2d :: Int -> Word32 -> Word32 -> Maybe Word32
xy2d n x y =
  let limit = shiftL 1 (2 * n)
      found =
        [ d
        | d <- [0 .. limit - 1]
        , d2xy n d == (x, y)
        ]
   in case found of
        (best : _) -> Just best
        [] -> Nothing

persistCurveIndex :: Word32 -> Word32 -> Int -> Word32
persistCurveIndex x y bits =
  let side = shiftL (1 :: Word32) bits
   in (x `mod` side) + (y `mod` side) * side

persistHilbertIndex :: Word64 -> Word64 -> PersistHilbert
persistHilbertIndex ucrs grid =
  let (x, y) = persistHilbertCoords ucrs grid
      raw =
        case xy2d persistHilbertBits x y of
          Just d -> d
          Nothing -> persistCurveIndex x y persistHilbertBits
   in PersistHilbert raw

fnv1aStep :: Word64 -> Word8 -> Word64
fnv1aStep h b =
  (h `xor` fromIntegral b) * 0x100000001b3

fnv1aString :: Word64 -> String -> Word64
fnv1aString h s =
  foldl (\h' c -> fnv1aStep h' (fromIntegral (fromEnum c))) h s

fnv1aPaths :: Word64 -> [String] -> Word64
fnv1aPaths h paths =
  foldl
    ( \h' path ->
        let h1 = fnv1aString h' path
            h2 = fnv1aStep h1 0
         in h2
    )
    h
    paths

occupancyHilbertIndex :: String -> [String] -> OccupancyHilbert
occupancyHilbertIndex cellId writeSet =
  let h = fnv1aPaths 0xcbf29ce484222325 (cellId : writeSet)
      raw = fromIntegral h `xor` fromIntegral (h `shiftR` 32)
   in OccupancyHilbert raw

data HilbertHomologWitness = HilbertHomologWitness
  { homologPersist :: PersistHilbert
  , homologOccupancy :: OccupancyHilbert
  , homologClaimsIdentityCopyFlag :: Bool
  }
  deriving (Eq, Show)

homologPersistToOccupancy ::
  PersistHilbert -> OccupancyHilbert -> Bool -> HilbertHomologWitness
homologPersistToOccupancy p o claimsCopy =
  HilbertHomologWitness
    { homologPersist = p
    , homologOccupancy = o
    , homologClaimsIdentityCopyFlag = claimsCopy
    }

homologClaimsIdentityCopy :: HilbertHomologWitness -> Bool
homologClaimsIdentityCopy w =
  homologClaimsIdentityCopyFlag w
    || persistHilbertRoleOf (homologPersist w)
      == occupancyHilbertRoleOf (homologOccupancy w)

homologNotCopy :: HilbertHomologWitness -> Bool
homologNotCopy w =
  not (homologClaimsIdentityCopyFlag w)
    && persistHilbertRoleOf (homologPersist w)
      /= occupancyHilbertRoleOf (homologOccupancy w)

data FiberVerdict
  = FiberVerdictAccept
  | FiberVerdictRefuse
  deriving (Eq, Show)

data FiberFixtureStep = FiberFixtureStep
  { fixtureStepId :: String
  , fixtureVerdict :: FiberVerdict
  , fixtureRefusal :: Maybe HilbertFuseRefused
  }
  deriving (Eq, Show)

evaluateFiberMorphism :: HilbertHomologWitness -> Bool -> FiberVerdict
evaluateFiberMorphism w attemptFuse
  | attemptFuse = FiberVerdictRefuse
  | homologClaimsIdentityCopy w = FiberVerdictRefuse
  | homologNotCopy w = FiberVerdictAccept
  | otherwise = FiberVerdictRefuse

samplePersistHilbert :: PersistHilbert
samplePersistHilbert = PersistHilbert 42

sampleOccupancyHilbert :: OccupancyHilbert
sampleOccupancyHilbert = OccupancyHilbert 99

homologRestrictionAdmittedStep :: FiberFixtureStep
homologRestrictionAdmittedStep =
  let w =
        homologPersistToOccupancy
          samplePersistHilbert
          sampleOccupancyHilbert
          False
   in FiberFixtureStep
        { fixtureStepId = "homolog-restriction-admitted"
        , fixtureVerdict = evaluateFiberMorphism w False
        , fixtureRefusal = Nothing
        }

fusePersistIntoOccupancyStep :: FiberFixtureStep
fusePersistIntoOccupancyStep =
  let w =
        homologPersistToOccupancy
          samplePersistHilbert
          sampleOccupancyHilbert
          False
   in FiberFixtureStep
        { fixtureStepId = "fuse-persist-into-occupancy"
        , fixtureVerdict = evaluateFiberMorphism w True
        , fixtureRefusal = Just FusePersistIntoOccupancy
        }

homologIdentityCopyStep :: FiberFixtureStep
homologIdentityCopyStep =
  let w =
        homologPersistToOccupancy
          samplePersistHilbert
          sampleOccupancyHilbert
          True
   in FiberFixtureStep
        { fixtureStepId = "homolog-identity-copy"
        , fixtureVerdict = evaluateFiberMorphism w False
        , fixtureRefusal = Just FuseHomologIsNotCopy
        }

persistVsOccupancyFixture :: [FiberFixtureStep]
persistVsOccupancyFixture =
  [ homologRestrictionAdmittedStep
  , fusePersistIntoOccupancyStep
  , homologIdentityCopyStep
  ]

countFiberVerdict :: [FiberFixtureStep] -> FiberVerdict -> Int
countFiberVerdict steps target =
  length [() | step <- steps, fixtureVerdict step == target]

persistVsOccupancyPositiveRefuseHonest :: Bool
persistVsOccupancyPositiveRefuseHonest =
  refuseFusePersistIntoOccupancy samplePersistHilbert
    == FuseRefused FusePersistIntoOccupancy
    && refuseFuseOccupancyIntoPersist sampleOccupancyHilbert
      == FuseRefused FuseOccupancyIntoPersist
    && fusePersistIntoOccupancyRefused == FusePersistIntoOccupancy
    && homologNotCopyRefused == FuseHomologIsNotCopy
    && (refuseSecondArgminSelector :: Either HilbertFuseRefused Bool)
      == Left FuseSecondArgmin

data PersistVsOccupancyAttempt = PersistVsOccupancyAttempt
  { persistVsOccupancyPersist :: PersistHilbert
  , persistVsOccupancyAttemptCellId :: String
  , persistVsOccupancyWriteSet :: [String]
  , persistVsOccupancySourceFreeEnergy :: Double
  , persistVsOccupancyAttemptFuse :: Bool
  , persistVsOccupancyClaimsCopy :: Bool
  }
  deriving (Eq, Show)

data PersistVsOccupancyRefusal
  = HomologCopyTheater
  | FuseRefusedPositive
  | SecondArgmin
  deriving (Eq, Show)

data PersistVsOccupancyOutcome
  = PersistVsOccupancyAdmitted
      { persistVsOccupancyCandidateId :: String
      , persistVsOccupancyHomologOk :: Bool
      }
  | PersistVsOccupancyRefused PersistVsOccupancyRefusal
  deriving (Eq, Show)

evaluatePersistVsOccupancy ::
  PersistVsOccupancyAttempt -> [ExcitementCand] -> PersistVsOccupancyOutcome
evaluatePersistVsOccupancy attempt cands =
  let o =
        occupancyHilbertIndex
          (persistVsOccupancyAttemptCellId attempt)
          (persistVsOccupancyWriteSet attempt)
      witness =
        homologPersistToOccupancy
          (persistVsOccupancyPersist attempt)
          o
          (persistVsOccupancyClaimsCopy attempt)
      verdict =
        evaluateFiberMorphism witness (persistVsOccupancyAttemptFuse attempt)
   in case verdict of
        FiberVerdictRefuse ->
          PersistVsOccupancyRefused
            ( if persistVsOccupancyAttemptFuse attempt
                then FuseRefusedPositive
                else HomologCopyTheater
            )
        FiberVerdictAccept ->
          if not persistVsOccupancyPositiveRefuseHonest
            then PersistVsOccupancyRefused FuseRefusedPositive
            else
              case
                selectExcitement (persistVsOccupancySourceFreeEnergy attempt) cands
                of
                Nothing -> PersistVsOccupancyRefused HomologCopyTheater
                Just cand ->
                  PersistVsOccupancyAdmitted
                    { persistVsOccupancyCandidateId = excitementCandId cand
                    , persistVsOccupancyHomologOk = homologNotCopy witness
                    }

urgePersistVsOccupancySelect :: Double -> [ExcitementCand] -> Maybe ExcitementCand
urgePersistVsOccupancySelect = selectExcitement

persistVsOccupancyModalityUnwired :: Bool
persistVsOccupancyModalityUnwired = True

persistVsOccupancyPhysicsGreen :: Bool
persistVsOccupancyPhysicsGreen = False

persistVsOccupancyProductionWired :: Bool
persistVsOccupancyProductionWired = False

fixtureAcceptPersistVsOccupancy :: PersistVsOccupancyOutcome
fixtureAcceptPersistVsOccupancy =
  evaluatePersistVsOccupancy
    PersistVsOccupancyAttempt
      { persistVsOccupancyPersist = persistHilbertIndex 10 0xabc
      , persistVsOccupancyAttemptCellId = "URGE-FORMAL-Q-HS-PERSIST-VS-OCCUPANCY"
      , persistVsOccupancyWriteSet =
          [ "umst/umst-formal-double-slit/Haskell/src/UrgeKnowing/PersistVsOccupancy.hs"
          , "umst/umst-formal-double-slit/Haskell/umst-formal-double-slit.cabal"
          ]
      , persistVsOccupancySourceFreeEnergy = 10
      , persistVsOccupancyAttemptFuse = False
      , persistVsOccupancyClaimsCopy = False
      }
    [ ExcitementCand
        { excitementCandId = "persist-vs-occupancy-best"
        , excitementCandFreeEnergy = 3
        , excitementCandProvenanceIntact = True
        , excitementCandDropsProvenance = False
        }
    ]

fixtureRefuseFusePersistIntoOccupancy :: PersistVsOccupancyOutcome
fixtureRefuseFusePersistIntoOccupancy =
  evaluatePersistVsOccupancy
    PersistVsOccupancyAttempt
      { persistVsOccupancyPersist = samplePersistHilbert
      , persistVsOccupancyAttemptCellId = "URGE-FORMAL-Q-HS-PERSIST-VS-OCCUPANCY"
      , persistVsOccupancyWriteSet = ["write/a.hs"]
      , persistVsOccupancySourceFreeEnergy = 10
      , persistVsOccupancyAttemptFuse = True
      , persistVsOccupancyClaimsCopy = False
      }
    [ ExcitementCand
        { excitementCandId = "fuse-refused"
        , excitementCandFreeEnergy = 3
        , excitementCandProvenanceIntact = True
        , excitementCandDropsProvenance = False
        }
    ]

fixtureRefuseHomologIdentityCopy :: PersistVsOccupancyOutcome
fixtureRefuseHomologIdentityCopy =
  evaluatePersistVsOccupancy
    PersistVsOccupancyAttempt
      { persistVsOccupancyPersist = samplePersistHilbert
      , persistVsOccupancyAttemptCellId = "URGE-FORMAL-Q-HS-PERSIST-VS-OCCUPANCY"
      , persistVsOccupancyWriteSet = ["write/a.hs"]
      , persistVsOccupancySourceFreeEnergy = 10
      , persistVsOccupancyAttemptFuse = False
      , persistVsOccupancyClaimsCopy = True
      }
    [ ExcitementCand
        { excitementCandId = "homolog-copy"
        , excitementCandFreeEnergy = 3
        , excitementCandProvenanceIntact = True
        , excitementCandDropsProvenance = False
        }
    ]

persistVsOccupancyPolicy :: Bool
persistVsOccupancyPolicy =
  persistNeOccupancyRole
    && persistVsOccupancyPositiveRefuseHonest
    && countFiberVerdict persistVsOccupancyFixture FiberVerdictAccept == 1
    && countFiberVerdict persistVsOccupancyFixture FiberVerdictRefuse == 2
    && homologNotCopy
      ( homologPersistToOccupancy
          samplePersistHilbert
          sampleOccupancyHilbert
          False
      )
    && homologClaimsIdentityCopy
      ( homologPersistToOccupancy
          samplePersistHilbert
          sampleOccupancyHilbert
          True
      )
    && occupancyHilbertIndex "CELL-B" ["write/a.rs", "write/b.rs"]
      /= occupancyHilbertIndex "CELL-C" ["write/a.rs", "write/b.rs"]
    && homologNotCopy
      ( homologPersistToOccupancy
          (persistHilbertIndex 1 2)
          (occupancyHilbertIndex "URGE-FORMAL-Q-HS-PERSIST-VS-OCCUPANCY" ["write/a.hs"])
          False
      )
    && (refuseSecondArgminSelector :: Either HilbertFuseRefused Bool)
      == Left FuseSecondArgmin
    && case fixtureAcceptPersistVsOccupancy of
      PersistVsOccupancyAdmitted
        { persistVsOccupancyCandidateId = cid
        , persistVsOccupancyHomologOk = ok
        } ->
        cid == "persist-vs-occupancy-best" && ok
      _ -> False
    && fixtureRefuseFusePersistIntoOccupancy
      == PersistVsOccupancyRefused FuseRefusedPositive
    && fixtureRefuseHomologIdentityCopy
      == PersistVsOccupancyRefused HomologCopyTheater
    && urgePersistVsOccupancySelect
      10
      [ ExcitementCand
          { excitementCandId = "compose-ok"
          , excitementCandFreeEnergy = 2
          , excitementCandProvenanceIntact = True
          , excitementCandDropsProvenance = False
          }
      ]
      == Just
        ExcitementCand
          { excitementCandId = "compose-ok"
          , excitementCandFreeEnergy = 2
          , excitementCandProvenanceIntact = True
          , excitementCandDropsProvenance = False
          }
    && composeSurrogateFor == "UMST.Excitement.select"
    && physicalSecondLawAxiom == "LandauerLaw.physicalSecondLaw"
    && persistHilbertAuthority /= occupancyHilbertAuthority
    && persistNotOccupancyCopyCollision /= ""
    && not persistVsOccupancyProductionWired
    && not persistVsOccupancyPhysicsGreen

data PersistVsOccupancyModality
  = PersistVsOccupancyUnwired
  | PersistVsOccupancyAssumed
  | PersistVsOccupancyProved
  | PersistVsOccupancySurrogate
  deriving (Eq, Show)

persistVsOccupancyModalityCurrent :: PersistVsOccupancyModality
persistVsOccupancyModalityCurrent = PersistVsOccupancyUnwired

persistVsOccupancyAxiom :: Bool
persistVsOccupancyAxiom =
  persistVsOccupancyPolicy
    && landauerNotSecondAxiom
    && persistVsOccupancyModalityUnwiredWitness
    && persistVsOccupancyPhysicsGreenFalse

persistVsOccupancyNamed :: String
persistVsOccupancyNamed =
  "persist_vs_occupancy: §12.7 persist Hilbert acting distinct from occupancy Hilbert knowing homolog not copy fuse refused compose Excitement not second argmin physicalSecondLaw sole axiom framing"

persistVsOccupancyCellId :: String
persistVsOccupancyCellId = "URGE-FORMAL-Q-HS-PERSIST-VS-OCCUPANCY"

persistVsOccupancyNonClaim :: String
persistVsOccupancyNonClaim =
  "URGE-FORMAL-Q-HS-PERSIST-VS-OCCUPANCY persist_vs_occupancy Unwired not Proved not GREEN not production_wired knowing fiber only not meso thermo G(T,P,x)"

persistHilbertAuthority :: String
persistHilbertAuthority = "umst/egoff/egoff/src/memory/hilbert_layout.rs"

occupancyHilbertAuthority :: String
occupancyHilbertAuthority = "umst/umst-meta/crates/umst-adk/src/hilbert_allocate.rs"

persistNotOccupancyCopyCollision :: String
persistNotOccupancyCopyCollision =
  "persist Hilbert xy2d(ucrs_seq, grid_hash) ne occupancy Hilbert FNV(cell_id, write_set) homolog not copy"

persistVsOccupancyPhysicsGreenAuthorized :: Bool
persistVsOccupancyPhysicsGreenAuthorized = False

persistVsOccupancyPhysicsGreenFalse :: Bool
persistVsOccupancyPhysicsGreenFalse = not persistVsOccupancyPhysicsGreenAuthorized

persistVsOccupancyModalityUnwiredWitness :: Bool
persistVsOccupancyModalityUnwiredWitness =
  persistVsOccupancyModalityCurrent == PersistVsOccupancyUnwired

persistVsOccupancyKnowingFiberOk :: Bool
persistVsOccupancyKnowingFiberOk =
  persistVsOccupancyModalityUnwiredWitness && persistVsOccupancyPhysicsGreenFalse
