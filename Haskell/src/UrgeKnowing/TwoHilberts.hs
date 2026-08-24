-- SPDX-FileCopyrightText: 2026 Santosh Prabhu Shenbagamoorthy and Santhosh Shyamsundar
-- SPDX-License-Identifier: MIT

{-|
Module      : UrgeKnowing.TwoHilberts
Description : TwoHilberts — persist vs occupancy geometric identity on knowing fiber
Copyright   : (c) UMST Project, 2026

§12.7 @two_hilberts@ — persist Hilbert (acting) distinct from occupancy Hilbert
(knowing). homolog relates fibers — homolog ≠ copy. Positive fuse refusal.
Mirrors Lean @UrgeKnowing.TwoHilberts@, Coq @TwoHilberts.v@, and Rust
@two_hilberts@.

* @persistHilbertIndex@ — egoff @hilbert_index(ucrs_seq, grid_hash)@ via @xy2d@.
* @occupancyHilbertIndex@ — ADK @cell_locality_hash@ FNV antichain sort surrogate.
* @homologNotCopy@ — homolog witness is restriction, not bitwise identity.
* Compose @selectExcitement@ — not a second ℚ argmin.
* **One** design axiom (@twoHilbertsAxiom@): @physicalSecondLaw@ framing only.
* @physics_green@ stays false; modality @TwoHilbertsUnwired@.

Not meso thermo G(T,P,x). Cell: @URGE-FORMAL-Q-HS-TWO-HILBERTS@.
Identity: @two_hilberts@.
-}
module UrgeKnowing.TwoHilberts
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
  , persistHilbertBits
  , persistHilbertCoords
  , persistCurveIndex
  , persistHilbertIndex
  , occupancyHilbertIndex
  , HilbertHomologWitness (..)
  , homologClaimsIdentityCopy
  , homologPersistToOccupancy
  , homologNotCopy
  , twoHilbertsPositiveRefuseHonest
  , TwoHilbertsAttempt (..)
  , TwoHilbertsRefusal (..)
  , TwoHilbertsOutcome (..)
  , refuseSecondArgminSelector
  , evaluateTwoHilberts
  , urgeTwoHilbertsSelect
  , twoHilbertsModalityUnwired
  , twoHilbertsPhysicsGreen
  , twoHilbertsProductionWired
  , fixtureAcceptTwoHilberts
  , fixtureRefuseHomologCopyTheater
  , fixtureRefuseSecondArgmin
  , twoHilbertsPolicy
  , TwoHilbertsModality (..)
  , twoHilbertsModalityCurrent
  , physicalSecondLawAxiom
  , landauerNotSecondAxiom
  , twoHilbertsAxiom
  , twoHilbertsNamed
  , twoHilbertsCellId
  , twoHilbertsNonClaim
  , persistHilbertAuthority
  , occupancyHilbertAuthority
  , twoHilbertsBlueprintAuthority
  , persistNotOccupancyCopyCollision
  , twoHilbertsPhysicsGreenAuthorized
  , twoHilbertsPhysicsGreenFalse
  , twoHilbertsModalityUnwiredWitness
  , twoHilbertsKnowingFiberOk
  ) where

import Data.Bits (shiftL, shiftR, xor, (.&.), (.|.))
import Data.Word (Word8, Word32, Word64)
import UrgeKnowing.CompactionMiCost
  ( ExcitementCand (..)
  , composeSurrogateFor
  , metaExcitementModule
  , selectExcitement
  )
import UrgeKnowing.EpistemicNullProbe
  ( landauerNotSecondAxiom
  , physicalSecondLawAxiom
  )

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
  , homologRawCoincident :: Bool
  }
  deriving (Eq, Show)

homologClaimsIdentityCopy :: HilbertHomologWitness -> Bool
homologClaimsIdentityCopy w =
  persistHilbertRoleOf (homologPersist w) == occupancyHilbertRoleOf (homologOccupancy w)

homologPersistToOccupancy ::
  PersistHilbert -> String -> [String] -> HilbertHomologWitness
homologPersistToOccupancy p cellId writeSet =
  let o = occupancyHilbertIndex cellId writeSet
   in HilbertHomologWitness
        { homologPersist = p
        , homologOccupancy = o
        , homologRawCoincident = persistRaw p == occupancyRaw o
        }

homologNotCopy :: HilbertHomologWitness -> Bool
homologNotCopy w =
  persistHilbertRoleOf (homologPersist w) /= occupancyHilbertRoleOf (homologOccupancy w)
    && not (homologClaimsIdentityCopy w)

twoHilbertsPositiveRefuseHonest :: Bool
twoHilbertsPositiveRefuseHonest =
  refuseFusePersistIntoOccupancy (PersistHilbert 0)
    == FuseRefused FusePersistIntoOccupancy
    && refuseFuseOccupancyIntoPersist (OccupancyHilbert 0)
      == FuseRefused FuseOccupancyIntoPersist
    && fusePersistIntoOccupancyRefused == FusePersistIntoOccupancy
    && homologNotCopyRefused == FuseHomologIsNotCopy

data TwoHilbertsAttempt = TwoHilbertsAttempt
  { twoHilbertsPersist :: PersistHilbert
  , twoHilbertsAttemptCellId :: String
  , twoHilbertsWriteSet :: [String]
  , twoHilbertsSourceFreeEnergy :: Double
  }

data TwoHilbertsRefusal
  = HomologCopyTheater
  | FuseRefusedPositive
  | SecondArgmin
  deriving (Eq, Show)

data TwoHilbertsOutcome
  = TwoHilbertsAdmitted
      { twoHilbertsCandidateId :: String
      , twoHilbertsHomologOk :: Bool
      }
  | TwoHilbertsRefused TwoHilbertsRefusal
  deriving (Eq, Show)

refuseSecondArgminSelector :: Either TwoHilbertsRefusal a
refuseSecondArgminSelector = Left SecondArgmin

evaluateTwoHilberts ::
  TwoHilbertsAttempt -> [ExcitementCand] -> TwoHilbertsOutcome
evaluateTwoHilberts attempt cands =
  let witness =
        homologPersistToOccupancy
          (twoHilbertsPersist attempt)
          (twoHilbertsAttemptCellId attempt)
          (twoHilbertsWriteSet attempt)
   in if not (homologNotCopy witness)
        then TwoHilbertsRefused HomologCopyTheater
        else
          if not twoHilbertsPositiveRefuseHonest
            then TwoHilbertsRefused FuseRefusedPositive
            else
              case
                selectExcitement (twoHilbertsSourceFreeEnergy attempt) cands
                of
                Nothing -> TwoHilbertsRefused HomologCopyTheater
                Just cand ->
                  TwoHilbertsAdmitted
                    { twoHilbertsCandidateId = excitementCandId cand
                    , twoHilbertsHomologOk = homologNotCopy witness
                    }

urgeTwoHilbertsSelect :: Double -> [ExcitementCand] -> Maybe ExcitementCand
urgeTwoHilbertsSelect = selectExcitement

twoHilbertsModalityUnwired :: Bool
twoHilbertsModalityUnwired = True

twoHilbertsPhysicsGreen :: Bool
twoHilbertsPhysicsGreen = False

twoHilbertsProductionWired :: Bool
twoHilbertsProductionWired = False

fixtureAcceptTwoHilberts :: TwoHilbertsOutcome
fixtureAcceptTwoHilberts =
  evaluateTwoHilberts
    TwoHilbertsAttempt
      { twoHilbertsPersist = persistHilbertIndex 10 0xabc
      , twoHilbertsAttemptCellId = "URGE-FORMAL-Q-HS-TWO-HILBERTS"
      , twoHilbertsWriteSet =
          [ "umst/umst-formal-double-slit/Haskell/src/UrgeKnowing/TwoHilberts.hs"
          , "umst/umst-formal-double-slit/Haskell/umst-formal-double-slit.cabal"
          ]
      , twoHilbertsSourceFreeEnergy = 10
      }
    [ ExcitementCand
        { excitementCandId = "two-hilberts-best"
        , excitementCandFreeEnergy = 3
        , excitementCandProvenanceIntact = True
        , excitementCandDropsProvenance = False
        }
    ]

fixtureRefuseHomologCopyTheater :: TwoHilbertsOutcome
fixtureRefuseHomologCopyTheater =
  evaluateTwoHilberts
    TwoHilbertsAttempt
      { twoHilbertsPersist = PersistHilbert 0
      , twoHilbertsAttemptCellId = ""
      , twoHilbertsWriteSet = []
      , twoHilbertsSourceFreeEnergy = 10
      }
    []

fixtureRefuseSecondArgmin :: Either TwoHilbertsRefusal Bool
fixtureRefuseSecondArgmin = refuseSecondArgminSelector

twoHilbertsPolicy :: Bool
twoHilbertsPolicy =
  persistNeOccupancyRole
    && twoHilbertsPositiveRefuseHonest
    && occupancyHilbertIndex "CELL-B" ["write/a.rs", "write/b.rs"]
      /= occupancyHilbertIndex "CELL-C" ["write/a.rs", "write/b.rs"]
    && homologNotCopy
      ( homologPersistToOccupancy
          (persistHilbertIndex 1 2)
          "URGE-FORMAL-Q-HS-TWO-HILBERTS"
          ["write/a.hs"]
      )
    && fixtureRefuseSecondArgmin == Left SecondArgmin
    && case fixtureAcceptTwoHilberts of
      TwoHilbertsAdmitted {twoHilbertsCandidateId = cid, twoHilbertsHomologOk = ok} ->
        cid == "two-hilberts-best" && ok
      _ -> False
    && urgeTwoHilbertsSelect
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
    && persistHilbertAuthority /= occupancyHilbertAuthority
    && persistNotOccupancyCopyCollision /= ""

data TwoHilbertsModality
  = TwoHilbertsUnwired
  | TwoHilbertsAssumed
  | TwoHilbertsProved
  | TwoHilbertsSurrogate
  deriving (Eq, Show)

twoHilbertsModalityCurrent :: TwoHilbertsModality
twoHilbertsModalityCurrent = TwoHilbertsUnwired

twoHilbertsAxiom :: Bool
twoHilbertsAxiom =
  twoHilbertsPolicy
    && landauerNotSecondAxiom
    && twoHilbertsModalityUnwiredWitness
    && twoHilbertsPhysicsGreenFalse

twoHilbertsNamed :: String
twoHilbertsNamed =
  "two_hilberts: persist Hilbert acting distinct from occupancy Hilbert knowing homolog not copy fuse refused compose Excitement not second argmin physicalSecondLaw sole axiom framing"

twoHilbertsCellId :: String
twoHilbertsCellId = "URGE-FORMAL-Q-HS-TWO-HILBERTS"

twoHilbertsNonClaim :: String
twoHilbertsNonClaim =
  "URGE-FORMAL-Q-HS-TWO-HILBERTS two_hilberts Unwired not Proved not GREEN not production_wired knowing fiber only not meso thermo G(T,P,x)"

persistHilbertAuthority :: String
persistHilbertAuthority = "umst/egoff/egoff/src/memory/hilbert_layout.rs"

occupancyHilbertAuthority :: String
occupancyHilbertAuthority = "umst/umst-meta/crates/umst-adk/src/hilbert_allocate.rs"

twoHilbertsBlueprintAuthority :: String
twoHilbertsBlueprintAuthority = "workspace/docs/UMST_URGE_BLUEPRINT.md"

persistNotOccupancyCopyCollision :: String
persistNotOccupancyCopyCollision =
  "persist Hilbert xy2d(ucrs_seq, grid_hash) ne occupancy Hilbert FNV(cell_id, write_set) homolog not copy"

twoHilbertsPhysicsGreenAuthorized :: Bool
twoHilbertsPhysicsGreenAuthorized = False

twoHilbertsPhysicsGreenFalse :: Bool
twoHilbertsPhysicsGreenFalse = not twoHilbertsPhysicsGreenAuthorized

twoHilbertsModalityUnwiredWitness :: Bool
twoHilbertsModalityUnwiredWitness =
  twoHilbertsModalityCurrent == TwoHilbertsUnwired

twoHilbertsKnowingFiberOk :: Bool
twoHilbertsKnowingFiberOk =
  twoHilbertsModalityUnwiredWitness && twoHilbertsPhysicsGreenFalse
