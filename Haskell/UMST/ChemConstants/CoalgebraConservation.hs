-- SPDX-FileCopyrightText: 2026 Santosh Prabhu Shenbagamoorthy and Santhosh Shyamsundar
-- SPDX-License-Identifier: MIT

{-|
Module      : UMST.ChemConstants.CoalgebraConservation
Description : Coalgebra conservation on the knowing fiber (Q lattice)
Copyright   : (c) UMST Project, 2026

Coalgebra conservation: @OreAssemblage@ unfold/fold scaffold for ore decomposition /
synthesis — coalgebra unfold peels fragments, algebra fold rebuilds assemblage; ore
identity conserved on roundtrip. Coalgebra laws and CAT-04 coalgebra are structure
witnesses only (@coalgebraLawsProved@ = False, @cat04CoalgebraProved@ = False).

* @OreAssemblage@ = Empty | Single | Pair — assemblage carrier, not @Vec@ list.
* @unfoldOre@ / @foldOre@ — decomposition unfold vs synthesis fold distinct.
* **One** design axiom (@coalgebraConservationAxiom@): second law + conservation.
* Ore identity conserved under unfold/fold roundtrip scaffold.
* @physics_green@ stays false.

Haskell mirror of coalgebra conservation on the quantum / knowing fiber.
Cell: @CHEM-FORMAL-Q-HS-COALGEBRA-CONSERVATION@.
-}
module UMST.ChemConstants.CoalgebraConservation
  ( CoalgebraConservationModality (..)
  , coalgebraConservationModalityCurrent
  , OreFragmentTag (..)
  , OreAssemblage (..)
  , oreAssemblageIsEmpty
  , oreAssemblageIsSingle
  , oreAssemblageIsPair
  , OreDecompositionStep (..)
  , OreSynthesisStep (..)
  , DecompositionVerdict (..)
  , SynthesisVerdict (..)
  , unfoldOre
  , foldOre
  , sampleSingleAssemblage
  , samplePairAssemblage
  , terminalDecomposeOk
  , singleUnfoldOk
  , pairUnfoldPeelsLeft
  , invalidTailSynthesisRefuse
  , greenInventSynthesisRefuse
  , oreIdentityConservedOnSingleRoundtrip
  , oreIdentityConservedOnPairRoundtrip
  , oreIdentityConservedOnEmptyRoundtrip
  , oreIdentityConservedOnRoundtrip
  , unfoldFoldScaffold
  , coalgebraLawsInventRefuse
  , oreAssemblageNotListBacked
  , unfoldFoldNotXor
  , coalgebraLawsProved
  , cat04CoalgebraProved
  , coalgebraConservationFraming
  , coalgebraConservationAxiom
  , coalgebraConservationNamed
  , oreCoalgebraAlgebraAuthority
  , chemL0Cat04Authority
  , coalgebraConservationCellId
  , coalgebraConservationNonClaim
  , coalgebraConservationPhysicsGreenAuthorized
  , coalgebraConservationPhysicsGreenFalse
  , coalgebraConservationModalityUnwired
  ) where

-- | Design modality for coalgebra conservation claims (TYPE-03 preview).
data CoalgebraConservationModality
  = CoalgebraConservationUnwired
  | CoalgebraConservationAssumed
  | CoalgebraConservationProved
  | CoalgebraConservationSurrogate
  deriving (Eq, Show)

-- | Current scaffold modality — always Unwired on this cell.
coalgebraConservationModalityCurrent :: CoalgebraConservationModality
coalgebraConservationModalityCurrent = CoalgebraConservationUnwired

-- | Ore fragment tags (bounded scaffold — not XOR enum).
data OreFragmentTag
  = FragAScaffold
  | FragBScaffold
  deriving (Eq, Show)

-- | Minimal ore assemblage carrier (design scaffold — not @Vec@ list).
data OreAssemblage
  = OreEmpty
  | OreSingle OreFragmentTag
  | OrePair OreFragmentTag OreFragmentTag
  deriving (Eq, Show)

oreAssemblageIsEmpty :: OreAssemblage -> Bool
oreAssemblageIsEmpty OreEmpty = True
oreAssemblageIsEmpty _ = False

oreAssemblageIsSingle :: OreAssemblage -> Bool
oreAssemblageIsSingle (OreSingle _) = True
oreAssemblageIsSingle _ = False

oreAssemblageIsPair :: OreAssemblage -> Bool
oreAssemblageIsPair (OrePair _ _) = True
oreAssemblageIsPair _ = False

-- | One coalgebra unfold step — head fragment + tail remainder.
data OreDecompositionStep = OreDecompositionStep
  { decompositionHead :: OreFragmentTag
  , decompositionTail :: OreAssemblage
  }
  deriving (Eq, Show)

-- | One algebra fold step — head fragment + tail remainder.
data OreSynthesisStep = OreSynthesisStep
  { synthesisHead :: OreFragmentTag
  , synthesisTail :: OreAssemblage
  }
  deriving (Eq, Show)

-- | Coalgebra unfold verdict (terminal vs unfold-ok).
data DecompositionVerdict
  = DecompositionTerminal
  | DecompositionUnfoldOk
  deriving (Eq, Show)

-- | Algebra fold verdict (fold-ok vs refuse).
data SynthesisVerdict
  = SynthesisFoldOk
  | SynthesisInvalidTailRefuse
  | SynthesisGreenInventRefuse
  deriving (Eq, Show)

-- | Coalgebra unfold — peel one fragment from assemblage.
unfoldOre :: OreAssemblage -> (DecompositionVerdict, Maybe OreDecompositionStep)
unfoldOre assemblage = case assemblage of
  OreEmpty -> (DecompositionTerminal, Nothing)
  OreSingle frag ->
    ( DecompositionUnfoldOk
    , Just (OreDecompositionStep frag OreEmpty)
    )
  OrePair left right ->
    ( DecompositionUnfoldOk
    , Just (OreDecompositionStep left (OreSingle right))
    )

-- | Algebra fold — rebuild assemblage from head + tail (refuse-closed).
foldOre :: OreSynthesisStep -> Bool -> (SynthesisVerdict, Maybe OreAssemblage)
foldOre step claimPhysicsGreen
  | claimPhysicsGreen = (SynthesisGreenInventRefuse, Nothing)
  | otherwise =
      case synthesisTail step of
        OreEmpty ->
          (SynthesisFoldOk, Just (OreSingle (synthesisHead step)))
        OreSingle tailFrag ->
          ( SynthesisFoldOk
          , Just (OrePair (synthesisHead step) tailFrag)
          )
        OrePair {} -> (SynthesisInvalidTailRefuse, Nothing)

-- | Sample single-fragment assemblage for roundtrip witnesses.
sampleSingleAssemblage :: OreAssemblage
sampleSingleAssemblage = OreSingle FragAScaffold

-- | Sample pair assemblage for roundtrip witnesses.
samplePairAssemblage :: OreAssemblage
samplePairAssemblage = OrePair FragAScaffold FragBScaffold

-- | Terminal assemblage decomposes without refuse.
terminalDecomposeOk :: Bool
terminalDecomposeOk =
  case unfoldOre OreEmpty of
    (DecompositionTerminal, Nothing) -> True
    _ -> False

-- | Single-fragment coalgebra unfold succeeds.
singleUnfoldOk :: Bool
singleUnfoldOk =
  case unfoldOre sampleSingleAssemblage of
    (DecompositionUnfoldOk, Just _) -> True
    _ -> False

-- | Pair unfold peels left fragment into single remainder.
pairUnfoldPeelsLeft :: Bool
pairUnfoldPeelsLeft =
  case unfoldOre (OrePair FragBScaffold FragAScaffold) of
    ( DecompositionUnfoldOk
      , Just (OreDecompositionStep FragBScaffold (OreSingle FragAScaffold))
      ) ->
        True
    _ -> False

-- | Invalid-tail synthesis is refused (no free purification).
invalidTailSynthesisRefuse :: Bool
invalidTailSynthesisRefuse =
  case
    foldOre
      ( OreSynthesisStep
          FragAScaffold
          (OrePair FragBScaffold FragAScaffold)
      )
      False
    of
    (SynthesisInvalidTailRefuse, Nothing) -> True
    _ -> False

-- | GREEN invent on synthesis is refused.
greenInventSynthesisRefuse :: Bool
greenInventSynthesisRefuse =
  case foldOre (OreSynthesisStep FragAScaffold OreEmpty) True of
    (SynthesisGreenInventRefuse, Nothing) -> True
    _ -> False

-- | Check ore identity conserved on unfold/fold roundtrip.
checkOreRoundtrip :: OreAssemblage -> Bool -> Bool
checkOreRoundtrip assemblage claimPhysicsGreen =
  case unfoldOre assemblage of
    (DecompositionTerminal, Nothing) -> oreAssemblageIsEmpty assemblage
    (DecompositionUnfoldOk, Just step) ->
      case foldOre (OreSynthesisStep (decompositionHead step) (decompositionTail step)) claimPhysicsGreen of
        (SynthesisFoldOk, Just rebuilt) -> rebuilt == assemblage
        _ -> False
    _ -> False

-- | Single-fragment ore identity conserved on roundtrip.
oreIdentityConservedOnSingleRoundtrip :: Bool
oreIdentityConservedOnSingleRoundtrip =
  checkOreRoundtrip sampleSingleAssemblage False

-- | Pair ore identity conserved on roundtrip.
oreIdentityConservedOnPairRoundtrip :: Bool
oreIdentityConservedOnPairRoundtrip =
  checkOreRoundtrip samplePairAssemblage False

-- | Empty terminal ore identity conserved on roundtrip.
oreIdentityConservedOnEmptyRoundtrip :: Bool
oreIdentityConservedOnEmptyRoundtrip = checkOreRoundtrip OreEmpty False

-- | Ore identity conserved under unfold/fold roundtrip scaffold.
oreIdentityConservedOnRoundtrip :: Bool
oreIdentityConservedOnRoundtrip =
  oreIdentityConservedOnSingleRoundtrip
    && oreIdentityConservedOnPairRoundtrip
    && oreIdentityConservedOnEmptyRoundtrip

-- | Both unfold and fold scaffolds admissible under Unwired design rules.
unfoldFoldScaffold :: Bool
unfoldFoldScaffold =
  oreIdentityConservedOnRoundtrip
    && terminalDecomposeOk
    && singleUnfoldOk
    && pairUnfoldPeelsLeft

-- | Coalgebra laws invent refuse-closed scaffold witness.
coalgebraLawsInventRefuse :: Bool
coalgebraLawsInventRefuse = not coalgebraLawsProved

-- | OreAssemblage algebra is not list-backed (unfold/fold scaffold).
oreAssemblageNotListBacked :: Bool
oreAssemblageNotListBacked =
  sampleSingleAssemblage /= samplePairAssemblage
    && oreAssemblageIsSingle sampleSingleAssemblage
    && oreAssemblageIsPair samplePairAssemblage

-- | Unfold/fold steps are concurrent Π_c — not XOR enum bucket.
unfoldFoldNotXor :: Bool
unfoldFoldNotXor =
  pairUnfoldPeelsLeft
    && invalidTailSynthesisRefuse
    && greenInventSynthesisRefuse
    && samplePairAssemblage /= sampleSingleAssemblage

-- | Coalgebra laws proved (always false on this Unwired cell).
coalgebraLawsProved :: Bool
coalgebraLawsProved = False

-- | CAT-04 coalgebra proved (always false on this Unwired cell).
cat04CoalgebraProved :: Bool
cat04CoalgebraProved = False

-- | One axiom framing: second law + conservation for coalgebra scaffold.
coalgebraConservationFraming :: String
coalgebraConservationFraming =
  "second_law_conservation_coalgebra_one_axiom"

-- | Single design axiom: second law + conservation coalgebra (not second axiom).
coalgebraConservationAxiom :: Bool
coalgebraConservationAxiom =
  oreAssemblageNotListBacked
    && unfoldFoldScaffold
    && oreIdentityConservedOnRoundtrip
    && invalidTailSynthesisRefuse
    && greenInventSynthesisRefuse
    && coalgebraLawsInventRefuse
    && unfoldFoldNotXor
    && not coalgebraLawsProved
    && not cat04CoalgebraProved
    && coalgebraConservationFraming
      == "second_law_conservation_coalgebra_one_axiom"

coalgebraConservationNamed :: String
coalgebraConservationNamed =
  "coalgebraConservation: OreAssemblage unfold/fold scaffold; ore identity conserved on roundtrip; coalgebraLawsProved false cat04CoalgebraProved false; second law + conservation one axiom"

-- | Upstream ore coalgebra/algebra authority (cited, not forked).
oreCoalgebraAlgebraAuthority :: String
oreCoalgebraAlgebraAuthority = "umst/umst-chem/src/ore_coalgebra_algebra.rs"

-- | L0 CAT-04 coalgebra scaffold authority (crosswalk).
chemL0Cat04Authority :: String
chemL0Cat04Authority = "umst/umst-chem/src/l0_tables/shared.rs"

coalgebraConservationCellId :: String
coalgebraConservationCellId = "CHEM-FORMAL-Q-HS-COALGEBRA-CONSERVATION"

-- | Non-claim fence — coalgebra conservation Unwired ≠ Proved GREEN.
coalgebraConservationNonClaim :: String
coalgebraConservationNonClaim =
  "CHEM-FORMAL-Q-HS-COALGEBRA-CONSERVATION OreAssemblage unfold fold oreIdentityConservedOnRoundtrip coalgebraLawsProved false cat04CoalgebraProved false Unwired one axiom second law conservation not XOR enum not Vec list not GREEN DFT not physics GREEN not production_wired"

-- | Physics GREEN is unauthorized on the knowing coalgebra conservation scaffold.
coalgebraConservationPhysicsGreenAuthorized :: Bool
coalgebraConservationPhysicsGreenAuthorized = False

coalgebraConservationPhysicsGreenFalse :: Bool
coalgebraConservationPhysicsGreenFalse =
  not coalgebraConservationPhysicsGreenAuthorized

coalgebraConservationModalityUnwired :: Bool
coalgebraConservationModalityUnwired =
  coalgebraConservationModalityCurrent == CoalgebraConservationUnwired
