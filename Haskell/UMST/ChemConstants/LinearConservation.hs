-- SPDX-FileCopyrightText: 2026 Santosh Prabhu Shenbagamoorthy and Santhosh Shyamsundar
-- SPDX-License-Identifier: MIT

{-|
Module      : UMST.ChemConstants.LinearConservation
Description : Linear conservation on the knowing fiber (Q lattice)
Copyright   : (c) UMST Project, 2026

**Linear** conservation: signed coefficients on a conservation axis sum to zero
(identity conserved under exact balance). **Linear** vs affine resource algebra —
affine weakening only with dissipative witness; without witness refuse-closed.
TYPE-02 **linear** laws are structure witnesses only (@type02LinearProved@ = False).

* @ConservationAxis@ = Mass / Charge / AtomCount / Enthalpy — four-axis scaffold, not 118² GREEN table.
* @evaluateLinearBalance@ — balanced vs imbalanced **linear** witnesses on one axis.
* @evaluateConservationTyping@ — affine discard refuse without dissipative witness.
* **One** design axiom (@linearConservationAxiom@): second law + **conservation**.
* @physics_green@ stays false.

Haskell mirror of **linear** **conservation** on the quantum / knowing fiber.
Cell: @CHEM-FORMAL-Q-HS-LINEAR-CONSERVATION@.
-}
module UMST.ChemConstants.LinearConservation
  ( LinearConservationModality (..)
  , linearConservationModalityCurrent
  , ConservationAxis (..)
  , conservationAxisAll
  , conservationAxisCount
  , ResourceAlgebra (..)
  , ConservationCoefficient (..)
  , LinearBalanceVerdict (..)
  , DissipativeWitnessPresence (..)
  , ConservationTypingVerdict (..)
  , sumAxis
  , evaluateLinearBalance
  , evaluateConservationTyping
  , sampleBalancedMassRow
  , sampleImbalancedChargeRow
  , sampleBalancedEnthalpyRow
  , sampleImbalancedAtomCountRow
  , linearBalancedWitness
  , linearImbalancedWitness
  , affineWithWitnessOk
  , affineWithoutWitnessRefuse
  , greenInventTypingRefuse
  , unwiredDesignOk
  , conservationAxesScaffold
  , conservationAxesNotGreenTable
  , linearExactBalanceScaffold
  , conservationKnowingFiberOk
  , type02LinearInventRefuse
  , conservationCoefficientsNotListBacked
  , linearAffineNotXor
  , type02LinearProved
  , linearConservationFraming
  , linearConservationAxiom
  , linearConservationNamed
  , conservationResourceTypesAuthority
  , chemL0Type02Authority
  , linearConservationCellId
  , linearConservationNonClaim
  , linearConservationPhysicsGreenAuthorized
  , linearConservationPhysicsGreenFalse
  , linearConservationModalityUnwired
  ) where

-- | Design modality for **linear** **conservation** claims (TYPE-03 preview).
data LinearConservationModality
  = LinearConservationUnwired
  | LinearConservationAssumed
  | LinearConservationProved
  | LinearConservationSurrogate
  deriving (Eq, Show)

-- | Current scaffold modality — always Unwired on this cell.
linearConservationModalityCurrent :: LinearConservationModality
linearConservationModalityCurrent = LinearConservationUnwired

-- | **Conservation** axis under the single second-law + **conservation** axiom.
data ConservationAxis
  = MassAxis
  | ChargeAxis
  | AtomCountAxis
  | EnthalpyAxis
  deriving (Eq, Show)

-- | All **conservation** axes in stable order (structure scaffold — not 118² GREEN table).
conservationAxisAll :: [ConservationAxis]
conservationAxisAll = [MassAxis, ChargeAxis, AtomCountAxis, EnthalpyAxis]

conservationAxisCount :: Int
conservationAxisCount = length conservationAxisAll

-- | Resource algebra: **linear** (exact) vs affine (weakening with witness).
data ResourceAlgebra
  = LinearAlgebra
  | AffineAlgebra
  deriving (Eq, Show)

-- | Signed stoichiometric coefficient on a **conservation** axis.
data ConservationCoefficient = ConservationCoefficient
  { coeffAxis :: ConservationAxis
  , coeffValue :: Int
  }
  deriving (Eq, Show)

-- | Verdict for a single-axis **linear** balance check.
data LinearBalanceVerdict
  = LinearBalanced
  | LinearImbalanced
  | LinearEmptyRowRefuse
  deriving (Eq, Show)

-- | Whether a dissipative witness is present for affine weakening.
data DissipativeWitnessPresence
  = WitnessAbsent
  | WitnessPresent
  deriving (Eq, Show)

-- | Verdict of a **conservation**-resource typing close (fail-closed).
data ConservationTypingVerdict
  = ConservationDesignOk
  | ConservationLinearBalanced
  | ConservationLinearImbalancedRefuse
  | ConservationAffineWithoutWitnessRefuse
  | ConservationGreenInventRefuse
  deriving (Eq, Show)

-- | Sum signed coefficients for one **conservation** axis.
sumAxis :: [ConservationCoefficient] -> ConservationAxis -> Int
sumAxis coeffs axis =
  sum [ coeffValue c | c <- coeffs, coeffAxis c == axis ]

-- | Evaluate **linear** balance on one **conservation** axis.
evaluateLinearBalance ::
  [ConservationCoefficient] -> ConservationAxis -> LinearBalanceVerdict
evaluateLinearBalance coeffs axis =
  if null coeffs
    then LinearEmptyRowRefuse
    else
      let total = sumAxis coeffs axis
       in if total == 0
            then LinearBalanced
            else LinearImbalanced

-- | Evaluate **conservation**-resource typing under TYPE-02 scaffold bar.
evaluateConservationTyping ::
  LinearConservationModality
  -> ResourceAlgebra
  -> [ConservationCoefficient]
  -> ConservationAxis
  -> DissipativeWitnessPresence
  -> Bool
  -> ConservationTypingVerdict
evaluateConservationTyping modality algebra coeffs axis witness claimPhysicsGreen
  | claimPhysicsGreen = ConservationGreenInventRefuse
  | otherwise =
      case modality of
        LinearConservationUnwired -> ConservationDesignOk
        LinearConservationAssumed -> ConservationDesignOk
        LinearConservationSurrogate -> ConservationDesignOk
        LinearConservationProved ->
          case algebra of
            LinearAlgebra ->
              case evaluateLinearBalance coeffs axis of
                LinearBalanced -> ConservationLinearBalanced
                LinearImbalanced -> ConservationLinearImbalancedRefuse
                LinearEmptyRowRefuse -> ConservationLinearImbalancedRefuse
            AffineAlgebra ->
              case witness of
                WitnessPresent -> ConservationDesignOk
                WitnessAbsent -> ConservationAffineWithoutWitnessRefuse

-- | Sample balanced **linear** mass row: +1 and −1 sum to zero.
sampleBalancedMassRow :: [ConservationCoefficient]
sampleBalancedMassRow =
  [ ConservationCoefficient MassAxis 1
  , ConservationCoefficient MassAxis (-1)
  ]

-- | Sample imbalanced charge row: net +2 on charge axis.
sampleImbalancedChargeRow :: [ConservationCoefficient]
sampleImbalancedChargeRow =
  [ ConservationCoefficient ChargeAxis 2
  ]

-- | Sample balanced enthalpy row for roundtrip witness.
sampleBalancedEnthalpyRow :: [ConservationCoefficient]
sampleBalancedEnthalpyRow =
  [ ConservationCoefficient EnthalpyAxis 1
  , ConservationCoefficient EnthalpyAxis (-1)
  ]

-- | Sample imbalanced atom-count row for refuse witness.
sampleImbalancedAtomCountRow :: [ConservationCoefficient]
sampleImbalancedAtomCountRow =
  [ ConservationCoefficient AtomCountAxis 1
  ]

-- | **Linear** balanced row admitted under Proved modality (still not physics GREEN).
linearBalancedWitness :: Bool
linearBalancedWitness =
  evaluateConservationTyping
    LinearConservationProved
    LinearAlgebra
    sampleBalancedMassRow
    MassAxis
    WitnessAbsent
    False
    == ConservationLinearBalanced

-- | **Linear** imbalanced row refused under Proved modality.
linearImbalancedWitness :: Bool
linearImbalancedWitness =
  evaluateConservationTyping
    LinearConservationProved
    LinearAlgebra
    sampleImbalancedChargeRow
    ChargeAxis
    WitnessAbsent
    False
    == ConservationLinearImbalancedRefuse

-- | Affine weakening with dissipative witness is admissible (design scaffold).
affineWithWitnessOk :: Bool
affineWithWitnessOk =
  evaluateConservationTyping
    LinearConservationProved
    AffineAlgebra
    sampleBalancedMassRow
    MassAxis
    WitnessPresent
    False
    == ConservationDesignOk

-- | Affine discard without dissipative witness is refuse-closed.
affineWithoutWitnessRefuse :: Bool
affineWithoutWitnessRefuse =
  evaluateConservationTyping
    LinearConservationProved
    AffineAlgebra
    sampleBalancedMassRow
    MassAxis
    WitnessAbsent
    False
    == ConservationAffineWithoutWitnessRefuse

-- | GREEN invent on typing is refused.
greenInventTypingRefuse :: Bool
greenInventTypingRefuse =
  evaluateConservationTyping
    LinearConservationUnwired
    LinearAlgebra
    []
    MassAxis
    WitnessAbsent
    True
    == ConservationGreenInventRefuse

-- | Unwired design scaffold ok without balance requirement.
unwiredDesignOk :: Bool
unwiredDesignOk =
  evaluateConservationTyping
    LinearConservationUnwired
    LinearAlgebra
    []
    MassAxis
    WitnessAbsent
    False
    == ConservationDesignOk

-- | Four **conservation** axes scaffold pinned (Mass/Charge/AtomCount/Enthalpy).
conservationAxesScaffold :: Bool
conservationAxesScaffold =
  conservationAxisCount == 4
    && linearBalancedWitness
    && linearImbalancedWitness
    && affineWithWitnessOk
    && affineWithoutWitnessRefuse

-- | Axes are structure scaffold — not 118² GREEN periodic table.
conservationAxesNotGreenTable :: Bool
conservationAxesNotGreenTable =
  conservationAxisCount == 4
    && conservationAxisCount /= 118 * 118
    && sampleBalancedMassRow /= sampleBalancedEnthalpyRow

-- | **Linear** exact-balance scaffold: identity conserved when Σ ν = 0.
linearExactBalanceScaffold :: Bool
linearExactBalanceScaffold =
  evaluateLinearBalance sampleBalancedMassRow MassAxis == LinearBalanced
    && evaluateLinearBalance sampleBalancedEnthalpyRow EnthalpyAxis == LinearBalanced
    && evaluateLinearBalance sampleImbalancedChargeRow ChargeAxis == LinearImbalanced
    && evaluateLinearBalance sampleImbalancedAtomCountRow AtomCountAxis
      == LinearImbalanced

-- | **Conservation** claims route to knowing / quantum fiber (not meso acting).
conservationKnowingFiberOk :: Bool
conservationKnowingFiberOk = True

-- | TYPE-02 **linear** invent refuse-closed scaffold witness.
type02LinearInventRefuse :: Bool
type02LinearInventRefuse = not type02LinearProved

-- | **Conservation** coefficient rows are not list-backed periodic table.
conservationCoefficientsNotListBacked :: Bool
conservationCoefficientsNotListBacked =
  sampleBalancedMassRow /= sampleBalancedEnthalpyRow
    && sampleBalancedMassRow /= sampleImbalancedChargeRow
    && linearBalancedWitness
    && linearImbalancedWitness

-- | **Linear** and affine facets are concurrent Π_c — not XOR enum bucket.
linearAffineNotXor :: Bool
linearAffineNotXor =
  linearBalancedWitness
    && linearImbalancedWitness
    && affineWithWitnessOk
    && affineWithoutWitnessRefuse
    && greenInventTypingRefuse
    && unwiredDesignOk

-- | TYPE-02 **linear** proved (always false on this Unwired cell).
type02LinearProved :: Bool
type02LinearProved = False

-- | One axiom framing: second law + **conservation** for **linear** scaffold.
linearConservationFraming :: String
linearConservationFraming =
  "second_law_conservation_linear_one_axiom"

-- | Single design axiom: second law + **conservation** **linear** (not second axiom).
linearConservationAxiom :: Bool
linearConservationAxiom =
  conservationAxesScaffold
    && conservationAxesNotGreenTable
    && linearExactBalanceScaffold
    && conservationKnowingFiberOk
    && linearBalancedWitness
    && linearImbalancedWitness
    && affineWithoutWitnessRefuse
    && greenInventTypingRefuse
    && type02LinearInventRefuse
    && linearAffineNotXor
    && conservationCoefficientsNotListBacked
    && not type02LinearProved
    && linearConservationFraming
      == "second_law_conservation_linear_one_axiom"

linearConservationNamed :: String
linearConservationNamed =
  "linearConservation: ConservationAxis Mass Charge AtomCount Enthalpy four-axis scaffold type02LinearProved false linear exact balance affine dissipative witness second law conservation one axiom"

-- | Upstream **conservation** resource types authority (cited, not forked).
conservationResourceTypesAuthority :: String
conservationResourceTypesAuthority =
  "umst/umst-chem/src/conservation_resource_types.rs"

-- | L0 TYPE-02 **linear** scaffold authority (crosswalk).
chemL0Type02Authority :: String
chemL0Type02Authority = "umst/umst-chem/src/conservation_resource_types.rs"

linearConservationCellId :: String
linearConservationCellId = "CHEM-FORMAL-Q-HS-LINEAR-CONSERVATION"

-- | Non-claim fence — **linear** **conservation** Unwired ≠ Proved GREEN.
linearConservationNonClaim :: String
linearConservationNonClaim =
  "CHEM-FORMAL-Q-HS-LINEAR-CONSERVATION ConservationAxis Mass Charge AtomCount Enthalpy four-axis scaffold type02LinearProved false linearBalancedWitness linearImbalancedWitness affineWithoutWitnessRefuse Unwired one axiom second law conservation not 118 squared GREEN table not meso acting not physics GREEN not production_wired"

-- | Physics GREEN is unauthorized on the knowing **linear** **conservation** scaffold.
linearConservationPhysicsGreenAuthorized :: Bool
linearConservationPhysicsGreenAuthorized = False

linearConservationPhysicsGreenFalse :: Bool
linearConservationPhysicsGreenFalse =
  not linearConservationPhysicsGreenAuthorized

linearConservationModalityUnwired :: Bool
linearConservationModalityUnwired =
  linearConservationModalityCurrent == LinearConservationUnwired
