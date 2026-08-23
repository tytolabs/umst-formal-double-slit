-- SPDX-FileCopyrightText: 2026 Santosh Prabhu Shenbagamoorthy and Santhosh Shyamsundar
-- SPDX-License-Identifier: MIT

{-|
Module      : UMST.ChemConstants.KleisliInteractConservation
Description : Kleisli Interact conservation on the knowing fiber (Q lattice)
Copyright   : (c) UMST Project, 2026

Kleisli Interact conservation: @InteractStep@ Kleisli arrows for Interact concurrent
Π_c — identity @id@, associator scaffold, compose **not** XOR enum buckets. Kleisli laws
are structure witnesses only (@kleisliLawsProved@ = False).

* @InteractStep@ = named from/to/tag — Kleisli carrier, not @Vec@ list.
* @interactComposeNotXor@ — concurrent Π_c may chain ≥2 interaction steps.
* **One** design axiom (@kleisliInteractConservationAxiom@): second law + conservation.
* Morphism identity (from/to endpoints) conserved under identity / associator scaffold.
* @physics_green@ stays false.

Haskell mirror of Kleisli Interact conservation on the quantum / knowing fiber.
Cell: @CHEM-FORMAL-Q-HS-KLEISLI-INTERACT-CONSERVATION@.
-}
module UMST.ChemConstants.KleisliInteractConservation
  ( KleisliInteractConservationModality (..)
  , kleisliInteractConservationModalityCurrent
  , InteractElementTag (..)
  , InteractStep (..)
  , interactIdentity
  , interactCompose
  , interactStepFrom
  , interactStepTo
  , interactStepIsIdentity
  , interactStepMorphismPresent
  , interactStepChainCount
  , kleisliLeftUnitScaffold
  , kleisliRightUnitScaffold
  , kleisliAssociator
  , kleisliAssociativeScaffold
  , morphismIdentityConservedUnderIdentity
  , morphismIdentityConservedUnderAssociator
  , interactComposeNotXor
  , interactStepNotListBacked
  , kleisliLawsProved
  , kleisliInteractConservationFraming
  , kleisliInteractConservationAxiom
  , kleisliInteractConservationNamed
  , kleisliInteractAuthority
  , kleisliAdoptLiftAuthority
  , kleisliInteractConservationCellId
  , kleisliInteractConservationNonClaim
  , kleisliInteractConservationPhysicsGreenAuthorized
  , kleisliInteractConservationPhysicsGreenFalse
  , kleisliInteractConservationModalityUnwired
  ) where

-- | Design modality for Kleisli Interact conservation claims (TYPE-03 preview).
data KleisliInteractConservationModality
  = KleisliInteractConservationUnwired
  | KleisliInteractConservationAssumed
  | KleisliInteractConservationProved
  | KleisliInteractConservationSurrogate
  deriving (Eq, Show)

-- | Current scaffold modality — always Unwired on this cell.
kleisliInteractConservationModalityCurrent :: KleisliInteractConservationModality
kleisliInteractConservationModalityCurrent = KleisliInteractConservationUnwired

-- | Named interaction element factor tags (bounded scaffold — not XOR enum).
data InteractElementTag
  = CaScaffold
  | OScaffold
  | HScaffold
  deriving (Eq, Show)

-- | Minimal L0 interaction step — Kleisli arrow carrier (design scaffold).
data InteractStep
  = InteractStep InteractElementTag InteractElementTag Int
  deriving (Eq, Show)

-- | Kleisli identity morphism — left/right unit witness carrier.
interactIdentity :: InteractElementTag -> InteractStep
interactIdentity element = InteractStep element element 0

-- | Kleisli compose @left >=> right@ when @left.to == right.from@ (fail-closed).
interactCompose :: InteractStep -> InteractStep -> Maybe InteractStep
interactCompose (InteractStep leftFrom leftTo leftTag) (InteractStep rightFrom rightTo rightTag) =
  if leftTo == rightFrom
    then Just (InteractStep leftFrom rightTo (leftTag + rightTag + 1))
    else Nothing

interactStepFrom :: InteractStep -> InteractElementTag
interactStepFrom (InteractStep from _ _) = from

interactStepTo :: InteractStep -> InteractElementTag
interactStepTo (InteractStep _ to _) = to

interactStepIsIdentity :: InteractStep -> Bool
interactStepIsIdentity step =
  interactStepFrom step == interactStepTo step && interactStepTag step == 0

interactStepTag :: InteractStep -> Int
interactStepTag (InteractStep _ _ tag) = tag

interactStepMorphismPresent :: InteractStep -> InteractElementTag -> Bool
interactStepMorphismPresent step tag =
  interactStepFrom step == tag || interactStepTo step == tag

interactStepChainCount :: InteractStep -> Int
interactStepChainCount step =
  sum
    [ if interactStepMorphismPresent step CaScaffold then 1 else 0
    , if interactStepMorphismPresent step OScaffold then 1 else 0
    , if interactStepMorphismPresent step HScaffold then 1 else 0
    ]

-- | Sample interaction step for unit-law scaffold witnesses.
sampleInteractStep :: InteractStep
sampleInteractStep = InteractStep CaScaffold OScaffold 1

-- | Left unit scaffold: @id >=> f@ preserves morphism identity.
kleisliLeftUnitScaffold :: Bool
kleisliLeftUnitScaffold =
  case interactCompose (interactIdentity (interactStepFrom sampleInteractStep)) sampleInteractStep of
    Just composed ->
      interactStepFrom composed == interactStepFrom sampleInteractStep
        && interactStepTo composed == interactStepTo sampleInteractStep
    _ -> False

-- | Right unit scaffold: @f >=> id@ preserves morphism identity.
kleisliRightUnitScaffold :: Bool
kleisliRightUnitScaffold =
  case interactCompose sampleInteractStep (interactIdentity (interactStepTo sampleInteractStep)) of
    Just composed ->
      interactStepFrom composed == interactStepFrom sampleInteractStep
        && interactStepTo composed == interactStepTo sampleInteractStep
    _ -> False

-- | Associator scaffold — left vs right Kleisli bracketings (laws still Unwired).
kleisliAssociator :: InteractStep -> InteractStep -> InteractStep -> (Maybe InteractStep, Maybe InteractStep)
kleisliAssociator f g h =
  let leftBracket = interactCompose f g >>= (`interactCompose` h)
      rightBracket =
        case interactCompose g h of
          Just gh -> interactCompose f gh
          Nothing -> Nothing
   in (leftBracket, rightBracket)

-- | Associativity bracketings agree on morphism identity (structure scaffold).
kleisliAssociativeScaffold :: Bool
kleisliAssociativeScaffold =
  let f = InteractStep CaScaffold OScaffold 1
      g = InteractStep OScaffold HScaffold 2
      h = InteractStep HScaffold CaScaffold 3
      (leftBracket, rightBracket) = kleisliAssociator f g h
   in case (leftBracket, rightBracket) of
        (Just left, Just right) ->
          interactStepFrom left == interactStepFrom right
            && interactStepTo left == interactStepTo right
            && left == right
        _ -> False

-- | Morphism endpoints conserved under Kleisli identity compose.
morphismIdentityConservedUnderIdentity :: Bool
morphismIdentityConservedUnderIdentity =
  kleisliLeftUnitScaffold && kleisliRightUnitScaffold

-- | Morphism endpoints conserved under associator bracketings.
morphismIdentityConservedUnderAssociator :: Bool
morphismIdentityConservedUnderAssociator = kleisliAssociativeScaffold

-- | Fixture chain Ca→O→H→Ca — concurrent Π_c interaction scaffold.
fixtureInteractChain :: InteractStep
fixtureInteractChain =
  case interactCompose
    (InteractStep CaScaffold OScaffold 1)
    (InteractStep OScaffold HScaffold 2) of
    Just fg ->
      case interactCompose fg (InteractStep HScaffold CaScaffold 3) of
        Just chain -> chain
        _ -> InteractStep CaScaffold CaScaffold (-1)
    _ -> InteractStep CaScaffold CaScaffold (-1)

-- | Compose factors are concurrent Π_c — not XOR enum bucket.
interactComposeNotXor :: Bool
interactComposeNotXor =
  interactStepChainCount fixtureInteractChain >= 2
    && interactStepFrom fixtureInteractChain == CaScaffold
    && interactStepTo fixtureInteractChain == CaScaffold

-- | InteractStep algebra is not list-backed (Kleisli chain scaffold).
interactStepNotListBacked :: Bool
interactStepNotListBacked =
  interactStepFrom fixtureInteractChain /= interactStepTo fixtureInteractChain
    || interactStepTag fixtureInteractChain /= 0

-- | Kleisli laws proved (always false on this Unwired cell).
kleisliLawsProved :: Bool
kleisliLawsProved = False

-- | One axiom framing: second law + conservation for Kleisli Interact scaffold.
kleisliInteractConservationFraming :: String
kleisliInteractConservationFraming =
  "second_law_conservation_kleisli_interact_one_axiom"

-- | Single design axiom: second law + conservation Kleisli Interact (not second axiom).
kleisliInteractConservationAxiom :: Bool
kleisliInteractConservationAxiom =
  interactStepNotListBacked
    && kleisliLeftUnitScaffold
    && kleisliRightUnitScaffold
    && kleisliAssociativeScaffold
    && morphismIdentityConservedUnderIdentity
    && morphismIdentityConservedUnderAssociator
    && interactComposeNotXor
    && not kleisliLawsProved
    && kleisliInteractConservationFraming
      == "second_law_conservation_kleisli_interact_one_axiom"

kleisliInteractConservationNamed :: String
kleisliInteractConservationNamed =
  "kleisliInteractConservation: InteractStep identity/compose associator; concurrent Π_c chain not XOR; Kleisli laws Unwired not Proved; morphism identity conserved; second law + conservation one axiom"

-- | Upstream Kleisli Interact authority (cited, not forked).
kleisliInteractAuthority :: String
kleisliInteractAuthority = "umst/umst-chem/src/kleisli_interact.rs"

-- | ARCS kleisli_adopt lift surface (read-only census path).
kleisliAdoptLiftAuthority :: String
kleisliAdoptLiftAuthority = "umst/umst-arcs/src/kleisli_adopt/lib.rs"

kleisliInteractConservationCellId :: String
kleisliInteractConservationCellId = "CHEM-FORMAL-Q-HS-KLEISLI-INTERACT-CONSERVATION"

-- | Non-claim fence — Kleisli Interact conservation Unwired ≠ Proved GREEN.
kleisliInteractConservationNonClaim :: String
kleisliInteractConservationNonClaim =
  "CHEM-FORMAL-Q-HS-KLEISLI-INTERACT-CONSERVATION InteractStep identity compose associator morphismIdentityConserved kleisliLawsProved false Unwired one axiom second law conservation not XOR enum not Vec list not GREEN DFT not physics GREEN not production_wired"

-- | Physics GREEN is unauthorized on the knowing Kleisli Interact conservation scaffold.
kleisliInteractConservationPhysicsGreenAuthorized :: Bool
kleisliInteractConservationPhysicsGreenAuthorized = False

kleisliInteractConservationPhysicsGreenFalse :: Bool
kleisliInteractConservationPhysicsGreenFalse =
  not kleisliInteractConservationPhysicsGreenAuthorized

kleisliInteractConservationModalityUnwired :: Bool
kleisliInteractConservationModalityUnwired =
  kleisliInteractConservationModalityCurrent == KleisliInteractConservationUnwired
