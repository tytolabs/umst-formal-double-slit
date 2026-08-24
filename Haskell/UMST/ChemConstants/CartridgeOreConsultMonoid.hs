-- SPDX-FileCopyrightText: 2026 Santosh Prabhu Shenbagamoorthy and Santhosh Shyamsundar
-- SPDX-License-Identifier: MIT

{-|
Module      : UMST.ChemConstants.CartridgeOreConsultMonoid
Description : Cartridge Ore consult monoid conservation on the matter fiber
Copyright   : (c) UMST Project, 2026

Cartridge Ore consult monoid conservation: C-S-H (Ca,Si,O,H) and pore solution
(Na,Cl,O,H) are Ore consults, not ElementId smuggle; pattern for Z=1..118
assemblages. Consult ChemistryService; no second periodic table. Monoid laws are
structure witnesses only (@consultMonoidLawsProved@ = False).

* @cshOreZ@ / @poreOreZ@ — Ore Z factors in 1..118 bar (not new ElementId rows).
* @cshIsElementId@ / @poreSolutionIsElementId@ — always false @ Unwired.
* **One** design axiom (@cartridgeOreConsultMonoidAxiom@): second law + conservation.
* @physics_green@ stays false.

Haskell mirror of cartridge Ore consult monoid conservation on the matter fiber.
Cell: @CHEM-FORMAL-Q-HS-CARTRIDGE-ORE-CONSULT-MONOID-CONSERVATION@.
WAVE100: not wired in cabal.
-}
module UMST.ChemConstants.CartridgeOreConsultMonoid
  ( CartridgeOreConsultMonoidModality (..)
  , cartridgeOreConsultMonoidModalityCurrent
  , OreConsultTag (..)
  , OreConsultTree (..)
  , oreConsultUnit
  , oreConsultLeaf
  , oreConsultTensor
  , oreConsultMonoidProduct
  , cshOreZ
  , poreOreZ
  , oreFactorInBar
  , oreFactorsInBar
  , cshIsElementId
  , poreSolutionIsElementId
  , cartridgeOreConsultHonestConjunct
  , oreConsultTreeConcurrentCount
  , oreConsultMonoidProductNotXor
  , elementIdSmuggleRefuse
  , CartridgeOreConsultMonoidVerdict (..)
  , evaluateCartridgeOreConsultMonoid
  , unwiredCartridgeOreConsultDesignOk
  , greenInventCartridgeOreConsultRefuse
  , cshElementIdSmuggleRefuse
  , poreElementIdSmuggleRefuse
  , provedWithoutBarCartridgeOreConsultRefuse
  , cartridgeOreConsultMonoidScaffold
  , CartridgeOreConsultMonoidProbe (..)
  , cartridgeOreConsultMonoidProbe
  , cartridgeOreConsultMonoidHonest
  , consultMonoidLawsProved
  , cartridgeOreConsultMonoidFraming
  , cartridgeOreConsultMonoidAxiom
  , cartridgeOreConsultMonoidNamed
  , cartridgeOreConsultMonoidAuthority
  , oreMonoidalProductAuthority
  , chemistryServiceAuthority
  , cartridgeOreConsultMonoidCellId
  , cartridgeOreConsultMonoidNonClaim
  , cartridgeOreConsultMonoidPhysicsGreenAuthorized
  , cartridgeOreConsultMonoidPhysicsGreenFalse
  , cartridgeOreConsultMonoidModalityUnwired
  ) where

-- | Design modality for cartridge Ore consult monoid claims (TYPE-03 preview).
data CartridgeOreConsultMonoidModality
  = CartridgeOreConsultMonoidUnwired
  | CartridgeOreConsultMonoidAssumed
  | CartridgeOreConsultMonoidProved
  | CartridgeOreConsultMonoidSurrogate
  deriving (Eq, Show)

-- | Current scaffold modality — always Unwired on this cell.
cartridgeOreConsultMonoidModalityCurrent :: CartridgeOreConsultMonoidModality
cartridgeOreConsultMonoidModalityCurrent = CartridgeOreConsultMonoidUnwired

-- | Named Ore consult factor tags (bounded scaffold — not XOR enum).
data OreConsultTag
  = CshConsult
  | PoreSolutionConsult
  deriving (Eq, Show)

-- | Algebraic OreConsultTree — unit @I@, leaf consult, tensor product (not ElementId).
data OreConsultTree
  = OreConsultUnit
  | OreConsultLeaf OreConsultTag
  | OreConsultTensor OreConsultTree OreConsultTree
  deriving (Eq, Show)

-- | Monoidal unit @I@ — inert / vacuum limit.
oreConsultUnit :: OreConsultTree
oreConsultUnit = OreConsultUnit

-- | Leaf Ore consult pin — C-S-H or pore solution, not ElementId smuggle.
oreConsultLeaf :: OreConsultTag -> OreConsultTree
oreConsultLeaf = OreConsultLeaf

-- | Tensor product node — concurrent Π_c consult, not XOR bucket.
oreConsultTensor :: OreConsultTree -> OreConsultTree -> OreConsultTree
oreConsultTensor = OreConsultTensor

-- | Monoidal product alias on @OreConsultTree@.
oreConsultMonoidProduct :: OreConsultTree -> OreConsultTree -> OreConsultTree
oreConsultMonoidProduct = oreConsultTensor

-- | C-S-H Ore Z factors (Ca, Si, O, H).
cshOreZ :: [Int]
cshOreZ = [20, 14, 8, 1]

-- | Pore-solution Ore Z factors (Na, Cl, O, H).
poreOreZ :: [Int]
poreOreZ = [11, 17, 8, 1]

-- | Whether a single Ore Z factor lies in the 1..118 bar.
oreFactorInBar :: Int -> Bool
oreFactorInBar z = z >= 1 && z <= 118

-- | All Ore Z factors in C-S-H and pore solution consults lie in 1..118.
oreFactorsInBar :: Bool
oreFactorsInBar = all oreFactorInBar cshOreZ && all oreFactorInBar poreOreZ

-- | Whether C-S-H is a new ElementId (always false @ Unwired).
cshIsElementId :: Bool
cshIsElementId = False

-- | Whether pore solution is a new ElementId (always false @ Unwired).
poreSolutionIsElementId :: Bool
poreSolutionIsElementId = False

-- | Consult conjunct — Ore consults, not ElementId smuggle.
cartridgeOreConsultHonestConjunct :: Bool
cartridgeOreConsultHonestConjunct =
  not cshIsElementId
    && not poreSolutionIsElementId
    && oreFactorsInBar

oreConsultTreeConstituentPresent :: OreConsultTree -> OreConsultTag -> Bool
oreConsultTreeConstituentPresent t tag = case t of
  OreConsultUnit -> False
  OreConsultLeaf t' -> t' == tag
  OreConsultTensor left right ->
    oreConsultTreeConstituentPresent left tag
      || oreConsultTreeConstituentPresent right tag

oreConsultTreeConcurrentCount :: OreConsultTree -> Int
oreConsultTreeConcurrentCount t =
  sum
    [ if oreConsultTreeConstituentPresent t CshConsult then 1 else 0
    , if oreConsultTreeConstituentPresent t PoreSolutionConsult then 1 else 0
    ]

-- | Paired C-S-H ⊗ pore-solution consult — concurrent Π_c, not XOR enum.
dualOreConsultTree :: OreConsultTree
dualOreConsultTree =
  oreConsultMonoidProduct
    (oreConsultLeaf CshConsult)
    (oreConsultLeaf PoreSolutionConsult)

-- | Product factors are concurrent Π_c — not XOR enum bucket.
oreConsultMonoidProductNotXor :: Bool
oreConsultMonoidProductNotXor =
  oreConsultTreeConcurrentCount dualOreConsultTree >= 2
    && oreConsultTreeConcurrentCount dualOreConsultTree == 2

-- | Verdict for cartridge Ore consult monoid close (fail-closed).
data CartridgeOreConsultMonoidVerdict
  = CartridgeOreConsultMonoidDesignOk
  | CartridgeOreConsultMonoidNamedOk
  | CartridgeOreConsultMonoidGreenInventRefuse
  | CartridgeOreConsultMonoidCshElementIdSmuggleRefuse
  | CartridgeOreConsultMonoidPoreElementIdSmuggleRefuse
  | CartridgeOreConsultMonoidProvedWithoutBarRefuse
  deriving (Eq, Show)

-- | Evaluate cartridge Ore consult monoid under honest bar (fail-closed).
evaluateCartridgeOreConsultMonoid ::
  CartridgeOreConsultMonoidModality
  -> Bool
  -> Bool
  -> Bool
  -> Bool
  -> Bool
  -> CartridgeOreConsultMonoidVerdict
evaluateCartridgeOreConsultMonoid
  modality
  claimPhysicsGreen
  claimProved
  claimCshElementId
  claimPoreElementId
  claimGreenInvent
  | claimPhysicsGreen || claimGreenInvent =
      CartridgeOreConsultMonoidGreenInventRefuse
  | claimCshElementId = CartridgeOreConsultMonoidCshElementIdSmuggleRefuse
  | claimPoreElementId = CartridgeOreConsultMonoidPoreElementIdSmuggleRefuse
  | claimProved = CartridgeOreConsultMonoidProvedWithoutBarRefuse
  | not cartridgeOreConsultHonestConjunct =
      CartridgeOreConsultMonoidDesignOk
  | otherwise =
      case modality of
        CartridgeOreConsultMonoidUnwired ->
          if oreFactorsInBar
            then CartridgeOreConsultMonoidNamedOk
            else CartridgeOreConsultMonoidDesignOk
        CartridgeOreConsultMonoidAssumed -> CartridgeOreConsultMonoidDesignOk
        CartridgeOreConsultMonoidSurrogate -> CartridgeOreConsultMonoidDesignOk
        CartridgeOreConsultMonoidProved ->
          CartridgeOreConsultMonoidProvedWithoutBarRefuse

-- | Unwired cartridge Ore consult modality OK — consults not ElementId smuggle.
unwiredCartridgeOreConsultDesignOk :: Bool
unwiredCartridgeOreConsultDesignOk =
  evaluateCartridgeOreConsultMonoid
    CartridgeOreConsultMonoidUnwired
    False
    False
    False
    False
    False
    == CartridgeOreConsultMonoidNamedOk

-- | GREEN invent on cartridge Ore consult promotion is refused.
greenInventCartridgeOreConsultRefuse :: Bool
greenInventCartridgeOreConsultRefuse =
  evaluateCartridgeOreConsultMonoid
    CartridgeOreConsultMonoidUnwired
    True
    False
    False
    False
    False
    == CartridgeOreConsultMonoidGreenInventRefuse
    && evaluateCartridgeOreConsultMonoid
      CartridgeOreConsultMonoidUnwired
      False
      False
      False
      False
      True
      == CartridgeOreConsultMonoidGreenInventRefuse

-- | C-S-H ElementId smuggle is refused.
cshElementIdSmuggleRefuse :: Bool
cshElementIdSmuggleRefuse =
  evaluateCartridgeOreConsultMonoid
    CartridgeOreConsultMonoidUnwired
    False
    False
    True
    False
    False
    == CartridgeOreConsultMonoidCshElementIdSmuggleRefuse

-- | Pore-solution ElementId smuggle is refused.
poreElementIdSmuggleRefuse :: Bool
poreElementIdSmuggleRefuse =
  evaluateCartridgeOreConsultMonoid
    CartridgeOreConsultMonoidUnwired
    False
    False
    False
    True
    False
    == CartridgeOreConsultMonoidPoreElementIdSmuggleRefuse

-- | ElementId smuggle refuse — both C-S-H and pore solution are Ore consults.
elementIdSmuggleRefuse :: Bool
elementIdSmuggleRefuse =
  cshElementIdSmuggleRefuse
    && poreElementIdSmuggleRefuse
    && not cshIsElementId
    && not poreSolutionIsElementId

-- | Proved cartridge Ore consult monoid without path census is refused.
provedWithoutBarCartridgeOreConsultRefuse :: Bool
provedWithoutBarCartridgeOreConsultRefuse =
  evaluateCartridgeOreConsultMonoid
    CartridgeOreConsultMonoidUnwired
    False
    True
    False
    False
    False
    == CartridgeOreConsultMonoidProvedWithoutBarRefuse
    && evaluateCartridgeOreConsultMonoid
      CartridgeOreConsultMonoidProved
      False
      False
      False
      False
      False
      == CartridgeOreConsultMonoidProvedWithoutBarRefuse

-- | Cartridge Ore consult monoid scaffold pinned.
cartridgeOreConsultMonoidScaffold :: Bool
cartridgeOreConsultMonoidScaffold =
  unwiredCartridgeOreConsultDesignOk
    && cartridgeOreConsultHonestConjunct
    && oreConsultMonoidProductNotXor
    && elementIdSmuggleRefuse
    && greenInventCartridgeOreConsultRefuse
    && provedWithoutBarCartridgeOreConsultRefuse
    && length cshOreZ == 4
    && length poreOreZ == 4

-- | Probe bundle for honest posture witnesses.
data CartridgeOreConsultMonoidProbe = CartridgeOreConsultMonoidProbe
  { cellIdNamed :: Bool
  , unwired :: Bool
  , physicsGreenRefused :: Bool
  , soleAxiom :: Bool
  , notProved :: Bool
  }
  deriving (Eq, Show)

-- | Honest probe — modality Unwired, physics GREEN refused.
cartridgeOreConsultMonoidProbe :: CartridgeOreConsultMonoidProbe
cartridgeOreConsultMonoidProbe =
  CartridgeOreConsultMonoidProbe
    { cellIdNamed =
        cartridgeOreConsultMonoidCellId
          == "CHEM-FORMAL-Q-HS-CARTRIDGE-ORE-CONSULT-MONOID-CONSERVATION"
    , unwired =
        cartridgeOreConsultMonoidModalityCurrent
          == CartridgeOreConsultMonoidUnwired
    , physicsGreenRefused =
        not cartridgeOreConsultMonoidPhysicsGreenAuthorized
    , soleAxiom = True
    , notProved = not consultMonoidLawsProved
    }

-- | Honest conjunct on probe bundle.
cartridgeOreConsultMonoidHonest :: Bool
cartridgeOreConsultMonoidHonest =
  let p = cartridgeOreConsultMonoidProbe
   in cellIdNamed p
        && unwired p
        && physicsGreenRefused p
        && soleAxiom p
        && notProved p
        && cartridgeOreConsultMonoidScaffold

-- | Consult monoid laws proved (always false on this Unwired cell).
consultMonoidLawsProved :: Bool
consultMonoidLawsProved = False

-- | One axiom framing: second law + conservation for cartridge Ore consult scaffold.
cartridgeOreConsultMonoidFraming :: String
cartridgeOreConsultMonoidFraming =
  "second_law_conservation_cartridge_ore_consult_monoid_one_axiom"

-- | Single design axiom: second law + conservation cartridge Ore consult (not second axiom).
cartridgeOreConsultMonoidAxiom :: Bool
cartridgeOreConsultMonoidAxiom =
  cartridgeOreConsultMonoidScaffold
    && cartridgeOreConsultHonestConjunct
    && cartridgeOreConsultMonoidHonest
    && elementIdSmuggleRefuse
    && not consultMonoidLawsProved
    && not cshIsElementId
    && not poreSolutionIsElementId
    && cartridgeOreConsultMonoidFraming
      == "second_law_conservation_cartridge_ore_consult_monoid_one_axiom"

cartridgeOreConsultMonoidNamed :: String
cartridgeOreConsultMonoidNamed =
  "cartridgeOreConsultMonoid: C-S-H Ca Si O H and pore solution Na Cl O H Ore consults not ElementId smuggle Z 1..118 assemblage pattern consult ChemistryService no second periodic table consultMonoidLawsProved false second law conservation one axiom"

-- | Upstream cartridge Ore consult monoid authority (cited, not forked).
cartridgeOreConsultMonoidAuthority :: String
cartridgeOreConsultMonoidAuthority =
  "umst/umst-chem/src/x_rows/cartridge_ore_consult_monoid.rs"

-- | Chem Ore monoidal product authority (matter ↔ knowing fiber crosswalk).
oreMonoidalProductAuthority :: String
oreMonoidalProductAuthority = "umst/umst-chem/src/ore_monoidal_product.rs"

-- | ChemistryService consult authority — no second periodic table.
chemistryServiceAuthority :: String
chemistryServiceAuthority = "umst/umst-chem/src/chemistry_service.rs"

cartridgeOreConsultMonoidCellId :: String
cartridgeOreConsultMonoidCellId =
  "CHEM-FORMAL-Q-HS-CARTRIDGE-ORE-CONSULT-MONOID-CONSERVATION"

-- | Non-claim fence — cartridge Ore consult monoid Unwired ≠ Proved GREEN.
cartridgeOreConsultMonoidNonClaim :: String
cartridgeOreConsultMonoidNonClaim =
  "CHEM-FORMAL-Q-HS-CARTRIDGE-ORE-CONSULT-MONOID-CONSERVATION C-S-H Ca Si O H pore solution Na Cl O H Ore consults not ElementId smuggle Z 1..118 assemblage pattern consultMonoidLawsProved false Unwired one axiom second law conservation not XOR enum not GREEN DFT not physics GREEN not production_wired"

-- | Physics GREEN is unauthorized on the cartridge Ore consult monoid scaffold.
cartridgeOreConsultMonoidPhysicsGreenAuthorized :: Bool
cartridgeOreConsultMonoidPhysicsGreenAuthorized = False

cartridgeOreConsultMonoidPhysicsGreenFalse :: Bool
cartridgeOreConsultMonoidPhysicsGreenFalse =
  not cartridgeOreConsultMonoidPhysicsGreenAuthorized

cartridgeOreConsultMonoidModalityUnwired :: Bool
cartridgeOreConsultMonoidModalityUnwired =
  cartridgeOreConsultMonoidModalityCurrent == CartridgeOreConsultMonoidUnwired
