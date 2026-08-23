-- SPDX-FileCopyrightText: 2026 Santosh Prabhu Shenbagamoorthy and Santhosh Shyamsundar
-- SPDX-License-Identifier: MIT

{-|
Module      : UMST.ChemConstants.OreMonoidalConservation
Description : Ore monoidal conservation on the knowing fiber (Q lattice)
Copyright   : (c) UMST Project, 2026

Ore monoidal conservation: @OreTree@ leaf/tensor product tree for OreAssemblage concurrent
Π_c — unit @I@, associator scaffold, product **not** XOR enum buckets. Monoid laws are
structure witnesses only (@monoidalLawsProved@ = False).

* @OreTree@ = Unit | Leaf | Tensor — binary product tree, not @Vec@ list.
* @oreMonoidalProductNotXor@ — concurrent Π_c may hold ≥2 constituents.
* **One** design axiom (@oreMonoidalConservationAxiom@): second law + conservation.
* @physics_green@ stays false.

Haskell mirror of ore monoidal conservation on the quantum / knowing fiber.
Cell: @CHEM-FORMAL-Q-HS-ORE-MONOIDAL-CONSERVATION@.
-}
module UMST.ChemConstants.OreMonoidalConservation
  ( OreMonoidalConservationModality (..)
  , oreMonoidalConservationModalityCurrent
  , OreConstituentTag (..)
  , OreTree (..)
  , oreUnit
  , oreLeaf
  , oreTensor
  , oreMonoidalProduct
  , oreTreeIsUnit
  , oreTreeIsTensor
  , oreTreeConstituentPresent
  , oreTreeConcurrentCount
  , oreMonoidalLeftUnitScaffold
  , oreMonoidalRightUnitScaffold
  , oreMonoidalAssociator
  , oreMonoidalAssociativeScaffold
  , oreMonoidalProductNotXor
  , oreTreeNotListBacked
  , monoidalLawsProved
  , oreMonoidalConservationFraming
  , oreMonoidalConservationAxiom
  , oreMonoidalConservationNamed
  , oreMonoidalProductAuthority
  , oreAssemblageAuthority
  , oreMonoidalConservationCellId
  , oreMonoidalConservationNonClaim
  , oreMonoidalConservationPhysicsGreenAuthorized
  , oreMonoidalConservationPhysicsGreenFalse
  , oreMonoidalConservationModalityUnwired
  ) where

-- | Design modality for ore monoidal conservation claims (TYPE-03 preview).
data OreMonoidalConservationModality
  = OreMonoidalConservationUnwired
  | OreMonoidalConservationAssumed
  | OreMonoidalConservationProved
  | OreMonoidalConservationSurrogate
  deriving (Eq, Show)

-- | Current scaffold modality — always Unwired on this cell.
oreMonoidalConservationModalityCurrent :: OreMonoidalConservationModality
oreMonoidalConservationModalityCurrent = OreMonoidalConservationUnwired

-- | Named monoidal constituent factor tags (bounded scaffold — not XOR enum).
data OreConstituentTag
  = HematiteScaffold
  | QuartzScaffold
  | GangueScaffold
  deriving (Eq, Show)

-- | Algebraic OreTree — unit @I@, leaf, tensor product (not @Vec@ list).
data OreTree
  = OreUnit
  | OreLeaf OreConstituentTag
  | OreTensor OreTree OreTree
  deriving (Eq, Show)

-- | Monoidal unit @I@ — inert / vacuum limit.
oreUnit :: OreTree
oreUnit = OreUnit

-- | Leaf constituent pin.
oreLeaf :: OreConstituentTag -> OreTree
oreLeaf = OreLeaf

-- | Tensor product node — concurrent Π_c, not XOR bucket.
oreTensor :: OreTree -> OreTree -> OreTree
oreTensor = OreTensor

-- | Monoidal product alias on @OreTree@.
oreMonoidalProduct :: OreTree -> OreTree -> OreTree
oreMonoidalProduct = oreTensor

oreTreeIsUnit :: OreTree -> Bool
oreTreeIsUnit t = case t of
  OreUnit -> True
  _ -> False

oreTreeIsTensor :: OreTree -> Bool
oreTreeIsTensor t = case t of
  OreTensor _ _ -> True
  _ -> False

oreTreeConstituentPresent :: OreTree -> OreConstituentTag -> Bool
oreTreeConstituentPresent t tag = case t of
  OreUnit -> False
  OreLeaf t' -> t' == tag
  OreTensor left right ->
    oreTreeConstituentPresent left tag
      || oreTreeConstituentPresent right tag

oreTreeConcurrentCount :: OreTree -> Int
oreTreeConcurrentCount t =
  sum
    [ if oreTreeConstituentPresent t HematiteScaffold then 1 else 0
    , if oreTreeConstituentPresent t QuartzScaffold then 1 else 0
    , if oreTreeConstituentPresent t GangueScaffold then 1 else 0
    ]

-- | Sample leaf for unit-law scaffold witnesses.
sampleOreLeaf :: OreTree
sampleOreLeaf = oreLeaf HematiteScaffold

-- | Left unit scaffold: @I ⊗ a@ is a tensor with unit on the left.
oreMonoidalLeftUnitScaffold :: Bool
oreMonoidalLeftUnitScaffold =
  case oreMonoidalProduct oreUnit sampleOreLeaf of
    OreTensor left _ -> oreTreeIsUnit left
    _ -> False

-- | Right unit scaffold: @a ⊗ I@ is a tensor with unit on the right.
oreMonoidalRightUnitScaffold :: Bool
oreMonoidalRightUnitScaffold =
  case oreMonoidalProduct sampleOreLeaf oreUnit of
    OreTensor _ right -> oreTreeIsUnit right
    _ -> False

-- | Associator scaffold — left vs right bracketings (laws still Unwired).
oreMonoidalAssociator :: OreTree -> OreTree -> OreTree -> (OreTree, OreTree)
oreMonoidalAssociator a b c =
  ( oreMonoidalProduct (oreMonoidalProduct a b) c
  , oreMonoidalProduct a (oreMonoidalProduct b c)
  )

-- | Associativity bracketings are both tensor trees but differ structurally.
oreMonoidalAssociativeScaffold :: Bool
oreMonoidalAssociativeScaffold =
  let a = oreLeaf HematiteScaffold
      b = oreLeaf QuartzScaffold
      c = oreLeaf GangueScaffold
      (leftAssoc, rightAssoc) = oreMonoidalAssociator a b c
   in oreTreeIsTensor leftAssoc
        && oreTreeIsTensor rightAssoc
        && leftAssoc /= rightAssoc

-- | Triple-ore concurrent product — Π_c not XOR enum growth.
tripleOreTree :: OreTree
tripleOreTree =
  oreMonoidalProduct
    (oreMonoidalProduct (oreLeaf HematiteScaffold) (oreLeaf QuartzScaffold))
    (oreLeaf GangueScaffold)

-- | Product factors are concurrent Π_c — not XOR enum bucket.
oreMonoidalProductNotXor :: Bool
oreMonoidalProductNotXor =
  oreTreeConcurrentCount tripleOreTree >= 2
    && oreTreeConcurrentCount tripleOreTree == 3

-- | OreTree algebra is not list-backed (product tree scaffold).
oreTreeNotListBacked :: Bool
oreTreeNotListBacked = oreTreeIsTensor tripleOreTree

-- | Monoid laws proved (always false on this Unwired cell).
monoidalLawsProved :: Bool
monoidalLawsProved = False

-- | One axiom framing: second law + conservation for ore monoidal scaffold.
oreMonoidalConservationFraming :: String
oreMonoidalConservationFraming =
  "second_law_conservation_ore_monoidal_one_axiom"

-- | Single design axiom: second law + conservation ore monoidal (not second axiom).
oreMonoidalConservationAxiom :: Bool
oreMonoidalConservationAxiom =
  oreTreeNotListBacked
    && oreMonoidalLeftUnitScaffold
    && oreMonoidalRightUnitScaffold
    && oreMonoidalAssociativeScaffold
    && oreMonoidalProductNotXor
    && not monoidalLawsProved
    && oreMonoidalConservationFraming
      == "second_law_conservation_ore_monoidal_one_axiom"

oreMonoidalConservationNamed :: String
oreMonoidalConservationNamed =
  "oreMonoidalConservation: OreTree leaf/tensor unit I associator; concurrent Π_c product not XOR; monoidal laws Unwired not Proved; second law + conservation one axiom"

-- | Upstream monoidal product authority (cited, not forked).
oreMonoidalProductAuthority :: String
oreMonoidalProductAuthority = "umst/umst-chem/src/ore_monoidal_product.rs"

-- | L0 OreAssemblage scaffold authority (ORE-00 crosswalk).
oreAssemblageAuthority :: String
oreAssemblageAuthority = "umst/umst-chem/src/ore_assemblage.rs"

oreMonoidalConservationCellId :: String
oreMonoidalConservationCellId = "CHEM-FORMAL-Q-HS-ORE-MONOIDAL-CONSERVATION"

-- | Non-claim fence — ore monoidal conservation Unwired ≠ Proved GREEN.
oreMonoidalConservationNonClaim :: String
oreMonoidalConservationNonClaim =
  "CHEM-FORMAL-Q-HS-ORE-MONOIDAL-CONSERVATION OreTree leaf/tensor unit I associator productNotXor monoidalLawsProved false Unwired one axiom second law conservation not XOR enum not Vec list not GREEN DFT not physics GREEN not production_wired"

-- | Physics GREEN is unauthorized on the knowing ore monoidal conservation scaffold.
oreMonoidalConservationPhysicsGreenAuthorized :: Bool
oreMonoidalConservationPhysicsGreenAuthorized = False

oreMonoidalConservationPhysicsGreenFalse :: Bool
oreMonoidalConservationPhysicsGreenFalse =
  not oreMonoidalConservationPhysicsGreenAuthorized

oreMonoidalConservationModalityUnwired :: Bool
oreMonoidalConservationModalityUnwired =
  oreMonoidalConservationModalityCurrent == OreMonoidalConservationUnwired
