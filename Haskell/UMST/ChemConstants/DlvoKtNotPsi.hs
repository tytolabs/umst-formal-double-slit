-- SPDX-FileCopyrightText: 2026 Santosh Prabhu Shenbagamoorthy and Santhosh Shyamsundar
-- SPDX-License-Identifier: MIT

{-|
Module      : UMST.ChemConstants.DlvoKtNotPsi
Description : DLVO kT coefficient pin not constitutive ψ conservation on the matter fiber
Copyright   : (c) UMST Project, 2026

Fluids DLVO kT is a **coefficient pin**, not constitutive ψ on the matter fiber. The thermal
pin tag occupies the fluids DLVO scaffold at coefficient level; constitutive ψ authority is not
smuggled as kT. Unwired scaffold; @physics_green@ stays false; not a 26th axiom.

* @dlvoKtPinTag@ — fluids DLVO kT coefficient pin tag.
* @psiTag@ — constitutive ψ tag (distinct from kT pin).
* @dlvoKtIsPsi@ = False — DLVO kT is **not** constitutive ψ.
* @pinDistinctFromPsi@ — coefficient pin layer distinct from constitutive ψ.
* **One** design axiom (@dlvoKtNotPsiAxiom@): second law + conservation.
* @dlvoKtNotPsiProved@ = False.

Haskell mirror of DLVO kT not-ψ conservation on the quantum / matter fiber.
Cell: @CHEM-FORMAL-Q-HS-DLVO-KT-NOT-PSI-CONSERVATION@.
WAVE100: not wired in cabal.
-}
module UMST.ChemConstants.DlvoKtNotPsi
  ( DlvoKtNotPsiModality (..)
  , dlvoKtNotPsiModalityCurrent
  , dlvoKtPinTag
  , psiTag
  , dlvoKtIsPsi
  , constStrNe
  , pinDistinctFromPsi
  , DlvoKtNotPsiProbe (..)
  , dlvoKtNotPsiProbe
  , dlvoKtNotPsiHonest
  , dlvoKtNotPsiScaffold
  , dlvoKtNotPsiProved
  , dlvoKtNotPsiAxiom
  , dlvoKtNotPsiConservationNamed
  , dlvoKtNotPsiChemAuthority
  , dlvoKtNotPsiCellId
  , dlvoKtNotPsiNonClaim
  , dlvoKtNotPsiPhysicsGreenAuthorized
  , dlvoKtNotPsiPhysicsGreenFalse
  , dlvoKtNotPsiModalityUnwired
  , soleAxiomCount
  ) where

-- | Design modality for DLVO kT not-ψ claims (TYPE-03 preview).
data DlvoKtNotPsiModality
  = DlvoKtNotPsiUnwired
  | DlvoKtNotPsiAssumed
  | DlvoKtNotPsiProved
  | DlvoKtNotPsiSurrogate
  deriving (Eq, Show)

-- | Current scaffold modality — always Unwired on this cell.
dlvoKtNotPsiModalityCurrent :: DlvoKtNotPsiModality
dlvoKtNotPsiModalityCurrent = DlvoKtNotPsiUnwired

-- | Sole axiom count (always 1 on this cell).
soleAxiomCount :: Int
soleAxiomCount = 1

-- | DLVO thermal kT coefficient pin tag.
dlvoKtPinTag :: String
dlvoKtPinTag = "coefficient_pin"

-- | Constitutive ψ tag — not the DLVO kT pin.
psiTag :: String
psiTag = "constitutive_psi"

-- | Whether DLVO kT is constitutive ψ (always false @ Unwired).
dlvoKtIsPsi :: Bool
dlvoKtIsPsi = False

-- | Const-time string inequality — pin tag ≠ ψ tag.
constStrNe :: String -> String -> Bool
constStrNe a b = a /= b

-- | Coefficient pin remains distinct from constitutive ψ.
pinDistinctFromPsi :: Bool
pinDistinctFromPsi =
  not dlvoKtIsPsi
    && constStrNe dlvoKtPinTag psiTag
    && dlvoKtPinTag == "coefficient_pin"
    && psiTag == "constitutive_psi"

-- | Probe bundle for honest posture witnesses.
data DlvoKtNotPsiProbe = DlvoKtNotPsiProbe
  { cellIdNamed :: Bool
  , unwired :: Bool
  , physicsGreenRefused :: Bool
  , soleAxiom :: Bool
  , notProved :: Bool
  }
  deriving (Eq, Show)

-- | Honest probe — modality Unwired, physics GREEN refused.
dlvoKtNotPsiProbe :: DlvoKtNotPsiProbe
dlvoKtNotPsiProbe =
  DlvoKtNotPsiProbe
    { cellIdNamed =
        dlvoKtNotPsiCellId
          == "CHEM-FORMAL-Q-HS-DLVO-KT-NOT-PSI-CONSERVATION"
    , unwired =
        dlvoKtNotPsiModalityCurrent == DlvoKtNotPsiUnwired
    , physicsGreenRefused = not dlvoKtNotPsiPhysicsGreenAuthorized
    , soleAxiom = soleAxiomCount == 1
    , notProved = not dlvoKtNotPsiProved
    }

-- | Honest conjunct on probe bundle.
dlvoKtNotPsiHonest :: Bool
dlvoKtNotPsiHonest =
  let p = dlvoKtNotPsiProbe
   in cellIdNamed p
        && unwired p
        && physicsGreenRefused p
        && soleAxiom p
        && notProved p
        && pinDistinctFromPsi

-- | DLVO kT not-ψ scaffold pinned.
dlvoKtNotPsiScaffold :: Bool
dlvoKtNotPsiScaffold =
  pinDistinctFromPsi
    && not dlvoKtIsPsi
    && dlvoKtNotPsiHonest
    && soleAxiomCount == 1

-- | DLVO kT not-ψ proved (always false on this Unwired cell).
dlvoKtNotPsiProved :: Bool
dlvoKtNotPsiProved = False

-- | Single design axiom: second law + conservation — kT is coefficient pin, not ψ.
dlvoKtNotPsiAxiom :: Bool
dlvoKtNotPsiAxiom =
  dlvoKtNotPsiScaffold
    && not dlvoKtIsPsi
    && pinDistinctFromPsi
    && not dlvoKtNotPsiProved
    && soleAxiomCount == 1

dlvoKtNotPsiConservationNamed :: String
dlvoKtNotPsiConservationNamed =
  "dlvoKtNotPsi: fluids DLVO kT is coefficient pin not constitutive psi dlvoKtIsPsi false pinDistinctFromPsi true dlvoKtPinTag coefficient_pin psiTag constitutive_psi second law conservation one axiom not 26th axiom"

-- | umst-chem DLVO kT not-ψ cross authority (cited, not forked).
dlvoKtNotPsiChemAuthority :: String
dlvoKtNotPsiChemAuthority =
  "umst/umst-chem/src/x_rows/dlvo_kt_not_psi.rs"

dlvoKtNotPsiCellId :: String
dlvoKtNotPsiCellId =
  "CHEM-FORMAL-Q-HS-DLVO-KT-NOT-PSI-CONSERVATION"

-- | Non-claim fence — DLVO kT not-ψ Unwired ≠ Proved GREEN.
dlvoKtNotPsiNonClaim :: String
dlvoKtNotPsiNonClaim =
  "CHEM-FORMAL-Q-HS-DLVO-KT-NOT-PSI-CONSERVATION Unwired — fluids DLVO kT is coefficient pin not constitutive psi not a 26th axiom; dlvoKtIsPsi false pinDistinctFromPsi true; not physics GREEN; not production_wired; not cabal wired"

-- | Physics GREEN is unauthorized on the DLVO kT not-ψ scaffold.
dlvoKtNotPsiPhysicsGreenAuthorized :: Bool
dlvoKtNotPsiPhysicsGreenAuthorized = False

dlvoKtNotPsiPhysicsGreenFalse :: Bool
dlvoKtNotPsiPhysicsGreenFalse =
  not dlvoKtNotPsiPhysicsGreenAuthorized

dlvoKtNotPsiModalityUnwired :: Bool
dlvoKtNotPsiModalityUnwired =
  dlvoKtNotPsiModalityCurrent == DlvoKtNotPsiUnwired
