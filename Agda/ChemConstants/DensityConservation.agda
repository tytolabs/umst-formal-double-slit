-- SPDX-FileCopyrightText: 2026 Santosh Prabhu Shenbagamoorthy and Santhosh Shyamsundar
-- SPDX-License-Identifier: MIT
------------------------------------------------------------------------
-- UMST-Formal: ChemConstants.DensityConservation.agda
--
-- DENSITY-01 **density** ladder **conservation** on the knowing fiber (Q lattice):
--   * Modality lattice Unwired/Assumed/Proved/Surrogate — structure not 118² GREEN
--   * Four named rungs mSDF → TE-SDF → SDF → FRep; order identity conserved
--   * Composed mSDF→TE-SDF→SDF→FRep identity equals mSDF→FRep direct (typed **conservation**)
--   * **density** leg mismatch refuse; total-claim refuse without witness
--   * SDF rung ≠ ρ unless explicitly named
--   * **density** laws Unwired (densityLadderProved = false)
--
-- Mirrors sibling `ChemConstants/ScaleConservation.agda` style.
-- No meso / acting theorems. Modality Unwired; physics GREEN false.
-- Not 118² GREEN table. Second-law + **conservation** framing (not wired).
-- Not DensityLadder Proved. Knowing/quantum fiber.
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module ChemConstants.DensityConservation where

open import Data.Bool.Base using (Bool; false; true; not; _∧_; if_then_else_)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Nat using (ℕ; zero; suc; _*_)
open import Data.Nat.Properties as ℕ-Props using (_≟_; _≤?_)
open import Data.Product using (_×_; _,_)
open import Data.String using (String)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl)
open import Relation.Nullary using (¬_; yes; no)
open import Relation.Nullary.Decidable using (does)

------------------------------------------------------------------------
-- Modality + DENSITY-01 **density** ladder **conservation** pins (knowing fiber — Unwired)
------------------------------------------------------------------------

data DensityConservationModality : Set where
  density-conservation-unwired density-conservation-assumed
    density-conservation-proved density-conservation-surrogate
    : DensityConservationModality

densityConservationModalityCurrent : DensityConservationModality
densityConservationModalityCurrent = density-conservation-unwired

densityLadderProved productionWired not118SquaredGreenTable
  densitySecondLawConservationFramed densityTypedConservation : Bool
densityLadderProved = false
productionWired = false
not118SquaredGreenTable = true
densitySecondLawConservationFramed = true
densityTypedConservation = true

------------------------------------------------------------------------
-- **Density** ladder cardinality (structure — not 118²)
------------------------------------------------------------------------

densityLadderCardinality : ℕ
densityLadderCardinality = 4

density-ladder-cardinality-four : densityLadderCardinality ≡ 4
density-ladder-cardinality-four = refl

density-ladder-not-118-squared :
  does (densityLadderCardinality ℕ-Props.≟ (118 * 118)) ≡ false
density-ladder-not-118-squared = refl

------------------------------------------------------------------------
-- SDF rung ≠ ρ unless named — explicit **density** symbol pins
------------------------------------------------------------------------

data DensitySymbolTag : Set where
  sdf-rung rho-density : DensitySymbolTag

isSdfRung isRhoDensity : DensitySymbolTag → Bool
isSdfRung sdf-rung = true
isSdfRung rho-density = false

isRhoDensity rho-density = true
isRhoDensity sdf-rung = false

sdf-rung-not-rho-unless-named :
  isSdfRung sdf-rung ≡ true × isRhoDensity sdf-rung ≡ false
sdf-rung-not-rho-unless-named = refl , refl

rho-density-named :
  isRhoDensity rho-density ≡ true × isSdfRung rho-density ≡ false
rho-density-named = refl , refl

sdf-rung-distinct-from-rho : sdf-rung ≢ rho-density
sdf-rung-distinct-from-rho ()

------------------------------------------------------------------------
-- Named element Z pins — H (Z=1), Fe (Z=26), Og (Z=118)
------------------------------------------------------------------------

data ElementTag : Set where
  hydrogen iron oganesson : ElementTag

elementAtomicZ : ElementTag → ℕ
elementAtomicZ hydrogen = 1
elementAtomicZ iron = 26
elementAtomicZ oganesson = 118

hydrogen-z-1 : elementAtomicZ hydrogen ≡ 1
hydrogen-z-1 = refl

iron-z-26 : elementAtomicZ iron ≡ 26
iron-z-26 = refl

oganesson-z-118 : elementAtomicZ oganesson ≡ 118
oganesson-z-118 = refl

------------------------------------------------------------------------
-- **Density** level + ladder legs (typed scaffold — ladder not Proved)
------------------------------------------------------------------------

data DensityLevel : Set where
  density-msdf density-te-sdf density-sdf density-frep : DensityLevel

data DensityLadderLeg : Set where
  msdf-to-te-sdf te-sdf-to-sdf sdf-to-frep msdf-to-frep-direct : DensityLadderLeg

densityLegSource : DensityLadderLeg → DensityLevel
densityLegSource msdf-to-te-sdf = density-msdf
densityLegSource te-sdf-to-sdf = density-te-sdf
densityLegSource sdf-to-frep = density-sdf
densityLegSource msdf-to-frep-direct = density-msdf

densityLegTarget : DensityLadderLeg → DensityLevel
densityLegTarget msdf-to-te-sdf = density-te-sdf
densityLegTarget te-sdf-to-sdf = density-sdf
densityLegTarget sdf-to-frep = density-frep
densityLegTarget msdf-to-frep-direct = density-frep

densityLegMsdfToTeSdf densityLegTeSdfToSdf densityLegSdfToFrep
  densityLegMsdfToFrepDirect : DensityLadderLeg
densityLegMsdfToTeSdf = msdf-to-te-sdf
densityLegTeSdfToSdf = te-sdf-to-sdf
densityLegSdfToFrep = sdf-to-frep
densityLegMsdfToFrepDirect = msdf-to-frep-direct

density-leg-msdf-to-te-sdf-named :
  densityLegMsdfToTeSdf ≡ msdf-to-te-sdf
density-leg-msdf-to-te-sdf-named = refl

density-leg-te-sdf-to-sdf-named :
  densityLegTeSdfToSdf ≡ te-sdf-to-sdf
density-leg-te-sdf-to-sdf-named = refl

density-leg-sdf-to-frep-named :
  densityLegSdfToFrep ≡ sdf-to-frep
density-leg-sdf-to-frep-named = refl

density-leg-msdf-to-frep-direct-named :
  densityLegMsdfToFrepDirect ≡ msdf-to-frep-direct
density-leg-msdf-to-frep-direct-named = refl

density-leg-first-composes-levels :
  densityLegTarget densityLegMsdfToTeSdf ≡ densityLegSource densityLegTeSdfToSdf
density-leg-first-composes-levels = refl

density-leg-second-composes-levels :
  densityLegTarget densityLegTeSdfToSdf ≡ densityLegSource densityLegSdfToFrep
density-leg-second-composes-levels = refl

density-leg-direct-endpoints-match :
  densityLegSource densityLegMsdfToTeSdf ≡ densityLegSource densityLegMsdfToFrepDirect ×
  densityLegTarget densityLegSdfToFrep ≡ densityLegTarget densityLegMsdfToFrepDirect
density-leg-direct-endpoints-match = refl , refl

density-leg-msdf-to-te-sdf-source :
  densityLegSource densityLegMsdfToTeSdf ≡ density-msdf
density-leg-msdf-to-te-sdf-source = refl

density-leg-sdf-to-frep-target :
  densityLegTarget densityLegSdfToFrep ≡ density-frep
density-leg-sdf-to-frep-target = refl

density-leg-distinct-indirect-vs-direct :
  densityLegMsdfToTeSdf ≢ densityLegMsdfToFrepDirect
density-leg-distinct-indirect-vs-direct ()

------------------------------------------------------------------------
-- Typed **density** ladder **conservation** — composed indirect equals direct endpoints
------------------------------------------------------------------------

record DensityLadderTypedWitness : Set where
  constructor mkDensityLadderTypedWitness
  field
    indirect-source : DensityLevel
    indirect-via-a    : DensityLevel
    indirect-via-b    : DensityLevel
    indirect-target   : DensityLevel
    direct-source     : DensityLevel
    direct-target     : DensityLevel

densityLadderTypedWitnessNamed : DensityLadderTypedWitness
densityLadderTypedWitnessNamed = record
  { indirect-source = density-msdf
  ; indirect-via-a    = density-te-sdf
  ; indirect-via-b    = density-sdf
  ; indirect-target   = density-frep
  ; direct-source     = density-msdf
  ; direct-target     = density-frep
  }

composed-indirect-identity-equals-direct-typed :
  DensityLadderTypedWitness.indirect-source densityLadderTypedWitnessNamed ≡
  DensityLadderTypedWitness.direct-source densityLadderTypedWitnessNamed ×
  DensityLadderTypedWitness.indirect-target densityLadderTypedWitnessNamed ≡
  DensityLadderTypedWitness.direct-target densityLadderTypedWitnessNamed ×
  densityLegTarget densityLegMsdfToTeSdf ≡ densityLegSource densityLegTeSdfToSdf ×
  densityLegTarget densityLegTeSdfToSdf ≡ densityLegSource densityLegSdfToFrep ×
  densityLegSource densityLegMsdfToTeSdf ≡ densityLegSource densityLegMsdfToFrepDirect ×
  densityLegTarget densityLegSdfToFrep ≡ densityLegTarget densityLegMsdfToFrepDirect
composed-indirect-identity-equals-direct-typed = refl , refl , refl , refl , refl , refl

density-typed-conservation-pin : densityTypedConservation ≡ true
density-typed-conservation-pin = refl

------------------------------------------------------------------------
-- ClassifierDensityStep scaffold — **density** ladder **conservation**
------------------------------------------------------------------------

data ClassifierDensityStep : Set where
  density-identity : ClassifierDensityStep
  density-leg-leaf : DensityLadderLeg → ClassifierDensityStep
  leg-compose : ClassifierDensityStep → ClassifierDensityStep → ClassifierDensityStep
  density-leg-mismatch : ClassifierDensityStep → ClassifierDensityStep → ClassifierDensityStep

densityIdentity : ClassifierDensityStep
densityIdentity = density-identity

legComposeOp densityMismatchOp :
  ClassifierDensityStep → ClassifierDensityStep → ClassifierDensityStep
legComposeOp = leg-compose
densityMismatchOp = density-leg-mismatch

msdfToTeSdfLeaf teSdfToSdfLeaf sdfToFrepLeaf msdfToFrepDirectLeaf : ClassifierDensityStep
msdfToTeSdfLeaf = density-leg-leaf msdf-to-te-sdf
teSdfToSdfLeaf = density-leg-leaf te-sdf-to-sdf
sdfToFrepLeaf = density-leg-leaf sdf-to-frep
msdfToFrepDirectLeaf = density-leg-leaf msdf-to-frep-direct

isLegCompose isDensityLeg isDensityIdentity : ClassifierDensityStep → Bool
isLegCompose (leg-compose _ _) = true
isLegCompose _ = false

isDensityLeg (density-leg-leaf _) = true
isDensityLeg _ = false

isDensityIdentity density-identity = true
isDensityIdentity _ = false

------------------------------------------------------------------------
-- **Density** identity conserved at density-identity — leg-compose scaffold
------------------------------------------------------------------------

density-left-identity :
  ∀ (a : ClassifierDensityStep) →
  isDensityIdentity densityIdentity ≡ true × isLegCompose (legComposeOp densityIdentity a) ≡ true
density-left-identity a = refl , refl

density-right-identity :
  ∀ (a : ClassifierDensityStep) →
  isLegCompose (legComposeOp a densityIdentity) ≡ true × isDensityIdentity densityIdentity ≡ true
density-right-identity a = refl , refl

density-identity-conserved-at-density :
  (∀ a → isLegCompose (legComposeOp densityIdentity a) ≡ true)
  × (∀ a → isLegCompose (legComposeOp a densityIdentity) ≡ true)
density-identity-conserved-at-density =
  (λ a → refl)
  , (λ a → refl)

------------------------------------------------------------------------
-- Named four-rung **density** ladder closed — indirect composed vs direct
------------------------------------------------------------------------

namedDensityIndirectPath : ClassifierDensityStep
namedDensityIndirectPath =
  legComposeOp (legComposeOp msdfToTeSdfLeaf teSdfToSdfLeaf) sdfToFrepLeaf

namedDensityDirectPath : ClassifierDensityStep
namedDensityDirectPath = msdfToFrepDirectLeaf

named-density-indirect-is-compose :
  isLegCompose namedDensityIndirectPath ≡ true
named-density-indirect-is-compose = refl

named-density-direct-is-leg :
  isDensityLeg namedDensityDirectPath ≡ true
named-density-direct-is-leg = refl

named-density-four-rungs-named :
  isDensityLeg msdfToTeSdfLeaf ≡ true
  × isDensityLeg teSdfToSdfLeaf ≡ true
  × isDensityLeg sdfToFrepLeaf ≡ true
  × isDensityLeg msdfToFrepDirectLeaf ≡ true
named-density-four-rungs-named = refl , refl , refl , refl

named-density-ladder-closed :
  isLegCompose namedDensityIndirectPath ≡ true
  × isDensityLeg namedDensityDirectPath ≡ true
  × densityLegTarget densityLegMsdfToTeSdf ≡ densityLegSource densityLegTeSdfToSdf
  × densityLegTarget densityLegTeSdfToSdf ≡ densityLegSource densityLegSdfToFrep
  × densityLegSource densityLegMsdfToTeSdf ≡ densityLegSource densityLegMsdfToFrepDirect
  × densityLegTarget densityLegSdfToFrep ≡ densityLegTarget densityLegMsdfToFrepDirect
named-density-ladder-closed = refl , refl , refl , refl , refl , refl

------------------------------------------------------------------------
-- **Density** leg mismatch refuse — wrong-order compose fail-closed
------------------------------------------------------------------------

densityLegMismatchPath : ClassifierDensityStep
densityLegMismatchPath = densityMismatchOp teSdfToSdfLeaf msdfToTeSdfLeaf

isDensityMismatch : ClassifierDensityStep → Bool
isDensityMismatch (density-leg-mismatch _ _) = true
isDensityMismatch _ = false

density-mismatch-is-mismatch :
  isDensityMismatch densityLegMismatchPath ≡ true
density-mismatch-is-mismatch = refl

density-mismatch-not-compose :
  isLegCompose densityLegMismatchPath ≡ false
density-mismatch-not-compose = refl

------------------------------------------------------------------------
-- **Density** admissibility — mismatch refuse fail-closed
------------------------------------------------------------------------

data DensityAdmissibility : Set where
  density-admissible density-leg-mismatch-refuse : DensityAdmissibility

isDensityPreserving : ClassifierDensityStep → Bool
isDensityPreserving density-identity = true
isDensityPreserving (density-leg-leaf _) = true
isDensityPreserving (leg-compose a b) =
  isDensityPreserving a ∧ isDensityPreserving b
isDensityPreserving (density-leg-mismatch _ _) = false

isDensityAdmissible : ClassifierDensityStep → Bool
isDensityAdmissible step = isDensityPreserving step

msdf-to-te-sdf-leaf-admissible : isDensityAdmissible msdfToTeSdfLeaf ≡ true
msdf-to-te-sdf-leaf-admissible = refl

te-sdf-to-sdf-leaf-admissible : isDensityAdmissible teSdfToSdfLeaf ≡ true
te-sdf-to-sdf-leaf-admissible = refl

sdf-to-frep-leaf-admissible : isDensityAdmissible sdfToFrepLeaf ≡ true
sdf-to-frep-leaf-admissible = refl

msdf-to-frep-direct-leaf-admissible : isDensityAdmissible msdfToFrepDirectLeaf ≡ true
msdf-to-frep-direct-leaf-admissible = refl

named-density-indirect-admissible : isDensityAdmissible namedDensityIndirectPath ≡ true
named-density-indirect-admissible = refl

named-density-direct-admissible : isDensityAdmissible namedDensityDirectPath ≡ true
named-density-direct-admissible = refl

density-leg-mismatch-not-admissible :
  isDensityAdmissible densityLegMismatchPath ≡ false
density-leg-mismatch-not-admissible = refl

------------------------------------------------------------------------
-- **Density** witness — total-claim refuse without witness
------------------------------------------------------------------------

data DensityWitnessPresence : Set where
  density-witness-absent density-witness-present : DensityWitnessPresence

record ClassifierDensityWitness : Set where
  constructor mkClassifierDensityWitness
  field
    witness-presence : DensityWitnessPresence
    density-gap-total : ℕ

densityWitnessAbsent : ClassifierDensityWitness
densityWitnessAbsent = mkClassifierDensityWitness density-witness-absent zero

densityWitnessPresentZeroGap : ClassifierDensityWitness
densityWitnessPresentZeroGap = mkClassifierDensityWitness density-witness-present zero

densityWitnessPresentWithGaps : ℕ → ClassifierDensityWitness
densityWitnessPresentWithGaps n = mkClassifierDensityWitness density-witness-present n

densityWitnessGapFree : ClassifierDensityWitness → Bool
densityWitnessGapFree (mkClassifierDensityWitness density-witness-absent _) = false
densityWitnessGapFree (mkClassifierDensityWitness density-witness-present n) =
  does (n ℕ-Props.≟ zero)

density-witness-present-zero-gap-free :
  densityWitnessGapFree densityWitnessPresentZeroGap ≡ true
density-witness-present-zero-gap-free = refl

density-witness-absent-not-gap-free :
  densityWitnessGapFree densityWitnessAbsent ≡ false
density-witness-absent-not-gap-free = refl

density-witness-with-gaps-not-gap-free :
  ∀ n → densityWitnessGapFree (densityWitnessPresentWithGaps (suc n)) ≡ false
density-witness-with-gaps-not-gap-free n = refl

------------------------------------------------------------------------
-- Classifier-DENSITY-01 **density** **conservation** close verdict — fail-closed lattice
------------------------------------------------------------------------

data DensityConservationVerdict : Set where
  verdict-unwired-ok verdict-density-ladder-admissible-ok
    verdict-density-leg-mismatch-refuse verdict-total-claim-refuse
    verdict-green-invent-refuse
    : DensityConservationVerdict

densityConservationVerdictOk : DensityConservationVerdict → Bool
densityConservationVerdictOk verdict-unwired-ok = true
densityConservationVerdictOk verdict-density-ladder-admissible-ok = true
densityConservationVerdictOk _ = false

evaluateDensityConservationClose :
  DensityConservationModality → ClassifierDensityStep → ClassifierDensityWitness → Bool
  → DensityConservationVerdict
evaluateDensityConservationClose _ _ _ true = verdict-green-invent-refuse
evaluateDensityConservationClose density-conservation-unwired _ _ false = verdict-unwired-ok
evaluateDensityConservationClose density-conservation-assumed _ _ false = verdict-unwired-ok
evaluateDensityConservationClose density-conservation-surrogate _ _ false = verdict-unwired-ok
evaluateDensityConservationClose density-conservation-proved _ (mkClassifierDensityWitness density-witness-absent _) false =
  verdict-total-claim-refuse
evaluateDensityConservationClose density-conservation-proved (density-leg-mismatch _ _) _ false =
  verdict-density-leg-mismatch-refuse
evaluateDensityConservationClose density-conservation-proved step (mkClassifierDensityWitness density-witness-present _) false
  with isDensityAdmissible step
... | false = verdict-density-leg-mismatch-refuse
... | true  = verdict-density-ladder-admissible-ok

------------------------------------------------------------------------
-- Unwired close — design scaffold without **density** witness
------------------------------------------------------------------------

unwired-close-without-witness :
  evaluateDensityConservationClose
    density-conservation-unwired namedDensityIndirectPath densityWitnessAbsent false ≡
  verdict-unwired-ok
unwired-close-without-witness = refl

assumed-close-without-witness :
  evaluateDensityConservationClose
    density-conservation-assumed namedDensityIndirectPath densityWitnessAbsent false ≡
  verdict-unwired-ok
assumed-close-without-witness = refl

surrogate-close-without-witness :
  evaluateDensityConservationClose
    density-conservation-surrogate namedDensityIndirectPath densityWitnessAbsent false ≡
  verdict-unwired-ok
surrogate-close-without-witness = refl

design-modalities-verdict-ok-without-witness :
  densityConservationVerdictOk
    (evaluateDensityConservationClose density-conservation-unwired namedDensityIndirectPath densityWitnessAbsent false)
    ≡ true
  × densityConservationVerdictOk
      (evaluateDensityConservationClose density-conservation-assumed namedDensityIndirectPath densityWitnessAbsent false)
      ≡ true
  × densityConservationVerdictOk
      (evaluateDensityConservationClose density-conservation-surrogate namedDensityIndirectPath densityWitnessAbsent false)
      ≡ true
design-modalities-verdict-ok-without-witness = refl , refl , refl

------------------------------------------------------------------------
-- Total-claim refuse — proved modality without **density** witness
------------------------------------------------------------------------

total-claim-refuse-without-witness :
  evaluateDensityConservationClose
    density-conservation-proved namedDensityIndirectPath densityWitnessAbsent false ≡
  verdict-total-claim-refuse
total-claim-refuse-without-witness = refl

total-claim-refuse-not-ok :
  densityConservationVerdictOk
    (evaluateDensityConservationClose
       density-conservation-proved namedDensityIndirectPath densityWitnessAbsent false)
    ≡ false
total-claim-refuse-not-ok = refl

TotalClaimWhenWitnessAbsent : Set
TotalClaimWhenWitnessAbsent =
  evaluateDensityConservationClose
    density-conservation-proved namedDensityIndirectPath densityWitnessAbsent false ≡
  verdict-density-ladder-admissible-ok

total-claim-⊥-when-witness-absent : TotalClaimWhenWitnessAbsent → ⊥
total-claim-⊥-when-witness-absent ()

------------------------------------------------------------------------
-- **Density** leg mismatch refuse — wrong-order compose fail-closed
------------------------------------------------------------------------

density-leg-mismatch-refuse-verdict :
  evaluateDensityConservationClose
    density-conservation-proved densityLegMismatchPath densityWitnessPresentZeroGap false ≡
  verdict-density-leg-mismatch-refuse
density-leg-mismatch-refuse-verdict = refl

density-leg-mismatch-refuse-not-ok :
  densityConservationVerdictOk
    (evaluateDensityConservationClose
       density-conservation-proved densityLegMismatchPath densityWitnessPresentZeroGap false)
    ≡ false
density-leg-mismatch-refuse-not-ok = refl

DensityMismatchWhenIndirectOk : Set
DensityMismatchWhenIndirectOk =
  evaluateDensityConservationClose
    density-conservation-proved densityLegMismatchPath densityWitnessPresentZeroGap false ≡
  verdict-density-ladder-admissible-ok

density-mismatch-⊥-when-indirect-ok : DensityMismatchWhenIndirectOk → ⊥
density-mismatch-⊥-when-indirect-ok ()

------------------------------------------------------------------------
-- Admissible classifier-**density** — witness present + typed ladder closed
------------------------------------------------------------------------

density-ladder-admissible-ok :
  evaluateDensityConservationClose
    density-conservation-proved namedDensityIndirectPath densityWitnessPresentZeroGap false ≡
  verdict-density-ladder-admissible-ok
density-ladder-admissible-ok = refl

density-ladder-admissible-verdict-ok :
  densityConservationVerdictOk
    (evaluateDensityConservationClose
       density-conservation-proved namedDensityIndirectPath densityWitnessPresentZeroGap false)
    ≡ true
density-ladder-admissible-verdict-ok = refl

density-ladder-admissible-ok-still-not-density-ladder-proved :
  densityConservationVerdictOk
    (evaluateDensityConservationClose
       density-conservation-proved namedDensityIndirectPath densityWitnessPresentZeroGap false)
    ≡ true
  × densityLadderProved ≡ false
density-ladder-admissible-ok-still-not-density-ladder-proved =
  density-ladder-admissible-verdict-ok , refl

------------------------------------------------------------------------
-- Green invent refuse — physics GREEN never authorized
------------------------------------------------------------------------

green-invent-refuse-unwired :
  evaluateDensityConservationClose
    density-conservation-unwired namedDensityIndirectPath densityWitnessPresentZeroGap true ≡
  verdict-green-invent-refuse
green-invent-refuse-unwired = refl

green-invent-always-refuse :
  densityConservationVerdictOk
    (evaluateDensityConservationClose
       density-conservation-unwired namedDensityIndirectPath densityWitnessPresentZeroGap true)
    ≡ false
green-invent-always-refuse = refl

------------------------------------------------------------------------
-- Knowing / quantum fiber routing — geometry not meso acting
------------------------------------------------------------------------

data FormalFiber : Set where
  fiber-quantum-knowing fiber-meso-acting : FormalFiber

densityConservationFiberOk : FormalFiber → Bool
densityConservationFiberOk fiber-quantum-knowing = true
densityConservationFiberOk fiber-meso-acting = false

density-conservation-knowing-fiber-ok :
  densityConservationFiberOk fiber-quantum-knowing ≡ true
density-conservation-knowing-fiber-ok = refl

density-conservation-meso-acting-not-ok :
  densityConservationFiberOk fiber-meso-acting ≡ false
density-conservation-meso-acting-not-ok = refl

density-conservation-routes-knowing-not-meso :
  densityConservationFiberOk fiber-quantum-knowing ≡ true ×
  densityConservationFiberOk fiber-meso-acting ≡ false
density-conservation-routes-knowing-not-meso = refl , refl

fiberNotMesoActing : Bool
fiberNotMesoActing =
  densityConservationFiberOk fiber-quantum-knowing ∧
  not (densityConservationFiberOk fiber-meso-acting)

fiber-not-meso-acting-true : fiberNotMesoActing ≡ true
fiber-not-meso-acting-true = refl

------------------------------------------------------------------------
-- Honest pins — not DensityLadder Proved, not physics GREEN
------------------------------------------------------------------------

density-ladder-not-proved : densityLadderProved ≡ false
density-ladder-not-proved = refl

production-not-wired : productionWired ≡ false
production-not-wired = refl

not-118-squared-green-table : not118SquaredGreenTable ≡ true
not-118-squared-green-table = refl

density-second-law-conservation-framed : densitySecondLawConservationFramed ≡ true
density-second-law-conservation-framed = refl

density-typed-conservation-framed : densityTypedConservation ≡ true
density-typed-conservation-framed = density-typed-conservation-pin

------------------------------------------------------------------------
-- One design axiom + authority cites (not a second DENSITY-01 axiom fork)
------------------------------------------------------------------------

densityConservationAxiom :
  (densityLadderProved ≡ false)
  × (productionWired ≡ false)
  × (not118SquaredGreenTable ≡ true)
  × (densitySecondLawConservationFramed ≡ true)
  × (densityTypedConservation ≡ true)
  × (evaluateDensityConservationClose density-conservation-unwired namedDensityIndirectPath densityWitnessAbsent false ≡ verdict-unwired-ok)
  × (evaluateDensityConservationClose density-conservation-proved namedDensityIndirectPath densityWitnessAbsent false ≡ verdict-total-claim-refuse)
  × (evaluateDensityConservationClose density-conservation-proved densityLegMismatchPath densityWitnessPresentZeroGap false ≡ verdict-density-leg-mismatch-refuse)
  × (evaluateDensityConservationClose density-conservation-proved namedDensityIndirectPath densityWitnessPresentZeroGap false ≡ verdict-density-ladder-admissible-ok)
  × (densityConservationFiberOk fiber-quantum-knowing ≡ true)
  × (densityConservationFiberOk fiber-meso-acting ≡ false)
  × (densityConservationVerdictOk (evaluateDensityConservationClose density-conservation-unwired namedDensityIndirectPath densityWitnessPresentZeroGap true) ≡ false)
  × (∀ a → isLegCompose (legComposeOp densityIdentity a) ≡ true)
  × (∀ a → isLegCompose (legComposeOp a densityIdentity) ≡ true)
  × (isDensityAdmissible densityLegMismatchPath ≡ false)
  × (densityLegTarget densityLegMsdfToTeSdf ≡ densityLegSource densityLegTeSdfToSdf)
  × (densityLegTarget densityLegTeSdfToSdf ≡ densityLegSource densityLegSdfToFrep)
  × (densityLegSource densityLegMsdfToTeSdf ≡ densityLegSource densityLegMsdfToFrepDirect)
  × (densityLegTarget densityLegSdfToFrep ≡ densityLegTarget densityLegMsdfToFrepDirect)
  × (isSdfRung sdf-rung ≡ true)
  × (isRhoDensity sdf-rung ≡ false)
  × (elementAtomicZ hydrogen ≡ 1)
  × (elementAtomicZ iron ≡ 26)
  × (elementAtomicZ oganesson ≡ 118)
densityConservationAxiom =
  density-ladder-not-proved
  , production-not-wired
  , not-118-squared-green-table
  , density-second-law-conservation-framed
  , density-typed-conservation-framed
  , unwired-close-without-witness
  , total-claim-refuse-without-witness
  , density-leg-mismatch-refuse-verdict
  , density-ladder-admissible-ok
  , density-conservation-knowing-fiber-ok
  , density-conservation-meso-acting-not-ok
  , green-invent-always-refuse
  , (λ a → refl)
  , (λ a → refl)
  , density-leg-mismatch-not-admissible
  , density-leg-first-composes-levels
  , density-leg-second-composes-levels
  , refl
  , refl
  , refl
  , refl
  , hydrogen-z-1
  , iron-z-26
  , oganesson-z-118

densityConservationNamed : String
densityConservationNamed =
  "densityConservation: DENSITY-01 density ladder conservation four rungs mSDF TE-SDF SDF FRep composed indirect equals direct typed conservation"

densityConservationCellId : String
densityConservationCellId = "CHEM-FORMAL-Q-AGDA-DENSITY-CONSERVATION"

densityConservationNonClaim : String
densityConservationNonClaim =
  "CHEM-FORMAL-Q-AGDA-DENSITY-CONSERVATION DENSITY-01 density ladder conservation four rungs mSDF TE-SDF SDF FRep composed indirect equals direct typed conservation density leg mismatch refuse total-claim refuse densityLadderProved false SDF not rho unless named not 118 squared GREEN table geometry knowing quantum fiber not meso acting Unwired one axiom second law conservation not second DENSITY axiom not physics GREEN not production_wired distinct from occupancy Z identity"

density-conservation-modality-unwired :
  densityConservationModalityCurrent ≡ density-conservation-unwired
density-conservation-modality-unwired = refl

densityConservationPhysicsGreenAuthorized : Set
densityConservationPhysicsGreenAuthorized = ⊥

density-conservation-physics-green-false : ¬ densityConservationPhysicsGreenAuthorized
density-conservation-physics-green-false ()
