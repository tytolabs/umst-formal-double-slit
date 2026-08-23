-- SPDX-FileCopyrightText: 2026 Santosh Prabhu Shenbagamoorthy and Santhosh Shyamsundar
-- SPDX-License-Identifier: MIT
------------------------------------------------------------------------
-- UMST-Formal: EnvironmentScaleCommute.agda
--
-- Quantum / knowing fiber preview for environment SCALE sheaf:
--   * Vacuum / contained / messy as simultaneous sample sections
--     (not XOR — all three present in each EnvironmentSection)
--   * Env sheaf sections commute Q ↔ meso ↔ macro as knowing probes
--   * Reuses AllotropeGeometry ScaleLevel + ScaleCommutingLeg (Unwired)
--
-- Mirrors `Coq/EnvironmentScaleCommute.v` + sibling `ChemGeometry.agda` style.
-- No meso / acting theorems. Modality Unwired; physics GREEN false.
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module EnvironmentScaleCommute where

open import AllotropeGeometry
open import Data.Nat as ℕ using (ℕ; zero; suc; _≤_)
open import Data.Nat.Properties using (≤-refl)
open import Data.Rational as ℚ using (ℚ; 0ℚ; 1ℚ; _+_; _<_)
open import Data.Product using (_×_; _,_)
open import Data.Empty using (⊥; ⊥-elim)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; sym; cong; subst)
open import Relation.Nullary using (¬_)

------------------------------------------------------------------------
-- Electronic row (knowing parent — Lean / Coq mirror)
------------------------------------------------------------------------

data ElectronicModality : Set where
  electronic-unwired electronic-assumed electronic-proved electronic-surrogate : ElectronicModality

electronicModalityCurrent : ElectronicModality
electronicModalityCurrent = electronic-unwired

record AtomicNumber : Set where
  constructor mkAtomicNumber
  field
    z     : ℕ
    hz-lo : ℕ.zero ℕ.< z
    hz-hi : z ℕ.≤ 118

record ElementElectronic : Set where
  constructor mkElementElectronic
  field
    atomicZ  : AtomicNumber
    occupied : QLatticeCell
    modality : ElectronicModality

------------------------------------------------------------------------
-- Environment modality + sample sections (not XOR)
------------------------------------------------------------------------

data EnvironmentScaleModality : Set where
  env-scale-unwired env-scale-assumed env-scale-proved env-scale-surrogate : EnvironmentScaleModality

environmentScaleModalityCurrent : EnvironmentScaleModality
environmentScaleModalityCurrent = env-scale-unwired

data EnvSampleAxis : Set where
  env-axis-vacuum env-axis-contained env-axis-messy : EnvSampleAxis

private
  env-sample-axes-distinct-vacuum-contained : env-axis-vacuum ≢ env-axis-contained
  env-sample-axes-distinct-vacuum-contained ()

  env-sample-axes-distinct-vacuum-messy : env-axis-vacuum ≢ env-axis-messy
  env-sample-axes-distinct-vacuum-messy ()

  env-sample-axes-distinct-contained-messy : env-axis-contained ≢ env-axis-messy
  env-sample-axes-distinct-contained-messy ()

record VacuumSample : Set where
  constructor mkVacuumSample
  field
    residualPO2Pa : ℚ

record ContainedSample : Set where
  constructor mkContainedSample
  field
    kelvin : ℚ
    pascal : ℚ

record MessySample : Set where
  constructor mkMessySample
  field
    oreGradeFraction : ℚ
    impurityFraction : ℚ

-- All three sample sections coexist — not an exclusive env choice.
record EnvironmentSection : Set where
  constructor mkEnvironmentSection
  field
    vacuum    : VacuumSample
    contained : ContainedSample
    messy     : MessySample

environment-section-has-all-samples : ∀ (s : EnvironmentSection) →
  EnvironmentSection.vacuum s ≡ EnvironmentSection.vacuum s ×
  EnvironmentSection.contained s ≡ EnvironmentSection.contained s ×
  EnvironmentSection.messy s ≡ EnvironmentSection.messy s
environment-section-has-all-samples s = refl , refl , refl

record EnvironmentSheafField : Set where
  constructor mkEnvironmentSheafField
  field
    atQuantum : EnvironmentSection
    atMeso    : EnvironmentSection
    atMacro   : EnvironmentSection

environmentAtLevel : EnvironmentSheafField → ScaleLevel → EnvironmentSection
environmentAtLevel f scale-quantum = EnvironmentSheafField.atQuantum f
environmentAtLevel f scale-meso    = EnvironmentSheafField.atMeso f
environmentAtLevel f scale-macro   = EnvironmentSheafField.atMacro f

vacuumSampleAtLevel : EnvironmentSheafField → ScaleLevel → VacuumSample
vacuumSampleAtLevel f lvl = EnvironmentSection.vacuum (environmentAtLevel f lvl)

containedSampleAtLevel : EnvironmentSheafField → ScaleLevel → ContainedSample
containedSampleAtLevel f lvl = EnvironmentSection.contained (environmentAtLevel f lvl)

messySampleAtLevel : EnvironmentSheafField → ScaleLevel → MessySample
messySampleAtLevel f lvl = EnvironmentSection.messy (environmentAtLevel f lvl)

environmentAtLegSource : EnvironmentSheafField → ScaleCommutingLeg → EnvironmentSection
environmentAtLegSource f leg = environmentAtLevel f (scaleLegSource leg)

environmentAtLegTarget : EnvironmentSheafField → ScaleCommutingLeg → EnvironmentSection
environmentAtLegTarget f leg = environmentAtLevel f (scaleLegTarget leg)

------------------------------------------------------------------------
-- Knowing probes — env sample axis × scale stratum
------------------------------------------------------------------------

record KnowingProbe : Set where
  constructor mkKnowingProbe
  field
    axis  : EnvSampleAxis
    scale : ScaleLevel

probeVacuumAtQuantum : KnowingProbe
probeVacuumAtQuantum = record { axis = env-axis-vacuum; scale = scale-quantum }

probeContainedAtMeso : KnowingProbe
probeContainedAtMeso = record { axis = env-axis-contained; scale = scale-meso }

probeMessyAtMacro : KnowingProbe
probeMessyAtMacro = record { axis = env-axis-messy; scale = scale-macro }

probeSample : EnvironmentSheafField → KnowingProbe → ℚ
probeSample f (mkKnowingProbe env-axis-vacuum    lvl) =
  VacuumSample.residualPO2Pa (vacuumSampleAtLevel f lvl)
probeSample f (mkKnowingProbe env-axis-contained lvl) =
  ContainedSample.kelvin (containedSampleAtLevel f lvl)
probeSample f (mkKnowingProbe env-axis-messy     lvl) =
  MessySample.oreGradeFraction (messySampleAtLevel f lvl)

probe-vacuum-at-quantum-named : ∀ (f : EnvironmentSheafField) →
  probeSample f probeVacuumAtQuantum ≡
  VacuumSample.residualPO2Pa (EnvironmentSection.vacuum (EnvironmentSheafField.atQuantum f))
probe-vacuum-at-quantum-named f = refl

------------------------------------------------------------------------
-- SCALE commute diagram (named legs — equality not Proved)
------------------------------------------------------------------------

scaleLegQuantumToMeso : ScaleCommutingLeg
scaleLegQuantumToMeso = quantum-to-meso

scaleLegMesoToMacro : ScaleCommutingLeg
scaleLegMesoToMacro = meso-to-macro

scaleLegQuantumToMacroDirect : ScaleCommutingLeg
scaleLegQuantumToMacroDirect = quantum-to-macro-direct

record ScaleCommuteDiagram : Set where
  constructor mkScaleCommuteDiagram
  field
    viaMeso   : ScaleCommutingLeg
    thenMacro : ScaleCommutingLeg
    direct    : ScaleCommutingLeg

scaleCommuteDiagramNamed : ScaleCommuteDiagram
scaleCommuteDiagramNamed = record
  { viaMeso   = scaleLegQuantumToMeso
  ; thenMacro = scaleLegMesoToMacro
  ; direct    = scaleLegQuantumToMacroDirect
  }

scale-commute-diagram-named-fields :
  ScaleCommuteDiagram.viaMeso scaleCommuteDiagramNamed ≡ scaleLegQuantumToMeso ×
  ScaleCommuteDiagram.thenMacro scaleCommuteDiagramNamed ≡ scaleLegMesoToMacro ×
  ScaleCommuteDiagram.direct scaleCommuteDiagramNamed ≡ scaleLegQuantumToMacroDirect
scale-commute-diagram-named-fields = refl , refl , refl

scale-leg-indirect-composes-levels :
  scaleLegTarget scaleLegQuantumToMeso ≡ scaleLegSource scaleLegMesoToMacro
scale-leg-indirect-composes-levels = refl

scale-leg-direct-endpoints-match :
  scaleLegSource scaleLegQuantumToMeso ≡ scaleLegSource scaleLegQuantumToMacroDirect ×
  scaleLegTarget scaleLegMesoToMacro ≡ scaleLegTarget scaleLegQuantumToMacroDirect
scale-leg-direct-endpoints-match = refl , refl

------------------------------------------------------------------------
-- Env sheaf commute along SCALE legs (named — not physics GREEN)
------------------------------------------------------------------------

environment-at-leg-source-quantum-to-meso : ∀ (f : EnvironmentSheafField) →
  environmentAtLegSource f scaleLegQuantumToMeso ≡ EnvironmentSheafField.atQuantum f
environment-at-leg-source-quantum-to-meso f = refl

environment-at-leg-target-quantum-to-meso : ∀ (f : EnvironmentSheafField) →
  environmentAtLegTarget f scaleLegQuantumToMeso ≡ EnvironmentSheafField.atMeso f
environment-at-leg-target-quantum-to-meso f = refl

environment-at-leg-source-meso-to-macro : ∀ (f : EnvironmentSheafField) →
  environmentAtLegSource f scaleLegMesoToMacro ≡ EnvironmentSheafField.atMeso f
environment-at-leg-source-meso-to-macro f = refl

environment-at-leg-target-meso-to-macro : ∀ (f : EnvironmentSheafField) →
  environmentAtLegTarget f scaleLegMesoToMacro ≡ EnvironmentSheafField.atMacro f
environment-at-leg-target-meso-to-macro f = refl

environment-at-leg-source-quantum-to-macro-direct : ∀ (f : EnvironmentSheafField) →
  environmentAtLegSource f scaleLegQuantumToMacroDirect ≡ EnvironmentSheafField.atQuantum f
environment-at-leg-source-quantum-to-macro-direct f = refl

environment-at-leg-target-quantum-to-macro-direct : ∀ (f : EnvironmentSheafField) →
  environmentAtLegTarget f scaleLegQuantumToMacroDirect ≡ EnvironmentSheafField.atMacro f
environment-at-leg-target-quantum-to-macro-direct f = refl

environment-indirect-leg-composes : ∀ (f : EnvironmentSheafField) →
  environmentAtLegTarget f scaleLegQuantumToMeso ≡
  environmentAtLegSource f scaleLegMesoToMacro
environment-indirect-leg-composes f = refl

environment-direct-endpoints-match : ∀ (f : EnvironmentSheafField) →
  environmentAtLegSource f scaleLegQuantumToMeso ≡
  environmentAtLegSource f scaleLegQuantumToMacroDirect ×
  environmentAtLegTarget f scaleLegMesoToMacro ≡
  environmentAtLegTarget f scaleLegQuantumToMacroDirect
environment-direct-endpoints-match f = refl , refl

vacuum-sample-at-leg-source-quantum-to-meso : ∀ (f : EnvironmentSheafField) →
  EnvironmentSection.vacuum (environmentAtLegSource f scaleLegQuantumToMeso) ≡
  EnvironmentSection.vacuum (EnvironmentSheafField.atQuantum f)
vacuum-sample-at-leg-source-quantum-to-meso f = refl

contained-sample-at-leg-target-meso-to-macro : ∀ (f : EnvironmentSheafField) →
  EnvironmentSection.contained (environmentAtLegTarget f scaleLegMesoToMacro) ≡
  EnvironmentSection.contained (EnvironmentSheafField.atMacro f)
contained-sample-at-leg-target-meso-to-macro f = refl

messy-sample-at-leg-source-quantum-to-macro-direct : ∀ (f : EnvironmentSheafField) →
  EnvironmentSection.messy (environmentAtLegSource f scaleLegQuantumToMacroDirect) ≡
  EnvironmentSection.messy (EnvironmentSheafField.atQuantum f)
messy-sample-at-leg-source-quantum-to-macro-direct f = refl

record ScaleCommute : Set where
  constructor mkScaleCommute
  field
    scaleParent   : ElementElectronic
    scaleDiagram  : ScaleCommuteDiagram
    scaleModality : ChemGeometryModality
    edgeModality  : ChemGeometryModality

scaleCommuteUnwired : ElementElectronic → ScaleCommute
scaleCommuteUnwired e = record
  { scaleParent   = e
  ; scaleDiagram  = scaleCommuteDiagramNamed
  ; scaleModality = chemGeometryModalityCurrent
  ; edgeModality  = chemGeometryModalityCurrent
  }

record EnvironmentScaleSheafDiagram : Set where
  constructor mkEnvironmentScaleSheafDiagram
  field
    scaleDiag : ScaleCommuteDiagram
    envField  : EnvironmentSheafField

environmentScaleSheafDiagramNamed : EnvironmentSheafField → EnvironmentScaleSheafDiagram
environmentScaleSheafDiagramNamed f = record
  { scaleDiag = scaleCommuteDiagramNamed
  ; envField  = f
  }

environment-scale-sheaf-diagram-named-scale : ∀ (f : EnvironmentSheafField) →
  EnvironmentScaleSheafDiagram.scaleDiag (environmentScaleSheafDiagramNamed f) ≡
  scaleCommuteDiagramNamed
environment-scale-sheaf-diagram-named-scale f = refl

record EnvironmentScaleSheafBinding : Set where
  constructor mkEnvironmentScaleSheafBinding
  field
    parent       : ElementElectronic
    sheafField   : EnvironmentSheafField
    scaleCommute : ScaleCommute

environmentScaleElement : EnvironmentScaleSheafBinding → AtomicNumber
environmentScaleElement b = ElementElectronic.atomicZ (EnvironmentScaleSheafBinding.parent b)

environment-scale-binding-same-element : ∀ (a b : EnvironmentScaleSheafBinding)
  (Heq : environmentScaleElement a ≡ environmentScaleElement b) →
  AtomicNumber.z (environmentScaleElement a) ≡ AtomicNumber.z (environmentScaleElement b)
environment-scale-binding-same-element a b Heq = cong AtomicNumber.z Heq

record EnvironmentScaleCommute : Set where
  constructor mkEnvironmentScaleCommute
  field
    binding                  : EnvironmentScaleSheafBinding
    diagram                  : EnvironmentScaleSheafDiagram
    scaleModality            : ChemGeometryModality
    edgeModality             : ChemGeometryModality
    environmentScaleModality : EnvironmentScaleModality

private
  natToℚ : ℕ → ℚ
  natToℚ ℕ.zero    = 0ℚ
  natToℚ (ℕ.suc k) = 1ℚ + natToℚ k

vacuumSampleAmbient : VacuumSample
vacuumSampleAmbient = record { residualPO2Pa = 0ℚ }

containedSampleAmbient : ContainedSample
containedSampleAmbient = record
  { kelvin = natToℚ 298
  ; pascal = natToℚ 101325
  }

messySampleAmbient : MessySample
messySampleAmbient = record
  { oreGradeFraction = 0ℚ
  ; impurityFraction = 0ℚ
  }

environmentSectionAmbient : EnvironmentSection
environmentSectionAmbient = record
  { vacuum    = vacuumSampleAmbient
  ; contained = containedSampleAmbient
  ; messy     = messySampleAmbient
  }

environmentSheafFieldAmbient : EnvironmentSheafField
environmentSheafFieldAmbient = record
  { atQuantum = environmentSectionAmbient
  ; atMeso    = environmentSectionAmbient
  ; atMacro   = environmentSectionAmbient
  }

environmentScaleCommuteUnwired : ElementElectronic → EnvironmentScaleCommute
environmentScaleCommuteUnwired e = record
  { binding = record
      { parent       = e
      ; sheafField   = environmentSheafFieldAmbient
      ; scaleCommute = scaleCommuteUnwired e
      }
  ; diagram                  = environmentScaleSheafDiagramNamed environmentSheafFieldAmbient
  ; scaleModality            = chemGeometryModalityCurrent
  ; edgeModality             = chemGeometryModalityCurrent
  ; environmentScaleModality = environmentScaleModalityCurrent
  }

environment-scale-commute-modality-unwired : ∀ (c : EnvironmentScaleCommute) →
  (EnvironmentScaleCommute.scaleModality c ≡ chemGeometryModalityCurrent ×
   EnvironmentScaleCommute.edgeModality c ≡ chemGeometryModalityCurrent ×
   EnvironmentScaleCommute.environmentScaleModality c ≡ environmentScaleModalityCurrent) ↔
  (EnvironmentScaleCommute.scaleModality c ≡ geom-unwired ×
   EnvironmentScaleCommute.edgeModality c ≡ geom-unwired ×
   EnvironmentScaleCommute.environmentScaleModality c ≡ env-scale-unwired)
environment-scale-commute-modality-unwired c =
  ( λ { (p , q , r) →
        subst (λ m → EnvironmentScaleCommute.scaleModality c ≡ m)
          chemGeometryModalityCurrent≡geom-unwired p ,
        subst (λ m → EnvironmentScaleCommute.edgeModality c ≡ m)
          chemGeometryModalityCurrent≡geom-unwired q ,
        r
      }) ,
  ( λ { (p , q , r) →
        subst (λ m → EnvironmentScaleCommute.scaleModality c ≡ m)
          (sym chemGeometryModalityCurrent≡geom-unwired) p ,
        subst (λ m → EnvironmentScaleCommute.edgeModality c ≡ m)
          (sym chemGeometryModalityCurrent≡geom-unwired) q ,
        r
      })

environment-scale-commute-lattice-anchor : ∀ (c : EnvironmentScaleCommute) →
  madelungPriority (ElementElectronic.occupied (EnvironmentScaleSheafBinding.parent (EnvironmentScaleCommute.binding c))) ≡
  madelungPriority (ElementElectronic.occupied (EnvironmentScaleSheafBinding.parent (EnvironmentScaleCommute.binding c)))
environment-scale-commute-lattice-anchor c = refl

environment-scale-sheaf-indirect-composes : ∀ (f : EnvironmentSheafField) →
  environmentAtLegTarget f (ScaleCommuteDiagram.viaMeso (EnvironmentScaleSheafDiagram.scaleDiag (environmentScaleSheafDiagramNamed f))) ≡
  environmentAtLegSource f (ScaleCommuteDiagram.thenMacro (EnvironmentScaleSheafDiagram.scaleDiag (environmentScaleSheafDiagramNamed f)))
environment-scale-sheaf-indirect-composes f = environment-indirect-leg-composes f

environment-scale-sheaf-direct-endpoints : ∀ (f : EnvironmentSheafField) →
  environmentAtLegSource f (ScaleCommuteDiagram.viaMeso (EnvironmentScaleSheafDiagram.scaleDiag (environmentScaleSheafDiagramNamed f))) ≡
  environmentAtLegSource f (ScaleCommuteDiagram.direct (EnvironmentScaleSheafDiagram.scaleDiag (environmentScaleSheafDiagramNamed f))) ×
  environmentAtLegTarget f (ScaleCommuteDiagram.thenMacro (EnvironmentScaleSheafDiagram.scaleDiag (environmentScaleSheafDiagramNamed f))) ≡
  environmentAtLegTarget f (ScaleCommuteDiagram.direct (EnvironmentScaleSheafDiagram.scaleDiag (environmentScaleSheafDiagramNamed f)))
environment-scale-sheaf-direct-endpoints f = environment-direct-endpoints-match f

environment-scale-commute-unwired-binding-parent : ∀ (e : ElementElectronic) →
  EnvironmentScaleSheafBinding.parent (EnvironmentScaleCommute.binding (environmentScaleCommuteUnwired e)) ≡ e
environment-scale-commute-unwired-binding-parent e = refl

environment-scale-commute-ambient-vacuum : ∀ (f : EnvironmentSheafField)
  (H : f ≡ environmentSheafFieldAmbient) →
  vacuumSampleAtLevel f scale-quantum ≡ vacuumSampleAmbient
environment-scale-commute-ambient-vacuum .environmentSheafFieldAmbient refl = refl

environment-scale-commute-ambient-contained : ∀ (f : EnvironmentSheafField)
  (H : f ≡ environmentSheafFieldAmbient) →
  containedSampleAtLevel f scale-macro ≡ containedSampleAmbient
environment-scale-commute-ambient-contained .environmentSheafFieldAmbient refl = refl

environmentSectionAllSamples : EnvironmentSection → VacuumSample × ContainedSample × MessySample
environmentSectionAllSamples s =
  ( EnvironmentSection.vacuum s
  , EnvironmentSection.contained s
  , EnvironmentSection.messy s
  )

environment-sections-coexist-not-xor : ∀ (s : EnvironmentSection) →
  environmentSectionAllSamples s ≡
  ( EnvironmentSection.vacuum s
  , EnvironmentSection.contained s
  , EnvironmentSection.messy s
  )
environment-sections-coexist-not-xor s = refl

environment-classify-bulk-of-neg : ∀ (sdf : ℚ) (h : sdf ℚ.< 0ℚ) →
  classifyEdgeSurface sdf ≡ regime-bulk
environment-classify-bulk-of-neg sdf h = classifyEdgeSurface-bulk-of-neg sdf h

environment-classify-surface-of-pos : ∀ (sdf : ℚ) (hneg : ¬ (sdf ℚ.< 0ℚ)) (hne : sdf ≢ 0ℚ) →
  classifyEdgeSurface sdf ≡ regime-surface
environment-classify-surface-of-pos sdf hneg hne =
  classifyEdgeSurface-surface-of-pos sdf hneg hne

environmentScaleSheafEqualityAuthorized : EnvironmentScaleSheafDiagram → Set
environmentScaleSheafEqualityAuthorized _ = ⊥

environment-scale-sheaf-equality-physics-green-false : ∀ (d : EnvironmentScaleSheafDiagram) →
  ¬ environmentScaleSheafEqualityAuthorized d
environment-scale-sheaf-equality-physics-green-false d h = h

environmentScaleCommutePhysicsGreenAuthorized : EnvironmentScaleCommute → Set
environmentScaleCommutePhysicsGreenAuthorized _ = ⊥

environment-scale-commute-physics-green-false : ∀ (c : EnvironmentScaleCommute) →
  ¬ environmentScaleCommutePhysicsGreenAuthorized c
environment-scale-commute-physics-green-false c h = h

environmentScaleElementElectronicPhysicsGreenAuthorized : ElementElectronic → Set
environmentScaleElementElectronicPhysicsGreenAuthorized _ = ⊥

environment-scale-element-physics-green-false : ∀ (e : ElementElectronic) →
  ¬ environmentScaleElementElectronicPhysicsGreenAuthorized e
environment-scale-element-physics-green-false e h = h
