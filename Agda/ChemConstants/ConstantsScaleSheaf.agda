-- SPDX-FileCopyrightText: 2026 Santosh Prabhu Shenbagamoorthy and Santhosh Shyamsundar
-- SPDX-License-Identifier: MIT
------------------------------------------------------------------------
-- UMST-Formal: ChemConstants.ConstantsScaleSheaf.agda
--
-- Quantum / knowing fiber preview for constants SCALE sheaf:
--   * Temperature, pressure, named thermodynamic constants as typed sections
--   * Constants sheaf sections commute Q ↔ meso ↔ macro as knowing probes
--   * Reuses AllotropeGeometry ScaleLevel + ScaleCommutingLeg (Unwired)
--
-- Mirrors `Lean/ChemConstants/ConstantsScaleSheaf.lean` +
-- sibling `EnvironmentScaleCommute.agda` style.
-- No meso / acting theorems. Modality Unwired; physics GREEN false.
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module ChemConstants.ConstantsScaleSheaf where

open import AllotropeGeometry using
  ( ScaleLevel; scale-quantum; scale-meso; scale-macro
  ; ScaleCommutingLeg; scaleLegSource; scaleLegTarget
  ; ChemGeometryModality; geom-unwired
  ; chemGeometryModalityCurrent; chemGeometryModalityCurrent≡geom-unwired
  ; classifyEdgeSurface; regime-bulk; regime-surface
  ; classifyEdgeSurface-bulk-of-neg; classifyEdgeSurface-surface-of-pos
  ; madelungPriority; _↔_
  )
open import Data.Nat as ℕ using (ℕ; zero; suc)
open import Data.Product using (_×_; _,_)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Rational as ℚ using (ℚ; 0ℚ; 1ℚ; _+_)
open import Data.Rational.Base as ℚBase using (_<_)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; sym; cong; subst)
open import Relation.Nullary using (¬_)

open import EnvironmentScaleCommute using
  ( ElementElectronic; AtomicNumber
  ; scaleLegQuantumToMeso; scaleLegMesoToMacro; scaleLegQuantumToMacroDirect
  ; ScaleCommuteDiagram; scaleCommuteDiagramNamed
  ; ScaleCommute; scaleCommuteUnwired
  )

------------------------------------------------------------------------
-- Constants modality + sample sections (T, P, named pins)
------------------------------------------------------------------------

data ConstantsScaleModality : Set where
  constants-scale-unwired constants-scale-assumed constants-scale-proved constants-scale-surrogate
    : ConstantsScaleModality

constantsScaleModalityCurrent : ConstantsScaleModality
constantsScaleModalityCurrent = constants-scale-unwired

record TemperatureSection : Set where
  constructor mkTemperatureSection
  field
    kelvin : ℚ

record PressureSection : Set where
  constructor mkPressureSection
  field
    pascal : ℚ

record NamedConstantsSection : Set where
  constructor mkNamedConstantsSection
  field
    gasConstantR       : ℚ
    boltzmannK         : ℚ
    standardPressurePa : ℚ

record ConstantsSheafSection : Set where
  constructor mkConstantsSheafSection
  field
    temperature : TemperatureSection
    pressure    : PressureSection
    named       : NamedConstantsSection

record ConstantsSheafField : Set where
  constructor mkConstantsSheafField
  field
    atQuantum : ConstantsSheafSection
    atMeso    : ConstantsSheafSection
    atMacro   : ConstantsSheafSection

constantsAtLevel : ConstantsSheafField → ScaleLevel → ConstantsSheafSection
constantsAtLevel f scale-quantum = ConstantsSheafField.atQuantum f
constantsAtLevel f scale-meso    = ConstantsSheafField.atMeso f
constantsAtLevel f scale-macro   = ConstantsSheafField.atMacro f

temperatureSectionAtLevel : ConstantsSheafField → ScaleLevel → TemperatureSection
temperatureSectionAtLevel f lvl = ConstantsSheafSection.temperature (constantsAtLevel f lvl)

pressureSectionAtLevel : ConstantsSheafField → ScaleLevel → PressureSection
pressureSectionAtLevel f lvl = ConstantsSheafSection.pressure (constantsAtLevel f lvl)

namedConstantsAtLevel : ConstantsSheafField → ScaleLevel → NamedConstantsSection
namedConstantsAtLevel f lvl = ConstantsSheafSection.named (constantsAtLevel f lvl)

constantsAtLegSource : ConstantsSheafField → ScaleCommutingLeg → ConstantsSheafSection
constantsAtLegSource f leg = constantsAtLevel f (scaleLegSource leg)

constantsAtLegTarget : ConstantsSheafField → ScaleCommutingLeg → ConstantsSheafSection
constantsAtLegTarget f leg = constantsAtLevel f (scaleLegTarget leg)

------------------------------------------------------------------------
-- SCALE commute along constants sheaf legs (named — not physics GREEN)
------------------------------------------------------------------------

constants-at-leg-source-quantum-to-meso : ∀ (f : ConstantsSheafField) →
  constantsAtLegSource f scaleLegQuantumToMeso ≡ ConstantsSheafField.atQuantum f
constants-at-leg-source-quantum-to-meso f = refl

constants-at-leg-target-quantum-to-meso : ∀ (f : ConstantsSheafField) →
  constantsAtLegTarget f scaleLegQuantumToMeso ≡ ConstantsSheafField.atMeso f
constants-at-leg-target-quantum-to-meso f = refl

constants-at-leg-source-meso-to-macro : ∀ (f : ConstantsSheafField) →
  constantsAtLegSource f scaleLegMesoToMacro ≡ ConstantsSheafField.atMeso f
constants-at-leg-source-meso-to-macro f = refl

constants-at-leg-target-meso-to-macro : ∀ (f : ConstantsSheafField) →
  constantsAtLegTarget f scaleLegMesoToMacro ≡ ConstantsSheafField.atMacro f
constants-at-leg-target-meso-to-macro f = refl

constants-at-leg-source-quantum-to-macro-direct : ∀ (f : ConstantsSheafField) →
  constantsAtLegSource f scaleLegQuantumToMacroDirect ≡ ConstantsSheafField.atQuantum f
constants-at-leg-source-quantum-to-macro-direct f = refl

constants-at-leg-target-quantum-to-macro-direct : ∀ (f : ConstantsSheafField) →
  constantsAtLegTarget f scaleLegQuantumToMacroDirect ≡ ConstantsSheafField.atMacro f
constants-at-leg-target-quantum-to-macro-direct f = refl

constants-indirect-leg-composes : ∀ (f : ConstantsSheafField) →
  constantsAtLegTarget f scaleLegQuantumToMeso ≡
  constantsAtLegSource f scaleLegMesoToMacro
constants-indirect-leg-composes f = refl

constants-direct-endpoints-match : ∀ (f : ConstantsSheafField) →
  constantsAtLegSource f scaleLegQuantumToMeso ≡
  constantsAtLegSource f scaleLegQuantumToMacroDirect ×
  constantsAtLegTarget f scaleLegMesoToMacro ≡
  constantsAtLegTarget f scaleLegQuantumToMacroDirect
constants-direct-endpoints-match f = refl , refl

temperature-section-at-leg-source-quantum-to-meso : ∀ (f : ConstantsSheafField) →
  ConstantsSheafSection.temperature (constantsAtLegSource f scaleLegQuantumToMeso) ≡
  ConstantsSheafSection.temperature (ConstantsSheafField.atQuantum f)
temperature-section-at-leg-source-quantum-to-meso f = refl

pressure-section-at-leg-target-meso-to-macro : ∀ (f : ConstantsSheafField) →
  ConstantsSheafSection.pressure (constantsAtLegTarget f scaleLegMesoToMacro) ≡
  ConstantsSheafSection.pressure (ConstantsSheafField.atMacro f)
pressure-section-at-leg-target-meso-to-macro f = refl

named-constants-at-leg-source-quantum-to-macro-direct : ∀ (f : ConstantsSheafField) →
  ConstantsSheafSection.named (constantsAtLegSource f scaleLegQuantumToMacroDirect) ≡
  ConstantsSheafSection.named (ConstantsSheafField.atQuantum f)
named-constants-at-leg-source-quantum-to-macro-direct f = refl

------------------------------------------------------------------------
-- Binding, diagram, and unwired witness
------------------------------------------------------------------------

record ConstantsScaleSheafBinding : Set where
  constructor mkConstantsScaleSheafBinding
  field
    parent       : ElementElectronic
    sheafField   : ConstantsSheafField
    scaleCommute : ScaleCommute

constantsScaleElement : ConstantsScaleSheafBinding → AtomicNumber
constantsScaleElement b = ElementElectronic.atomicZ (ConstantsScaleSheafBinding.parent b)

constants-scale-binding-same-element : ∀ (a b : ConstantsScaleSheafBinding)
  (Heq : constantsScaleElement a ≡ constantsScaleElement b) →
  AtomicNumber.z (constantsScaleElement a) ≡ AtomicNumber.z (constantsScaleElement b)
constants-scale-binding-same-element a b Heq = cong AtomicNumber.z Heq

record ConstantsScaleSheafDiagram : Set where
  constructor mkConstantsScaleSheafDiagram
  field
    scaleDiag : ScaleCommuteDiagram
    constField : ConstantsSheafField

constantsScaleSheafDiagramNamed : ConstantsSheafField → ConstantsScaleSheafDiagram
constantsScaleSheafDiagramNamed f = record
  { scaleDiag  = scaleCommuteDiagramNamed
  ; constField = f
  }

constants-scale-sheaf-diagram-named-scale : ∀ (f : ConstantsSheafField) →
  ConstantsScaleSheafDiagram.scaleDiag (constantsScaleSheafDiagramNamed f) ≡
  scaleCommuteDiagramNamed
constants-scale-sheaf-diagram-named-scale f = refl

record ConstantsScaleSheaf : Set where
  constructor mkConstantsScaleSheaf
  field
    binding                  : ConstantsScaleSheafBinding
    diagram                  : ConstantsScaleSheafDiagram
    scaleModality            : ChemGeometryModality
    edgeModality             : ChemGeometryModality
    constantsScaleModality   : ConstantsScaleModality

private
  natToℚ : ℕ → ℚ
  natToℚ ℕ.zero    = 0ℚ
  natToℚ (ℕ.suc k) = 1ℚ + natToℚ k

namedConstantsAmbient : NamedConstantsSection
namedConstantsAmbient = record
  { gasConstantR       = natToℚ 8
  ; boltzmannK         = 0ℚ
  ; standardPressurePa = natToℚ 101325
  }

constantsSheafSectionAmbient : ConstantsSheafSection
constantsSheafSectionAmbient = record
  { temperature = record { kelvin = natToℚ 298 }
  ; pressure    = record { pascal = natToℚ 101325 }
  ; named       = namedConstantsAmbient
  }

constantsSheafFieldAmbient : ConstantsSheafField
constantsSheafFieldAmbient = record
  { atQuantum = constantsSheafSectionAmbient
  ; atMeso    = constantsSheafSectionAmbient
  ; atMacro   = constantsSheafSectionAmbient
  }

constantsScaleSheafUnwired : ElementElectronic → ConstantsScaleSheaf
constantsScaleSheafUnwired e = record
  { binding = record
      { parent       = e
      ; sheafField   = constantsSheafFieldAmbient
      ; scaleCommute = scaleCommuteUnwired e
      }
  ; diagram                = constantsScaleSheafDiagramNamed constantsSheafFieldAmbient
  ; scaleModality          = chemGeometryModalityCurrent
  ; edgeModality           = chemGeometryModalityCurrent
  ; constantsScaleModality = constantsScaleModalityCurrent
  }

constants-scale-sheaf-modality-unwired : ∀ (c : ConstantsScaleSheaf) →
  (ConstantsScaleSheaf.scaleModality c ≡ chemGeometryModalityCurrent ×
   ConstantsScaleSheaf.edgeModality c ≡ chemGeometryModalityCurrent ×
   ConstantsScaleSheaf.constantsScaleModality c ≡ constantsScaleModalityCurrent) ↔
  (ConstantsScaleSheaf.scaleModality c ≡ geom-unwired ×
   ConstantsScaleSheaf.edgeModality c ≡ geom-unwired ×
   ConstantsScaleSheaf.constantsScaleModality c ≡ constants-scale-unwired)
constants-scale-sheaf-modality-unwired c =
  ( λ { (p , q , r) →
        subst (λ m → ConstantsScaleSheaf.scaleModality c ≡ m)
          chemGeometryModalityCurrent≡geom-unwired p ,
        subst (λ m → ConstantsScaleSheaf.edgeModality c ≡ m)
          chemGeometryModalityCurrent≡geom-unwired q ,
        r
      }) ,
  ( λ { (p , q , r) →
        subst (λ m → ConstantsScaleSheaf.scaleModality c ≡ m)
          (sym chemGeometryModalityCurrent≡geom-unwired) p ,
        subst (λ m → ConstantsScaleSheaf.edgeModality c ≡ m)
          (sym chemGeometryModalityCurrent≡geom-unwired) q ,
        r
      })

constants-scale-sheaf-lattice-anchor : ∀ (c : ConstantsScaleSheaf) →
  madelungPriority (ElementElectronic.occupied (ConstantsScaleSheafBinding.parent (ConstantsScaleSheaf.binding c))) ≡
  madelungPriority (ElementElectronic.occupied (ConstantsScaleSheafBinding.parent (ConstantsScaleSheaf.binding c)))
constants-scale-sheaf-lattice-anchor c = refl

constants-scale-sheaf-diagram-scale-fields : ∀ (f : ConstantsSheafField) →
  ScaleCommuteDiagram.viaMeso (ConstantsScaleSheafDiagram.scaleDiag (constantsScaleSheafDiagramNamed f)) ≡
  scaleLegQuantumToMeso ×
  ScaleCommuteDiagram.thenMacro (ConstantsScaleSheafDiagram.scaleDiag (constantsScaleSheafDiagramNamed f)) ≡
  scaleLegMesoToMacro ×
  ScaleCommuteDiagram.direct (ConstantsScaleSheafDiagram.scaleDiag (constantsScaleSheafDiagramNamed f)) ≡
  scaleLegQuantumToMacroDirect
constants-scale-sheaf-diagram-scale-fields f = refl , refl , refl

constants-scale-sheaf-indirect-composes : ∀ (f : ConstantsSheafField) →
  constantsAtLegTarget f (ScaleCommuteDiagram.viaMeso (ConstantsScaleSheafDiagram.scaleDiag (constantsScaleSheafDiagramNamed f))) ≡
  constantsAtLegSource f (ScaleCommuteDiagram.thenMacro (ConstantsScaleSheafDiagram.scaleDiag (constantsScaleSheafDiagramNamed f)))
constants-scale-sheaf-indirect-composes f = constants-indirect-leg-composes f

constants-scale-sheaf-direct-endpoints : ∀ (f : ConstantsSheafField) →
  constantsAtLegSource f (ScaleCommuteDiagram.viaMeso (ConstantsScaleSheafDiagram.scaleDiag (constantsScaleSheafDiagramNamed f))) ≡
  constantsAtLegSource f (ScaleCommuteDiagram.direct (ConstantsScaleSheafDiagram.scaleDiag (constantsScaleSheafDiagramNamed f))) ×
  constantsAtLegTarget f (ScaleCommuteDiagram.thenMacro (ConstantsScaleSheafDiagram.scaleDiag (constantsScaleSheafDiagramNamed f))) ≡
  constantsAtLegTarget f (ScaleCommuteDiagram.direct (ConstantsScaleSheafDiagram.scaleDiag (constantsScaleSheafDiagramNamed f)))
constants-scale-sheaf-direct-endpoints f = constants-direct-endpoints-match f

constants-scale-sheaf-unwired-binding-parent : ∀ (e : ElementElectronic) →
  ConstantsScaleSheafBinding.parent (ConstantsScaleSheaf.binding (constantsScaleSheafUnwired e)) ≡ e
constants-scale-sheaf-unwired-binding-parent e = refl

constants-scale-sheaf-ambient-temperature : ∀ (f : ConstantsSheafField)
  (H : f ≡ constantsSheafFieldAmbient) →
  temperatureSectionAtLevel f scale-quantum ≡ record { kelvin = natToℚ 298 }
constants-scale-sheaf-ambient-temperature .constantsSheafFieldAmbient refl = refl

constants-scale-sheaf-ambient-pressure : ∀ (f : ConstantsSheafField)
  (H : f ≡ constantsSheafFieldAmbient) →
  pressureSectionAtLevel f scale-macro ≡ record { pascal = natToℚ 101325 }
constants-scale-sheaf-ambient-pressure .constantsSheafFieldAmbient refl = refl

constants-classify-bulk-of-neg : ∀ (sdf : ℚ) (h : sdf ℚBase.< 0ℚ) →
  classifyEdgeSurface sdf ≡ regime-bulk
constants-classify-bulk-of-neg sdf h = classifyEdgeSurface-bulk-of-neg sdf h

constants-classify-surface-of-pos : ∀ (sdf : ℚ) (hneg : ¬ (sdf ℚBase.< 0ℚ)) (hne : sdf ≢ 0ℚ) →
  classifyEdgeSurface sdf ≡ regime-surface
constants-classify-surface-of-pos sdf hneg hne =
  classifyEdgeSurface-surface-of-pos sdf hneg hne

constantsScaleSheafEqualityAuthorized : ConstantsScaleSheafDiagram → Set
constantsScaleSheafEqualityAuthorized _ = ⊥

constants-scale-sheaf-equality-physics-green-false : ∀ (d : ConstantsScaleSheafDiagram) →
  ¬ constantsScaleSheafEqualityAuthorized d
constants-scale-sheaf-equality-physics-green-false d h = h

constantsScaleSheafPhysicsGreenAuthorized : ConstantsScaleSheaf → Set
constantsScaleSheafPhysicsGreenAuthorized _ = ⊥

constants-scale-sheaf-physics-green-false : ∀ (c : ConstantsScaleSheaf) →
  ¬ constantsScaleSheafPhysicsGreenAuthorized c
constants-scale-sheaf-physics-green-false c h = h

constantsScaleElementElectronicPhysicsGreenAuthorized : ElementElectronic → Set
constantsScaleElementElectronicPhysicsGreenAuthorized _ = ⊥

constants-scale-element-physics-green-false : ∀ (e : ElementElectronic) →
  ¬ constantsScaleElementElectronicPhysicsGreenAuthorized e
constants-scale-element-physics-green-false e h = h
