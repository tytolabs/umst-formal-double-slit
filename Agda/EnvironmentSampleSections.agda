-- SPDX-FileCopyrightText: 2026 Santosh Prabhu Shenbagamoorthy and Santhosh Shyamsundar
-- SPDX-License-Identifier: MIT
------------------------------------------------------------------------
-- UMST-Formal: EnvironmentSampleSections.agda
--
-- Quantum / knowing fiber preview for environment SAMPLE sections (v15):
--   * Vacuum / contained / messy as simultaneous knowing probes
--     (not XOR — all three present in each EnvironmentSection)
--   * Imports and reuses sibling EnvironmentScaleCommute sample sheaf
--
-- Mirrors `Lean/ChemConstants/EnvironmentSampleSections.lean` +
-- sibling `Haskell/src/EnvironmentSampleSections.hs` style.
-- No meso / acting theorems. Modality Unwired; physics GREEN false.
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module EnvironmentSampleSections where

open import AllotropeGeometry using (ScaleLevel; scaleLegSource; scaleLegTarget)
open import Data.Nat as ℕ using (ℕ; suc)
open import Data.Product using (_×_; _,_)
open import Data.Empty using (⊥; ⊥-elim)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl)
open import Relation.Nullary using (¬_)

open import EnvironmentScaleCommute

------------------------------------------------------------------------
-- Env sample axis distinctness (not XOR pick-one)
------------------------------------------------------------------------

env-sample-axes-distinct-vacuum-contained : env-axis-vacuum ≢ env-axis-contained
env-sample-axes-distinct-vacuum-contained ()

env-sample-axes-distinct-vacuum-messy : env-axis-vacuum ≢ env-axis-messy
env-sample-axes-distinct-vacuum-messy ()

env-sample-axes-distinct-contained-messy : env-axis-contained ≢ env-axis-messy
env-sample-axes-distinct-contained-messy ()

env-sample-axes-all-distinct :
  env-axis-vacuum ≢ env-axis-contained ×
  env-axis-vacuum ≢ env-axis-messy ×
  env-axis-contained ≢ env-axis-messy
env-sample-axes-all-distinct =
  env-sample-axes-distinct-vacuum-contained ,
  env-sample-axes-distinct-vacuum-messy ,
  env-sample-axes-distinct-contained-messy

------------------------------------------------------------------------
-- Knowing probes simultaneous at every stratum (not XOR)
------------------------------------------------------------------------

probe-samples-simultaneous-at-level : ∀ (f : EnvironmentSheafField) (lvl : ScaleLevel) →
  probeSample f (mkKnowingProbe env-axis-vacuum    lvl) ≡
  probeSample f (mkKnowingProbe env-axis-vacuum    lvl) ×
  probeSample f (mkKnowingProbe env-axis-contained lvl) ≡
  probeSample f (mkKnowingProbe env-axis-contained lvl) ×
  probeSample f (mkKnowingProbe env-axis-messy     lvl) ≡
  probeSample f (mkKnowingProbe env-axis-messy     lvl)
probe-samples-simultaneous-at-level f lvl = refl , refl , refl

probe-vacuum-at-leg-source-quantum-to-meso : ∀ (f : EnvironmentSheafField) →
  probeSample f (mkKnowingProbe env-axis-vacuum (scaleLegSource scaleLegQuantumToMeso)) ≡
  VacuumSample.residualPO2Pa (EnvironmentSection.vacuum (EnvironmentSheafField.atQuantum f))
probe-vacuum-at-leg-source-quantum-to-meso f = refl

probe-contained-at-leg-target-meso-to-macro : ∀ (f : EnvironmentSheafField) →
  probeSample f (mkKnowingProbe env-axis-contained (scaleLegTarget scaleLegMesoToMacro)) ≡
  ContainedSample.kelvin (EnvironmentSection.contained (EnvironmentSheafField.atMacro f))
probe-contained-at-leg-target-meso-to-macro f = refl

probe-messy-at-leg-source-quantum-to-macro-direct : ∀ (f : EnvironmentSheafField) →
  probeSample f (mkKnowingProbe env-axis-messy (scaleLegSource scaleLegQuantumToMacroDirect)) ≡
  MessySample.oreGradeFraction (EnvironmentSection.messy (EnvironmentSheafField.atQuantum f))
probe-messy-at-leg-source-quantum-to-macro-direct f = refl

------------------------------------------------------------------------
-- Ambient knowing probes (Unwired placeholder — not physics GREEN)
------------------------------------------------------------------------

probe-sample-ambient-vacuum-quantum :
  probeSample environmentSheafFieldAmbient probeVacuumAtQuantum ≡
  VacuumSample.residualPO2Pa vacuumSampleAmbient
probe-sample-ambient-vacuum-quantum = refl

probe-sample-ambient-contained-meso :
  probeSample environmentSheafFieldAmbient probeContainedAtMeso ≡
  ContainedSample.kelvin containedSampleAmbient
probe-sample-ambient-contained-meso = refl

probe-sample-ambient-messy-macro :
  probeSample environmentSheafFieldAmbient probeMessyAtMacro ≡
  MessySample.oreGradeFraction messySampleAmbient
probe-sample-ambient-messy-macro = refl

env-sample-axis-cardinality : ℕ
env-sample-axis-cardinality = 3

env-sample-axis-cardinality-three : env-sample-axis-cardinality ≡ 3
env-sample-axis-cardinality-three = refl

------------------------------------------------------------------------
-- Environment section has all three probes (not XOR)
------------------------------------------------------------------------

environment-section-has-all-probes : ∀ (s : EnvironmentSection) →
  EnvironmentSection.vacuum s ≡ EnvironmentSection.vacuum s ×
  EnvironmentSection.contained s ≡ EnvironmentSection.contained s ×
  EnvironmentSection.messy s ≡ EnvironmentSection.messy s
environment-section-has-all-probes s = refl , refl , refl

environment-section-has-all-probes-at-level : ∀ (f : EnvironmentSheafField) (lvl : ScaleLevel) →
  vacuumSampleAtLevel f lvl ≡ EnvironmentSection.vacuum (environmentAtLevel f lvl) ×
  containedSampleAtLevel f lvl ≡ EnvironmentSection.contained (environmentAtLevel f lvl) ×
  messySampleAtLevel f lvl ≡ EnvironmentSection.messy (environmentAtLevel f lvl)
environment-section-has-all-probes-at-level f lvl = refl , refl , refl

probe-ambient-triple-not-xor :
  probeSample environmentSheafFieldAmbient probeVacuumAtQuantum ≡
  VacuumSample.residualPO2Pa vacuumSampleAmbient ×
  probeSample environmentSheafFieldAmbient probeContainedAtMeso ≡
  ContainedSample.kelvin containedSampleAmbient ×
  probeSample environmentSheafFieldAmbient probeMessyAtMacro ≡
  MessySample.oreGradeFraction messySampleAmbient
probe-ambient-triple-not-xor =
  probe-sample-ambient-vacuum-quantum ,
  probe-sample-ambient-contained-meso ,
  probe-sample-ambient-messy-macro

------------------------------------------------------------------------
-- Honesty — physics GREEN false on knowing probes
------------------------------------------------------------------------

environmentSampleProbeEqualityAuthorized : KnowingProbe → Set
environmentSampleProbeEqualityAuthorized _ = ⊥

environment-sample-probe-equality-physics-green-false : ∀ (p : KnowingProbe) →
  ¬ environmentSampleProbeEqualityAuthorized p
environment-sample-probe-equality-physics-green-false p h = h

environmentSampleSectionsPhysicsGreenAuthorized : KnowingProbe → Set
environmentSampleSectionsPhysicsGreenAuthorized _ = ⊥

environment-sample-sections-physics-green-false : ∀ (p : KnowingProbe) →
  ¬ environmentSampleSectionsPhysicsGreenAuthorized p
environment-sample-sections-physics-green-false p h = h
