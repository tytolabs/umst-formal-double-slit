-- SPDX-FileCopyrightText: 2026 Santosh Prabhu Shenbagamoorthy and Santhosh Shyamsundar
-- SPDX-License-Identifier: MIT
------------------------------------------------------------------------
-- UMST-Formal: AllotropeGeometry.agda
--
-- Geometry preview for L0 chemistry on the quantum / knowing fiber
-- (`umst-formal-double-slit` only):
--
--   * SCALE: Q ↔ meso ↔ macro legs are typed; commute is not Proved here.
--   * EDGE-SURFACE: sdf < 0 bulk, sdf = 0 interface, sdf > 0 surface.
--
-- Mirrors `Lean/ChemGeometry.lean` + `QLatticeCell` from `ElementElectronic.lean`.
-- Pairs `umst-chem` scaffolds CHEM-L0-SCALE-01 and CHEM-L0-EDGE-SURFACE.
-- No meso acting theorems. `physics_green` stays false.
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module AllotropeGeometry where

open import Data.Nat.Base using (z<s)
open import Data.Nat as ℕ using (ℕ; zero; suc; _+_; _≤_)
open import Data.Nat.Properties using (≤-refl; 0≢1+n; suc-injective; 0<1+n)
open import Data.Integer as ℤ using (ℤ; ∣_∣)
open import Data.Bool using (Bool; true; false; if_then_else_)
open import Data.Rational as ℚ using (ℚ; 0ℚ)
open import Data.Rational.Base as ℚBase using (_<_)
open import Data.Rational.Properties as ℚ-Props using (_<?_; _≟_)
open import Data.Product using (_×_; _,_)
open import Data.Empty using (⊥; ⊥-elim)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; sym; cong; subst)
open import Relation.Nullary using (Dec; yes; no; ¬_)
open import Relation.Nullary.Negation using (contradiction)
open import Relation.Nullary.Decidable using (does)

------------------------------------------------------------------------
-- Q-lattice cell (knowing primary discrete identity — Lean mirror)
------------------------------------------------------------------------

data SpinProjection : Set where
  spin-down spin-up : SpinProjection

record QLatticeCell : Set where
  constructor mkQLatticeCell
  field
    nQ    : ℕ
    hnQ   : ℕ.zero ℕ.< nQ
    ell   : ℕ
    hell  : ell ℕ.< nQ
    mEll  : ℤ
    hmEll : ∣ mEll ∣ ≤ ell
    spin  : SpinProjection

madelungPriority : QLatticeCell → ℕ
madelungPriority q = QLatticeCell.nQ q ℕ.+ QLatticeCell.ell q

madelungPriority-pos : ∀ q → ℕ.zero ℕ.< madelungPriority q
madelungPriority-pos q with QLatticeCell.hnQ q
... | z<s = z<s

hydrogen1s : QLatticeCell
hydrogen1s = record
  { nQ = suc zero
  ; hnQ = 0<1+n
  ; ell = zero
  ; hell = 0<1+n
  ; mEll = ℤ.+ zero
  ; hmEll = ≤-refl
  ; spin = spin-down
  }

hydrogen1s-madelung : madelungPriority hydrogen1s ≡ 1
hydrogen1s-madelung = refl

------------------------------------------------------------------------
-- SCALE ladder (typed legs; commute not Proved)
------------------------------------------------------------------------

data ScaleLevel : Set where
  scale-quantum scale-meso scale-macro : ScaleLevel

data ScaleCommutingLeg : Set where
  quantum-to-meso meso-to-macro quantum-to-macro-direct : ScaleCommutingLeg

scaleLegSource : ScaleCommutingLeg → ScaleLevel
scaleLegSource quantum-to-meso = scale-quantum
scaleLegSource meso-to-macro = scale-meso
scaleLegSource quantum-to-macro-direct = scale-quantum

scaleLegTarget : ScaleCommutingLeg → ScaleLevel
scaleLegTarget quantum-to-meso = scale-meso
scaleLegTarget meso-to-macro = scale-macro
scaleLegTarget quantum-to-macro-direct = scale-macro

scaleLevelTag : ScaleLevel → ℕ
scaleLevelTag scale-quantum = 0
scaleLevelTag scale-meso = 1
scaleLevelTag scale-macro = 2

private
  scale-quantum≢scale-meso : scale-quantum ≢ scale-meso
  scale-quantum≢scale-meso ()

  scale-meso≢scale-macro : scale-meso ≢ scale-macro
  scale-meso≢scale-macro ()

  scale-quantum≢scale-macro : scale-quantum ≢ scale-macro
  scale-quantum≢scale-macro ()

scale-leg-source-target-distinct : ∀ leg → scaleLegSource leg ≢ scaleLegTarget leg
scale-leg-source-target-distinct quantum-to-meso = scale-quantum≢scale-meso
scale-leg-source-target-distinct meso-to-macro = scale-meso≢scale-macro
scale-leg-source-target-distinct quantum-to-macro-direct = scale-quantum≢scale-macro

------------------------------------------------------------------------
-- Chem geometry modality (design witness — Unwired)
------------------------------------------------------------------------

data ChemGeometryModality : Set where
  geom-unwired geom-assumed geom-proved geom-surrogate : ChemGeometryModality

chemGeometryModalityCurrent : ChemGeometryModality
chemGeometryModalityCurrent = geom-unwired

------------------------------------------------------------------------
-- EDGE-SURFACE SDF sign convention (ℚ samples — decidable mirror)
------------------------------------------------------------------------

data EdgeSurfaceRegime : Set where
  regime-bulk regime-interface regime-surface : EdgeSurfaceRegime

classifyEdgeSurface′ : ∀ sdf → Dec (sdf ℚBase.< 0ℚ) → Dec (sdf ≡ 0ℚ) → EdgeSurfaceRegime
classifyEdgeSurface′ sdf (yes _) _ = regime-bulk
classifyEdgeSurface′ sdf (no _) (yes _) = regime-interface
classifyEdgeSurface′ sdf (no _) (no _) = regime-surface

classifyEdgeSurface : ℚ → EdgeSurfaceRegime
classifyEdgeSurface sdf = classifyEdgeSurface′ sdf (sdf <? 0ℚ) (sdf ≟ 0ℚ)

classifyEdgeSurface-bulk-of-neg : ∀ sdf → sdf ℚBase.< 0ℚ → classifyEdgeSurface sdf ≡ regime-bulk
classifyEdgeSurface-bulk-of-neg sdf h with sdf <? 0ℚ
... | yes p = refl
... | no ¬p = ⊥-elim (¬p h)

classifyEdgeSurface-surface-of-pos : ∀ sdf → ¬ (sdf ℚBase.< 0ℚ) → sdf ≢ 0ℚ →
  classifyEdgeSurface sdf ≡ regime-surface
classifyEdgeSurface-surface-of-pos sdf hneg hne with sdf <? 0ℚ
... | yes p = ⊥-elim (hneg p)
... | no ¬lt with sdf ≟ 0ℚ
... | yes eq = ⊥-elim (hne eq)
... | no ¬eq = refl

------------------------------------------------------------------------
-- SCALE + EDGE-SURFACE geometry witness (Unwired)
------------------------------------------------------------------------

record ChemGeometry : Set where
  constructor mkChemGeometry
  field
    lattice       : QLatticeCell
    scaleModality : ChemGeometryModality
    edgeModality  : ChemGeometryModality

chemGeometryUnwired : QLatticeCell → ChemGeometry
chemGeometryUnwired q = record
  { lattice = q
  ; scaleModality = chemGeometryModalityCurrent
  ; edgeModality = chemGeometryModalityCurrent
  }

chemGeometryModalityCurrent≡geom-unwired : chemGeometryModalityCurrent ≡ geom-unwired
chemGeometryModalityCurrent≡geom-unwired = refl

_↔_ : Set → Set → Set
A ↔ B = (A → B) × (B → A)

chem-geometry-modality-unwired : ∀ g →
  (ChemGeometry.scaleModality g ≡ chemGeometryModalityCurrent ×
   ChemGeometry.edgeModality g ≡ chemGeometryModalityCurrent) ↔
  (ChemGeometry.scaleModality g ≡ geom-unwired ×
   ChemGeometry.edgeModality g ≡ geom-unwired)
chem-geometry-modality-unwired g =
  ( λ { (p , q) →
        subst (λ m → ChemGeometry.scaleModality g ≡ m) chemGeometryModalityCurrent≡geom-unwired p ,
        subst (λ m → ChemGeometry.edgeModality g ≡ m) chemGeometryModalityCurrent≡geom-unwired q
      }) ,
  ( λ { (p , q) →
        subst (λ m → ChemGeometry.scaleModality g ≡ m) (sym chemGeometryModalityCurrent≡geom-unwired) p ,
        subst (λ m → ChemGeometry.edgeModality g ≡ m) (sym chemGeometryModalityCurrent≡geom-unwired) q
      })

chemGeometryPhysicsGreenAuthorized : ChemGeometry → Set
chemGeometryPhysicsGreenAuthorized _ = ⊥

chem-geometry-physics-green-false : ∀ g → ¬ chemGeometryPhysicsGreenAuthorized g
chem-geometry-physics-green-false g h = h
