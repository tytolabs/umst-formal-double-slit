-- SPDX-FileCopyrightText: 2026 Santosh Prabhu Shenbagamoorthy and Santhosh Shyamsundar
-- SPDX-License-Identifier: MIT
------------------------------------------------------------------------
-- UMST-Formal: Gate.agda
--
-- Core admissible-state predicate and Theorem 1 (categorical safety).
--
-- This module formalises the thermodynamic gate from the Rust kernel
-- (umst-core/science/thermodynamic_filter.rs) as a dependent type.
-- The gate accepts a proposed state transition (old → new) if and only
-- if four physical invariants hold simultaneously:
--
--   1. Mass conservation       |ρ_new − ρ_old| ≤ δ
--   2. Clausius-Duhem          D_int = −ρ · ψ̇  ≥ 0
--   3. Hydration irreversibility   α_new ≥ α_old
--   4. Strength monotonicity   fc_new ≥ fc_old
--
-- Physical meaning:
--   A material state records the thermodynamic condition of a specimen at
--   a single instant (density, free energy, hydration degree, compressive
--   strength).  A proposed transition (old → new) is admissible if and
--   only if all four invariants hold simultaneously.  The gate implements
--   that check as a decidable predicate.
--   See Docs/Architecture-Invariants.md for the empirical basis of each
--   invariant.
--
-- Correspondence to Rust:
--   ThermodynamicState  ↔  ThermodynamicState in thermodynamic_filter.rs
--   Admissible          ↔  check_transition returning accepted = true
--   gate                ↔  ThermodynamicFilter::check_transition
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Gate where

open import Data.Nat as Nat using (ℕ)
open import Data.Rational as ℚ using (ℚ; 0ℚ; 1ℚ; _+_; _*_; _-_; _≤_; _<_)
open import Data.Rational.Properties as ℚ-Props
open import Data.Bool using (Bool; true; false; if_then_else_)
open import Data.Product using (_×_; _,_; proj₁; proj₂; ∃-syntax)
open import Data.Empty using (⊥-elim)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; sym; trans)
open import Relation.Nullary using (Dec; yes; no; ¬_)
open import Data.Sum using (_⊎_; inj₁; inj₂)

------------------------------------------------------------------------
-- 1. Thermodynamic State
------------------------------------------------------------------------

-- A ThermodynamicState captures the minimal set of fields needed to
-- evaluate the four invariants.  We use rationals (ℚ) throughout for
-- decidable arithmetic; the Rust kernel uses f64 with tolerance ε = 10⁻⁶.
--
-- Physical meaning of each field:
--   density          ρ  (kg/m³)     bulk density of the paste/concrete
--   free-energy      ψ  (J/kg)      Helmholtz free energy per unit mass
--   hydration        α  (0–1)       degree of cement hydration
--   strength         fc (MPa)       compressive strength (Powers model)

record ThermodynamicState : Set where
  constructor mkState
  field
    density     : ℚ   -- ρ
    free-energy : ℚ   -- ψ = −Q_hyd · α  in the Rust kernel
    hydration   : ℚ   -- α
    strength    : ℚ   -- fc

open ThermodynamicState

------------------------------------------------------------------------
-- 2. Physical Constants
------------------------------------------------------------------------

-- | [n] copies of [1ℚ], i.e. ℕ → ℚ without [mkℚ] / coprimality proofs
--   (stdlib names for coprime witnesses differ across Agda versions).
private
  natToℚ : ℕ → ℚ
  natToℚ Nat.zero    = 0ℚ
  natToℚ (Nat.suc k) = 1ℚ + natToℚ k

-- Tolerance for mass conservation check.
-- In the Rust kernel this is 100.0 kg/m³ (a generous bound that catches
-- gross density jumps while allowing normal hydration-induced changes).
δ-mass : ℚ
δ-mass = natToℚ 100

-- Tolerance for dissipation and strength checks.
-- In the Rust kernel this is 1e-6.  For rational proofs we use 0
-- (the strict version), since the toleranced version follows trivially.
-- The key mathematical content is the sign of D_int, not the epsilon.

------------------------------------------------------------------------
-- 3. Admissibility Predicate
------------------------------------------------------------------------

-- The four invariants bundled as a single proposition.
-- Admissible old new holds iff the transition old → new satisfies all
-- four physical laws simultaneously.
--
-- Note on dt: the time step appears in the Rust computation of ψ̇ but
-- cancels out in the sign check (D_int ≥ 0 ⟺ ψ̇ ≤ 0 for ρ > 0).
-- We therefore omit dt from the formalisation without loss of generality.

record Admissible (old new : ThermodynamicState) : Set where
  constructor mkAdmissible
  field
    -- Invariant 1: Mass conservation
    -- |ρ_new − ρ_old| < δ
    mass-conserved : (density new - density old ≤ δ-mass)
                   × (density old - density new ≤ δ-mass)

    -- Invariant 2: Clausius-Duhem dissipation (sign condition)
    -- D_int = −ρ · ψ̇ ≥ 0
    -- Since ρ > 0, this reduces to ψ̇ ≤ 0, i.e., ψ_new ≤ ψ_old
    dissipation-nonneg : free-energy new ≤ free-energy old

    -- Invariant 3: Hydration irreversibility
    -- α_new ≥ α_old (cement hydration is a one-way chemical reaction)
    hydration-monotone : hydration old ≤ hydration new

    -- Invariant 4: Strength monotonicity
    -- fc_new ≥ fc_old (undamaged concrete cannot lose strength)
    strength-monotone : strength old ≤ strength new

open Admissible

------------------------------------------------------------------------
-- 4. Gate Decision Procedure
------------------------------------------------------------------------

-- The gate is a decision procedure: given two states, it either
-- produces a proof of admissibility or a proof of inadmissibility.
-- This mirrors ThermodynamicFilter::check_transition in Rust.
--
-- In category-theoretic terms, this is a morphism in the arrow category
-- of Set:  gate : State × State → 1 + 1  (i.e., Bool with evidence).

gate : (old new : ThermodynamicState) → Dec (Admissible old new)
gate old new with (density new - density old) ℚ.≤? δ-mass
                 | (density old - density new) ℚ.≤? δ-mass
                 | free-energy new ℚ.≤? free-energy old
                 | hydration old ℚ.≤? hydration new
                 | strength old ℚ.≤? strength new
... | yes mc₁ | yes mc₂ | yes diss | yes hyd | yes str =
      yes (mkAdmissible (mc₁ , mc₂) diss hyd str)
... | no ¬mc₁ | _       | _        | _       | _       =
      no (λ adm → ¬mc₁ (proj₁ (mass-conserved adm)))
... | _       | no ¬mc₂ | _        | _       | _       =
      no (λ adm → ¬mc₂ (proj₂ (mass-conserved adm)))
... | _       | _       | no ¬diss | _       | _       =
      no (λ adm → ¬diss (dissipation-nonneg adm))
... | _       | _       | _        | no ¬hyd | _       =
      no (λ adm → ¬hyd (hydration-monotone adm))
... | _       | _       | _        | _       | no ¬str =
      no (λ adm → ¬str (strength-monotone adm))


------------------------------------------------------------------------
-- 7. CSG Decomposition (SDF / FRep Interpretation)
------------------------------------------------------------------------

-- The four gate conditions as named sub-predicates.
-- In SDF/FRep terms, each defines one implicit half-space in the
-- product space ThermodynamicState × ThermodynamicState.  The
-- admissible region is the CSG intersection of all four.

MassCond : ThermodynamicState → ThermodynamicState → Set
MassCond old new = (density new - density old ≤ δ-mass)
                 × (density old - density new ≤ δ-mass)

DissipCond : ThermodynamicState → ThermodynamicState → Set
DissipCond old new = free-energy new ≤ free-energy old

HydrationCond : ThermodynamicState → ThermodynamicState → Set
HydrationCond old new = hydration old ≤ hydration new

StrengthCond : ThermodynamicState → ThermodynamicState → Set
StrengthCond old new = strength old ≤ strength new

-- Theorem (CSG Decomposition):
--   Admissible old new decomposes into exactly the four named sub-conditions.
--   This is the formal statement that the gate is a CSG intersection:
--
--     admissible(old, new)
--       ⟺ massCond(old,new) ∩ dissipCond(old,new)
--            ∩ hydrationCond(old,new) ∩ strengthCond(old,new)
--
-- Forward direction: extract each field from the Admissible record.
admissible-to-csg
  : ∀ (old new : ThermodynamicState)
  → Admissible old new
  → MassCond old new × DissipCond old new
  × HydrationCond old new × StrengthCond old new
admissible-to-csg old new adm =
  mass-conserved adm , dissipation-nonneg adm ,
  hydration-monotone adm , strength-monotone adm

-- Backward direction: construct an Admissible record from the four conditions.
csg-to-admissible
  : ∀ (old new : ThermodynamicState)
  → MassCond old new × DissipCond old new
  × HydrationCond old new × StrengthCond old new
  → Admissible old new
csg-to-admissible old new (mc , diss , hyd , str) =
  mkAdmissible mc diss hyd str
