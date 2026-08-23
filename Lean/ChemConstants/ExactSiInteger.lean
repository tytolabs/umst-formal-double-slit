-- SPDX-FileCopyrightText: 2026 Santosh Prabhu Shenbagamoorthy and Santhosh Shyamsundar
-- SPDX-License-Identifier: MIT

import LandauerEinsteinBridge

/-!
# ExactSiInteger — knowing-fiber SI-2019 exact integer mantissa identity (Q lattice)

SI-2019 defining constants **k** and **N_A** as integer mantissa × 10^decimal exponent;
**DerivedSI** **R** = N_A ∘ k as **integer product** (mantissa multiply + exponent add) — never
`f64` multiply. Mirrors `umst-chem` `si_exact_integer_mantissa` (`CHEM-INT-SI-EXACT-INTEGER-MANTISSA`).

- **k** rational lift: `kBoltzmannSI = 1380649 / 10^29` (matches `LandauerEinsteinBridge`).
- **R** identity is a **named composition** (`composeMolarGasConstantInteger`) — unique
  factorization is name/identity, not a 26th axiom.
- No meso / acting theorems. No new physics `axiom`.
- `physics_green` stays false.
-/

namespace UMST.Chem

/-- Design modality for exact SI integer-mantissa claims (TYPE-03 preview). -/
inductive ExactSiIntegerModality where
  | unwired | assumed | proved | surrogate
  deriving DecidableEq, Repr

def exactSiIntegerModalityCurrent : ExactSiIntegerModality := .unwired

/-- Exact SI decimal as integer mantissa × 10^decimalExp (identity, not `f64`). -/
structure ExactSiDecimal where
  mantissa : ℤ
  decimalExp : ℤ
  deriving DecidableEq, Repr

/-- Integer multiply of two exact SI decimals: mantissa product + exponent sum. -/
def exactSiDecimalProduct (a b : ExactSiDecimal) : ExactSiDecimal :=
  { mantissa := a.mantissa * b.mantissa
    decimalExp := a.decimalExp + b.decimalExp }

/-- Named integer composition morphism (DerivedSI — not unique-factorization axiom). -/
def composeExactSiDecimal (a b : ExactSiDecimal) : ExactSiDecimal :=
  exactSiDecimalProduct a b

theorem exact_si_decimal_product_mantissa (a b : ExactSiDecimal) :
    (exactSiDecimalProduct a b).mantissa = a.mantissa * b.mantissa := rfl

theorem exact_si_decimal_product_decimal_exp (a b : ExactSiDecimal) :
    (exactSiDecimalProduct a b).decimalExp = a.decimalExp + b.decimalExp := rfl

theorem compose_exact_si_decimal_eq_product (a b : ExactSiDecimal) :
    composeExactSiDecimal a b = exactSiDecimalProduct a b := rfl

namespace ExactSi

/-- SI-2019 defining: Boltzmann constant **k** [J K⁻¹] — 1380649 × 10⁻²⁹ J/K. -/
def kJPerK : ExactSiDecimal := { mantissa := 1380649, decimalExp := -29 }

/-- SI-2019 defining: Avogadro constant **N_A** [mol⁻¹] — 602214076 × 10¹⁵ mol⁻¹. -/
def nAPerMol : ExactSiDecimal := { mantissa := 602214076, decimalExp := 15 }

/-- Derived SI: molar gas constant **R** = N_A ∘ k — integer product, not `f64`. -/
def rJPerMolK : ExactSiDecimal := composeExactSiDecimal nAPerMol kJPerK

/-- Named DerivedSI composition (identity by definition — not axiom). -/
def composeMolarGasConstantInteger : ExactSiDecimal := rJPerMolK

theorem compose_molar_gas_constant_integer_named :
    composeMolarGasConstantInteger = composeExactSiDecimal nAPerMol kJPerK := rfl

theorem r_is_named_integer_product :
    rJPerMolK = exactSiDecimalProduct nAPerMol kJPerK := rfl

theorem r_mantissa_is_integer_product :
    rJPerMolK.mantissa = nAPerMol.mantissa * kJPerK.mantissa := rfl

theorem r_decimal_exp_is_sum :
    rJPerMolK.decimalExp = nAPerMol.decimalExp + kJPerK.decimalExp := rfl

theorem k_mantissa_value : kJPerK.mantissa = 1380649 := rfl

theorem k_decimal_exp_value : kJPerK.decimalExp = -29 := rfl

theorem n_a_mantissa_value : nAPerMol.mantissa = 602214076 := rfl

theorem n_a_decimal_exp_value : nAPerMol.decimalExp = 15 := rfl

theorem r_mantissa_value : rJPerMolK.mantissa = 831446261815324 := by native_decide

theorem r_decimal_exp_value : rJPerMolK.decimalExp = -14 := by native_decide

theorem r_mantissa_matches_explicit_product :
    rJPerMolK.mantissa = 602214076 * 1380649 := by native_decide

/-- Rational **k** view matching `LandauerEinsteinBridge.kBoltzmannSI`. -/
noncomputable def kBoltzmannRational : ℝ :=
  (kJPerK.mantissa : ℝ) / (10 : ℝ) ^ (-kJPerK.decimalExp)

theorem k_rational_matches_landauer_bridge :
    kBoltzmannRational = kBoltzmannSI := by
  unfold kBoltzmannRational kBoltzmannSI kJPerK
  norm_num

/-- Unique factorization enters only as **name/identity** on the integer composition — no new axiom. -/
structure DerivedSiRIdentity where
  /-- Named mantissa product (definitional, not postulated unique factorization). -/
  rMantissa : ℤ := rJPerMolK.mantissa
  /-- Named exponent sum. -/
  rDecimalExp : ℤ := rJPerMolK.decimalExp

def derivedSiRIdentityNamed : DerivedSiRIdentity := {}

theorem derived_si_r_identity_named_mantissa :
    derivedSiRIdentityNamed.rMantissa = rJPerMolK.mantissa := rfl

theorem derived_si_r_identity_named_decimal_exp :
    derivedSiRIdentityNamed.rDecimalExp = rJPerMolK.decimalExp := rfl

theorem derived_si_r_not_unique_factorization_axiom :
    composeMolarGasConstantInteger = exactSiDecimalProduct nAPerMol kJPerK := rfl

end ExactSi

/-- Cited Rust integer-mantissa authority (views only — identity is integer here). -/
def exactSiIntegerCitedModule : String :=
  "umst/umst-chem/src/si_exact_integer_mantissa.rs"

/-- Cell id for the Lean exact SI integer rational knowing-fiber. -/
def exactSiIntegerCellId : String := "CHEM-FORMAL-Q-LEAN-EXACT-SI-RATIONAL"

/-- Non-claim fence — integer ExactSI identity Unwired ≠ Proved GREEN. -/
def exactSiIntegerNonClaim : String :=
  "CHEM-FORMAL-Q-LEAN-EXACT-SI-RATIONAL SI-2019 exact k N_A as integer mantissa+decimal exponent; DerivedSI R=N_A k integer product not f64 multiply; cites si_exact_integer_mantissa; unique factorization name/identity not 26th axiom; not physics GREEN; not production_wired"

/-- Physics GREEN is unauthorized on the knowing exact SI integer scaffold. -/
def exactSiIntegerPhysicsGreenAuthorized : Prop := False

theorem exact_si_integer_physics_green_false :
    ¬ exactSiIntegerPhysicsGreenAuthorized := id

theorem exact_si_integer_modality_unwired :
    exactSiIntegerModalityCurrent = .unwired := rfl

theorem exact_si_integer_k_matches_chem_mantissa :
    ExactSi.kJPerK.mantissa = 1380649 ∧ ExactSi.kJPerK.decimalExp = -29 := by
  constructor <;> rfl

theorem exact_si_integer_r_rejects_theater_product :
    ExactSi.rJPerMolK.mantissa ≠ 831446 := by native_decide

end UMST.Chem
