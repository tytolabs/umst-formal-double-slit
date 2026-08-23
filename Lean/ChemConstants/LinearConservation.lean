-- SPDX-FileCopyrightText: 2026 Santosh Prabhu Shenbagamoorthy and Santhosh Shyamsundar
-- SPDX-License-Identifier: MIT

import ElementElectronic

/-!
# LinearConservation — knowing-fiber TYPE-02 linear conservation (Q lattice)

Signed-coefficient **linear** exact-balance on conservation axes — Mass / Charge / AtomCount /
Enthalpy as typed structure, not a 118² GREEN table. Pairs `umst-chem` scaffold
`CHEM-L0-TYPE-02` / `CHEM-INT-PROVE-TYPE-02-LINEAR` conservation posture.

- `ConservationAxis` — `Mass` / `Charge` / `AtomCount` / `Enthalpy` (not SpeciesId-backed).
- `LinearCoeffRow` — signed integer coeffs on bounded scaffold terms; axis sum **0** = balanced.
- `linearAxisBalanced` — exact linear conservation; imbalanced rows **refuse**.
- `AffineSlackRow` — affine weakening only with `DissipativeWitness`; without witness **refuse**.
- Second-law framing cites meso `UMST.Chem.Conservation` / `LandauerLaw.physicalSecondLaw` — not imported.
- No meso / acting theorems. No new physics `axiom`.
- `physics_green` stays false. Does **not** claim TYPE-02 Proved or physics GREEN.
-/

namespace UMST.Chem

/-- Design modality for TYPE-02 linear conservation claims (TYPE-03 preview). -/
inductive LinearConservationModality where
  | unwired | assumed | proved | surrogate
  deriving DecidableEq, Repr

def linearConservationModalityCurrent : LinearConservationModality := .unwired

/-- Conservation resource axes — linear vs affine scaffold (not 118² periodic table). -/
inductive ConservationAxis where
  | Mass
  | Charge
  | AtomCount
  | Enthalpy
  deriving DecidableEq, Repr

def conservationAxisString : ConservationAxis → String
  | .Mass => "mass"
  | .Charge => "charge"
  | .AtomCount => "atom_count"
  | .Enthalpy => "enthalpy"

theorem conservation_axis_mass : conservationAxisString .Mass = "mass" := rfl

theorem conservation_axis_charge : conservationAxisString .Charge = "charge" := rfl

theorem conservation_axis_atom_count : conservationAxisString .AtomCount = "atom_count" := rfl

theorem conservation_axis_enthalpy : conservationAxisString .Enthalpy = "enthalpy" := rfl

/-- Cardinality of named conservation axes (structure witness — not element enumeration). -/
def conservationAxisCardinality : Nat := 4

theorem conservation_axis_cardinality_four : conservationAxisCardinality = 4 := rfl

/-- Bounded linear term tags (knowing scaffold — not SpeciesId / 118² GREEN). -/
inductive LinearTermTag where
  | reactantA | reactantB | productC | productD
  deriving DecidableEq, Repr

def linearTermTagString : LinearTermTag → String
  | .reactantA => "reactant_a"
  | .reactantB => "reactant_b"
  | .productC => "product_c"
  | .productD => "product_d"

theorem linear_term_tag_reactant_a :
    linearTermTagString .reactantA = "reactant_a" := rfl

/-- Signed coefficient row on one conservation axis (stoichiometric scaffold). -/
structure LinearCoeffRow where
  axis : ConservationAxis
  reactantA : Int
  reactantB : Int
  productC : Int
  productD : Int
  deriving DecidableEq, Repr

/-- Signed linear conservation sum on an axis — exact balance when zero. -/
def linearCoeffSum (row : LinearCoeffRow) : Int :=
  row.reactantA + row.reactantB + row.productC + row.productD

/-- Linear exact-balance gate — coeffs on axis sum to 0 (balanced admit / imbalanced refuse). -/
def linearAxisBalanced (row : LinearCoeffRow) : Bool :=
  decide (linearCoeffSum row = 0)

/-- Mass-axis balanced scaffold — signed coeffs sum to 0 (linear conservation witness). -/
def massBalancedRow : LinearCoeffRow :=
  { axis := .Mass, reactantA := 1, reactantB := 1, productC := -1, productD := -1 }

theorem mass_balanced_linear_conservation :
    linearAxisBalanced massBalancedRow = true := rfl

/-- Charge-axis balanced scaffold — signed coeffs sum to 0. -/
def chargeBalancedRow : LinearCoeffRow :=
  { axis := .Charge, reactantA := 2, reactantB := -1, productC := -1, productD := 0 }

theorem charge_balanced_linear_conservation :
    linearAxisBalanced chargeBalancedRow = true := rfl

/-- Mass-axis imbalanced scaffold — signed coeffs refuse (not exact linear balance). -/
def massImbalancedRow : LinearCoeffRow :=
  { axis := .Mass, reactantA := 1, reactantB := 1, productC := -1, productD := 0 }

theorem mass_imbalanced_linear_refuse :
    linearAxisBalanced massImbalancedRow = false := rfl

/-- AtomCount-axis imbalanced scaffold — refuse without balance. -/
def atomCountImbalancedRow : LinearCoeffRow :=
  { axis := .AtomCount, reactantA := 3, reactantB := 0, productC := -1, productD := -1 }

theorem atom_count_imbalanced_linear_refuse :
    linearAxisBalanced atomCountImbalancedRow = false := rfl

/-- Enthalpy-axis zero-delta balanced scaffold — all coeffs zero. -/
def enthalpyZeroRow : LinearCoeffRow :=
  { axis := .Enthalpy, reactantA := 0, reactantB := 0, productC := 0, productD := 0 }

theorem enthalpy_zero_linear_conservation :
    linearAxisBalanced enthalpyZeroRow = true := rfl

/-- Whether a conservation axis tag matches the row axis (structure witness). -/
def linearRowOnAxis (row : LinearCoeffRow) (axis : ConservationAxis) : Bool :=
  decide (row.axis = axis)

theorem mass_balanced_on_mass_axis :
    linearRowOnAxis massBalancedRow .Mass = true := rfl

/-- Affine slack row — linear coeffs plus recorded nonnegative slack (weakening axis). -/
structure AffineSlackRow where
  linear : LinearCoeffRow
  slack : Nat
  deriving DecidableEq, Repr

/-- Affine closure scaffold — linear balance with slack discharged on the knowing fiber. -/
def affineConservationClosed (row : AffineSlackRow) : Bool :=
  decide (linearCoeffSum row.linear + (row.slack : Int) = 0)

/-- Dissipative witness scaffold — slack · T ≤ dissipated work (second-law framing). -/
structure DissipativeWitness where
  slack : Nat
  bathTempScaffold : Nat
  dissipatedWorkScaffold : Nat
  deriving DecidableEq, Repr

/-- Dissipative witness ok — mirrors meso `affineDissipativeWitness` posture (Unwired). -/
def dissipativeWitnessOk (w : DissipativeWitness) : Bool :=
  decide (w.slack * w.bathTempScaffold ≤ w.dissipatedWorkScaffold)

/-- Affine weakening admitted only with dissipative witness; without witness refuse. -/
def affineWeakeningAdmitted (row : AffineSlackRow) (witness : Option DissipativeWitness) : Bool :=
  match witness with
  | none => false
  | some w =>
      affineConservationClosed row &&
        decide (w.slack = row.slack) &&
        dissipativeWitnessOk w

/-- Affine row with slack=1 on negatively imbalanced linear coeffs — closed only with slack. -/
def massAffineLinearRow : LinearCoeffRow :=
  { axis := .Mass, reactantA := -2, reactantB := 1, productC := 0, productD := 0 }

theorem mass_affine_linear_row_imbalanced :
    linearAxisBalanced massAffineLinearRow = false := rfl

def massAffineSlackRow : AffineSlackRow :=
  { linear := massAffineLinearRow, slack := 1 }

theorem mass_affine_conservation_closed :
    affineConservationClosed massAffineSlackRow = true := rfl

def massDissipativeWitness : DissipativeWitness :=
  { slack := 1, bathTempScaffold := 2, dissipatedWorkScaffold := 3 }

theorem mass_dissipative_witness_ok :
    dissipativeWitnessOk massDissipativeWitness = true := rfl

theorem mass_affine_weakening_admitted_with_witness :
    affineWeakeningAdmitted massAffineSlackRow (some massDissipativeWitness) = true := rfl

theorem mass_affine_weakening_refuse_without_witness :
    affineWeakeningAdmitted massAffineSlackRow none = false := rfl

/-- Wrong slack witness — refuse even when affine row is closed. -/
def massWrongSlackWitness : DissipativeWitness :=
  { slack := 2, bathTempScaffold := 2, dissipatedWorkScaffold := 10 }

theorem mass_affine_weakening_refuse_wrong_witness :
    affineWeakeningAdmitted massAffineSlackRow (some massWrongSlackWitness) = false := rfl

/-- Linear algebra is not SpeciesId-backed (bounded term tags only). -/
def linearAlgebraNotSpeciesBacked : Bool := true

theorem linear_algebra_not_species_backed : linearAlgebraNotSpeciesBacked = true := rfl

/-- Conservation axes are structure — not 118² GREEN periodic enumeration. -/
def conservationAxesNot118GreenTable : Bool := true

theorem conservation_axes_not_118_green_table :
    conservationAxesNot118GreenTable = true := rfl

/-- Second-law + conservation framing — cites meso SSOT, not wired on knowing scaffold. -/
def linearConservationSecondLawFramed : Bool := true

theorem linear_conservation_second_law_framed :
    linearConservationSecondLawFramed = true := rfl

/-- TYPE-02 linear conservation is **not** claimed Proved on the knowing scaffold. -/
def type02LinearProved : Bool := false

theorem type02_linear_not_proved : type02LinearProved = false := rfl

/-- Production wiring is **not** claimed on the knowing scaffold. -/
def linearConservationProductionWired : Bool := false

theorem linear_conservation_production_not_wired :
    linearConservationProductionWired = false := rfl

/-- Cell id for the Lean TYPE-02 linear conservation knowing-fiber. -/
def linearConservationCellId : String :=
  "CHEM-FORMAL-Q-LEAN-LINEAR-CONSERVATION"

/-- Non-claim fence — linear exact-balance; affine weakening with dissipative witness; TYPE-02 Unwired. -/
def linearConservationNonClaim : String :=
  "CHEM-FORMAL-Q-LEAN-LINEAR-CONSERVATION ConservationAxis Mass Charge AtomCount Enthalpy linear exact-balance affine slack dissipative witness type02LinearProved false Unwired not TYPE-02 Proved not physics GREEN; not 118² GREEN DFT"

/-- Physics GREEN is unauthorized on the knowing TYPE-02 linear conservation scaffold. -/
def linearConservationPhysicsGreenAuthorized : Prop := False

theorem linear_conservation_physics_green_false :
    ¬ linearConservationPhysicsGreenAuthorized := id

theorem linear_conservation_modality_unwired :
    linearConservationModalityCurrent = .unwired := rfl

theorem linear_conservation_honest_bundle :
    type02LinearProved = false ∧
    linearConservationProductionWired = false ∧
    linearAlgebraNotSpeciesBacked = true ∧
    conservationAxesNot118GreenTable = true ∧
    linearConservationSecondLawFramed = true ∧
    linearAxisBalanced massBalancedRow = true ∧
    linearAxisBalanced chargeBalancedRow = true ∧
    linearAxisBalanced massImbalancedRow = false ∧
    linearAxisBalanced massAffineLinearRow = false ∧
    linearAxisBalanced atomCountImbalancedRow = false ∧
    affineWeakeningAdmitted massAffineSlackRow (some massDissipativeWitness) = true ∧
    affineWeakeningAdmitted massAffineSlackRow none = false ∧
    affineWeakeningAdmitted massAffineSlackRow (some massWrongSlackWitness) = false :=
  ⟨rfl, rfl, linear_algebra_not_species_backed, conservation_axes_not_118_green_table,
    linear_conservation_second_law_framed, mass_balanced_linear_conservation,
    charge_balanced_linear_conservation, mass_imbalanced_linear_refuse,
    mass_affine_linear_row_imbalanced, atom_count_imbalanced_linear_refuse,
    mass_affine_weakening_admitted_with_witness, mass_affine_weakening_refuse_without_witness,
    mass_affine_weakening_refuse_wrong_witness⟩

end UMST.Chem
