import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic

/-!
# UMSTCore (double-slit repository)

Minimal **ℝ-valued** classical layer so the quantum extension can compile standalone
without importing the full `umst-formal` `Gate.lean` (ℚ core). Intended for
`GateCompat`: map quantum / classical projections into these predicates.

Lineage: mirrors the *shape* of `UMST.Gate` admissibility and Landauer energy scale
from `LandauerEinsteinBridge` / `LandauerLaw`.
-/

open Real

namespace UMST.Core

-- ---------------------------------------------------------------------
-- SI and Landauer scale
-- ---------------------------------------------------------------------

/-- Boltzmann constant k_B (SI, exact definition). -/
noncomputable def kB : ℝ := (1380649 : ℝ) / (10 : ℝ) ^ 29

/-- Speed of light c (SI, exact). -/
noncomputable def cSI : ℝ := 299792458

lemma kB_pos : 0 < kB := by
  unfold kB
  positivity

lemma cSI_pos : 0 < cSI := by
  unfold cSI
  positivity

/-- Landauer bit energy at temperature `T` (joules per bit): `k_B T ln 2`. -/
noncomputable def landauerBitEnergy (T : ℝ) : ℝ :=
  kB * T * log 2

lemma landauerBitEnergy_nonneg {T : ℝ} (hT : 0 ≤ T) : 0 ≤ landauerBitEnergy T := by
  unfold landauerBitEnergy
  have hlog : 0 ≤ log 2 := le_of_lt (log_pos (by norm_num))
  exact mul_nonneg (mul_nonneg (le_of_lt kB_pos) hT) hlog

/-- Mass equivalent `E/c²` for a Landauer-scale energy `E`. -/
noncomputable def massEquivalentOfEnergy (E : ℝ) : ℝ :=
  E / (cSI ^ 2)

lemma massEquivalentOfEnergy_nonneg {E : ℝ} (hE : 0 ≤ E) : 0 ≤ massEquivalentOfEnergy E := by
  unfold massEquivalentOfEnergy
  have hc : 0 < cSI ^ 2 := by nlinarith [cSI_pos]
  exact div_nonneg hE (le_of_lt hc)

-- ---------------------------------------------------------------------
-- ℝ-valued thermodynamic state (operational view for composition with QM)
-- ---------------------------------------------------------------------

/-- One-step material state; real coefficients for compatibility with projections. -/
structure ThermodynamicState where
  density     : ℝ
  freeEnergy  : ℝ
  hydration   : ℝ
  strength    : ℝ

/-- Same tolerance as classical gate: 100 kg/m³. -/
noncomputable def δMass : ℝ := 100

noncomputable def Q_hyd : ℝ := 450

noncomputable def helmholtz (α : ℝ) : ℝ := -(Q_hyd * α)

/-- Four conjuncts aligned with `UMST.Gate.Admissible` (ℝ version). -/
def MassCond (old new : ThermodynamicState) : Prop :=
  |new.density - old.density| ≤ δMass

def DissipCond (old new : ThermodynamicState) : Prop :=
  new.freeEnergy ≤ old.freeEnergy

def HydratCond (old new : ThermodynamicState) : Prop :=
  old.hydration ≤ new.hydration

def StrengthCond (old new : ThermodynamicState) : Prop :=
  old.strength ≤ new.strength

def Admissible (old new : ThermodynamicState) : Prop :=
  MassCond old new ∧ DissipCond old new ∧ HydratCond old new ∧ StrengthCond old new

theorem admissibleRefl (s : ThermodynamicState) : Admissible s s := by
  constructor
  · simp [MassCond, δMass, sub_self, abs_zero]
  constructor
  · simp [DissipCond, le_refl]
  constructor
  · simp [HydratCond, le_refl]
  · simp [StrengthCond, le_refl]

theorem dissipCond_transitive (s₁ s₂ s₃ : ThermodynamicState) :
    DissipCond s₁ s₂ → DissipCond s₂ s₃ → DissipCond s₁ s₃ := fun h₁ h₂ => le_trans h₂ h₁

theorem hydratCond_transitive (s₁ s₂ s₃ : ThermodynamicState) :
    HydratCond s₁ s₂ → HydratCond s₂ s₃ → HydratCond s₁ s₃ := fun h₁ h₂ => le_trans h₁ h₂

theorem strengthCond_transitive (s₁ s₂ s₃ : ThermodynamicState) :
    StrengthCond s₁ s₂ → StrengthCond s₂ s₃ → StrengthCond s₁ s₃ := fun h₁ h₂ => le_trans h₁ h₂

end UMST.Core
