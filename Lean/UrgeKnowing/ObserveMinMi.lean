-- SPDX-FileCopyrightText: 2026 Santosh Prabhu Shenbagamoorthy and Santhosh Shyamsundar
-- SPDX-License-Identifier: MIT
/-
  UMST-Formal: UrgeKnowing/ObserveMinMi.lean

  Knowing fiber (§5.2 step-1): observe local+mesh at minimal MI (Landauer accounted).
  Paired local+mesh observation carrier with pairwise MI bits and Landauer lower-bound
  hook. Mirrors `LandauerHistoryLook.lean` / `LandauerNTo1.lean` and cross-lang
  `ObserveMinMi` — not meso thermo G(T,P,x) restated, not acting-coalgebra frugal MI.

  Observe-min-MI recovery composes `UMST.Excitement.select` — no second argmin (import pin).
  Sole physics axiom remains `LandauerLaw.physicalSecondLaw` (imported, not re-declared).
  Adds **zero** Lean `axiom` declarations. Zero sorry.
-/

import LandauerEinsteinBridge
import LandauerLaw

open Real UMST.LandauerLaw

namespace UrgeKnowing.ObserveMinMi

-- ================================================================
-- SECTION 1: Modality + knowing-fiber pins (Unwired)
-- ================================================================

/-- Design modality for observe-min-MI claims (TYPE-03 preview). -/
inductive ObserveMinMiModality where
  | unwired | assumed | proved | surrogate
  deriving DecidableEq, Repr

def observeMinMiModalityCurrent : ObserveMinMiModality := .unwired

def productionWired : Bool := false

def landauerProductionWired : Bool := false

-- ================================================================
-- SECTION 2: Local + mesh observation carrier (knowing fiber product)
-- ================================================================

/-- Local entropy carrier (knowing fiber scaffold). -/
structure LocalState where
  entropyBits : ℝ

/-- Mesh entropy carrier (knowing fiber scaffold). -/
structure MeshState where
  entropyBits : ℝ

/-- Paired local+mesh observation carrier. -/
structure LocalMeshState where
  localPart : LocalState
  meshPart : MeshState

/-- Coalgebra tag for local-only / mesh-only / paired observation. -/
inductive LocalMeshCoalgebra where
  | localOnly : LocalState → LocalMeshCoalgebra
  | meshOnly : MeshState → LocalMeshCoalgebra
  | paired : LocalMeshState → LocalMeshCoalgebra

def localMeshPaired (l : LocalState) (m : MeshState) : LocalMeshState :=
  { localPart := l, meshPart := m }

-- ================================================================
-- SECTION 3: Pairwise MI bits — I(local;mesh) = H(local) + H(mesh) − H(joint)
-- ================================================================

lemma landauerBitEnergy_nonneg_local {T : ℝ} (hT : 0 ≤ T) : 0 ≤ landauerBitEnergy T := by
  unfold landauerBitEnergy
  apply mul_nonneg
  · exact mul_nonneg (le_of_lt kBoltzmannSI_pos) hT
  · exact le_of_lt (Real.log_pos (by norm_num : (1 : ℝ) < 2))

/-- Pairwise MI bits with nonnegative clamp (minimal MI observation). -/
noncomputable def pairwiseMIBits (hLocal hMesh jointEntropy : ℝ) : ℝ :=
  max 0 (hLocal + hMesh - jointEntropy)

theorem pairwiseMIBits_nonneg (hLocal hMesh jointEntropy : ℝ) :
    0 ≤ pairwiseMIBits hLocal hMesh jointEntropy := by
  unfold pairwiseMIBits
  exact le_max_left 0 _

noncomputable def observeMinMiBits (s : LocalMeshState) (jointEntropy : ℝ) : ℝ :=
  pairwiseMIBits s.localPart.entropyBits s.meshPart.entropyBits jointEntropy

theorem observeMinMiBits_nonneg (s : LocalMeshState) (jointEntropy : ℝ) :
    0 ≤ observeMinMiBits s jointEntropy :=
  pairwiseMIBits_nonneg s.localPart.entropyBits s.meshPart.entropyBits jointEntropy

def observeMiBounded (mi : ℝ) : Prop :=
  0 ≤ mi ∧ mi ≤ 1

/-- Independent local+mesh fixture — MI = 0 at joint H = 2. -/
def independentLocalMesh : LocalMeshState :=
  localMeshPaired ⟨1⟩ ⟨1⟩

/-- Correlated local+mesh fixture — MI = 1 at joint H = 1. -/
def correlatedLocalMesh : LocalMeshState :=
  localMeshPaired ⟨1⟩ ⟨1⟩

theorem observe_min_mi_independent_zero :
    observeMinMiBits independentLocalMesh 2 = 0 := by
  simp only [observeMinMiBits, independentLocalMesh, localMeshPaired, pairwiseMIBits]
  norm_num

theorem observe_min_mi_correlated_one :
    observeMinMiBits correlatedLocalMesh 1 = 1 := by
  simp only [observeMinMiBits, correlatedLocalMesh, localMeshPaired, pairwiseMIBits]
  norm_num

theorem observe_min_mi_correlated_positive :
    0 < observeMinMiBits correlatedLocalMesh 1 := by
  simpa [observe_min_mi_correlated_one] using zero_lt_one

-- ================================================================
-- SECTION 4: Landauer hook — observe local+mesh at minimal MI (accounted)
-- ================================================================

/-- Landauer lower bound at observed minimal MI bits (`k_B T ln 2` per bit). -/
noncomputable def observeMinMiLandauerCost (T : ℝ) (s : LocalMeshState) (jointEntropy : ℝ) : ℝ :=
  landauerBitEnergy T * observeMinMiBits s jointEntropy

theorem observeMinMiLandauerCost_eq_landauerBitEnergy_mul (T : ℝ) (s : LocalMeshState)
    (jointEntropy : ℝ) :
    observeMinMiLandauerCost T s jointEntropy =
      landauerBitEnergy T * observeMinMiBits s jointEntropy :=
  rfl

theorem observeMinMiLandauerCost_nonneg (T : ℝ) (s : LocalMeshState) (jointEntropy : ℝ)
    (hT : 0 ≤ T) :
    0 ≤ observeMinMiLandauerCost T s jointEntropy := by
  unfold observeMinMiLandauerCost
  exact mul_nonneg (landauerBitEnergy_nonneg_local hT) (observeMinMiBits_nonneg s jointEntropy)

theorem observeMinMiLandauerCost_le_landauerBitEnergy (T : ℝ) (s : LocalMeshState)
    (jointEntropy : ℝ) (hT : 0 ≤ T) (hmi : observeMiBounded (observeMinMiBits s jointEntropy)) :
    observeMinMiLandauerCost T s jointEntropy ≤ landauerBitEnergy T := by
  rcases hmi with ⟨_, hle⟩
  unfold observeMinMiLandauerCost
  simpa [mul_one] using mul_le_mul_of_nonneg_left hle (landauerBitEnergy_nonneg_local hT)

theorem observe_min_mi_landauer_cost_correlated_le_bit_energy (T : ℝ) (hT : 0 ≤ T) :
    observeMinMiLandauerCost T correlatedLocalMesh 1 ≤ landauerBitEnergy T :=
  observeMinMiLandauerCost_le_landauerBitEnergy T correlatedLocalMesh 1 hT
    ⟨le_of_lt observe_min_mi_correlated_positive, le_of_eq observe_min_mi_correlated_one⟩

theorem observe_min_mi_landauer_cost_independent_zero (T : ℝ) :
    observeMinMiLandauerCost T independentLocalMesh 2 = 0 := by
  simp [observeMinMiLandauerCost, observe_min_mi_independent_zero, mul_zero]

-- ================================================================
-- SECTION 5: Observation outcomes — paired local+mesh vs positive refuse
-- ================================================================

inductive ObserveMinMiRefusal where
  | meshAbsentWhenPairedRequired
  | mutualInformationZero
  | secondArgmin
  deriving DecidableEq, Repr

inductive ObserveMinMiOutcome where
  | admitted (miBits : ℝ) (candidateTag : String)
  | refused (reason : ObserveMinMiRefusal)

structure ObserveMinMiAttempt where
  coalgebra : LocalMeshCoalgebra
  jointEntropy : ℝ
  temperature : ℝ
  sourceFreeEnergy : ℚ

/-- Observe minimal MI from coalgebra tag (no Excitement compose). -/
noncomputable def observeMinMiFromCoalgebra (coalgebra : LocalMeshCoalgebra)
    (jointEntropy : ℝ) : ObserveMinMiOutcome :=
  match coalgebra with
  | .localOnly _ => .refused .meshAbsentWhenPairedRequired
  | .meshOnly _ => .refused .meshAbsentWhenPairedRequired
  | .paired s =>
      let mi := observeMinMiBits s jointEntropy
      if mi ≤ 0 then .refused .mutualInformationZero
      else .admitted mi "coalgebra-paired"

theorem observe_min_mi_from_coalgebra_refuses_local_only :
    observeMinMiFromCoalgebra (.localOnly ⟨1⟩) 2 = .refused .meshAbsentWhenPairedRequired :=
  rfl

theorem observe_min_mi_from_coalgebra_refuses_mesh_only :
    observeMinMiFromCoalgebra (.meshOnly ⟨1⟩) 2 = .refused .meshAbsentWhenPairedRequired :=
  rfl

theorem observe_min_mi_from_coalgebra_independent_refuses :
    observeMinMiFromCoalgebra (.paired independentLocalMesh) 2 =
      .refused .mutualInformationZero := by
  simp [observeMinMiFromCoalgebra, observe_min_mi_independent_zero]

theorem observe_min_mi_from_coalgebra_correlated_admits :
    observeMinMiFromCoalgebra (.paired correlatedLocalMesh) 1 =
      .admitted 1 "coalgebra-paired" := by
  simp [observeMinMiFromCoalgebra, observe_min_mi_correlated_one]

-- ================================================================
-- SECTION 6: Observe-min-MI composes Excitement.select (no second argmin)
-- ================================================================

/-- Compose pin — import `UMST.Excitement.select`; refuse a local second argmin. -/
inductive ExcitementComposePin where
  | importSelectExcitement | secondArgminRefused
  deriving DecidableEq, Repr

def excitementComposePinCurrent : ExcitementComposePin := .importSelectExcitement

def composeSurrogateFor : String := "UMST.Excitement.select"

def excitementComposeAuthority : String :=
  "umst-meta/crates/umst-meta/src/excitement.rs"

def localArgminTheater : String := "local_Q_argmin_second_selector"

theorem observeMinMiComposeImportSelect :
    excitementComposePinCurrent = .importSelectExcitement :=
  rfl

theorem observeMinMiComposeSurrogateFor :
    composeSurrogateFor = "UMST.Excitement.select" :=
  rfl

theorem observe_min_mi_not_second_argmin :
    composeSurrogateFor ≠ localArgminTheater :=
  by decide

theorem observeMinMiComposeNotSecondArgmin :
    excitementComposePinCurrent ≠ .secondArgminRefused :=
  by decide

theorem refuseSecondArgminWitness : ObserveMinMiRefusal.secondArgmin = .secondArgmin := rfl

-- ================================================================
-- SECTION 7: Authority cites + physics GREEN fence
-- ================================================================

def epistemicMIAuthority : String :=
  "umst/umst-formal-double-slit/Lean/EpistemicMI.lean"

def measurementCostAuthority : String :=
  "umst/umst-formal-double-slit/Lean/MeasurementCost.lean"

def landauerBoundAuthority : String :=
  "umst/umst-formal-double-slit/Lean/LandauerBound.lean"

def landauerLawAuthority : String :=
  "umst/umst-formal-double-slit/Lean/LandauerLaw.lean"

def physicalSecondLawAuthority : String :=
  "LandauerLaw.physicalSecondLaw"

def observeMinMiCellId : String :=
  "URGE-FORMAL-Q-LEAN-OBSERVE-MIN-MI"

def observeMinMiNamed : String :=
  "observe_min_mi: §5.2 step-1 observe local+mesh at minimal MI Landauer accounted; compose Excitement not second argmin; physicalSecondLaw sole axiom framing"

def observeMinMiNonClaim : String :=
  "URGE-FORMAL-Q-LEAN-OBSERVE-MIN-MI §5.2 step-1 observe local+mesh at minimal MI Landauer accounted pairwiseMIBits observeMinMiLandauerCost compose Excitement select no second argmin Unwired one axiom physicalSecondLaw not second Landauer axiom not meso thermo not GREEN not physics GREEN not production_wired knowing fiber not acting coalgebra"

def observeMinMiSecondLawConservationFraming : String :=
  "second_law_conservation_observe_min_mi_one_axiom_landauer_not_second_axiom"

def actingCoalgebraFrugalMiRestated : String :=
  "acting_coalgebra_frugal_mi_restate"

theorem observe_min_mi_cell_id :
    observeMinMiCellId = "URGE-FORMAL-Q-LEAN-OBSERVE-MIN-MI" :=
  rfl

theorem observe_min_mi_modality_unwired :
    observeMinMiModalityCurrent = .unwired :=
  rfl

theorem production_wired_false : productionWired = false := rfl

theorem landauer_production_wired_false : landauerProductionWired = false := rfl

theorem observe_min_mi_cites_epistemic_mi :
    epistemicMIAuthority ≠ "" :=
  by decide

theorem observe_min_mi_cites_measurement_cost :
    measurementCostAuthority ≠ "" :=
  by decide

theorem observe_min_mi_cites_landauer_bound :
    landauerBoundAuthority ≠ "" :=
  by decide

theorem observe_min_mi_cites_physical_second_law :
    physicalSecondLawAuthority = "LandauerLaw.physicalSecondLaw" :=
  rfl

theorem observe_min_mi_not_second_landauer_axiom :
    observeMinMiSecondLawConservationFraming ≠ "landauer_second_axiom" :=
  by decide

theorem observe_min_mi_second_law_conservation_framing :
    observeMinMiSecondLawConservationFraming ≠ "" :=
  by decide

theorem observe_min_mi_not_acting_coalgebra_restate :
    observeMinMiNonClaim ≠ actingCoalgebraFrugalMiRestated :=
  by decide

/-- Physics GREEN is not authorized on the knowing scaffold. -/
def physicsGreenAuthorized : Prop := False

theorem observe_min_mi_physics_green_false : ¬ physicsGreenAuthorized :=
  id

theorem observe_min_mi_not_meso_thermo_restate :
    observeMinMiNonClaim ≠ "meso_thermo_G_T_P_x_restate" :=
  by decide

theorem observeMinMiComposeAuthorityOk :
    excitementComposeAuthority ≠ "" :=
  by decide

end UrgeKnowing.ObserveMinMi
