-- SPDX-FileCopyrightText: 2026 Santosh Prabhu Shenbagamoorthy and Santhosh Shyamsundar
-- SPDX-License-Identifier: MIT

import ChemConstants.NamedOccupancyExceptions
import ChemConstants.ActinideOccupancyExceptions
import ChemConstants.DBlockOccupancyExceptions

/-!
# OccupancyExceptionSetsDisjoint — pairwise disjoint Z-sets across occupancy exception families

Lean composition of existing ChemConstants occupancy-exception modules:

- `NamedOccupancyExceptions` (La / Ce / Gd / Pt / Au)
- `ActinideOccupancyExceptions` (Ac / Th / Pa / U / Np / Cm / Lr)
- `DBlockOccupancyExceptions` (Cr / Cu / Nb / Mo / Ru / Rh / Pd / Ag)

Pins:

- Pairwise disjoint atomic-number sets across the three finite families.
- Z = 94 (Pu) in none — Pu has no qlattice override.
- Z = 103 (Lr) in actinide set, not in named set.
- Modality Unwired; `physicsGreenAuthorized` = False.
- No meso / acting theorems. No new physics `axiom`. Not GREEN DFT.
-/

namespace UMST.Chem

/-- Design modality for occupancy exception set composition (TYPE-03 preview). -/
inductive OccupancyExceptionSetsModality where
  | unwired | assumed | proved | surrogate
  deriving DecidableEq, Repr

def occupancyExceptionSetsModalityCurrent : OccupancyExceptionSetsModality := .unwired

/-- Named occupancy exception Z-set (La / Ce / Gd / Pt / Au). -/
def namedOccupancyExceptionZSet : List Nat :=
  namedExceptionList.map fun ex => ex.z

/-- Actinide occupancy exception Z-set (Ac / Th / Pa / U / Np / Cm / Lr). -/
def actinideOccupancyExceptionZSet : List Nat :=
  actinideExceptionList.map fun ex => ex.z

/-- D-block occupancy exception Z-set (Cr / Cu / Nb / Mo / Ru / Rh / Pd / Ag). -/
def dBlockOccupancyExceptionZSet : List Nat :=
  dBlockExceptionList.map fun ex => ex.z

theorem named_occupancy_exception_z_set_five :
    namedOccupancyExceptionZSet.length = 5 := by native_decide

theorem actinide_occupancy_exception_z_set_seven :
    actinideOccupancyExceptionZSet.length = 7 := by native_decide

theorem d_block_occupancy_exception_z_set_eight :
    dBlockOccupancyExceptionZSet.length = 8 := by native_decide

/-- Named vs actinide Z pins never coincide (finite pairwise disjoint). -/
theorem named_actinide_exception_z_disjoint (n : NamedException) (a : ActinideException) :
    n.z ≠ a.z := by
  cases n <;> cases a <;> native_decide

/-- Named vs d-block Z pins never coincide (finite pairwise disjoint). -/
theorem named_d_block_exception_z_disjoint (n : NamedException) (d : DBlockException) :
    n.z ≠ d.z := by
  cases n <;> cases d <;> native_decide

/-- Actinide vs d-block Z pins never coincide (finite pairwise disjoint). -/
theorem actinide_d_block_exception_z_disjoint (a : ActinideException) (d : DBlockException) :
    a.z ≠ d.z := by
  cases a <;> cases d <;> native_decide

/-- All three occupancy exception Z-sets are pairwise disjoint at the pin level. -/
theorem occupancy_exception_z_sets_pairwise_disjoint :
    (∀ n : NamedException, ∀ a : ActinideException, n.z ≠ a.z) ∧
    (∀ n : NamedException, ∀ d : DBlockException, n.z ≠ d.z) ∧
    (∀ a : ActinideException, ∀ d : DBlockException, a.z ≠ d.z) :=
  ⟨named_actinide_exception_z_disjoint, named_d_block_exception_z_disjoint,
    actinide_d_block_exception_z_disjoint⟩

theorem z94_not_named_exception_z (ex : NamedException) : ex.z ≠ 94 := by
  cases ex <;> native_decide

theorem z94_not_actinide_exception_z (ex : ActinideException) : ex.z ≠ 94 := by
  cases ex <;> native_decide

theorem z94_not_d_block_exception_z (ex : DBlockException) : ex.z ≠ 94 := by
  cases ex <;> native_decide

/-- Z = 94 (Pu) is in no occupancy exception override set — Pu has no qlattice override. -/
theorem z94_not_in_any_occupancy_exception_set :
    (∀ ex : NamedException, ex.z ≠ 94) ∧
    (∀ ex : ActinideException, ex.z ≠ 94) ∧
    (∀ ex : DBlockException, ex.z ≠ 94) :=
  ⟨z94_not_named_exception_z, z94_not_actinide_exception_z, z94_not_d_block_exception_z⟩

theorem z103_in_actinide_occupancy_exception_set :
    ∃ ex : ActinideException, ex.z = 103 :=
  ⟨.Lr, actinide_exception_lr_z⟩

theorem z103_not_named_exception_z (ex : NamedException) : ex.z ≠ 103 := by
  cases ex <;> native_decide

/-- Z = 103 (Lr) is in actinide set, not in named set. -/
theorem z103_in_actinide_not_named :
    (∃ ex : ActinideException, ex.z = 103) ∧
    (∀ ex : NamedException, ex.z ≠ 103) :=
  ⟨z103_in_actinide_occupancy_exception_set, z103_not_named_exception_z⟩

/-- Cell id for the Lean occupancy exception set disjointness knowing-fiber. -/
def occupancyExceptionSetsDisjointCellId : String :=
  "CHEM-FORMAL-Q-LEAN-OCCUPANCY-EXCEPTION-SETS-DISJOINT"

/-- Non-claim fence — pairwise disjoint Z-sets Unwired ≠ Proved GREEN. -/
def occupancyExceptionSetsDisjointNonClaim : String :=
  "CHEM-FORMAL-Q-LEAN-OCCUPANCY-EXCEPTION-SETS-DISJOINT Lean composition of Named Actinide DBlock occupancy exception Z-sets pairwise disjoint; Z94 Pu not in any; Z103 Lr in actinide not named; cites sibling modules not second axiom; not GREEN DFT; not physics GREEN; not production_wired"

/-- Physics GREEN is unauthorized on the knowing occupancy exception set composition scaffold. -/
def occupancyExceptionSetsPhysicsGreenAuthorized : Prop := False

theorem occupancy_exception_sets_physics_green_false :
    ¬ occupancyExceptionSetsPhysicsGreenAuthorized := id

theorem occupancy_exception_sets_modality_unwired :
    occupancyExceptionSetsModalityCurrent = .unwired := rfl

theorem occupancy_exception_sets_cell_id :
    occupancyExceptionSetsDisjointCellId =
      "CHEM-FORMAL-Q-LEAN-OCCUPANCY-EXCEPTION-SETS-DISJOINT" := rfl

end UMST.Chem
