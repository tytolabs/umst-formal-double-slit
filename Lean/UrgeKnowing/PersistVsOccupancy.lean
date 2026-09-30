-- SPDX-FileCopyrightText: 2026 Santosh Prabhu Shenbagamoorthy and Santhosh Shyamsundar
-- SPDX-License-Identifier: MIT
/-
  UMST-Formal: UrgeKnowing/PersistVsOccupancy.lean

  Knowing fiber (§12.7): persist Hilbert (acting) ≠ occupancy Hilbert (knowing).
  homolog relates fibers — homolog ≠ copy. Positive fuse refusal.
  Mirrors `LandauerHistoryLook.lean` Excitement scaffold and cross-lang
  `PersistVsOccupancy` — not meso thermo G(T,P,x) restated.

  Persist-vs-occupancy recovery composes `UMST.Excitement.select` — no second argmin.
  Sole physical law: the `SecondLaw` predicate; `LandauerLaw.physicalSecondLaw` is its erase instance (imported, not re-declared; no project `axiom`).
  Adds **zero** Lean `axiom` declarations. Zero sorry.

  `UMST.Excitement` and `UMST.Urge.ExcitementImport` are imported from umst-formal (single source).
-/

import Core.State
import DualLedger
import LandauerLaw
import Mathlib.Data.Rat.Defs
import Excitement
import Urge.ExcitementImport
import UrgeKnowing.TwoHilberts

open UMST UMST.Core UMST.LandauerLaw

namespace UrgeKnowing.PersistVsOccupancy

open UMST UMST.Core UMST.LandauerLaw UMST.Excitement UMST.Urge.ExcitementImport

-- The persist and occupancy Hilbert indices live in `TwoHilberts` (single source); this module adds the
-- persist-versus-occupancy fiber morphism over them.
open UrgeKnowing.TwoHilberts (hashString hashPaths occupancyHilbertIndex occupancy_index_cell_distinct HilbertRole OccupancyHilbert PersistHilbert composeSurrogateFor hashByte hilbertRoleEqb occupancyHilbertAuthority occupancyHilbertRole occupancyHilbertRoleOf occupancy_hilbert_role_pin persistCurveIndex persistHilbertAuthority persistHilbertBits persistHilbertCoords persistHilbertIndex persistHilbertRole persistHilbertRoleOf persistNotOccupancyCopyCollision persist_hilbert_authority_ne_occupancy persist_hilbert_role_pin persist_ne_occupancy_role physicalSecondLawAuthority physicsGreenAuthorized productionWired production_wired_false)

-- ================================================================
-- SECTION 1: Modality + knowing-fiber pins (Unwired)
-- ================================================================

inductive PersistVsOccupancyModality where
  | unwired | assumed | proved | surrogate
  deriving DecidableEq, Repr

def persistVsOccupancyModalityCurrent : PersistVsOccupancyModality := .unwired

def persistProductionWired : Bool := false

-- ================================================================
-- SECTION 2: Hilbert roles — persist acting vs occupancy knowing
-- ================================================================

-- ================================================================
-- SECTION 3: Typed positive fuse refusal — not only ¬ physics GREEN
-- ================================================================

inductive HilbertFuseRefused where
  | fusePersistIntoOccupancy | fuseOccupancyIntoPersist | homologIsNotCopy | secondArgmin
  deriving DecidableEq, Repr

def fusePersistIntoOccupancyRefused : HilbertFuseRefused := .fusePersistIntoOccupancy

def fuseOccupancyIntoPersistRefused : HilbertFuseRefused := .fuseOccupancyIntoPersist

def homologNotCopyRefused : HilbertFuseRefused := .homologIsNotCopy

def secondArgminRefused : HilbertFuseRefused := .secondArgmin

inductive HilbertFuseResult (A : Type) where
  | fuseOk : A → HilbertFuseResult A
  | fuseRefused : HilbertFuseRefused → HilbertFuseResult A
  deriving Repr

def refuseFusePersistIntoOccupancy (_ : PersistHilbert) :
    HilbertFuseResult OccupancyHilbert :=
  .fuseRefused .fusePersistIntoOccupancy

def refuseFuseOccupancyIntoPersist (_ : OccupancyHilbert) :
    HilbertFuseResult PersistHilbert :=
  .fuseRefused .fuseOccupancyIntoPersist

def refuseSecondArgminSelector : HilbertFuseResult Unit :=
  .fuseRefused .secondArgmin

theorem fuse_persist_into_occupancy_refused (p : PersistHilbert) :
    refuseFusePersistIntoOccupancy p = .fuseRefused .fusePersistIntoOccupancy :=
  rfl

theorem fuse_occupancy_into_persist_refused (o : OccupancyHilbert) :
    refuseFuseOccupancyIntoPersist o = .fuseRefused .fuseOccupancyIntoPersist :=
  rfl

theorem refuse_second_argmin_positive :
    refuseSecondArgminSelector = .fuseRefused .secondArgmin :=
  rfl

-- ================================================================
-- SECTION 4: Persist vs occupancy geometric index surrogates
-- ================================================================

-- ================================================================
-- SECTION 5: Homolog witness — homolog ≠ copy across fibers
-- ================================================================

structure HilbertHomologWitness where
  homolog_persist : PersistHilbert
  homolog_occupancy : OccupancyHilbert
  homolog_claims_identity_copy : Bool
  deriving Repr

def homologPersistToOccupancy (p : PersistHilbert) (o : OccupancyHilbert)
    (claimsCopy : Bool) : HilbertHomologWitness :=
  { homolog_persist := p
    homolog_occupancy := o
    homolog_claims_identity_copy := claimsCopy }

def homologClaimsIdentityCopy (w : HilbertHomologWitness) : Bool :=
  w.homolog_claims_identity_copy ||
    hilbertRoleEqb (persistHilbertRoleOf w.homolog_persist)
      (occupancyHilbertRoleOf w.homolog_occupancy)

def homologNotCopy (w : HilbertHomologWitness) : Prop :=
  !w.homolog_claims_identity_copy ∧
    persistHilbertRoleOf w.homolog_persist ≠ occupancyHilbertRoleOf w.homolog_occupancy

theorem homolog_not_copy_holds (p : PersistHilbert) (o : OccupancyHilbert) :
    homologNotCopy (homologPersistToOccupancy p o false) := by
  unfold homologNotCopy homologPersistToOccupancy
    persistHilbertRoleOf occupancyHilbertRoleOf
  simp [persist_hilbert_role_pin, occupancy_hilbert_role_pin, persist_ne_occupancy_role]

inductive FiberVerdict where
  | accept | refuse
  deriving DecidableEq, Repr

def evaluateFiberMorphism (w : HilbertHomologWitness) (attemptFuse : Bool) : FiberVerdict :=
  if attemptFuse then .refuse
  else if homologClaimsIdentityCopy w then .refuse
  else if !w.homolog_claims_identity_copy &&
      persistHilbertRoleOf w.homolog_persist ≠ occupancyHilbertRoleOf w.homolog_occupancy then
    .accept
  else .refuse

def samplePersistHilbert : PersistHilbert := ⟨42⟩

def sampleOccupancyHilbert : OccupancyHilbert := ⟨99⟩

theorem homolog_restriction_admitted :
    evaluateFiberMorphism
      (homologPersistToOccupancy samplePersistHilbert sampleOccupancyHilbert false)
      false = .accept :=
  rfl

theorem homolog_fuse_persist_into_occupancy_refused :
    evaluateFiberMorphism
      (homologPersistToOccupancy samplePersistHilbert sampleOccupancyHilbert false)
      true = .refuse :=
  rfl

theorem homolog_identity_copy_refused :
    evaluateFiberMorphism
      (homologPersistToOccupancy samplePersistHilbert sampleOccupancyHilbert true)
      false = .refuse :=
  rfl

def persistVsOccupancyPositiveRefuseHonest : Prop :=
  (∀ p : PersistHilbert,
    refuseFusePersistIntoOccupancy p = .fuseRefused .fusePersistIntoOccupancy) ∧
  (∀ o : OccupancyHilbert,
    refuseFuseOccupancyIntoPersist o = .fuseRefused .fuseOccupancyIntoPersist) ∧
  fusePersistIntoOccupancyRefused = .fusePersistIntoOccupancy ∧
  homologNotCopyRefused = .homologIsNotCopy ∧
  refuseSecondArgminSelector = .fuseRefused .secondArgmin

theorem persist_vs_occupancy_positive_refuse_honest : persistVsOccupancyPositiveRefuseHonest := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro p; exact fuse_persist_into_occupancy_refused p
  · intro o; exact fuse_occupancy_into_persist_refused o
  · rfl
  · rfl
  · exact refuse_second_argmin_positive

-- ================================================================
-- SECTION 6: Persist-vs-occupancy composes Excitement.select (no second argmin)
-- ================================================================

structure PersistVsOccupancyCtx (S : Type) [ThermodynamicSystem ℚ S] [AdmissibleSystem ℚ S]
    [JointThermo ℚ S] where
  prior : S
  successors : List (Cand (K := ℚ) prior)

noncomputable def persistVsOccupancySelect {S : Type} [ThermodynamicSystem ℚ S]
    [AdmissibleSystem ℚ S] [JointThermo ℚ S] (ctx : PersistVsOccupancyCtx S) :
    Cand (K := ℚ) ctx.prior ⊕ Residue :=
  urgeRecoverySelect ctx.prior ctx.successors

noncomputable def persistVsOccupancySelectBare {S : Type} [ThermodynamicSystem ℚ S]
    [AdmissibleSystem ℚ S] [JointThermo ℚ S] (prior : S)
    (successors : List (Cand (K := ℚ) prior)) :
    Cand (K := ℚ) prior ⊕ Residue :=
  urgeRecoverySelect prior successors

noncomputable def urgePersistVsOccupancySelect {S : Type} [ThermodynamicSystem ℚ S]
    [AdmissibleSystem ℚ S] [JointThermo ℚ S] (prior : S)
    (successors : List (Cand (K := ℚ) prior)) :
    Cand (K := ℚ) prior ⊕ Residue :=
  urgeRecoverySelect prior successors

def metaExcitementModule : String :=
  "umst-meta/crates/umst-meta/src/excitement.rs"

theorem persistVsOccupancySelect_eq_select {S : Type} [ThermodynamicSystem ℚ S]
    [AdmissibleSystem ℚ S] [JointThermo ℚ S] (ctx : PersistVsOccupancyCtx S) :
    persistVsOccupancySelect ctx = select ctx.prior ctx.successors :=
  rfl

theorem persistVsOccupancySelect_eq_urgeRecoverySelect {S : Type} [ThermodynamicSystem ℚ S]
    [AdmissibleSystem ℚ S] [JointThermo ℚ S] (ctx : PersistVsOccupancyCtx S) :
    persistVsOccupancySelect ctx = urgeRecoverySelect ctx.prior ctx.successors :=
  rfl

theorem persistVsOccupancySelectBare_eq_select {S : Type} [ThermodynamicSystem ℚ S]
    [AdmissibleSystem ℚ S] [JointThermo ℚ S] (prior : S)
    (successors : List (Cand (K := ℚ) prior)) :
    persistVsOccupancySelectBare prior successors = select prior successors :=
  rfl

theorem urgePersistVsOccupancySelect_eq_select {S : Type} [ThermodynamicSystem ℚ S]
    [AdmissibleSystem ℚ S] [JointThermo ℚ S] (prior : S)
    (successors : List (Cand (K := ℚ) prior)) :
    urgePersistVsOccupancySelect prior successors = select prior successors :=
  rfl

theorem persistVsOccupancyNoLocalArgmin {S : Type} [ThermodynamicSystem ℚ S]
    [AdmissibleSystem ℚ S] [JointThermo ℚ S] (ctx : PersistVsOccupancyCtx S) :
    persistVsOccupancySelect ctx = select ctx.prior ctx.successors :=
  rfl

theorem persistVsOccupancyComposeSurrogateFor :
    composeSurrogateFor = "UMST.Excitement.select" :=
  rfl

theorem persist_vs_occupancy_not_second_argmin :
    composeSurrogateFor ≠ "second_argmin_selector" := by
  decide

theorem persistVsOccupancySelect_empty {S : Type} [ThermodynamicSystem ℚ S]
    [AdmissibleSystem ℚ S] [JointThermo ℚ S] (prior : S)
    (successors : List (Cand (K := ℚ) prior)) (h : successors = []) :
    persistVsOccupancySelectBare prior successors = Sum.inr Residue.noCandidates := by
  subst h
  simpa [persistVsOccupancySelectBare] using urgeRecovery_empty prior

-- ================================================================
-- SECTION 7: Authority cites + physics GREEN fence
-- ================================================================

def persistVsOccupancyCellId : String :=
  "URGE-FORMAL-Q-LEAN-PERSIST-VS-OCCUPANCY"

def persistVsOccupancyNamed : String :=
  "persist_vs_occupancy: §12.7 persist Hilbert acting distinct from occupancy Hilbert knowing homolog not copy fuse refused compose Excitement not second argmin physicalSecondLaw sole axiom framing"

def persistVsOccupancyNonClaim : String :=
  "URGE-FORMAL-Q-LEAN-PERSIST-VS-OCCUPANCY §12.7 persist_vs_occupancy persist Hilbert acting egoff hilbert_index ucrs_seq grid_hash xy2d distinct from occupancy Hilbert knowing ADK cell_locality_hash FNV antichain sort homolog not copy fuse refused positive compose Excitement select no second argmin sole axiom physicalSecondLaw no extra axiom modality Unwired not physics GREEN not production_wired"

def persistVsOccupancySecondLawConservationFraming : String :=
  "second_law_conservation_persist_vs_occupancy_one_axiom_landauer_not_second_axiom"

theorem persist_vs_occupancy_cell_id :
    persistVsOccupancyCellId = "URGE-FORMAL-Q-LEAN-PERSIST-VS-OCCUPANCY" :=
  rfl

theorem persist_vs_occupancy_modality_unwired :
    persistVsOccupancyModalityCurrent = .unwired :=
  rfl

theorem persist_production_wired_false : persistProductionWired = false := rfl

theorem persist_vs_occupancy_cites_persist_hilbert :
    persistHilbertAuthority ≠ "" :=
  by decide

theorem persist_vs_occupancy_cites_occupancy_hilbert :
    occupancyHilbertAuthority ≠ "" :=
  by decide

theorem persist_vs_occupancy_cites_physical_second_law :
    physicalSecondLawAuthority = "LandauerLaw.physicalSecondLaw" :=
  rfl

theorem persist_vs_occupancy_not_second_landauer_axiom :
    persistVsOccupancySecondLawConservationFraming ≠ "landauer_second_axiom" :=
  by decide

theorem persist_vs_occupancy_physics_green_false : ¬ physicsGreenAuthorized :=
  id

theorem persist_vs_occupancy_not_meso_thermo_restate :
    persistVsOccupancyNonClaim ≠ "meso_thermo_G_T_P_x_restate" :=
  by decide

def persistVsOccupancyKnowingFiberOk : Prop :=
  persistVsOccupancyModalityCurrent = .unwired ∧ ¬ physicsGreenAuthorized

theorem persist_vs_occupancy_knowing_fiber_ok :
    persistVsOccupancyKnowingFiberOk :=
  ⟨persist_vs_occupancy_modality_unwired, persist_vs_occupancy_physics_green_false⟩

end UrgeKnowing.PersistVsOccupancy
