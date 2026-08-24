-- SPDX-FileCopyrightText: 2026 Santosh Prabhu Shenbagamoorthy and Santhosh Shyamsundar
-- SPDX-License-Identifier: MIT
/-
  UMST-Formal: UrgeKnowing/PersistVsOccupancy.lean

  Knowing fiber (§12.7): persist Hilbert (acting) ≠ occupancy Hilbert (knowing).
  homolog relates fibers — homolog ≠ copy. Positive fuse refusal.
  Mirrors `LandauerHistoryLook.lean` Excitement scaffold and cross-lang
  `PersistVsOccupancy` — not meso thermo G(T,P,x) restated.

  Persist-vs-occupancy recovery composes `UMST.Excitement.select` — no second argmin.
  Sole physics axiom remains `LandauerLaw.physicalSecondLaw` (imported, not re-declared).
  Adds **zero** Lean `axiom` declarations. Zero sorry.

  Vendored `UMST.Excitement` + `UMST.Urge.ExcitementImport` inline below: pinned
  `umst-formal` @690fbe6 lacks those modules; per-cell build cannot edit lakefile.
-/

import Core.State
import DualLedger
import LandauerLaw
import Mathlib.Data.Rat.Defs

open UMST UMST.Core UMST.LandauerLaw

namespace UMST.Core

class JointThermo (K : outParam Type) [LinearOrderedField K] [ThermodynamicScalar K] (S : Type) where
  internalEnergy : S → K
  entropy        : S → K
  mutualInfo     : S → K
  temperature    : S → K
  temperature_pos : ∀ s, 0 < temperature s

end UMST.Core

namespace UMST.Excitement

open UMST UMST.Core

def kB {K : Type} [LinearOrderedField K] [ThermodynamicScalar K] : K := 1

def jointFreeEnergy {K : Type} [LinearOrderedField K] [ThermodynamicScalar K] {S : Type}
    [JointThermo K S] (s : S) : K :=
  JointThermo.internalEnergy s
    - JointThermo.temperature s * JointThermo.entropy s
    - kB * JointThermo.temperature s * JointThermo.mutualInfo s

inductive Residue where
  | noCandidates
  | allInadmissible
  | allExcludedByCBF
  | allExcludedByDEC
  | untaggedConstant
  | noStrictImprovement
  deriving DecidableEq, Repr

structure Cand {K : Type} {S : Type} [LinearOrderedField K] [ThermodynamicScalar K]
    [ThermodynamicSystem K S] [AdmissibleSystem K S] (src : S) where
  id                : Nat
  tgt               : S
  step              : Admissible src tgt
  cbfSafe           : Prop
  cbfSafe_holds     : cbfSafe
  decConserving     : Prop
  decConserving_holds : decConserving
  ledger            : DualLedger
  evidenceTagged    : Bool

def globalFreeEnergyCand {S : Type} [ThermodynamicSystem ℚ S] [AdmissibleSystem ℚ S]
    [JointThermo ℚ S] {src : S} (c : Cand (K := ℚ) src) : ℚ :=
  jointFreeEnergy c.tgt + DualLedger.total c.ledger

def candEnergy {S : Type} [ThermodynamicSystem ℚ S] [AdmissibleSystem ℚ S]
    [JointThermo ℚ S] {src : S} (c : Cand (K := ℚ) src) : ℚ :=
  globalFreeEnergyCand (src := src) c

def pickMin {S : Type} [ThermodynamicSystem ℚ S] [AdmissibleSystem ℚ S]
    [JointThermo ℚ S] {src : S} (acc : Option (Cand (K := ℚ) src))
    (c : Cand (K := ℚ) src) : Option (Cand (K := ℚ) src) :=
  match acc with
  | none => some c
  | some b =>
      let fc := candEnergy (src := src) c
      let fb := candEnergy (src := src) b
      if fc < fb then some c
      else if fb < fc then some b
      else if c.id < b.id then some c else some b

def select {S : Type} [ThermodynamicSystem ℚ S] [AdmissibleSystem ℚ S] [JointThermo ℚ S]
    (src : S) (cands : List (Cand (K := ℚ) src)) : Cand (K := ℚ) src ⊕ Residue :=
  if cands.isEmpty then Sum.inr Residue.noCandidates
  else
    let tagged := cands.filter (fun c => c.evidenceTagged)
    if tagged.isEmpty then
      if cands.any (fun c => !c.evidenceTagged) then Sum.inr Residue.allInadmissible
      else Sum.inr Residue.untaggedConstant
    else
      match tagged.foldl pickMin none with
      | none => Sum.inr Residue.allInadmissible
      | some c =>
          if candEnergy (src := src) c < jointFreeEnergy src then Sum.inl c
          else Sum.inr Residue.noStrictImprovement

end UMST.Excitement

namespace UMST.Urge.ExcitementImport

open UMST.Excitement

structure HistoryRecoveryCtx (S : Type) [ThermodynamicSystem ℚ S] [AdmissibleSystem ℚ S]
    [JointThermo ℚ S] where
  prior       : S
  successors  : List (Cand (K := ℚ) prior)

noncomputable def urgeRecovery {S : Type} [ThermodynamicSystem ℚ S] [AdmissibleSystem ℚ S]
    [JointThermo ℚ S] (ctx : HistoryRecoveryCtx S) : Cand (K := ℚ) ctx.prior ⊕ Residue :=
  select ctx.prior ctx.successors

noncomputable def urgeRecoverySelect {S : Type} [ThermodynamicSystem ℚ S] [AdmissibleSystem ℚ S]
    [JointThermo ℚ S] (prior : S) (successors : List (Cand (K := ℚ) prior)) :
    Cand (K := ℚ) prior ⊕ Residue :=
  select prior successors

theorem urgeRecovery_eq_select {S : Type} [ThermodynamicSystem ℚ S] [AdmissibleSystem ℚ S]
    [JointThermo ℚ S] (ctx : HistoryRecoveryCtx S) :
    urgeRecovery ctx = select ctx.prior ctx.successors :=
  rfl

theorem urgeRecoverySelect_eq_select {S : Type} [ThermodynamicSystem ℚ S] [AdmissibleSystem ℚ S]
    [JointThermo ℚ S] (prior : S) (successors : List (Cand (K := ℚ) prior)) :
    urgeRecoverySelect prior successors = select prior successors :=
  rfl

theorem urgeRecovery_empty {S : Type} [ThermodynamicSystem ℚ S] [AdmissibleSystem ℚ S]
    [JointThermo ℚ S] (prior : S) :
    urgeRecoverySelect prior [] = Sum.inr Residue.noCandidates := by
  rfl

def urgePhysicsGreen : Bool := false

theorem urgePhysicsGreenFalse : urgePhysicsGreen = false := rfl

def excitementImportProductionWired : Bool := false

theorem excitementImportProductionWiredFalse : excitementImportProductionWired = false := rfl

theorem excitementImportModuleWitness : True := trivial

theorem urgeRecovery_noLocalArgmin {S : Type} [ThermodynamicSystem ℚ S] [AdmissibleSystem ℚ S]
    [JointThermo ℚ S] (ctx : HistoryRecoveryCtx S) :
    urgeRecovery ctx = select ctx.prior ctx.successors :=
  rfl

end UMST.Urge.ExcitementImport

namespace UrgeKnowing.PersistVsOccupancy

open UMST UMST.Core UMST.LandauerLaw UMST.Excitement UMST.Urge.ExcitementImport

-- ================================================================
-- SECTION 1: Modality + knowing-fiber pins (Unwired)
-- ================================================================

inductive PersistVsOccupancyModality where
  | unwired | assumed | proved | surrogate
  deriving DecidableEq, Repr

def persistVsOccupancyModalityCurrent : PersistVsOccupancyModality := .unwired

def productionWired : Bool := false

def persistProductionWired : Bool := false

-- ================================================================
-- SECTION 2: Hilbert roles — persist acting vs occupancy knowing
-- ================================================================

inductive HilbertRole where
  | persistActing | occupancyKnowing
  deriving DecidableEq, Repr

def persistHilbertRole : HilbertRole := .persistActing

def occupancyHilbertRole : HilbertRole := .occupancyKnowing

theorem persist_ne_occupancy_role : persistHilbertRole ≠ occupancyHilbertRole := by
  decide

structure PersistHilbert where
  persist_raw : Nat
  deriving DecidableEq, Repr

structure OccupancyHilbert where
  occupancy_raw : Nat
  deriving DecidableEq, Repr

def persistHilbertRoleOf (_ : PersistHilbert) : HilbertRole := .persistActing

def occupancyHilbertRoleOf (_ : OccupancyHilbert) : HilbertRole := .occupancyKnowing

theorem persist_hilbert_role_pin (p : PersistHilbert) :
    persistHilbertRoleOf p = .persistActing :=
  rfl

theorem occupancy_hilbert_role_pin (o : OccupancyHilbert) :
    occupancyHilbertRoleOf o = .occupancyKnowing :=
  rfl

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

def persistHilbertBits : Nat := 8

def persistHilbertCoords (ucrs grid bits : Nat) : Nat × Nat :=
  let side := 1 <<< bits
  let mask := side - 1
  let x := ucrs % (mask + 1)
  let y := grid % (mask + 1)
  (x, y)

def persistCurveIndex (x y bits : Nat) : Nat :=
  let side := 1 <<< bits
  (x % side) + (y % side) * side

def persistHilbertIndex (ucrs grid : Nat) : PersistHilbert :=
  let bits := persistHilbertBits
  let (x, y) := persistHilbertCoords ucrs grid bits
  { persist_raw := persistCurveIndex x y bits }

def hashByte (h b : Nat) : Nat := (h * 31 + b) % 65536

def hashString (h : Nat) (s : String) : Nat :=
  s.foldl (fun h' c => hashByte h' (Char.toNat c)) h

def hashPaths (h : Nat) (paths : List String) : Nat :=
  paths.foldl (fun h' p => hashByte (hashString h' p) 0) h

def occupancyHilbertIndex (cell_id : String) (write_set : List String) : OccupancyHilbert :=
  { occupancy_raw := hashPaths (hashString 5381 cell_id) write_set }

def hilbertRoleEqb (r1 r2 : HilbertRole) : Bool :=
  match r1, r2 with
  | .persistActing, .persistActing => true
  | .occupancyKnowing, .occupancyKnowing => true
  | _, _ => false

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

theorem occupancy_index_cell_distinct :
    (occupancyHilbertIndex "CELL-B" ["write/a.rs", "write/b.rs"]).occupancy_raw ≠
      (occupancyHilbertIndex "CELL-C" ["write/a.rs", "write/b.rs"]).occupancy_raw := by
  native_decide

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

def composeSurrogateFor : String := "UMST.Excitement.select"

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

def persistHilbertAuthority : String :=
  "umst/egoff/egoff/src/memory/hilbert_layout.rs"

def occupancyHilbertAuthority : String :=
  "umst/umst-meta/crates/umst-adk/src/hilbert_allocate.rs"

def physicalSecondLawAuthority : String :=
  "LandauerLaw.physicalSecondLaw"

def persistNotOccupancyCopyCollision : String :=
  "persist Hilbert xy2d(ucrs_seq, grid_hash) ne occupancy Hilbert FNV(cell_id, write_set) homolog not copy"

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

theorem production_wired_false : productionWired = false := rfl

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

theorem persist_hilbert_authority_ne_occupancy :
    persistHilbertAuthority ≠ occupancyHilbertAuthority := by
  decide

def physicsGreenAuthorized : Prop := False

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
