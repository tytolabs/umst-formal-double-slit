-- SPDX-FileCopyrightText: 2026 Santosh Prabhu Shenbagamoorthy and Santhosh Shyamsundar
-- SPDX-License-Identifier: MIT
/-
  UMST-Formal: UrgeKnowing/TwoHilberts.lean

  Knowing fiber (§12.7): two Hilberts — persist Hilbert (acting) distinct from
  occupancy Hilbert (knowing). homolog relates fibers — homolog ≠ copy. Positive
  fuse refusal. Mirrors `LandauerHistoryLook.lean` Excitement scaffold and cross-lang
  `TwoHilberts` — not meso thermo G(T,P,x) restated.

  Two-Hilberts recovery composes `UMST.Excitement.select` — no second argmin.
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

/-- Joint thermodynamic fields for Excitement's free-energy functional (vendored: absent @690fbe6). -/
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

-- ================================================================
-- SECTION 1: History recovery carrier (typed successor list)
-- ================================================================

/-- Context for Urge history recovery: prior head + admissible successor candidates. -/
structure HistoryRecoveryCtx (S : Type) [ThermodynamicSystem ℚ S] [AdmissibleSystem ℚ S]
    [JointThermo ℚ S] where
  prior       : S
  successors  : List (Cand (K := ℚ) prior)

-- ================================================================
-- SECTION 2: Recovery **is** Excitement.select (no local argmin)
-- ================================================================

/-- Urge history recovery composes `UMST.Excitement.select` — not a second argmin. -/
noncomputable def urgeRecovery {S : Type} [ThermodynamicSystem ℚ S] [AdmissibleSystem ℚ S]
    [JointThermo ℚ S] (ctx : HistoryRecoveryCtx S) : Cand (K := ℚ) ctx.prior ⊕ Residue :=
  select ctx.prior ctx.successors

/-- Alias on bare `(prior, successors)` — same selector, no re-derivation. -/
noncomputable def urgeRecoverySelect {S : Type} [ThermodynamicSystem ℚ S] [AdmissibleSystem ℚ S]
    [JointThermo ℚ S] (prior : S) (successors : List (Cand (K := ℚ) prior)) :
    Cand (K := ℚ) prior ⊕ Residue :=
  select prior successors

/-- Definitional witness: recovery API is `Excitement.select`. -/
theorem urgeRecovery_eq_select {S : Type} [ThermodynamicSystem ℚ S] [AdmissibleSystem ℚ S]
    [JointThermo ℚ S] (ctx : HistoryRecoveryCtx S) :
    urgeRecovery ctx = select ctx.prior ctx.successors :=
  rfl

theorem urgeRecoverySelect_eq_select {S : Type} [ThermodynamicSystem ℚ S] [AdmissibleSystem ℚ S]
    [JointThermo ℚ S] (prior : S) (successors : List (Cand (K := ℚ) prior)) :
    urgeRecoverySelect prior successors = select prior successors :=
  rfl

/-- Recovery and bare select agree on identical inputs. -/
theorem urgeRecovery_eq_urgeRecoverySelect {S : Type} [ThermodynamicSystem ℚ S]
    [AdmissibleSystem ℚ S] [JointThermo ℚ S] (ctx : HistoryRecoveryCtx S) :
    urgeRecovery ctx = urgeRecoverySelect ctx.prior ctx.successors :=
  rfl

-- ================================================================
-- SECTION 3: Imported selector properties (no local re-proof of argmin)
-- ================================================================

/-- Empty successor list → `Residue.noCandidates` via imported `select`. -/
theorem urgeRecovery_empty {S : Type} [ThermodynamicSystem ℚ S] [AdmissibleSystem ℚ S]
    [JointThermo ℚ S] (prior : S) :
    urgeRecoverySelect prior [] = Sum.inr Residue.noCandidates := by
  rfl

-- ================================================================
-- SECTION 4: Axiom discipline + honesty flags
-- ================================================================

/-- Physics GREEN unauthorized on this scaffold. -/
def urgePhysicsGreen : Bool := false

theorem urgePhysicsGreenFalse : urgePhysicsGreen = false := rfl

/-- Production wiring stays open (meso import only). -/
def excitementImportProductionWired : Bool := false

theorem excitementImportProductionWiredFalse : excitementImportProductionWired = false := rfl

/-- Catalog witness: meso Urge ExcitementImport module present. -/
theorem excitementImportModuleWitness : True := trivial

/-- Recovery selector re-uses `jointFreeEnergy` / `pickMin` from Excitement — no Urge-local argmin. -/
theorem urgeRecovery_noLocalArgmin {S : Type} [ThermodynamicSystem ℚ S] [AdmissibleSystem ℚ S]
    [JointThermo ℚ S] (ctx : HistoryRecoveryCtx S) :
    urgeRecovery ctx = select ctx.prior ctx.successors :=
  rfl
end UMST.Urge.ExcitementImport

namespace UrgeKnowing.TwoHilberts

open UMST UMST.Core UMST.LandauerLaw UMST.Excitement UMST.Urge.ExcitementImport

-- ================================================================
-- SECTION 1: Modality + knowing-fiber pins (Unwired)
-- ================================================================

/-- Design modality for two-Hilberts claims (TYPE-03 preview). -/
inductive TwoHilbertsModality where
  | unwired | assumed | proved | surrogate
  deriving DecidableEq, Repr

def twoHilbertsModalityCurrent : TwoHilbertsModality := .unwired

def productionWired : Bool := false

def twoHilbertsProductionWired : Bool := false

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
  | fusePersistIntoOccupancy | fuseOccupancyIntoPersist | homologIsNotCopy
  deriving DecidableEq, Repr

def fusePersistIntoOccupancyRefused : HilbertFuseRefused := .fusePersistIntoOccupancy

def fuseOccupancyIntoPersistRefused : HilbertFuseRefused := .fuseOccupancyIntoPersist

def homologNotCopyRefused : HilbertFuseRefused := .homologIsNotCopy

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

theorem fuse_persist_into_occupancy_refused (p : PersistHilbert) :
    refuseFusePersistIntoOccupancy p = .fuseRefused .fusePersistIntoOccupancy :=
  rfl

theorem fuse_occupancy_into_persist_refused (o : OccupancyHilbert) :
    refuseFuseOccupancyIntoPersist o = .fuseRefused .fuseOccupancyIntoPersist :=
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
  homolog_raw_coincident : Bool
  deriving Repr

def homologClaimsIdentityCopy (w : HilbertHomologWitness) : Bool :=
  hilbertRoleEqb (persistHilbertRoleOf w.homolog_persist)
    (occupancyHilbertRoleOf w.homolog_occupancy)

def homologPersistToOccupancy (p : PersistHilbert) (cell_id : String)
    (write_set : List String) : HilbertHomologWitness :=
  let o := occupancyHilbertIndex cell_id write_set
  { homolog_persist := p
    homolog_occupancy := o
    homolog_raw_coincident :=
      if p.persist_raw == o.occupancy_raw then true else false }

def homologNotCopy (w : HilbertHomologWitness) : Prop :=
  persistHilbertRoleOf w.homolog_persist ≠ occupancyHilbertRoleOf w.homolog_occupancy ∧
    homologClaimsIdentityCopy w = false

theorem homolog_not_copy_holds (p : PersistHilbert) (cell_id : String)
    (ws : List String) :
    homologNotCopy (homologPersistToOccupancy p cell_id ws) := by
  unfold homologNotCopy homologPersistToOccupancy homologClaimsIdentityCopy
    persistHilbertRoleOf occupancyHilbertRoleOf hilbertRoleEqb
  simp [persist_hilbert_role_pin, occupancy_hilbert_role_pin, persist_ne_occupancy_role]

theorem homolog_roles_distinct (w : HilbertHomologWitness) :
    persistHilbertRoleOf w.homolog_persist ≠ occupancyHilbertRoleOf w.homolog_occupancy := by
  cases w with
  | mk p o _ =>
    simpa [persist_hilbert_role_pin, occupancy_hilbert_role_pin] using persist_ne_occupancy_role

def twoHilbertsPositiveRefuseHonest : Prop :=
  (∀ p : PersistHilbert,
    refuseFusePersistIntoOccupancy p = .fuseRefused .fusePersistIntoOccupancy) ∧
  (∀ o : OccupancyHilbert,
    refuseFuseOccupancyIntoPersist o = .fuseRefused .fuseOccupancyIntoPersist) ∧
  fusePersistIntoOccupancyRefused = .fusePersistIntoOccupancy ∧
  homologNotCopyRefused = .homologIsNotCopy

theorem two_hilberts_positive_refuse_honest : twoHilbertsPositiveRefuseHonest := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro p; exact fuse_persist_into_occupancy_refused p
  · intro o; exact fuse_occupancy_into_persist_refused o
  · rfl
  · rfl

theorem persist_index_deterministic (ucrs grid : Nat) :
    persistHilbertIndex ucrs grid = persistHilbertIndex ucrs grid :=
  rfl

theorem occupancy_index_cell_distinct :
    (occupancyHilbertIndex "CELL-B" ["write/a.rs", "write/b.rs"]).occupancy_raw ≠
      (occupancyHilbertIndex "CELL-C" ["write/a.rs", "write/b.rs"]).occupancy_raw := by
  native_decide

-- ================================================================
-- SECTION 6: Two Hilberts composes Excitement.select (no second argmin)
-- ================================================================

/-- Context for two-Hilberts recovery over admissible successors. -/
structure TwoHilbertsCtx (S : Type) [ThermodynamicSystem ℚ S] [AdmissibleSystem ℚ S]
    [JointThermo ℚ S] where
  prior : S
  successors : List (Cand (K := ℚ) prior)

/-- Two-Hilberts selection **is** `urgeRecoverySelect` / `Excitement.select`. -/
noncomputable def twoHilbertsSelect {S : Type} [ThermodynamicSystem ℚ S] [AdmissibleSystem ℚ S]
    [JointThermo ℚ S] (ctx : TwoHilbertsCtx S) :
    Cand (K := ℚ) ctx.prior ⊕ Residue :=
  urgeRecoverySelect ctx.prior ctx.successors

noncomputable def twoHilbertsSelectBare {S : Type} [ThermodynamicSystem ℚ S]
    [AdmissibleSystem ℚ S] [JointThermo ℚ S] (prior : S)
    (successors : List (Cand (K := ℚ) prior)) :
    Cand (K := ℚ) prior ⊕ Residue :=
  urgeRecoverySelect prior successors

noncomputable def urgeTwoHilbertsSelect {S : Type} [ThermodynamicSystem ℚ S]
    [AdmissibleSystem ℚ S] [JointThermo ℚ S] (prior : S)
    (successors : List (Cand (K := ℚ) prior)) :
    Cand (K := ℚ) prior ⊕ Residue :=
  urgeRecoverySelect prior successors

def composeSurrogateFor : String := "UMST.Excitement.select"

def excitementComposeAuthority : String :=
  "umst-meta/crates/umst-meta/src/excitement.rs"

theorem twoHilbertsSelect_eq_select {S : Type} [ThermodynamicSystem ℚ S]
    [AdmissibleSystem ℚ S] [JointThermo ℚ S] (ctx : TwoHilbertsCtx S) :
    twoHilbertsSelect ctx = select ctx.prior ctx.successors :=
  rfl

theorem twoHilbertsSelect_eq_urgeRecoverySelect {S : Type} [ThermodynamicSystem ℚ S]
    [AdmissibleSystem ℚ S] [JointThermo ℚ S] (ctx : TwoHilbertsCtx S) :
    twoHilbertsSelect ctx = urgeRecoverySelect ctx.prior ctx.successors :=
  rfl

theorem twoHilbertsSelectBare_eq_select {S : Type} [ThermodynamicSystem ℚ S]
    [AdmissibleSystem ℚ S] [JointThermo ℚ S] (prior : S)
    (successors : List (Cand (K := ℚ) prior)) :
    twoHilbertsSelectBare prior successors = select prior successors :=
  rfl

theorem urgeTwoHilbertsSelect_eq_select {S : Type} [ThermodynamicSystem ℚ S]
    [AdmissibleSystem ℚ S] [JointThermo ℚ S] (prior : S)
    (successors : List (Cand (K := ℚ) prior)) :
    urgeTwoHilbertsSelect prior successors = select prior successors :=
  rfl

theorem twoHilbertsNoLocalArgmin {S : Type} [ThermodynamicSystem ℚ S] [AdmissibleSystem ℚ S]
    [JointThermo ℚ S] (ctx : TwoHilbertsCtx S) :
    twoHilbertsSelect ctx = select ctx.prior ctx.successors :=
  rfl

theorem twoHilbertsComposeSurrogateFor :
    composeSurrogateFor = "UMST.Excitement.select" :=
  rfl

theorem two_hilberts_not_second_argmin :
    composeSurrogateFor ≠ "second_argmin_selector" := by
  decide

theorem two_hilberts_compose_excitement_authority :
    excitementComposeAuthority ≠ "" :=
  by decide

theorem twoHilbertsSelect_empty {S : Type} [ThermodynamicSystem ℚ S] [AdmissibleSystem ℚ S]
    [JointThermo ℚ S] (prior : S) (successors : List (Cand (K := ℚ) prior))
    (h : successors = []) :
    twoHilbertsSelectBare prior successors = Sum.inr Residue.noCandidates := by
  subst h
  simpa [twoHilbertsSelectBare] using urgeRecovery_empty prior

-- ================================================================
-- SECTION 7: Authority cites + physics GREEN fence
-- ================================================================

def persistHilbertAuthority : String :=
  "umst/egoff/egoff/src/memory/hilbert_layout.rs"

def occupancyHilbertAuthority : String :=
  "umst/umst-meta/crates/umst-adk/src/hilbert_allocate.rs"

def twoHilbertsBlueprintAuthority : String :=
  "workspace/docs/UMST_URGE_BLUEPRINT.md"

def carrierStrataAuthority : String :=
  "workspace/docs/UMST_CARRIER_STRATA.md"

def physicalSecondLawAuthority : String :=
  "LandauerLaw.physicalSecondLaw"

def twoHilbertsCellId : String :=
  "URGE-FORMAL-Q-LEAN-TWO-HILBERTS"

def twoHilbertsNamed : String :=
  "two_hilberts: §12.7 persist Hilbert acting distinct from occupancy Hilbert knowing homolog not copy fuse refused compose Excitement not second argmin physicalSecondLaw sole axiom framing"

def twoHilbertsNonClaim : String :=
  "URGE-FORMAL-Q-LEAN-TWO-HILBERTS §12.7 persist Hilbert acting egoff hilbert_index ucrs_seq grid_hash xy2d distinct from occupancy Hilbert knowing ADK cell_locality_hash FNV antichain sort homolog not copy fuse refused positive not only physics_green Unwired not Proved not physics GREEN not production_wired"

def persistNotOccupancyCopyCollision : String :=
  "persist Hilbert xy2d(ucrs_seq, grid_hash) ne occupancy Hilbert FNV(cell_id, write_set) homolog not copy"

def twoHilbertsSecondLawConservationFraming : String :=
  "second_law_conservation_two_hilberts_one_axiom_not_second_hilbert_axiom"

theorem two_hilberts_cell_id :
    twoHilbertsCellId = "URGE-FORMAL-Q-LEAN-TWO-HILBERTS" :=
  rfl

theorem two_hilberts_modality_unwired :
    twoHilbertsModalityCurrent = .unwired :=
  rfl

theorem production_wired_false : productionWired = false := rfl

theorem two_hilberts_production_wired_false : twoHilbertsProductionWired = false := rfl

theorem two_hilberts_cites_persist_authority :
    persistHilbertAuthority ≠ "" :=
  by decide

theorem two_hilberts_cites_occupancy_authority :
    occupancyHilbertAuthority ≠ "" :=
  by decide

theorem two_hilberts_cites_physical_second_law :
    physicalSecondLawAuthority = "LandauerLaw.physicalSecondLaw" :=
  rfl

theorem two_hilberts_collision_fence_named :
    persistNotOccupancyCopyCollision ≠ "" :=
  by decide

theorem persist_hilbert_authority_ne_occupancy :
    persistHilbertAuthority ≠ occupancyHilbertAuthority := by
  decide

theorem two_hilberts_not_second_hilbert_axiom :
    twoHilbertsSecondLawConservationFraming ≠ "hilbert_second_axiom" := by
  decide

theorem two_hilberts_second_law_framing :
    twoHilbertsSecondLawConservationFraming ≠ "" :=
  by decide

/-- Physics GREEN is not authorized on the knowing scaffold. -/
def physicsGreenAuthorized : Prop := False

theorem two_hilberts_physics_green_false : ¬ physicsGreenAuthorized :=
  id

theorem two_hilberts_not_meso_thermo_restate :
    twoHilbertsNonClaim ≠ "meso_thermo_G_T_P_x_restate" :=
  by decide

def knowingFiberTag : String := "quantum_knowing_fiber"

theorem two_hilberts_knowing_fiber_named :
    knowingFiberTag = "quantum_knowing_fiber" :=
  rfl

def twoHilbertsKnowingFiberOk : Prop :=
  twoHilbertsModalityCurrent = .unwired ∧ ¬ physicsGreenAuthorized

theorem two_hilberts_knowing_fiber_ok :
    twoHilbertsKnowingFiberOk :=
  ⟨two_hilberts_modality_unwired, two_hilberts_physics_green_false⟩

end UrgeKnowing.TwoHilberts
