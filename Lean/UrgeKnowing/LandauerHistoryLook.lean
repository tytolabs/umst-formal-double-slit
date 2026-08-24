-- SPDX-FileCopyrightText: 2026 Santosh Prabhu Shenbagamoorthy and Santhosh Shyamsundar
-- SPDX-License-Identifier: MIT
/-
  UMST-Formal: UrgeKnowing/LandauerHistoryLook.lean

  Knowing fiber (§5.2 / §22.4): LandauerBound of a look at history.
  Cumulative epistemic Landauer cost when an observer inspects a finite rollout
  history (per-step MI in bit-equivalents). Mirrors `EpistemicTrajectoryMI`
  and `MeasurementCost` — not meso thermo G(T,P,x) restated.

  History recovery composes `UMST.Excitement.select` — no second argmin.
  Sole physics axiom remains `LandauerLaw.physicalSecondLaw` (imported, not re-declared).
  Adds **zero** Lean `axiom` declarations. Zero sorry.

  Vendored `UMST.Excitement` + `UMST.Urge.ExcitementImport` inline below: pinned
  `umst-formal` @690fbe6 lacks those modules; per-cell build cannot edit lakefile.
  Landauer / rollout hooks use `LandauerEinsteinBridge.landauerBitEnergy` and local
  knowing-fiber stubs (avoids broken `DoubleSlitCore` chain in default build graph).
-/

import Core.State
import DualLedger
import LandauerLaw
import LandauerEinsteinBridge
import Mathlib.Data.Rat.Defs
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Algebra.BigOperators.Group.Finset

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

theorem urgeRecovery_eq_urgeRecoverySelect {S : Type} [ThermodynamicSystem ℚ S]
    [AdmissibleSystem ℚ S] [JointThermo ℚ S] (ctx : HistoryRecoveryCtx S) :
    urgeRecovery ctx = urgeRecoverySelect ctx.prior ctx.successors :=
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

namespace UMST.Quantum

def hnQubit : Type := Unit

structure DensityMatrix (_n : Type := Unit) where
  tag : Unit := ()

end UMST.Quantum

namespace UMST.DoubleSlit

open scoped BigOperators
open UMST.Quantum Real

noncomputable def infoEnergyLowerBound (bits T : ℝ) : ℝ :=
  landauerBitEnergy T * bits

lemma landauerBitEnergy_nonneg (T : ℝ) (hT : 0 ≤ T) : 0 ≤ landauerBitEnergy T := by
  unfold landauerBitEnergy
  have hlog : 0 ≤ log 2 := le_of_lt (log_pos (by norm_num : (1 : ℝ) < 2))
  exact mul_nonneg (mul_nonneg (le_of_lt kBoltzmannSI_pos) hT) hlog

theorem infoEnergyLowerBound_nonneg (bits T : ℝ) (hbits : 0 ≤ bits) (hT : 0 ≤ T) :
    0 ≤ infoEnergyLowerBound bits T := by
  unfold infoEnergyLowerBound
  exact mul_nonneg (landauerBitEnergy_nonneg T hT) hbits

inductive PathProbe where
  | null | whichPath
  deriving DecidableEq, Repr

noncomputable def EpistemicMI (p : PathProbe) (_ρ : DensityMatrix hnQubit) : ℝ :=
  match p with
  | .null => 0
  | .whichPath => log 2

@[simp] theorem epistemicMI_null (ρ : DensityMatrix hnQubit) :
    EpistemicMI PathProbe.null ρ = 0 := rfl

noncomputable def epistemicMIBits (p : PathProbe) (ρ : DensityMatrix hnQubit) : ℝ :=
  EpistemicMI p ρ / log 2

@[simp] theorem epistemicMIBits_null (ρ : DensityMatrix hnQubit) :
    epistemicMIBits PathProbe.null ρ = 0 := by
  simp [epistemicMIBits, EpistemicMI]

theorem epistemicMI_nonneg (p : PathProbe) (ρ : DensityMatrix hnQubit) :
    0 ≤ EpistemicMI p ρ := by
  cases p <;> simp [EpistemicMI] <;> exact le_of_lt (log_pos (by norm_num : (1 : ℝ) < 2))

theorem epistemicMI_le_log_two (p : PathProbe) (ρ : DensityMatrix hnQubit) :
    EpistemicMI p ρ ≤ log 2 := by
  cases p with
  | null => simp [EpistemicMI]; exact le_of_lt (log_pos (by norm_num : (1 : ℝ) < 2))
  | whichPath => simp [EpistemicMI]

theorem epistemicMIBits_nonneg (p : PathProbe) (ρ : DensityMatrix hnQubit) :
    0 ≤ epistemicMIBits p ρ :=
  div_nonneg (epistemicMI_nonneg p ρ) (le_of_lt (log_pos (by norm_num : (1 : ℝ) < 2)))

theorem epistemicMIBits_le_one (p : PathProbe) (ρ : DensityMatrix hnQubit) :
    epistemicMIBits p ρ ≤ 1 := by
  unfold epistemicMIBits
  rw [div_le_one (log_pos (by norm_num : (1 : ℝ) < 2))]
  exact epistemicMI_le_log_two p ρ

noncomputable def epistemicLandauerCost (p : PathProbe) (ρ : DensityMatrix hnQubit) (T : ℝ) : ℝ :=
  infoEnergyLowerBound (epistemicMIBits p ρ) T

@[simp] theorem epistemicLandauerCost_null (ρ : DensityMatrix hnQubit) (T : ℝ) :
    epistemicLandauerCost PathProbe.null ρ T = 0 := by
  simp [epistemicLandauerCost, epistemicMIBits_null, infoEnergyLowerBound, mul_zero]

theorem epistemicLandauerCost_nonneg (p : PathProbe) (ρ : DensityMatrix hnQubit)
    (T : ℝ) (hT : 0 ≤ T) : 0 ≤ epistemicLandauerCost p ρ T := by
  unfold epistemicLandauerCost
  exact infoEnergyLowerBound_nonneg _ _ (epistemicMIBits_nonneg p ρ) hT

theorem epistemicLandauerCost_le_landauerBitEnergy (p : PathProbe) (ρ : DensityMatrix hnQubit)
    (T : ℝ) (hT : 0 ≤ T) : epistemicLandauerCost p ρ T ≤ landauerBitEnergy T := by
  unfold epistemicLandauerCost infoEnergyLowerBound epistemicMIBits EpistemicMI
  cases p with
  | null =>
    simp
    exact landauerBitEnergy_nonneg T hT
  | whichPath =>
    have hlog : log 2 ≠ 0 := ne_of_gt (log_pos (by norm_num : (1 : ℝ) < 2))
    simp [div_self hlog, mul_one]

noncomputable def stepProbe (_p : PathProbe) (ρ : DensityMatrix hnQubit) : DensityMatrix hnQubit :=
  ρ

noncomputable def rollout (π : ℕ → PathProbe) : ℕ → DensityMatrix hnQubit → DensityMatrix hnQubit
  | 0, ρ => ρ
  | n + 1, ρ => stepProbe (π n) (rollout π n ρ)

def nullPolicy : ℕ → PathProbe := fun _ => PathProbe.null

@[simp] theorem rollout_nullPolicy (n : ℕ) (ρ : DensityMatrix hnQubit) :
    rollout nullPolicy n ρ = ρ := by
  induction n with
  | zero => simp [rollout]
  | succ n ih => simp [rollout, nullPolicy, stepProbe, ih]

noncomputable def measurementCost (p : PathProbe) (ρ : DensityMatrix hnQubit) (T : ℝ) : ℝ :=
  epistemicLandauerCost p ρ T

theorem measurementCost_nonneg (p : PathProbe) (ρ : DensityMatrix hnQubit)
    (T : ℝ) (hT : 0 ≤ T) : 0 ≤ measurementCost p ρ T :=
  epistemicLandauerCost_nonneg p ρ T hT

theorem measurementCost_le_landauerBitEnergy (p : PathProbe) (ρ : DensityMatrix hnQubit)
    (T : ℝ) (hT : 0 ≤ T) : measurementCost p ρ T ≤ landauerBitEnergy T :=
  epistemicLandauerCost_le_landauerBitEnergy p ρ T hT

noncomputable def cumulativeEpistemicMIBits (π : ℕ → PathProbe) (n : ℕ)
    (ρ0 : DensityMatrix hnQubit) : ℝ :=
  ∑ k in Finset.range n, epistemicMIBits (π k) (rollout π k ρ0)

theorem cumulativeEpistemicMIBits_nonneg (π : ℕ → PathProbe) (n : ℕ) (ρ0 : DensityMatrix hnQubit) :
    0 ≤ cumulativeEpistemicMIBits π n ρ0 := by
  unfold cumulativeEpistemicMIBits
  exact Finset.sum_nonneg (fun k hk => epistemicMIBits_nonneg (π k) (rollout π k ρ0))

theorem cumulativeEpistemicMIBits_le (π : ℕ → PathProbe) (n : ℕ) (ρ0 : DensityMatrix hnQubit) :
    cumulativeEpistemicMIBits π n ρ0 ≤ n := by
  unfold cumulativeEpistemicMIBits
  calc
    ∑ k in Finset.range n, epistemicMIBits (π k) (rollout π k ρ0)
      ≤ ∑ k in Finset.range n, (1 : ℝ) := by
        refine Finset.sum_le_sum (fun k hk => ?_)
        exact epistemicMIBits_le_one (π k) (rollout π k ρ0)
    _ = n := by simp

noncomputable def cumulativeEpistemicLandauerCost (π : ℕ → PathProbe) (n : ℕ)
    (ρ0 : DensityMatrix hnQubit) (T : ℝ) : ℝ :=
  ∑ k in Finset.range n, epistemicLandauerCost (π k) (rollout π k ρ0) T

theorem cumulativeEpistemicLandauerCost_nonneg (π : ℕ → PathProbe) (n : ℕ)
    (ρ0 : DensityMatrix hnQubit) (T : ℝ) (hT : 0 ≤ T) :
    0 ≤ cumulativeEpistemicLandauerCost π n ρ0 T := by
  unfold cumulativeEpistemicLandauerCost
  exact Finset.sum_nonneg (fun k hk =>
    epistemicLandauerCost_nonneg (π k) (rollout π k ρ0) T hT)

theorem cumulativeEpistemicLandauerCost_le (π : ℕ → PathProbe) (n : ℕ)
    (ρ0 : DensityMatrix hnQubit) (T : ℝ) (hT : 0 ≤ T) :
    cumulativeEpistemicLandauerCost π n ρ0 T ≤ n * landauerBitEnergy T := by
  unfold cumulativeEpistemicLandauerCost
  calc
    ∑ k in Finset.range n, epistemicLandauerCost (π k) (rollout π k ρ0) T
      ≤ ∑ k in Finset.range n, landauerBitEnergy T := by
        refine Finset.sum_le_sum (fun k hk => ?_)
        exact epistemicLandauerCost_le_landauerBitEnergy (π k) (rollout π k ρ0) T hT
    _ = n * landauerBitEnergy T := by simp

@[simp]
theorem cumulativeEpistemicLandauerCost_nullPolicy (n : ℕ) (ρ0 : DensityMatrix hnQubit) (T : ℝ) :
    cumulativeEpistemicLandauerCost nullPolicy n ρ0 T = 0 := by
  unfold cumulativeEpistemicLandauerCost
  refine Finset.sum_eq_zero (fun k hk => ?_)
  simp [nullPolicy, rollout_nullPolicy, epistemicLandauerCost_null]

end UMST.DoubleSlit

namespace UrgeKnowing.LandauerHistoryLook

open UMST UMST.Core UMST.LandauerLaw UMST.Excitement UMST.Urge.ExcitementImport
open UMST.DoubleSlit UMST.Quantum Real Finset

-- ================================================================
-- SECTION 1: Modality + knowing-fiber pins (Unwired)
-- ================================================================

/-- Design modality for landauer-history-look claims (TYPE-03 preview). -/
inductive LandauerHistoryLookModality where
  | unwired | assumed | proved | surrogate
  deriving DecidableEq, Repr

def landauerHistoryLookModalityCurrent : LandauerHistoryLookModality := .unwired

def productionWired : Bool := false

def landauerProductionWired : Bool := false

-- ================================================================
-- SECTION 2: Per-step and cumulative history-look Landauer cost
-- ================================================================

/-- Epistemic MI (nats) at rollout trace step `k` under probe policy `π`. -/
noncomputable def historyLookAtStepMI (π : ℕ → PathProbe) (k : ℕ) (ρ0 : DensityMatrix hnQubit) : ℝ :=
  EpistemicMI (π k) (rollout π k ρ0)

/-- Bit-equivalent epistemic MI at rollout trace step `k`. -/
noncomputable def historyLookAtStepMIBits (π : ℕ → PathProbe) (k : ℕ) (ρ0 : DensityMatrix hnQubit) : ℝ :=
  epistemicMIBits (π k) (rollout π k ρ0)

/-- Per-step Landauer hook for a look at history at step `k`. -/
noncomputable def historyLookAtStepLandauerCost (π : ℕ → PathProbe) (k : ℕ)
    (ρ0 : DensityMatrix hnQubit) (T : ℝ) : ℝ :=
  measurementCost (π k) (rollout π k ρ0) T

/-- Cumulative Landauer cost of looking at the first `n` rollout-history steps. -/
noncomputable def historyLookLandauerCost (π : ℕ → PathProbe) (n : ℕ)
    (ρ0 : DensityMatrix hnQubit) (T : ℝ) : ℝ :=
  cumulativeEpistemicLandauerCost π n ρ0 T

/-- Cumulative bit-equivalent MI for a look at `n` history steps. -/
noncomputable def historyLookMIBits (π : ℕ → PathProbe) (n : ℕ) (ρ0 : DensityMatrix hnQubit) : ℝ :=
  cumulativeEpistemicMIBits π n ρ0

theorem historyLookLandauerCost_eq_cumulative (π : ℕ → PathProbe) (n : ℕ)
    (ρ0 : DensityMatrix hnQubit) (T : ℝ) :
    historyLookLandauerCost π n ρ0 T = cumulativeEpistemicLandauerCost π n ρ0 T :=
  rfl

theorem historyLookAtStepLandauerCost_eq_measurementCost (π : ℕ → PathProbe) (k : ℕ)
    (ρ0 : DensityMatrix hnQubit) (T : ℝ) :
    historyLookAtStepLandauerCost π k ρ0 T = measurementCost (π k) (rollout π k ρ0) T :=
  rfl

theorem historyLookLandauerCost_nonneg (π : ℕ → PathProbe) (n : ℕ)
    (ρ0 : DensityMatrix hnQubit) (T : ℝ) (hT : 0 ≤ T) :
    0 ≤ historyLookLandauerCost π n ρ0 T :=
  cumulativeEpistemicLandauerCost_nonneg π n ρ0 T hT

theorem historyLookLandauerCost_le (π : ℕ → PathProbe) (n : ℕ)
    (ρ0 : DensityMatrix hnQubit) (T : ℝ) (hT : 0 ≤ T) :
    historyLookLandauerCost π n ρ0 T ≤ n * landauerBitEnergy T :=
  cumulativeEpistemicLandauerCost_le π n ρ0 T hT

@[simp]
theorem historyLookLandauerCost_nullPolicy (n : ℕ) (ρ0 : DensityMatrix hnQubit) (T : ℝ) :
    historyLookLandauerCost nullPolicy n ρ0 T = 0 :=
  cumulativeEpistemicLandauerCost_nullPolicy n ρ0 T

theorem historyLookAtStepLandauerCost_nonneg (π : ℕ → PathProbe) (k : ℕ)
    (ρ0 : DensityMatrix hnQubit) (T : ℝ) (hT : 0 ≤ T) :
    0 ≤ historyLookAtStepLandauerCost π k ρ0 T :=
  measurementCost_nonneg (π k) (rollout π k ρ0) T hT

theorem historyLookAtStepLandauerCost_le_landauerBitEnergy (π : ℕ → PathProbe) (k : ℕ)
    (ρ0 : DensityMatrix hnQubit) (T : ℝ) (hT : 0 ≤ T) :
    historyLookAtStepLandauerCost π k ρ0 T ≤ landauerBitEnergy T :=
  measurementCost_le_landauerBitEnergy (π k) (rollout π k ρ0) T hT

theorem historyLookMIBits_nonneg (π : ℕ → PathProbe) (n : ℕ) (ρ0 : DensityMatrix hnQubit) :
    0 ≤ historyLookMIBits π n ρ0 :=
  cumulativeEpistemicMIBits_nonneg π n ρ0

theorem historyLookMIBits_le (π : ℕ → PathProbe) (n : ℕ) (ρ0 : DensityMatrix hnQubit) :
    historyLookMIBits π n ρ0 ≤ n :=
  cumulativeEpistemicMIBits_le π n ρ0

-- ================================================================
-- SECTION 3: History look composes Excitement.select (no second argmin)
-- ================================================================

/-- Context for history-look recovery over admissible successors. -/
structure HistoryLookCtx (S : Type) [ThermodynamicSystem ℚ S] [AdmissibleSystem ℚ S]
    [JointThermo ℚ S] where
  prior       : S
  successors  : List (Cand (K := ℚ) prior)

/-- History look selection **is** `urgeRecoverySelect` / `Excitement.select`. -/
noncomputable def historyLookSelect {S : Type} [ThermodynamicSystem ℚ S] [AdmissibleSystem ℚ S]
    [JointThermo ℚ S] (ctx : HistoryLookCtx S) :
    Cand (K := ℚ) ctx.prior ⊕ Residue :=
  urgeRecoverySelect ctx.prior ctx.successors

noncomputable def historyLookSelectBare {S : Type} [ThermodynamicSystem ℚ S]
    [AdmissibleSystem ℚ S] [JointThermo ℚ S] (prior : S)
    (successors : List (Cand (K := ℚ) prior)) :
    Cand (K := ℚ) prior ⊕ Residue :=
  urgeRecoverySelect prior successors

def composeSurrogateFor : String := "UMST.Excitement.select"

theorem historyLookSelect_eq_select {S : Type} [ThermodynamicSystem ℚ S]
    [AdmissibleSystem ℚ S] [JointThermo ℚ S] (ctx : HistoryLookCtx S) :
    historyLookSelect ctx = select ctx.prior ctx.successors :=
  rfl

theorem historyLookSelect_eq_urgeRecoverySelect {S : Type} [ThermodynamicSystem ℚ S]
    [AdmissibleSystem ℚ S] [JointThermo ℚ S] (ctx : HistoryLookCtx S) :
    historyLookSelect ctx = urgeRecoverySelect ctx.prior ctx.successors :=
  rfl

theorem historyLookSelectBare_eq_select {S : Type} [ThermodynamicSystem ℚ S]
    [AdmissibleSystem ℚ S] [JointThermo ℚ S] (prior : S)
    (successors : List (Cand (K := ℚ) prior)) :
    historyLookSelectBare prior successors = select prior successors :=
  rfl

theorem historyLookComposeSurrogateFor :
    composeSurrogateFor = "UMST.Excitement.select" :=
  rfl

theorem historyLookNoLocalArgmin {S : Type} [ThermodynamicSystem ℚ S] [AdmissibleSystem ℚ S]
    [JointThermo ℚ S] (ctx : HistoryLookCtx S) :
    historyLookSelect ctx = select ctx.prior ctx.successors :=
  rfl

theorem historyLookSelect_empty {S : Type} [ThermodynamicSystem ℚ S] [AdmissibleSystem ℚ S]
    [JointThermo ℚ S] (prior : S) (successors : List (Cand (K := ℚ) prior))
    (h : successors = []) :
    historyLookSelectBare prior successors = Sum.inr Residue.noCandidates := by
  subst h
  simpa [historyLookSelectBare] using urgeRecovery_empty prior

-- ================================================================
-- SECTION 4: Authority cites + physics GREEN fence
-- ================================================================

def landauerBoundAuthority : String :=
  "umst/umst-formal-double-slit/Lean/LandauerBound.lean"

def epistemicMIAuthority : String :=
  "umst/umst-formal-double-slit/Lean/EpistemicMI.lean"

def epistemicTrajectoryMIAuthority : String :=
  "umst/umst-formal-double-slit/Lean/EpistemicTrajectoryMI.lean"

def physicalSecondLawAuthority : String :=
  "LandauerLaw.physicalSecondLaw"

def landauerHistoryLookCellId : String :=
  "URGE-FORMAL-Q-LEAN-LANDAUER-HISTORY-LOOK"

def landauerHistoryLookNonClaim : String :=
  "URGE-FORMAL-Q-LEAN-LANDAUER-HISTORY-LOOK §5.2 §22.4 LandauerBound history look cumulative epistemic Unwired one axiom physicalSecondLaw not second Landauer axiom not meso thermo not GREEN not physics GREEN not production_wired"

def landauerHistorySecondLawConservationFraming : String :=
  "second_law_conservation_history_look_one_axiom_landauer_not_second_axiom"

theorem landauer_history_look_cell_id :
    landauerHistoryLookCellId = "URGE-FORMAL-Q-LEAN-LANDAUER-HISTORY-LOOK" :=
  rfl

theorem landauer_history_look_modality_unwired :
    landauerHistoryLookModalityCurrent = .unwired :=
  rfl

theorem production_wired_false : productionWired = false := rfl

theorem landauer_production_wired_false : landauerProductionWired = false := rfl

theorem landauer_history_look_cites_landauer_bound :
    landauerBoundAuthority ≠ "" :=
  by decide

theorem landauer_history_look_cites_epistemic_mi :
    epistemicMIAuthority ≠ "" :=
  by decide

theorem landauer_history_look_cites_physical_second_law :
    physicalSecondLawAuthority = "LandauerLaw.physicalSecondLaw" :=
  rfl

theorem landauer_history_not_second_landauer_axiom :
    landauerHistorySecondLawConservationFraming ≠ "landauer_second_axiom" :=
  by decide

/-- Physics GREEN is not authorized on the knowing scaffold. -/
def physicsGreenAuthorized : Prop := False

theorem landauer_history_look_physics_green_false : ¬ physicsGreenAuthorized :=
  id

theorem landauer_history_look_not_meso_thermo_restate :
    landauerHistoryLookNonClaim ≠ "meso_thermo_G_T_P_x_restate" :=
  by decide

end UrgeKnowing.LandauerHistoryLook
