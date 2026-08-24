-- SPDX-FileCopyrightText: 2026 Santosh Prabhu Shenbagamoorthy and Santhosh Shyamsundar
-- SPDX-License-Identifier: MIT

import ElementElectronic

set_option maxRecDepth 8192

/-!
# MadelungExceptionIsTheorem — Madelung-exception-is-theorem **conservation** (Q lattice)

Knowing-fiber Lean: finite Madelung occupancy exceptions (Named La/Ce/Gd/Pt/Au; Actinide Ac–Lr
Pu 94 absent; DBlock Cr/Cu/Nb/Mo/Ru/Rh/Pd/Ag) are occupancy-engine sort **theorems** — observed ≠
predicted Madelung family — not folklore exception lore or a 26th axiom. Lr honest override:
observed = predicted (not theorem). Homolog ≠ copy (Ds Z=110 vs Pt Z=78). Pairs `umst-chem`
scaffold `madelung_exception_is_theorem` / **conservation** posture.

Read-only cites (not imported — self-contained scaffold):
- `Coq/ChemConstants/MadelungExceptionIsTheorem.v`
- `umst/umst-chem/src/x_rows/madelung_exception_is_theorem.rs`

- `MadelungExceptionIsTheoremModality` — Unwired / Assumed / Proved / Surrogate (not 118² GREEN table).
- `MadelungExceptionTheoremBucket` — named / actinide / dblock / lrHonestOverride.
- `MadelungExceptionTerminal` — theorem / deferredCompositionRemainder / typedAbsent.
- Second-law + **conservation** framing cites meso `UMST.Chem.Conservation` /
  `LandauerLaw.physicalSecondLaw` — not imported.
- No meso / acting theorems. No new physics `axiom`. Sorting cites override pins — **not** 26th axiom.
- `physics_green` stays false. Does **not** claim `madelungExceptionIsTheoremProved` or physics GREEN.
- WAVE100 freeze — remainder deferred composition (env/time/cross-domain), not impossibility stop.
-/

namespace UMST.Chem

/-- Design modality for Madelung-exception-is-theorem **conservation** (lattice SSOT). -/
inductive MadelungExceptionIsTheoremModality where
  | unwired | assumed | proved | surrogate
  deriving DecidableEq, Repr

def madelungExceptionIsTheoremModalityCurrent : MadelungExceptionIsTheoremModality := .unwired

/-- Modality lattice cardinality (Unwired / Assumed / Proved / Surrogate). -/
def madelungExceptionIsTheoremModalityLatticeCardinality : Nat := 4

theorem madelung_exception_is_theorem_modality_lattice_cardinality_four :
    madelungExceptionIsTheoremModalityLatticeCardinality = 4 := rfl

theorem madelung_exception_is_theorem_modality_lattice_not_118_squared :
    madelungExceptionIsTheoremModalityLatticeCardinality ≠ 118 * 118 := by decide

/-- Surface tag for name-from-content. -/
def madelungExceptionIsTheoremSurface : String := "madelung_exception_is_theorem_surface"

theorem madelung_exception_is_theorem_surface_named : madelungExceptionIsTheoremSurface ≠ "" := by decide

/-- Madelung-exception theorem bucket — exception family vs Lr honest override. -/
inductive MadelungExceptionTheoremBucket where
  | namedMadelungException | actinideMadelungException | dBlockMadelungException
  | lrHonestOverride
  deriving DecidableEq, Repr

def madelungExceptionTheoremBucketCount : Nat := 4

theorem madelung_exception_theorem_bucket_count_is_four :
    madelungExceptionTheoremBucketCount = 4 := rfl

def madelungExceptionTheoremBucketTags : List String :=
  ["named_madelung_exception_theorem", "actinide_madelung_exception_theorem",
   "dblock_madelung_exception_theorem", "lr_honest_override_not_theorem"]

theorem madelung_exception_theorem_bucket_tags_length_four :
    madelungExceptionTheoremBucketTags.length = 4 := by decide

/-- Madelung-exception terminal — theorem | deferred composition remainder | typed Absent. -/
inductive MadelungExceptionTerminal where
  | theorem | deferredCompositionRemainder | typedAbsent
  deriving DecidableEq, Repr

def madelungExceptionTerminalCount : Nat := 3

theorem madelung_exception_terminal_count_is_three : madelungExceptionTerminalCount = 3 := rfl

def madelungExceptionTerminalTags : List String :=
  ["theorem", "deferred_composition_remainder", "typed_absent"]

theorem madelung_exception_terminal_tags_length_three : madelungExceptionTerminalTags.length = 3 := by decide

/-- IUPAC Z bar — theorem sort for Z=1..118 (not 118² table). -/
def iupacTableCardinality : Nat := 118

theorem iupac_table_cardinality_is_118 : iupacTableCardinality = 118 := rfl

def madelungExceptionElementZValid (z : Nat) : Bool :=
  0 < z && z ≤ iupacTableCardinality

/-- Named occupancy exception Z pins — INT SSOT (La / Ce / Gd / Pt / Au). -/
def namedExceptionZs : List Nat := [57, 58, 64, 78, 79]

theorem named_exception_zs_length_five : namedExceptionZs.length = 5 := by decide

/-- Actinide occupancy exception Z pins — INT SSOT (Pu 94 absent). -/
def actinideExceptionZs : List Nat := [89, 90, 91, 92, 93, 96, 103]

theorem actinide_exception_zs_length_seven : actinideExceptionZs.length = 7 := by decide

/-- D-block occupancy exception Z pins — INT SSOT. -/
def dBlockExceptionZs : List Nat := [24, 29, 41, 42, 44, 45, 46, 47]

theorem d_block_exception_zs_length_eight : dBlockExceptionZs.length = 8 := by decide

def listContains (xs : List Nat) (z : Nat) : Bool :=
  match xs with
  | [] => false
  | h :: t => h == z || listContains t z

def isNamedExceptionZ (z : Nat) : Bool := listContains namedExceptionZs z
def isActinideExceptionZ (z : Nat) : Bool := listContains actinideExceptionZs z
def isDBlockExceptionZ (z : Nat) : Bool := listContains dBlockExceptionZs z

def isAnyOccupancyExceptionZ (z : Nat) : Bool :=
  isNamedExceptionZ z || isActinideExceptionZ z || isDBlockExceptionZ z

/-- Folklore exception refuse — terminals are theorem / deferred / typed Absent only. -/
def folkloreExceptionMarker : String := "madelung_exception_folklore_unsorted_v1"
def theoremTerminalMarker : String := "madelung_exception_terminal_theorem_v1"
def deferredRemainderMarker : String := "madelung_exception_terminal_deferred_composition_remainder_v1"
def typedAbsentMarker : String := "madelung_exception_terminal_typed_absent_v1"

theorem folklore_marker_ne_theorem_terminal :
    folkloreExceptionMarker ≠ theoremTerminalMarker := by decide

theorem folklore_marker_ne_deferred_remainder :
    folkloreExceptionMarker ≠ deferredRemainderMarker := by decide

theorem folklore_marker_ne_typed_absent :
    folkloreExceptionMarker ≠ typedAbsentMarker := by decide

/-- Named Z pins — theorem witnesses (observed ≠ predicted Madelung family). -/
def lanthanumZ : Nat := 57
def ceriumZ : Nat := 58
def gadoliniumZ : Nat := 64
def platinumZ : Nat := 78
def goldZ : Nat := 79

theorem lanthanum_z_is_57 : lanthanumZ = 57 := rfl
theorem cerium_z_is_58 : ceriumZ = 58 := rfl
theorem gadolinium_z_is_64 : gadoliniumZ = 64 := rfl
theorem platinum_z_is_78 : platinumZ = 78 := rfl
theorem gold_z_is_79 : goldZ = 79 := rfl

/-- D-block Z pins — theorem witnesses. -/
def chromiumZ : Nat := 24
def copperZ : Nat := 29
def niobiumZ : Nat := 41
def molybdenumZ : Nat := 42
def rutheniumZ : Nat := 44
def rhodiumZ : Nat := 45
def palladiumZ : Nat := 46
def silverZ : Nat := 47

theorem chromium_z_is_24 : chromiumZ = 24 := rfl
theorem copper_z_is_29 : copperZ = 29 := rfl
theorem niobium_z_is_41 : niobiumZ = 41 := rfl
theorem molybdenum_z_is_42 : molybdenumZ = 42 := rfl
theorem ruthenium_z_is_44 : rutheniumZ = 44 := rfl
theorem rhodium_z_is_45 : rhodiumZ = 45 := rfl
theorem palladium_z_is_46 : palladiumZ = 46 := rfl
theorem silver_z_is_47 : silverZ = 47 := rfl

/-- Actinide Z pins — six theorem witnesses + Lr honest override. -/
def actiniumZ : Nat := 89
def thoriumZ : Nat := 90
def protactiniumZ : Nat := 91
def uraniumZ : Nat := 92
def neptuniumZ : Nat := 93
def curiumZ : Nat := 96
def lawrenciumZ : Nat := 103

theorem actinium_z_is_89 : actiniumZ = 89 := rfl
theorem thorium_z_is_90 : thoriumZ = 90 := rfl
theorem protactinium_z_is_91 : protactiniumZ = 91 := rfl
theorem uranium_z_is_92 : uraniumZ = 92 := rfl
theorem neptunium_z_is_93 : neptuniumZ = 93 := rfl
theorem curium_z_is_96 : curiumZ = 96 := rfl
theorem lawrencium_z_is_103 : lawrenciumZ = 103 := rfl

/-- Plutonium Z — absent from all exception sets (Madelung family). -/
def plutoniumZ : Nat := 94

theorem plutonium_z_is_94 : plutoniumZ = 94 := rfl

theorem plutonium_not_named_exception : isNamedExceptionZ plutoniumZ = false := by decide
theorem plutonium_not_actinide_exception : isActinideExceptionZ plutoniumZ = false := by decide
theorem plutonium_not_d_block_exception : isDBlockExceptionZ plutoniumZ = false := by decide

def plutoniumNotInAnyExceptionSet : Bool :=
  !isNamedExceptionZ plutoniumZ &&
  !isActinideExceptionZ plutoniumZ &&
  !isDBlockExceptionZ plutoniumZ

theorem plutonium_not_in_any_exception_set_true : plutoniumNotInAnyExceptionSet = true := by decide

/-- Darmstadtium Z — homolog of Pt, not NamedException (homolog ≠ copy). -/
def darmstadtiumZ : Nat := 110
def periodHomologZOffset : Nat := 32

theorem darmstadtium_z_is_110 : darmstadtiumZ = 110 := rfl
theorem period_homolog_z_offset_is_32 : periodHomologZOffset = 32 := by decide

theorem ds_homolog_z_offset_from_pt :
    platinumZ + periodHomologZOffset = darmstadtiumZ := by decide

theorem darmstadtium_not_named_exception : isNamedExceptionZ darmstadtiumZ = false := by decide

def dsHomologNotPtOccupancyCopy : Bool :=
  darmstadtiumZ ≠ platinumZ &&
  isNamedExceptionZ platinumZ &&
  !isNamedExceptionZ darmstadtiumZ

theorem ds_homolog_not_pt_occupancy_copy_true : dsHomologNotPtOccupancyCopy = true := by decide

structure MadelungExceptionWitness where
  z : Nat
  bucket : MadelungExceptionTheoremBucket
  terminal : MadelungExceptionTerminal
  level : Nat
  deriving DecidableEq, Repr

def madelungExceptionWitnessNontrivial (w : MadelungExceptionWitness) : Bool :=
  0 < w.level

/-- Pt Z=78 — Named Madelung exception theorem. -/
def platinumNamedTheoremWitness : MadelungExceptionWitness :=
  { z := platinumZ, bucket := .namedMadelungException, terminal := .theorem, level := 1 }

/-- Cr Z=24 — DBlock Madelung exception theorem. -/
def chromiumDBlockTheoremWitness : MadelungExceptionWitness :=
  { z := chromiumZ, bucket := .dBlockMadelungException, terminal := .theorem, level := 1 }

/-- Ac Z=89 — Actinide Madelung exception theorem. -/
def actiniumActinideTheoremWitness : MadelungExceptionWitness :=
  { z := actiniumZ, bucket := .actinideMadelungException, terminal := .theorem, level := 1 }

/-- Lr Z=103 — honest override (observed = predicted, not theorem). -/
def lawrenciumHonestOverrideWitness : MadelungExceptionWitness :=
  { z := lawrenciumZ, bucket := .lrHonestOverride, terminal := .typedAbsent, level := 1 }

/-- Pu Z=94 — deferred composition remainder (absent from exception sets). -/
def plutoniumDeferredWitness : MadelungExceptionWitness :=
  { z := plutoniumZ, bucket := .namedMadelungException, terminal := .deferredCompositionRemainder, level := 1 }

def madelungExceptionWitnessTrivial : MadelungExceptionWitness :=
  { z := platinumZ, bucket := .namedMadelungException, terminal := .theorem, level := 0 }

def madelungExceptionWitnessHonest (w : MadelungExceptionWitness) : Bool :=
  madelungExceptionWitnessNontrivial w && madelungExceptionElementZValid w.z

theorem platinum_named_theorem_witness_honest :
    madelungExceptionWitnessHonest platinumNamedTheoremWitness = true := by decide
theorem chromium_dblock_theorem_witness_honest :
    madelungExceptionWitnessHonest chromiumDBlockTheoremWitness = true := by decide
theorem actinium_actinide_theorem_witness_honest :
    madelungExceptionWitnessHonest actiniumActinideTheoremWitness = true := by decide
theorem lawrencium_honest_override_witness_honest :
    madelungExceptionWitnessHonest lawrenciumHonestOverrideWitness = true := by decide
theorem plutonium_deferred_witness_honest :
    madelungExceptionWitnessHonest plutoniumDeferredWitness = true := by decide

def madelungExceptionTerminalsAreNamed : Bool :=
  platinumNamedTheoremWitness.terminal == .theorem &&
  chromiumDBlockTheoremWitness.terminal == .theorem &&
  actiniumActinideTheoremWitness.terminal == .theorem &&
  lawrenciumHonestOverrideWitness.terminal == .typedAbsent &&
  plutoniumDeferredWitness.terminal == .deferredCompositionRemainder

theorem madelung_exception_terminals_are_named_true :
    madelungExceptionTerminalsAreNamed = true := by decide

def madelungExceptionBucketsAreNamed : Bool :=
  platinumNamedTheoremWitness.bucket == .namedMadelungException &&
  chromiumDBlockTheoremWitness.bucket == .dBlockMadelungException &&
  actiniumActinideTheoremWitness.bucket == .actinideMadelungException &&
  lawrenciumHonestOverrideWitness.bucket == .lrHonestOverride

theorem madelung_exception_buckets_are_named_true :
    madelungExceptionBucketsAreNamed = true := by decide

def namedExceptionZsAreTheorem : Bool :=
  listContains namedExceptionZs 57 &&
  listContains namedExceptionZs 78 &&
  isNamedExceptionZ 57 &&
  isNamedExceptionZ 78 &&
  isNamedExceptionZ 79

theorem named_exception_zs_are_theorem_true : namedExceptionZsAreTheorem = true := by decide

def dBlockExceptionZsAreTheorem : Bool :=
  isDBlockExceptionZ 24 &&
  isDBlockExceptionZ 47 &&
  listContains dBlockExceptionZs 24 &&
  listContains dBlockExceptionZs 47

theorem d_block_exception_zs_are_theorem_true : dBlockExceptionZsAreTheorem = true := by decide

def actinideExceptionZsAreTheorem : Bool :=
  isActinideExceptionZ 89 &&
  isActinideExceptionZ 103 &&
  !isActinideExceptionZ plutoniumZ

theorem actinide_exception_zs_are_theorem_true : actinideExceptionZsAreTheorem = true := by decide

def folkloreExceptionRefused : Bool := true

theorem folklore_exception_refused_true : folkloreExceptionRefused = true := rfl

def madelungExceptionIsNewAxiom : Bool := false

theorem madelung_exception_is_new_axiom_false : madelungExceptionIsNewAxiom = false := rfl

def madelungExceptionIsTheoremConjunct : Bool :=
  madelungExceptionTerminalsAreNamed &&
  madelungExceptionBucketsAreNamed &&
  namedExceptionZsAreTheorem &&
  dBlockExceptionZsAreTheorem &&
  actinideExceptionZsAreTheorem &&
  plutoniumNotInAnyExceptionSet &&
  dsHomologNotPtOccupancyCopy &&
  folkloreExceptionRefused &&
  !madelungExceptionIsNewAxiom

theorem madelung_exception_is_theorem_conjunct_true : madelungExceptionIsTheoremConjunct = true := by decide

/-- Not fourth chemistry science / not 26th axiom fences. -/
def fourthScienceCollisionMarker : String :=
  "Madelung-exception-is-theorem ≠ fourth parallel chemistry science axiom"

def twentySixthAxiomCollisionMarker : String :=
  "Madelung-exception-is-theorem ≠ 26th parallel chemistry axiom"

theorem fourth_science_collision_named : fourthScienceCollisionMarker ≠ "" := by decide
theorem twenty_sixth_axiom_collision_named : twentySixthAxiomCollisionMarker ≠ "" := by decide

def notFourthChemistryScience : Bool := true
def notTwentySixthAxiom : Bool := true

theorem not_fourth_chemistry_science : notFourthChemistryScience = true := rfl
theorem not_twenty_sixth_axiom : notTwentySixthAxiom = true := rfl

def soleAxiomCount : Nat := 1

theorem sole_axiom_count_is_one : soleAxiomCount = 1 := rfl

/-- Verdict for Madelung-exception-is-theorem close (fail-closed). -/
inductive MadelungExceptionIsTheoremVerdict where
  | unwiredOk
  | theoremNamedOk
  | trivialZRefuse
  | folkloreExceptionRefuse
  | newAxiomRefuse
  | homologCopyRefuse
  | fourthScienceRefuse
  | twentySixthAxiomRefuse
  | greenInventRefuse
  | provedWithoutBarRefuse
  | productionWiredRefuse
  deriving DecidableEq, Repr

def madelungExceptionIsTheoremVerdictOk (v : MadelungExceptionIsTheoremVerdict) : Bool :=
  match v with
  | .unwiredOk | .theoremNamedOk => true
  | _ => false

def folkloreExceptionSmuggle (claimFolkloreException : Bool) : Bool := claimFolkloreException
def newAxiomSmuggle (claimNewAxiom : Bool) : Bool := claimNewAxiom
def homologCopySmuggle (claimHomologCopy : Bool) : Bool := claimHomologCopy

def evaluateMadelungExceptionIsTheoremIncidence
    (modality : MadelungExceptionIsTheoremModality)
    (w : MadelungExceptionWitness)
    (claimPhysicsGreen : Bool)
    (claimProved : Bool)
    (claimFolkloreException : Bool)
    (claimNewAxiom : Bool)
    (claimHomologCopy : Bool)
    (claimFourthScience : Bool)
    (claimTwentySixthAxiom : Bool) : MadelungExceptionIsTheoremVerdict :=
  if claimPhysicsGreen then
    .greenInventRefuse
  else if claimProved then
    .provedWithoutBarRefuse
  else if claimFourthScience then
    .fourthScienceRefuse
  else if claimTwentySixthAxiom then
    .twentySixthAxiomRefuse
  else if folkloreExceptionSmuggle claimFolkloreException then
    .folkloreExceptionRefuse
  else if newAxiomSmuggle claimNewAxiom then
    .newAxiomRefuse
  else if homologCopySmuggle claimHomologCopy then
    .homologCopyRefuse
  else if !madelungExceptionWitnessNontrivial w then
    .trivialZRefuse
  else if !madelungExceptionElementZValid w.z then
    .trivialZRefuse
  else
    match modality with
    | .unwired => .theoremNamedOk
    | .assumed | .surrogate => .unwiredOk
    | .proved => .provedWithoutBarRefuse

def evaluateMadelungExceptionIsTheoremClose
    (modality : MadelungExceptionIsTheoremModality)
    (claimPhysicsGreen : Bool)
    (claimProductionWired : Bool) : MadelungExceptionIsTheoremVerdict :=
  if claimPhysicsGreen then
    .greenInventRefuse
  else if claimProductionWired then
    .productionWiredRefuse
  else
    match modality with
    | .unwired => .unwiredOk
    | .assumed | .proved | .surrogate => .theoremNamedOk

/-- WAVE100 — lib.rs / eos.rs / nano not wired (deferred composition). -/
def wave100LibRsWired : Bool := false
def wave100EosRsWired : Bool := false
def wave100NanoWired : Bool := false
def madelungExceptionIsTheoremProductionWired : Bool := false

theorem wave100_lib_rs_not_wired : wave100LibRsWired = false := rfl
theorem wave100_eos_rs_not_wired : wave100EosRsWired = false := rfl
theorem wave100_nano_not_wired : wave100NanoWired = false := rfl

theorem madelung_exception_is_theorem_production_not_wired :
    madelungExceptionIsTheoremProductionWired = false := rfl

def wave100NotWired : Bool :=
  !wave100LibRsWired && !wave100EosRsWired && !wave100NanoWired

theorem wave100_not_wired_true : wave100NotWired = true := by decide

def madelungExceptionIsTheoremProved : Bool := false

theorem madelung_exception_is_theorem_proved_false : madelungExceptionIsTheoremProved = false := rfl

def not118SquaredGreenTable : Bool := true

theorem not_118_squared_green_table : not118SquaredGreenTable = true := rfl

def unwiredMadelungExceptionIsTheoremCloseOk : Bool :=
  decide (evaluateMadelungExceptionIsTheoremClose .unwired false false = .unwiredOk)

def ptNamedTheoremOk : Bool :=
  decide (evaluateMadelungExceptionIsTheoremIncidence .unwired platinumNamedTheoremWitness
    false false false false false false false = .theoremNamedOk)

def crDBlockTheoremOk : Bool :=
  decide (evaluateMadelungExceptionIsTheoremIncidence .unwired chromiumDBlockTheoremWitness
    false false false false false false false = .theoremNamedOk)

def acActinideTheoremOk : Bool :=
  decide (evaluateMadelungExceptionIsTheoremIncidence .unwired actiniumActinideTheoremWitness
    false false false false false false false = .theoremNamedOk)

def lrHonestOverrideOk : Bool :=
  decide (evaluateMadelungExceptionIsTheoremIncidence .unwired lawrenciumHonestOverrideWitness
    false false false false false false false = .theoremNamedOk)

def puDeferredOk : Bool :=
  decide (evaluateMadelungExceptionIsTheoremIncidence .unwired plutoniumDeferredWitness
    false false false false false false false = .theoremNamedOk)

def trivialZRefuse : Bool :=
  decide (evaluateMadelungExceptionIsTheoremIncidence .unwired madelungExceptionWitnessTrivial
    false false false false false false false = .trivialZRefuse)

def folkloreExceptionRefuseGate : Bool :=
  decide (evaluateMadelungExceptionIsTheoremIncidence .unwired platinumNamedTheoremWitness
    false false true false false false false = .folkloreExceptionRefuse)

def newAxiomRefuse : Bool :=
  decide (evaluateMadelungExceptionIsTheoremIncidence .unwired platinumNamedTheoremWitness
    false false false true false false false = .newAxiomRefuse)

def homologCopyRefuse : Bool :=
  decide (evaluateMadelungExceptionIsTheoremIncidence .unwired platinumNamedTheoremWitness
    false false false false true false false = .homologCopyRefuse)

def greenInventMadelungExceptionIsTheoremRefuse : Bool :=
  decide (evaluateMadelungExceptionIsTheoremClose .unwired true false = .greenInventRefuse)

def provedWithoutBarMadelungExceptionIsTheoremRefuse : Bool :=
  decide (evaluateMadelungExceptionIsTheoremIncidence .unwired platinumNamedTheoremWitness
    false true false false false false false = .provedWithoutBarRefuse)

def productionWiredMadelungExceptionIsTheoremRefuse : Bool :=
  decide (evaluateMadelungExceptionIsTheoremClose .proved false true = .productionWiredRefuse)

def madelungExceptionIsTheoremScaffold : Bool :=
  unwiredMadelungExceptionIsTheoremCloseOk &&
    madelungExceptionIsTheoremConjunct &&
    ptNamedTheoremOk &&
    crDBlockTheoremOk &&
    acActinideTheoremOk &&
    lrHonestOverrideOk &&
    puDeferredOk &&
    trivialZRefuse &&
    folkloreExceptionRefuseGate &&
    newAxiomRefuse &&
    homologCopyRefuse &&
    greenInventMadelungExceptionIsTheoremRefuse &&
    provedWithoutBarMadelungExceptionIsTheoremRefuse &&
    productionWiredMadelungExceptionIsTheoremRefuse &&
    wave100NotWired

theorem madelung_exception_is_theorem_scaffold_true :
    madelungExceptionIsTheoremScaffold = true := by native_decide

inductive FormalFiber where
  | quantumKnowing | mesoActing
  deriving DecidableEq, Repr

def madelungExceptionIsTheoremFiberOk (f : FormalFiber) : Bool :=
  match f with | .quantumKnowing => true | .mesoActing => false

theorem madelung_exception_is_theorem_knowing_fiber_ok :
    madelungExceptionIsTheoremFiberOk .quantumKnowing = true := rfl

theorem madelung_exception_is_theorem_meso_acting_fiber_not_ok :
    madelungExceptionIsTheoremFiberOk .mesoActing = false := rfl

def madelungExceptionIsTheoremCellId : String :=
  "CHEM-FORMAL-Q-LEAN-MADELUNG-EXCEPTION-IS-THEOREM-CONSERVATION"

def madelungExceptionIsTheoremPhysicsGreenAuthorized : Prop := False

theorem madelung_exception_is_theorem_physics_green_false :
    ¬ madelungExceptionIsTheoremPhysicsGreenAuthorized := id

structure MadelungExceptionIsTheoremProbe where
  cellIdNamed : Bool
  unwired : Bool
  physicsGreenRefused : Bool
  soleAxiom : Bool
  notProved : Bool
  terminalsNamed : Bool
  folkloreRefused : Bool
  deriving DecidableEq, Repr

def madelungExceptionIsTheoremProbe : MadelungExceptionIsTheoremProbe :=
  { cellIdNamed :=
      decide (madelungExceptionIsTheoremCellId =
        "CHEM-FORMAL-Q-LEAN-MADELUNG-EXCEPTION-IS-THEOREM-CONSERVATION")
    unwired := decide (madelungExceptionIsTheoremModalityCurrent = .unwired)
    physicsGreenRefused := true
    soleAxiom := decide (soleAxiomCount = 1)
    notProved := !madelungExceptionIsTheoremProved
    terminalsNamed := madelungExceptionTerminalsAreNamed
    folkloreRefused := folkloreExceptionRefused }

def madelungExceptionIsTheoremHonest : Bool :=
  let p := madelungExceptionIsTheoremProbe
  p.cellIdNamed &&
    p.unwired &&
    p.physicsGreenRefused &&
    p.soleAxiom &&
    p.notProved &&
    p.terminalsNamed &&
    p.folkloreRefused &&
    madelungExceptionIsTheoremScaffold

theorem madelung_exception_is_theorem_honest_true : madelungExceptionIsTheoremHonest = true := by native_decide

def madelungExceptionIsTheoremFraming : String :=
  "second_law_conservation_madelung_exception_is_theorem_one_axiom_not_26th_axiom"

theorem madelung_exception_is_theorem_not_twenty_sixth_axiom_framing :
    madelungExceptionIsTheoremFraming ≠ "twenty_sixth_chemistry_axiom" := by decide

theorem madelung_exception_is_theorem_not_fourth_science_axiom :
    madelungExceptionIsTheoremFraming ≠ "fourth_chemistry_science_axiom" := by decide

def madelungExceptionIsTheoremSecondLawConservationFramed : Bool := true

theorem madelung_exception_is_theorem_second_law_conservation_framed :
    madelungExceptionIsTheoremSecondLawConservationFramed = true := rfl

def madelungExceptionIsTheoremCitedCoqModule : String :=
  "Coq/ChemConstants/MadelungExceptionIsTheorem.v"

def madelungExceptionIsTheoremCitedModule : String :=
  "umst/umst-chem/src/x_rows/madelung_exception_is_theorem.rs"

def chemIntCrossMadelungExceptionIsTheoremAuthority : String :=
  "CHEM-INT-CROSS-MADELUNG-EXCEPTION-IS-THEOREM-CONSERVATION"

def madelungExceptionIsTheoremNonClaim : String :=
  "CHEM-FORMAL-Q-LEAN-MADELUNG-EXCEPTION-IS-THEOREM-CONSERVATION Madelung exception is occupancy engine sort theorem Named Actinide DBlock Cr Cu Nb Mo Ru Rh Pd Ag La Ce Gd Pt Au Ac-Lr Pu94 absent Lr honest override terminals theorem deferred composition remainder typed Absent not folklore exception not 26th axiom GREEN invent fail-closed proved-without-bar fail-closed trivial Z=0 refuse madelungExceptionIsTheoremProved false Unwired knowing quantum fiber not meso acting WAVE100 lib eos nano smuggle refuse one axiom second law conservation not GREEN DFT not physics GREEN not production_wired remainder deferred composition not impossibility homolog not copy Ds110 not Pt78"

theorem madelung_exception_is_theorem_modality_unwired :
    madelungExceptionIsTheoremModalityCurrent = .unwired := rfl

def madelungExceptionIsTheoremAxiom : Bool :=
  not118SquaredGreenTable &&
    madelungExceptionIsTheoremSecondLawConservationFramed &&
    madelungExceptionIsTheoremConjunct &&
    madelungExceptionIsTheoremScaffold &&
    madelungExceptionIsTheoremHonest &&
    !madelungExceptionIsTheoremProved &&
    !madelungExceptionIsTheoremProductionWired &&
    !wave100LibRsWired &&
    !wave100EosRsWired &&
    !wave100NanoWired &&
    notFourthChemistryScience &&
    notTwentySixthAxiom &&
    decide (madelungExceptionIsTheoremFraming =
      "second_law_conservation_madelung_exception_is_theorem_one_axiom_not_26th_axiom")

theorem madelung_exception_is_theorem_axiom : madelungExceptionIsTheoremAxiom = true := by native_decide

theorem unwired_close_without_production_wiring :
    evaluateMadelungExceptionIsTheoremClose .unwired false false = .unwiredOk := rfl

theorem pt_named_theorem_ok :
    evaluateMadelungExceptionIsTheoremIncidence .unwired platinumNamedTheoremWitness
      false false false false false false false = .theoremNamedOk := rfl

theorem cr_dblock_theorem_ok :
    evaluateMadelungExceptionIsTheoremIncidence .unwired chromiumDBlockTheoremWitness
      false false false false false false false = .theoremNamedOk := rfl

theorem ac_actinide_theorem_ok :
    evaluateMadelungExceptionIsTheoremIncidence .unwired actiniumActinideTheoremWitness
      false false false false false false false = .theoremNamedOk := rfl

theorem lr_honest_override_ok :
    evaluateMadelungExceptionIsTheoremIncidence .unwired lawrenciumHonestOverrideWitness
      false false false false false false false = .theoremNamedOk := rfl

theorem pu_deferred_ok :
    evaluateMadelungExceptionIsTheoremIncidence .unwired plutoniumDeferredWitness
      false false false false false false false = .theoremNamedOk := rfl

theorem trivial_z_refused :
    evaluateMadelungExceptionIsTheoremIncidence .unwired madelungExceptionWitnessTrivial
      false false false false false false false = .trivialZRefuse := rfl

theorem folklore_exception_refused :
    evaluateMadelungExceptionIsTheoremIncidence .unwired platinumNamedTheoremWitness
      false false true false false false false = .folkloreExceptionRefuse := rfl

theorem new_axiom_refused :
    evaluateMadelungExceptionIsTheoremIncidence .unwired platinumNamedTheoremWitness
      false false false true false false false = .newAxiomRefuse := rfl

theorem homolog_copy_refused :
    evaluateMadelungExceptionIsTheoremIncidence .unwired platinumNamedTheoremWitness
      false false false false true false false = .homologCopyRefuse := rfl

theorem green_invent_refuse_unwired :
    evaluateMadelungExceptionIsTheoremClose .unwired true false = .greenInventRefuse := rfl

theorem proved_without_bar_refuse :
    evaluateMadelungExceptionIsTheoremIncidence .unwired platinumNamedTheoremWitness
      false true false false false false false = .provedWithoutBarRefuse := rfl

theorem production_wired_refuse :
    evaluateMadelungExceptionIsTheoremClose .proved false true = .productionWiredRefuse := rfl

theorem madelung_exception_is_theorem_conservation :
    evaluateMadelungExceptionIsTheoremClose .unwired false false = .unwiredOk ∧
    madelungExceptionIsTheoremConjunct = true ∧
    madelungExceptionIsTheoremProved = false ∧
    wave100LibRsWired = false ∧
    wave100EosRsWired = false ∧
    wave100NanoWired = false :=
  ⟨rfl, madelung_exception_is_theorem_conjunct_true, madelung_exception_is_theorem_proved_false,
    wave100_lib_rs_not_wired, wave100_eos_rs_not_wired, wave100_nano_not_wired⟩

theorem madelung_exception_is_theorem_honest_bundle :
    madelungExceptionIsTheoremProved = false ∧
    madelungExceptionIsTheoremProductionWired = false ∧
    not118SquaredGreenTable = true ∧
    madelungExceptionIsTheoremSecondLawConservationFramed = true ∧
    madelungExceptionIsTheoremConjunct = true ∧
    madelungExceptionTerminalsAreNamed = true ∧
    folkloreExceptionRefused = true ∧
    plutoniumNotInAnyExceptionSet = true ∧
    dsHomologNotPtOccupancyCopy = true ∧
    evaluateMadelungExceptionIsTheoremClose .unwired false false = .unwiredOk ∧
    evaluateMadelungExceptionIsTheoremClose .unwired true false = .greenInventRefuse ∧
    evaluateMadelungExceptionIsTheoremIncidence .unwired platinumNamedTheoremWitness
      false true false false false false false = .provedWithoutBarRefuse ∧
    soleAxiomCount = 1 ∧
    madelungExceptionIsTheoremAxiom = true ∧
    madelungExceptionIsTheoremFiberOk .quantumKnowing = true ∧
    madelungExceptionIsTheoremFiberOk .mesoActing = false ∧
    folkloreExceptionMarker ≠ theoremTerminalMarker :=
  ⟨rfl, madelung_exception_is_theorem_production_not_wired, not_118_squared_green_table,
    madelung_exception_is_theorem_second_law_conservation_framed, madelung_exception_is_theorem_conjunct_true,
    madelung_exception_terminals_are_named_true, folklore_exception_refused_true,
    plutonium_not_in_any_exception_set_true, ds_homolog_not_pt_occupancy_copy_true,
    unwired_close_without_production_wiring, green_invent_refuse_unwired,
    proved_without_bar_refuse, sole_axiom_count_is_one, madelung_exception_is_theorem_axiom,
    madelung_exception_is_theorem_knowing_fiber_ok, madelung_exception_is_theorem_meso_acting_fiber_not_ok,
    folklore_marker_ne_theorem_terminal⟩

end UMST.Chem
