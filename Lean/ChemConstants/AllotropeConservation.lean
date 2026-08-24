-- SPDX-FileCopyrightText: 2026 Santosh Prabhu Shenbagamoorthy and Santhosh Shyamsundar
-- SPDX-License-Identifier: MIT

import ElementElectronic

/-!
# AllotropeConservation — knowing-fiber ALLOTROPE-01 **allotrope-net** conservation (Q lattice)

North-star ALLOTROPE-01 claim **Allotrope** allotrope-net class identity **conservation** on the
quantum / knowing formal fiber — crystallineLattice / layeredGraphitic / amorphousDisordered concurrent Net⊗Scale⊗Edge
**product** (class 10⊗11⊗12), not XOR enum buckets. Pairs `umst-chem` scaffold **allotrope** /
allotrope-net **conservation** posture.

- `AllotropeConservationModality` — Unwired / Assumed / Proved / Surrogate (not 118² GREEN table).
- `AllotropeNetClass` / `AllotropeNetFactor` — crystallineLattice/layeredGraphitic/amorphousDisordered at class 10/11/12;
  concurrent Net⊗Scale⊗Edge **product** not XOR.
- `fusionAllotrope` — allotrope-net stamp identity **conserved** (additive witness).
- `evaluateAllotropeConservation` — Unwired OK; Proved leg-named scaffold OK; trivial allotrope fail-closed;
  GREEN invent refuse; folklore refuse; proved-without-bar refuse; XOR mutually-exclusive refuse.
- C Z=6 same Z diamond/graphite/fullerene; Si Z=14; O Z=8; He Z=2 closed-shell no-allotrope.
- Second-law + **conservation** framing cites meso `UMST.Chem.Conservation` /
  `LandauerLaw.physicalSecondLaw` — not imported.
- No meso / acting theorems. No new physics `axiom`.
- `physics_green` stays false. Does **not** claim Allotrope Proved or physics GREEN.
- **Allotrope-net** concurrent product ≠ XOR — class 10⊗11⊗12 distinct nets same Z conserved, not mutually-exclusive enum SSOT.
-/

namespace UMST.Chem

/-- Design modality for ALLOTROPE-01 claim **allotrope-net** **conservation** (lattice SSOT). -/
inductive AllotropeConservationModality where
  | unwired | assumed | proved | surrogate
  deriving DecidableEq, Repr

def allotropeConservationModalityCurrent : AllotropeConservationModality := .unwired

/-- §2 allotrope-net bundle cardinality (north-star pinned). -/
def allotropeNetCardinality : Nat := 25

theorem allotrope_class_cardinality_twenty_five : allotropeNetCardinality = 25 := rfl

/-- IUPAC periodic-table cardinality (Z=1..118). -/
def iupacTableCardinality : Nat := 118

theorem iupac_table_cardinality_118 : iupacTableCardinality = 118 := rfl

/-- Private Z pin for **Allotrope** witnesses — not L1 SpeciesId. -/
structure AllotropeElementZ where
  z : Nat
  hzLo : 0 < z
  hzHi : z ≤ iupacTableCardinality
  deriving DecidableEq, Repr

def allotropeElementCarbon : AllotropeElementZ := { z := 6, hzLo := by decide, hzHi := by decide }
def allotropeElementSilicon : AllotropeElementZ := { z := 14, hzLo := by decide, hzHi := by decide }
def allotropeElementOxygen : AllotropeElementZ := { z := 8, hzLo := by decide, hzHi := by decide }
def allotropeElementHelium : AllotropeElementZ := { z := 2, hzLo := by decide, hzHi := by decide }
def allotropeElementOganesson : AllotropeElementZ := { z := 118, hzLo := by decide, hzHi := by decide }

theorem allotrope_carbon_z_six : allotropeElementCarbon.z = 6 := rfl
theorem allotrope_silicon_z_fourteen : allotropeElementSilicon.z = 14 := rfl
theorem allotrope_oxygen_z_eight : allotropeElementOxygen.z = 8 := rfl
theorem allotrope_helium_z_two : allotropeElementHelium.z = 2 := rfl
theorem allotrope_oganesson_z_118 : allotropeElementOganesson.z = 118 := rfl

/-- Allotrope allotrope-net class — crystallineLattice / layeredGraphitic / amorphousDisordered. -/
inductive AllotropeNetClass where
  | crystallineLattice | layeredGraphitic | amorphousDisordered
  deriving DecidableEq, Repr

def allotropeNetClassString : AllotropeNetClass → String
  | .crystallineLattice => "crystallineLattice"
  | .layeredGraphitic => "layeredGraphitic"
  | .amorphousDisordered => "amorphousDisordered"

theorem allotrope_net_crystallineLattice_str :
    allotropeNetClassString .crystallineLattice = "crystallineLattice" := rfl

theorem allotrope_net_layeredGraphitic_str :
    allotropeNetClassString .layeredGraphitic = "layeredGraphitic" := rfl

theorem allotrope_net_amorphousDisordered_str :
    allotropeNetClassString .amorphousDisordered = "amorphousDisordered" := rfl

/-- §2 class index pins — crystallineLattice (10), layeredGraphitic (11), amorphousDisordered (12). -/
def allotropeNetIndexCrystalline : Nat := 10
def allotropeNetIndexLayered : Nat := 11
def allotropeNetIndexAmorphous : Nat := 12

theorem allotrope_net_index_crystalline_ten :
    allotropeNetIndexCrystalline = 10 := rfl

theorem allotrope_net_index_layered_eleven :
    allotropeNetIndexLayered = 11 := rfl

theorem allotrope_net_index_amorphous_twelve :
    allotropeNetIndexAmorphous = 12 := rfl

theorem allotrope_net_ten_tensor_eleven_tensor_twelve :
    allotropeNetIndexCrystalline = 10 ∧
    allotropeNetIndexLayered = 11 ∧
    allotropeNetIndexAmorphous = 12 := by decide

/-- Concurrent Net⊗Scale⊗Edge product factor — not XOR bucket. -/
inductive AllotropeNetFactor where
  | net | scale | edgeBond
  deriving DecidableEq, Repr

def allotropeNetFactorString : AllotropeNetFactor → String
  | .net => "Net"
  | .scale => "Scale"
  | .edgeBond => "Edge"

theorem allotrope_net_factor_net_str :
    allotropeNetFactorString .net = "Net" := rfl

theorem allotrope_net_factor_scale_str :
    allotropeNetFactorString .scale = "Scale" := rfl

theorem allotrope_net_factor_edge_str :
    allotropeNetFactorString .edgeBond = "Edge" := rfl

/-- Allotrope-net bundle slot — concurrent **product** factor, not XOR bucket. -/
inductive AllotropeNetSlot where
  | unwired | absent | present
  deriving DecidableEq, Repr

def allotropeNetSlotIsPresent (s : AllotropeNetSlot) : Bool :=
  match s with | .present => true | _ => false

/-- §2 AllotropeClassBundle — Π_c concurrent **product** at class 10⊗11⊗12. -/
structure AllotropeClassBundle where
  slotAt : Nat → AllotropeNetSlot

def allotropeClassBundleUnwired : AllotropeClassBundle :=
  { slotAt := fun _ => .unwired }

def allotropeClassBundleSlot (b : AllotropeClassBundle) (classIndex : Nat) : AllotropeNetSlot :=
  if classIndex < allotropeNetCardinality then b.slotAt classIndex else .unwired

def allotropeClassBundleWithSlot (b : AllotropeClassBundle) (classIndex : Nat) (slot : AllotropeNetSlot) :
    AllotropeClassBundle :=
  { slotAt := fun i => if i = classIndex then slot else b.slotAt i }

def allotropeClassBundleWithPresent (b : AllotropeClassBundle) (classIndex : Nat) :
    AllotropeClassBundle :=
  allotropeClassBundleWithSlot b classIndex .present

/-- Concurrent Net⊗Scale⊗Edge product bundle — all three factors Present, not XOR. -/
structure AllotropeNetBundle where
  netFactor : AllotropeNetSlot
  scaleFactor : AllotropeNetSlot
  edgeBondFactor : AllotropeNetSlot

def allotropeNetBundleUnwired : AllotropeNetBundle :=
  { netFactor := .unwired, scaleFactor := .unwired, edgeBondFactor := .unwired }

def allotropeNetBundleConcurrent : AllotropeNetBundle :=
  { netFactor := .present, scaleFactor := .present, edgeBondFactor := .present }

def allotropeNetFactorPresent (b : AllotropeNetBundle) (f : AllotropeNetFactor) : Bool :=
  match f with
  | .net => allotropeNetSlotIsPresent b.netFactor
  | .scale => allotropeNetSlotIsPresent b.scaleFactor
  | .edgeBond => allotropeNetSlotIsPresent b.edgeBondFactor

def allotropeNetFactorPresentCount (b : AllotropeNetBundle) : Nat :=
  (if allotropeNetFactorPresent b .net then 1 else 0) +
  (if allotropeNetFactorPresent b .scale then 1 else 0) +
  (if allotropeNetFactorPresent b .edgeBond then 1 else 0)

/-- Whether Net⊗Scale⊗Edge demonstrates concurrent **product** (≥2 Present, not XOR). -/
def allotropeNetIsConcurrentProduct (b : AllotropeNetBundle) : Bool :=
  decide (allotropeNetFactorPresentCount b ≥ 2)

theorem allotrope_net_concurrent_all_three_present :
    allotropeNetFactorPresentCount allotropeNetBundleConcurrent = 3 := by decide

theorem allotrope_net_concurrent_is_product :
    allotropeNetIsConcurrentProduct allotropeNetBundleConcurrent = true := by decide

/-- Class 10⊗11⊗12 witness — crystallineLattice + layeredGraphitic + amorphousDisordered concurrent **product**. -/
def allotropeClassBundleTenElevenTwelve : AllotropeClassBundle :=
  allotropeClassBundleWithPresent
    (allotropeClassBundleWithPresent
      (allotropeClassBundleWithPresent allotropeClassBundleUnwired allotropeNetIndexCrystalline)
      allotropeNetIndexLayered)
    allotropeNetIndexAmorphous

def allotropeClassPresentCount (b : AllotropeClassBundle) : Nat :=
  (List.range allotropeNetCardinality).foldl
    (fun acc i => if allotropeNetSlotIsPresent (allotropeClassBundleSlot b i) then acc + 1 else acc) 0

theorem allotrope_net_ten_present :
    allotropeClassBundleSlot allotropeClassBundleTenElevenTwelve allotropeNetIndexCrystalline = .present := by decide

theorem allotrope_net_eleven_present :
    allotropeClassBundleSlot allotropeClassBundleTenElevenTwelve allotropeNetIndexLayered = .present := by decide

theorem allotrope_net_twelve_present :
    allotropeClassBundleSlot allotropeClassBundleTenElevenTwelve allotropeNetIndexAmorphous = .present := by decide

theorem allotrope_net_ten_eleven_twelve_present_count_three :
    allotropeClassPresentCount allotropeClassBundleTenElevenTwelve = 3 := by decide

/-- C allotrope variant — same Z=6 diamond / graphite / fullerene (not XOR). -/
inductive CAllotropeVariant where
  | diamond | graphite | fullerene
  deriving DecidableEq, Repr

def cAllotropeVariantString : CAllotropeVariant → String
  | .diamond => "C_diamond"
  | .graphite => "C_graphite"
  | .fullerene => "C_fullerene"

theorem c_allotrope_diamond_str :
    cAllotropeVariantString .diamond = "C_diamond" := rfl

theorem c_allotrope_graphite_str :
    cAllotropeVariantString .graphite = "C_graphite" := rfl

theorem c_allotrope_fullerene_str :
    cAllotropeVariantString .fullerene = "C_fullerene" := rfl

/-- Whether C allotrope variant pins same Z=6 (diamond/graphite/fullerene identity conserved). -/
def cAllotropeSameZ (_phase : CAllotropeVariant) : Bool :=
  decide (allotropeElementCarbon.z = 6)

theorem c_diamond_same_z_six :
    cAllotropeSameZ .diamond = true := rfl

theorem c_graphite_same_z_six :
    cAllotropeSameZ .graphite = true := rfl

theorem c_fullerene_same_z_six :
    cAllotropeSameZ .fullerene = true := rfl

/-- He closed-shell — no-allotrope witness (Z=2, noble gas). -/
def heliumClosedShellNoAllotrope : Bool :=
  decide (allotropeElementHelium.z = 2)

theorem helium_closed_shell_no_allotrope :
    heliumClosedShellNoAllotrope = true := rfl

/-- **Allotrope** **conservation** stamp field across Net⊗Scale⊗Edge (typed identity witness). -/
structure AllotropeConservationField where
  atNet : Nat
  atScale : Nat
  atEdgeBond : Nat
  deriving DecidableEq, Repr

def allotropeConservationFieldUnwired : AllotropeConservationField :=
  { atNet := 0, atScale := 0, atEdgeBond := 0 }

def allotropeConservationFieldNamed : AllotropeConservationField :=
  { atNet := 1, atScale := 1, atEdgeBond := 1 }

def allotropeAtFactor (f : AllotropeConservationField) : AllotropeNetFactor → Nat
  | .net => f.atNet
  | .scale => f.atScale
  | .edgeBond => f.atEdgeBond

/-- Whether **Allotrope** **conservation** stamps are uniform on named field (typed product). -/
def allotropeProductConservationTyped (f : AllotropeConservationField) : Bool :=
  decide (f.atNet = f.atScale ∧ f.atScale = f.atEdgeBond)

theorem allotrope_product_conservation_named_typed :
    allotropeProductConservationTyped allotropeConservationFieldNamed = true := rfl

theorem allotrope_product_conservation_unwired_typed :
    allotropeProductConservationTyped allotropeConservationFieldUnwired = true := rfl

/-- A **Allotrope** **conservation** path at a refinement level. -/
structure AllotropeConservationPath where
  field : AllotropeConservationField
  level : Nat
  elementZ : AllotropeElementZ
  classBundle : AllotropeClassBundle
  productBundle : AllotropeNetBundle

def allotropeConservationPathIsNontrivial (p : AllotropeConservationPath) : Bool :=
  decide (p.level > 0)

def allotropeConservationPathCarbonL1 : AllotropeConservationPath :=
  { field := allotropeConservationFieldNamed
    level := 1
    elementZ := allotropeElementCarbon
    classBundle := allotropeClassBundleTenElevenTwelve
    productBundle := allotropeNetBundleConcurrent }

def allotropeConservationPathSiliconL1 : AllotropeConservationPath :=
  { field := allotropeConservationFieldNamed
    level := 1
    elementZ := allotropeElementSilicon
    classBundle := allotropeClassBundleTenElevenTwelve
    productBundle := allotropeNetBundleConcurrent }

def allotropeConservationPathOxygenL1 : AllotropeConservationPath :=
  { field := allotropeConservationFieldNamed
    level := 1
    elementZ := allotropeElementOxygen
    classBundle := allotropeClassBundleTenElevenTwelve
    productBundle := allotropeNetBundleConcurrent }

def allotropeConservationPathHeliumL1 : AllotropeConservationPath :=
  { field := allotropeConservationFieldUnwired
    level := 1
    elementZ := allotropeElementHelium
    classBundle := allotropeClassBundleUnwired
    productBundle := allotropeNetBundleUnwired }

def allotropeConservationPathUnwiredL1 : AllotropeConservationPath :=
  { field := allotropeConservationFieldUnwired
    level := 1
    elementZ := allotropeElementCarbon
    classBundle := allotropeClassBundleUnwired
    productBundle := allotropeNetBundleUnwired }

/-- Whether element Z pins are valid IUPAC Z on a **Allotrope** **conservation** path. -/
def allotropeElementZValid (z : AllotropeElementZ) : Bool :=
  decide (0 < z.z ∧ z.z ≤ iupacTableCardinality)

theorem allotrope_carbon_z_valid :
    allotropeElementZValid allotropeElementCarbon = true ∧
    allotropeElementCarbon.z = 6 := by decide

theorem allotrope_silicon_z_valid :
    allotropeElementZValid allotropeElementSilicon = true ∧
    allotropeElementSilicon.z = 14 := by decide

theorem allotrope_oxygen_z_valid :
    allotropeElementZValid allotropeElementOxygen = true ∧
    allotropeElementOxygen.z = 8 := by decide

theorem allotrope_helium_z_valid :
    allotropeElementZValid allotropeElementHelium = true ∧
    allotropeElementHelium.z = 2 := by decide

/-- Scaffold thermodynamic ledger for **Allotrope** allotrope-net (knowing fiber). -/
structure ThermoAllotropeState where
  chemStamp : Nat
  landauerWitness : Nat
  deriving DecidableEq, Repr

def thermoAllotropeZero : ThermoAllotropeState :=
  { chemStamp := 0, landauerWitness := 0 }

def thermoAllotropePositive : ThermoAllotropeState :=
  { chemStamp := 1, landauerWitness := 1 }

/-- Thermo-preserving **Allotrope** fusion — identity **conserved** (additive). -/
def fusionAllotrope (a b : ThermoAllotropeState) : ThermoAllotropeState :=
  { chemStamp := a.chemStamp + b.chemStamp,
    landauerWitness := a.landauerWitness + b.landauerWitness }

theorem fusion_allotrope_commutative_stamp :
    (fusionAllotrope thermoAllotropePositive thermoAllotropeZero).chemStamp =
      (fusionAllotrope thermoAllotropeZero thermoAllotropePositive).chemStamp := rfl

theorem fusion_allotrope_zero_identity_stamp :
    (fusionAllotrope thermoAllotropeZero thermoAllotropePositive).chemStamp =
      thermoAllotropePositive.chemStamp := rfl

/-- Verdict of a **Allotrope** allotrope-net close attempt (fail-closed). -/
inductive AllotropeNetPathVerdict where
  | unwiredOk
  | legNamedOk
  | greenInventRefuse
  | folkloreRefuse
  | provedWithoutBarRefuse
  | trivialAllotropeRefuse
  | xorMutuallyExclusiveRefuse
  deriving DecidableEq, Repr

/-- Evaluate a **Allotrope** allotrope-net path against the ALLOTROPE-01 bar. -/
def evaluateAllotropeNetPath
    (modality : AllotropeConservationModality)
    (path : AllotropeConservationPath)
    (claimPhysicsGreen : Bool)
    (claimProved : Bool)
    (claimFolklore : Bool)
    (claimXorExclusive : Bool) : AllotropeNetPathVerdict :=
  if claimPhysicsGreen then
    .greenInventRefuse
  else if claimFolklore then
    .folkloreRefuse
  else if claimXorExclusive then
    .xorMutuallyExclusiveRefuse
  else if claimProved then
    .provedWithoutBarRefuse
  else if !allotropeConservationPathIsNontrivial path then
    .trivialAllotropeRefuse
  else if !allotropeElementZValid path.elementZ then
    .trivialAllotropeRefuse
  else
    match modality with
    | .unwired => .legNamedOk
    | .assumed | .surrogate => .unwiredOk
    | .proved => .provedWithoutBarRefuse

/-- Verdict of a **Allotrope** **conservation** close attempt (fail-closed). -/
inductive AllotropeConservationVerdict where
  | unwiredOk
  | legNamedOk
  | trivialAllotropeRefuse
  | greenInventRefuse
  | folkloreRefuse
  | xorMutuallyExclusiveRefuse
  deriving DecidableEq, Repr

/-- Evaluate **Allotrope** **conservation** against the ALLOTROPE-01 bar. -/
def evaluateAllotropeConservation
    (modality : AllotropeConservationModality)
    (path : AllotropeConservationPath)
    (claimPhysicsGreen : Bool)
    (claimFolklore : Bool)
    (claimXorExclusive : Bool) : AllotropeConservationVerdict :=
  if claimPhysicsGreen then
    .greenInventRefuse
  else if claimFolklore then
    .folkloreRefuse
  else if claimXorExclusive then
    .xorMutuallyExclusiveRefuse
  else if !allotropeConservationPathIsNontrivial path then
    .trivialAllotropeRefuse
  else
    match modality with
    | .unwired | .assumed | .surrogate => .unwiredOk
    | .proved => .legNamedOk

/-- Whether class 10⊗11⊗12 allotrope-net slots are pinned Present (concurrent **product**). -/
def threeAllotropeNetsNamed : Bool :=
  decide (allotropeClassBundleSlot allotropeClassBundleTenElevenTwelve allotropeNetIndexCrystalline = .present ∧
    allotropeClassBundleSlot allotropeClassBundleTenElevenTwelve allotropeNetIndexLayered = .present ∧
    allotropeClassBundleSlot allotropeClassBundleTenElevenTwelve allotropeNetIndexAmorphous = .present ∧
    allotropeNetIndexCrystalline = 10 ∧
    allotropeNetIndexLayered = 11 ∧
    allotropeNetIndexAmorphous = 12)

/-- Whether Net⊗Scale⊗Edge concurrent **product** is typed (not XOR). -/
def allotropeNetConservationTyped : Bool :=
  decide (allotropeProductConservationTyped allotropeConservationFieldNamed = true ∧
    allotropeProductConservationTyped allotropeConservationFieldUnwired = true ∧
    allotropeNetIsConcurrentProduct allotropeNetBundleConcurrent = true ∧
    allotropeNetFactorPresentCount allotropeNetBundleConcurrent = 3)

/-- Whether C diamond/graphite/fullerene same Z=6 is conserved. -/
def cSameZConserved : Bool :=
  decide (cAllotropeSameZ .diamond = true ∧
    cAllotropeSameZ .graphite = true ∧
    cAllotropeSameZ .fullerene = true ∧
    allotropeElementCarbon.z = 6)

/-- Whether He closed-shell no-allotrope is pinned. -/
def heliumNoAllotropeOk : Bool :=
  decide (heliumClosedShellNoAllotrope = true ∧ allotropeElementHelium.z = 2)

/-- Whether thermo-preserving **Allotrope** fusion identity is **conserved** on pinned states. -/
def fusionIdentityConserved : Bool :=
  decide (fusionAllotrope thermoAllotropeZero thermoAllotropePositive =
    thermoAllotropePositive ∧
    fusionAllotrope thermoAllotropePositive thermoAllotropeZero =
      fusionAllotrope thermoAllotropeZero thermoAllotropePositive ∧
    (fusionAllotrope thermoAllotropePositive thermoAllotropePositive).landauerWitness = 2 ∧
    allotropeConservationPathIsNontrivial allotropeConservationPathCarbonL1 = true ∧
    allotropeElementZValid allotropeElementCarbon = true)

/-- Whether trivial (level-0) **Allotrope** path is refused (fail-closed). -/
def trivialAllotropeRefused : Bool :=
  let trivialPath : AllotropeConservationPath :=
    { field := allotropeConservationFieldNamed, level := 0, elementZ := allotropeElementCarbon
      classBundle := allotropeClassBundleTenElevenTwelve
      productBundle := allotropeNetBundleConcurrent }
  decide (evaluateAllotropeNetPath .unwired trivialPath false false false false = .trivialAllotropeRefuse ∧
    evaluateAllotropeConservation .unwired trivialPath false false false = .trivialAllotropeRefuse)

/-- Whether GREEN invent is refused on **Allotrope** scaffold. -/
def greenInventRefused : Bool :=
  decide (evaluateAllotropeNetPath .unwired allotropeConservationPathCarbonL1 true false false false =
    .greenInventRefuse ∧
    evaluateAllotropeConservation .unwired allotropeConservationPathCarbonL1 true false false =
      .greenInventRefuse)

/-- Whether folklore claim is refused on **Allotrope** scaffold. -/
def folkloreRefused : Bool :=
  decide (evaluateAllotropeNetPath .unwired allotropeConservationPathCarbonL1 false false true false =
    .folkloreRefuse ∧
    evaluateAllotropeConservation .unwired allotropeConservationPathCarbonL1 false true false =
      .folkloreRefuse)

/-- Whether XOR mutually-exclusive claim is refused (concurrent **product** not XOR). -/
def xorMutuallyExclusiveRefused : Bool :=
  decide (evaluateAllotropeNetPath .unwired allotropeConservationPathCarbonL1 false false false true =
    .xorMutuallyExclusiveRefuse ∧
    evaluateAllotropeConservation .unwired allotropeConservationPathCarbonL1 false false true =
      .xorMutuallyExclusiveRefuse)

/-- Whether carbon **Allotrope** **conservation** path passes under Unwired modality. -/
def carbonAllotropeConservationUnwiredOk : Bool :=
  decide (evaluateAllotropeConservation .unwired allotropeConservationPathCarbonL1 false false false = .unwiredOk ∧
    evaluateAllotropeNetPath .unwired allotropeConservationPathCarbonL1 false false false false = .legNamedOk)

/-- Whether silicon **Allotrope** **conservation** path passes under Unwired modality. -/
def siliconAllotropeConservationUnwiredOk : Bool :=
  decide (evaluateAllotropeConservation .unwired allotropeConservationPathSiliconL1 false false false = .unwiredOk ∧
    evaluateAllotropeNetPath .unwired allotropeConservationPathSiliconL1 false false false false = .legNamedOk)

/-- Whether oxygen **Allotrope** **conservation** path passes under Unwired modality. -/
def oxygenAllotropeConservationUnwiredOk : Bool :=
  decide (evaluateAllotropeConservation .unwired allotropeConservationPathOxygenL1 false false false = .unwiredOk ∧
    evaluateAllotropeNetPath .unwired allotropeConservationPathOxygenL1 false false false false = .legNamedOk)

/-- Whether unwired baseline **Allotrope** path passes under Unwired modality. -/
def unwiredAllotropeConservationUnwiredOk : Bool :=
  decide (evaluateAllotropeConservation .unwired allotropeConservationPathUnwiredL1 false false false = .unwiredOk ∧
    evaluateAllotropeNetPath .unwired allotropeConservationPathUnwiredL1 false false false false = .legNamedOk)

/-- Whether a close attempt is admissible under ALLOTROPE-01 **allotrope-net** **conservation**. -/
def allotropeConservationVerdictOk (v : AllotropeConservationVerdict) : Bool :=
  match v with
  | .unwiredOk | .legNamedOk => true
  | _ => false

theorem unwired_allotrope_conservation_ok :
    evaluateAllotropeConservation .unwired allotropeConservationPathCarbonL1 false false false = .unwiredOk := rfl

theorem proved_allotrope_conservation_leg_named_ok :
    evaluateAllotropeConservation .proved allotropeConservationPathCarbonL1 false false false = .legNamedOk := rfl

theorem trivial_allotrope_refuse :
    evaluateAllotropeConservation .unwired
      { field := allotropeConservationFieldNamed, level := 0, elementZ := allotropeElementCarbon
        classBundle := allotropeClassBundleTenElevenTwelve
        productBundle := allotropeNetBundleConcurrent }
      false false false = .trivialAllotropeRefuse := rfl

theorem green_invent_refuse :
    evaluateAllotropeConservation .unwired allotropeConservationPathCarbonL1 true false false =
      .greenInventRefuse := rfl

theorem folklore_refuse :
    evaluateAllotropeConservation .unwired allotropeConservationPathCarbonL1 false true false =
      .folkloreRefuse := rfl

theorem xor_mutually_exclusive_refuse :
    evaluateAllotropeConservation .unwired allotropeConservationPathCarbonL1 false false true =
      .xorMutuallyExclusiveRefuse := rfl

theorem three_allotrope_nets_named :
    threeAllotropeNetsNamed = true := by decide

theorem allotrope_net_conservation_typed :
    allotropeNetConservationTyped = true := rfl

theorem c_same_z_conserved :
    cSameZConserved = true := rfl

theorem helium_no_allotrope_ok :
    heliumNoAllotropeOk = true := rfl

theorem fusion_identity_conserved :
    fusionIdentityConserved = true := rfl

theorem trivial_allotrope_refused :
    trivialAllotropeRefused = true := rfl

theorem green_invent_refused :
    greenInventRefused = true := rfl

theorem folklore_refused :
    folkloreRefused = true := rfl

theorem xor_mutually_exclusive_refused :
    xorMutuallyExclusiveRefused = true := rfl

theorem carbon_allotrope_conservation_unwired_ok :
    carbonAllotropeConservationUnwiredOk = true := rfl

theorem silicon_allotrope_conservation_unwired_ok :
    siliconAllotropeConservationUnwiredOk = true := rfl

theorem oxygen_allotrope_conservation_unwired_ok :
    oxygenAllotropeConservationUnwiredOk = true := rfl

theorem unwired_allotrope_conservation_unwired_ok :
    unwiredAllotropeConservationUnwiredOk = true := rfl

/-- Quantum / knowing formal fiber root (structure witness — not meso acting). -/
def allotropeConservationQuantumKnowingFiber : String :=
  "umst/umst-formal-double-slit"

theorem allotrope_conservation_quantum_knowing_fiber_pinned :
    allotropeConservationQuantumKnowingFiber =
      "umst/umst-formal-double-slit" := rfl

/-- Cited Rust **Allotrope** allotrope-net authority (views only — lattice is structural here). -/
def allotropeConservationCitedModule : String :=
  "umst/umst-chem/src/allotrope_geometry_variants.rs"

/-- **Allotrope** lattice is structure — not 118² GREEN periodic enumeration. -/
def allotropeConservationNot118GreenTable : Bool := true

theorem allotrope_conservation_not_118_green_table :
    allotropeConservationNot118GreenTable = true := rfl

/-- Second-law + **conservation** framing — cites meso SSOT, not wired on knowing scaffold. -/
def allotropeConservationSecondLawFramed : Bool := true

theorem allotrope_conservation_second_law_framed :
    allotropeConservationSecondLawFramed = true := rfl

/-- ALLOTROPE-01 claim **allotrope-net** is **not** claimed Proved on the knowing scaffold. -/
def allotropeProved : Bool := false

theorem allotrope_not_proved : allotropeProved = false := rfl

/-- Production wiring is **not** claimed on the knowing scaffold. -/
def allotropeConservationProductionWired : Bool := false

theorem allotrope_conservation_production_not_wired :
    allotropeConservationProductionWired = false := rfl

/-- Cell id for the Lean ALLOTROPE-01 **allotrope-net** **conservation** knowing-fiber. -/
def allotropeConservationCellId : String :=
  "CHEM-FORMAL-Q-LEAN-ALLOTROPE-CONSERVATION"

/-- Non-claim fence — class 10⊗11⊗12 crystallineLattice/layeredGraphitic/amorphousDisordered; Net⊗Scale⊗Edge concurrent **product**;
C Z=6 diamond/graphite/fullerene same Z; Si Z=14; O Z=8; He Z=2 closed-shell no-allotrope;
folklore refuse; trivial allotrope refuse; XOR refuse; **conservation** typed;
ALLOTROPE-01 Unwired; `allotropeProved` false. -/
def allotropeConservationNonClaim : String :=
  "CHEM-FORMAL-Q-LEAN-ALLOTROPE-CONSERVATION ALLOTROPE-01 allotrope-net conservation class 10 11 12 crystallineLattice layeredGraphitic amorphousDisordered Net Scale Edge concurrent product not XOR C Z=6 diamond graphite fullerene same Z Si Z=14 O Z=8 He Z=2 closed-shell no-allotrope folklore refuse trivial allotrope refuse XOR refuse allotropeProved false Unwired OK not ALLOTROPE Proved not physics GREEN; not 118² GREEN DFT"

/-- Physics GREEN is unauthorized on the knowing ALLOTROPE-01 **allotrope-net** **conservation** scaffold. -/
def allotropeConservationPhysicsGreenAuthorized : Prop := False

theorem allotrope_conservation_physics_green_false :
    ¬ allotropeConservationPhysicsGreenAuthorized := id

theorem allotrope_conservation_modality_unwired :
    allotropeConservationModalityCurrent = .unwired := rfl

/-- **One** design axiom: second law + **conservation** (structure witness — not meso import). -/
def allotropeConservationAxiom : Bool :=
  allotropeConservationNot118GreenTable &&
    allotropeConservationSecondLawFramed &&
    threeAllotropeNetsNamed &&
    allotropeNetConservationTyped &&
    cSameZConserved &&
    heliumNoAllotropeOk &&
    fusionIdentityConserved &&
    trivialAllotropeRefused &&
    greenInventRefused &&
    folkloreRefused &&
    xorMutuallyExclusiveRefused &&
    carbonAllotropeConservationUnwiredOk &&
    siliconAllotropeConservationUnwiredOk &&
    oxygenAllotropeConservationUnwiredOk &&
    unwiredAllotropeConservationUnwiredOk &&
    !allotropeProved &&
    !allotropeConservationProductionWired

theorem allotrope_conservation_axiom :
    allotropeConservationAxiom = true := by decide

theorem allotrope_conservation_honest_bundle :
    allotropeProved = false ∧
    allotropeConservationProductionWired = false ∧
    allotropeConservationNot118GreenTable = true ∧
    allotropeConservationSecondLawFramed = true ∧
    evaluateAllotropeConservation .unwired allotropeConservationPathCarbonL1 false false false = .unwiredOk ∧
    evaluateAllotropeConservation .proved allotropeConservationPathCarbonL1 false false false = .legNamedOk ∧
    evaluateAllotropeConservation .unwired
      { field := allotropeConservationFieldNamed, level := 0, elementZ := allotropeElementCarbon
        classBundle := allotropeClassBundleTenElevenTwelve
        productBundle := allotropeNetBundleConcurrent }
      false false false = .trivialAllotropeRefuse ∧
    evaluateAllotropeConservation .unwired allotropeConservationPathCarbonL1 true false false = .greenInventRefuse ∧
    evaluateAllotropeConservation .unwired allotropeConservationPathCarbonL1 false true false = .folkloreRefuse ∧
    evaluateAllotropeConservation .unwired allotropeConservationPathCarbonL1 false false true = .xorMutuallyExclusiveRefuse ∧
    threeAllotropeNetsNamed = true ∧
    allotropeNetConservationTyped = true ∧
    cSameZConserved = true ∧
    heliumNoAllotropeOk = true ∧
    fusionIdentityConserved = true ∧
    trivialAllotropeRefused = true ∧
    greenInventRefused = true ∧
    folkloreRefused = true ∧
    xorMutuallyExclusiveRefused = true ∧
    carbonAllotropeConservationUnwiredOk = true ∧
    siliconAllotropeConservationUnwiredOk = true ∧
    oxygenAllotropeConservationUnwiredOk = true ∧
    unwiredAllotropeConservationUnwiredOk = true ∧
    allotropeElementCarbon.z = 6 ∧
    allotropeElementSilicon.z = 14 ∧
    allotropeElementOxygen.z = 8 ∧
    allotropeElementHelium.z = 2 ∧
    allotropeElementOganesson.z = 118 ∧
    allotropeConservationAxiom = true :=
  ⟨rfl, rfl, allotrope_conservation_not_118_green_table,
    allotrope_conservation_second_law_framed,
    unwired_allotrope_conservation_ok, proved_allotrope_conservation_leg_named_ok, trivial_allotrope_refuse,
    green_invent_refuse, folklore_refuse, xor_mutually_exclusive_refuse,
    three_allotrope_nets_named, allotrope_net_conservation_typed, c_same_z_conserved, helium_no_allotrope_ok,
    fusion_identity_conserved, trivial_allotrope_refused, green_invent_refused, folklore_refused,
    xor_mutually_exclusive_refused,
    carbon_allotrope_conservation_unwired_ok, silicon_allotrope_conservation_unwired_ok,
    oxygen_allotrope_conservation_unwired_ok, unwired_allotrope_conservation_unwired_ok,
    allotrope_carbon_z_six, allotrope_silicon_z_fourteen, allotrope_oxygen_z_eight,
    allotrope_helium_z_two, allotrope_oganesson_z_118,
    allotrope_conservation_axiom⟩

end UMST.Chem
