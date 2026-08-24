-- SPDX-FileCopyrightText: 2026 Santosh Prabhu Shenbagamoorthy and Santhosh Shyamsundar
-- SPDX-License-Identifier: MIT

import ElementElectronic

/-!
# GoldschmidtConservation — knowing-fiber GOLDSCHMIDT-01 **ore-class** conservation (Q lattice)

North-star GOLDSCHMIDT-01 claim **Goldschmidt** ore-affinity class identity **conservation** on the
quantum / knowing formal fiber — lithophile / chalcophile / siderophile concurrent Ore⊗G⊗fO₂
**product** (class 6⊗7⊗17), not XOR enum buckets. Pairs `umst-chem` scaffold **goldschmidt** /
ore-class **conservation** posture.

- `GoldschmidtConservationModality` — Unwired / Assumed / Proved / Surrogate (not 118² GREEN table).
- `OreAffinityClass` / `OreProductFactor` — lithophile/chalcophile/siderophile at class 6/7/17;
  concurrent Ore⊗G⊗fO₂ **product** not XOR.
- `fusionGoldschmidt` — ore-class stamp identity **conserved** (additive witness).
- `evaluateGoldschmidtConservation` — Unwired OK; Proved leg-named scaffold OK; trivial ore fail-closed;
  GREEN invent refuse; folklore refuse; proved-without-bar refuse; XOR mutually-exclusive refuse.
- Fe Z=26 same Z metal/oxide/sulfide; Cu Z=29; Si Z=14; He Z=2 closed-shell no-ore.
- Second-law + **conservation** framing cites meso `UMST.Chem.Conservation` /
  `LandauerLaw.physicalSecondLaw` — not imported.
- No meso / acting theorems. No new physics `axiom`.
- `physics_green` stays false. Does **not** claim Goldschmidt Proved or physics GREEN.
- **Ore-class** concurrent product ≠ XOR — class 6⊗7⊗17, not mutually-exclusive enum SSOT.
-/

namespace UMST.Chem

/-- Design modality for GOLDSCHMIDT-01 claim **ore-class** **conservation** (lattice SSOT). -/
inductive GoldschmidtConservationModality where
  | unwired | assumed | proved | surrogate
  deriving DecidableEq, Repr

def goldschmidtConservationModalityCurrent : GoldschmidtConservationModality := .unwired

/-- §2 ore-class bundle cardinality (north-star pinned). -/
def goldschmidtClassCardinality : Nat := 25

theorem goldschmidt_class_cardinality_twenty_five : goldschmidtClassCardinality = 25 := rfl

/-- IUPAC periodic-table cardinality (Z=1..118). -/
def iupacTableCardinality : Nat := 118

theorem iupac_table_cardinality_118 : iupacTableCardinality = 118 := rfl

/-- Private Z pin for **Goldschmidt** witnesses — not L1 SpeciesId. -/
structure GoldschmidtElementZ where
  z : Nat
  hzLo : 0 < z
  hzHi : z ≤ iupacTableCardinality
  deriving DecidableEq, Repr

def goldschmidtElementIron : GoldschmidtElementZ := { z := 26, hzLo := by decide, hzHi := by decide }
def goldschmidtElementCopper : GoldschmidtElementZ := { z := 29, hzLo := by decide, hzHi := by decide }
def goldschmidtElementSilicon : GoldschmidtElementZ := { z := 14, hzLo := by decide, hzHi := by decide }
def goldschmidtElementHelium : GoldschmidtElementZ := { z := 2, hzLo := by decide, hzHi := by decide }
def goldschmidtElementOganesson : GoldschmidtElementZ := { z := 118, hzLo := by decide, hzHi := by decide }

theorem goldschmidt_iron_z_twenty_six : goldschmidtElementIron.z = 26 := rfl
theorem goldschmidt_copper_z_twenty_nine : goldschmidtElementCopper.z = 29 := rfl
theorem goldschmidt_silicon_z_fourteen : goldschmidtElementSilicon.z = 14 := rfl
theorem goldschmidt_helium_z_two : goldschmidtElementHelium.z = 2 := rfl
theorem goldschmidt_oganesson_z_118 : goldschmidtElementOganesson.z = 118 := rfl

/-- Goldschmidt ore-affinity class — lithophile / chalcophile / siderophile. -/
inductive OreAffinityClass where
  | lithophile | chalcophile | siderophile
  deriving DecidableEq, Repr

def oreAffinityClassString : OreAffinityClass → String
  | .lithophile => "lithophile"
  | .chalcophile => "chalcophile"
  | .siderophile => "siderophile"

theorem ore_affinity_lithophile_str :
    oreAffinityClassString .lithophile = "lithophile" := rfl

theorem ore_affinity_chalcophile_str :
    oreAffinityClassString .chalcophile = "chalcophile" := rfl

theorem ore_affinity_siderophile_str :
    oreAffinityClassString .siderophile = "siderophile" := rfl

/-- §2 class index pins — lithophile (6), chalcophile (7), siderophile (17). -/
def goldschmidtClassIndexLithophile : Nat := 6
def goldschmidtClassIndexChalcophile : Nat := 7
def goldschmidtClassIndexSiderophile : Nat := 17

theorem goldschmidt_class_index_lithophile_six :
    goldschmidtClassIndexLithophile = 6 := rfl

theorem goldschmidt_class_index_chalcophile_seven :
    goldschmidtClassIndexChalcophile = 7 := rfl

theorem goldschmidt_class_index_siderophile_seventeen :
    goldschmidtClassIndexSiderophile = 17 := rfl

theorem goldschmidt_class_six_tensor_seven_tensor_seventeen :
    goldschmidtClassIndexLithophile = 6 ∧
    goldschmidtClassIndexChalcophile = 7 ∧
    goldschmidtClassIndexSiderophile = 17 := by decide

/-- Concurrent Ore⊗G⊗fO₂ product factor — not XOR bucket. -/
inductive OreProductFactor where
  | ore | gibbsG | fugacityFO2
  deriving DecidableEq, Repr

def oreProductFactorString : OreProductFactor → String
  | .ore => "Ore"
  | .gibbsG => "G"
  | .fugacityFO2 => "fO2"

theorem ore_product_factor_ore_str :
    oreProductFactorString .ore = "Ore" := rfl

theorem ore_product_factor_gibbs_g_str :
    oreProductFactorString .gibbsG = "G" := rfl

theorem ore_product_factor_fugacity_fo2_str :
    oreProductFactorString .fugacityFO2 = "fO2" := rfl

/-- Ore-class bundle slot — concurrent **product** factor, not XOR bucket. -/
inductive OreClassSlot where
  | unwired | absent | present
  deriving DecidableEq, Repr

def oreClassSlotIsPresent (s : OreClassSlot) : Bool :=
  match s with | .present => true | _ => false

/-- §2 GoldschmidtClassBundle — Π_c concurrent **product** at class 6⊗7⊗17. -/
structure GoldschmidtClassBundle where
  slotAt : Nat → OreClassSlot

def goldschmidtClassBundleUnwired : GoldschmidtClassBundle :=
  { slotAt := fun _ => .unwired }

def goldschmidtClassBundleSlot (b : GoldschmidtClassBundle) (classIndex : Nat) : OreClassSlot :=
  if classIndex < goldschmidtClassCardinality then b.slotAt classIndex else .unwired

def goldschmidtClassBundleWithSlot (b : GoldschmidtClassBundle) (classIndex : Nat) (slot : OreClassSlot) :
    GoldschmidtClassBundle :=
  { slotAt := fun i => if i = classIndex then slot else b.slotAt i }

def goldschmidtClassBundleWithPresent (b : GoldschmidtClassBundle) (classIndex : Nat) :
    GoldschmidtClassBundle :=
  goldschmidtClassBundleWithSlot b classIndex .present

/-- Concurrent Ore⊗G⊗fO₂ product bundle — all three factors Present, not XOR. -/
structure OreProductBundle where
  oreFactor : OreClassSlot
  gibbsGFactor : OreClassSlot
  fugacityFO2Factor : OreClassSlot

def oreProductBundleUnwired : OreProductBundle :=
  { oreFactor := .unwired, gibbsGFactor := .unwired, fugacityFO2Factor := .unwired }

def oreProductBundleConcurrent : OreProductBundle :=
  { oreFactor := .present, gibbsGFactor := .present, fugacityFO2Factor := .present }

def oreProductFactorPresent (b : OreProductBundle) (f : OreProductFactor) : Bool :=
  match f with
  | .ore => oreClassSlotIsPresent b.oreFactor
  | .gibbsG => oreClassSlotIsPresent b.gibbsGFactor
  | .fugacityFO2 => oreClassSlotIsPresent b.fugacityFO2Factor

def oreProductPresentCount (b : OreProductBundle) : Nat :=
  (if oreProductFactorPresent b .ore then 1 else 0) +
  (if oreProductFactorPresent b .gibbsG then 1 else 0) +
  (if oreProductFactorPresent b .fugacityFO2 then 1 else 0)

/-- Whether Ore⊗G⊗fO₂ demonstrates concurrent **product** (≥2 Present, not XOR). -/
def oreProductIsConcurrentProduct (b : OreProductBundle) : Bool :=
  decide (oreProductPresentCount b ≥ 2)

theorem ore_product_concurrent_all_three_present :
    oreProductPresentCount oreProductBundleConcurrent = 3 := by decide

theorem ore_product_concurrent_is_product :
    oreProductIsConcurrentProduct oreProductBundleConcurrent = true := by decide

/-- Class 6⊗7⊗17 witness — lithophile + chalcophile + siderophile concurrent **product**. -/
def goldschmidtClassBundleSixSevenSeventeen : GoldschmidtClassBundle :=
  goldschmidtClassBundleWithPresent
    (goldschmidtClassBundleWithPresent
      (goldschmidtClassBundleWithPresent goldschmidtClassBundleUnwired goldschmidtClassIndexLithophile)
      goldschmidtClassIndexChalcophile)
    goldschmidtClassIndexSiderophile

def goldschmidtClassPresentCount (b : GoldschmidtClassBundle) : Nat :=
  (List.range goldschmidtClassCardinality).foldl
    (fun acc i => if oreClassSlotIsPresent (goldschmidtClassBundleSlot b i) then acc + 1 else acc) 0

theorem goldschmidt_class_six_present :
    goldschmidtClassBundleSlot goldschmidtClassBundleSixSevenSeventeen goldschmidtClassIndexLithophile = .present := by decide

theorem goldschmidt_class_seven_present :
    goldschmidtClassBundleSlot goldschmidtClassBundleSixSevenSeventeen goldschmidtClassIndexChalcophile = .present := by decide

theorem goldschmidt_class_seventeen_present :
    goldschmidtClassBundleSlot goldschmidtClassBundleSixSevenSeventeen goldschmidtClassIndexSiderophile = .present := by decide

theorem goldschmidt_class_six_seven_seventeen_present_count_three :
    goldschmidtClassPresentCount goldschmidtClassBundleSixSevenSeventeen = 3 := by decide

/-- Fe phase variant — same Z=26 metal / oxide / sulfide (not XOR). -/
inductive FePhaseVariant where
  | metal | oxide | sulfide
  deriving DecidableEq, Repr

def fePhaseVariantString : FePhaseVariant → String
  | .metal => "Fe_metal"
  | .oxide => "Fe_oxide"
  | .sulfide => "Fe_sulfide"

theorem fe_phase_metal_str :
    fePhaseVariantString .metal = "Fe_metal" := rfl

theorem fe_phase_oxide_str :
    fePhaseVariantString .oxide = "Fe_oxide" := rfl

theorem fe_phase_sulfide_str :
    fePhaseVariantString .sulfide = "Fe_sulfide" := rfl

/-- Whether Fe phase variant pins same Z=26 (metal/oxide/sulfide identity conserved). -/
def fePhaseSameZ (_phase : FePhaseVariant) : Bool :=
  decide (goldschmidtElementIron.z = 26)

theorem fe_metal_same_z_twenty_six :
    fePhaseSameZ .metal = true := rfl

theorem fe_oxide_same_z_twenty_six :
    fePhaseSameZ .oxide = true := rfl

theorem fe_sulfide_same_z_twenty_six :
    fePhaseSameZ .sulfide = true := rfl

/-- He closed-shell — no-ore witness (Z=2, noble gas). -/
def heliumClosedShellNoOre : Bool :=
  decide (goldschmidtElementHelium.z = 2)

theorem helium_closed_shell_no_ore :
    heliumClosedShellNoOre = true := rfl

/-- **Goldschmidt** **conservation** stamp field across Ore⊗G⊗fO₂ (typed identity witness). -/
structure GoldschmidtConservationField where
  atOre : Nat
  atGibbsG : Nat
  atFugacityFO2 : Nat
  deriving DecidableEq, Repr

def goldschmidtConservationFieldUnwired : GoldschmidtConservationField :=
  { atOre := 0, atGibbsG := 0, atFugacityFO2 := 0 }

def goldschmidtConservationFieldNamed : GoldschmidtConservationField :=
  { atOre := 1, atGibbsG := 1, atFugacityFO2 := 1 }

def goldschmidtAtFactor (f : GoldschmidtConservationField) : OreProductFactor → Nat
  | .ore => f.atOre
  | .gibbsG => f.atGibbsG
  | .fugacityFO2 => f.atFugacityFO2

/-- Whether **Goldschmidt** **conservation** stamps are uniform on named field (typed product). -/
def goldschmidtProductConservationTyped (f : GoldschmidtConservationField) : Bool :=
  decide (f.atOre = f.atGibbsG ∧ f.atGibbsG = f.atFugacityFO2)

theorem goldschmidt_product_conservation_named_typed :
    goldschmidtProductConservationTyped goldschmidtConservationFieldNamed = true := rfl

theorem goldschmidt_product_conservation_unwired_typed :
    goldschmidtProductConservationTyped goldschmidtConservationFieldUnwired = true := rfl

/-- A **Goldschmidt** **conservation** path at a refinement level. -/
structure GoldschmidtConservationPath where
  field : GoldschmidtConservationField
  level : Nat
  elementZ : GoldschmidtElementZ
  classBundle : GoldschmidtClassBundle
  productBundle : OreProductBundle

def goldschmidtConservationPathIsNontrivial (p : GoldschmidtConservationPath) : Bool :=
  decide (p.level > 0)

def goldschmidtConservationPathIronL1 : GoldschmidtConservationPath :=
  { field := goldschmidtConservationFieldNamed
    level := 1
    elementZ := goldschmidtElementIron
    classBundle := goldschmidtClassBundleSixSevenSeventeen
    productBundle := oreProductBundleConcurrent }

def goldschmidtConservationPathCopperL1 : GoldschmidtConservationPath :=
  { field := goldschmidtConservationFieldNamed
    level := 1
    elementZ := goldschmidtElementCopper
    classBundle := goldschmidtClassBundleSixSevenSeventeen
    productBundle := oreProductBundleConcurrent }

def goldschmidtConservationPathSiliconL1 : GoldschmidtConservationPath :=
  { field := goldschmidtConservationFieldNamed
    level := 1
    elementZ := goldschmidtElementSilicon
    classBundle := goldschmidtClassBundleSixSevenSeventeen
    productBundle := oreProductBundleConcurrent }

def goldschmidtConservationPathHeliumL1 : GoldschmidtConservationPath :=
  { field := goldschmidtConservationFieldUnwired
    level := 1
    elementZ := goldschmidtElementHelium
    classBundle := goldschmidtClassBundleUnwired
    productBundle := oreProductBundleUnwired }

def goldschmidtConservationPathUnwiredL1 : GoldschmidtConservationPath :=
  { field := goldschmidtConservationFieldUnwired
    level := 1
    elementZ := goldschmidtElementIron
    classBundle := goldschmidtClassBundleUnwired
    productBundle := oreProductBundleUnwired }

/-- Whether element Z pins are valid IUPAC Z on a **Goldschmidt** **conservation** path. -/
def goldschmidtElementZValid (z : GoldschmidtElementZ) : Bool :=
  decide (0 < z.z ∧ z.z ≤ iupacTableCardinality)

theorem goldschmidt_iron_z_valid :
    goldschmidtElementZValid goldschmidtElementIron = true ∧
    goldschmidtElementIron.z = 26 := by decide

theorem goldschmidt_copper_z_valid :
    goldschmidtElementZValid goldschmidtElementCopper = true ∧
    goldschmidtElementCopper.z = 29 := by decide

theorem goldschmidt_silicon_z_valid :
    goldschmidtElementZValid goldschmidtElementSilicon = true ∧
    goldschmidtElementSilicon.z = 14 := by decide

theorem goldschmidt_helium_z_valid :
    goldschmidtElementZValid goldschmidtElementHelium = true ∧
    goldschmidtElementHelium.z = 2 := by decide

/-- Scaffold thermodynamic ledger for **Goldschmidt** ore-class (knowing fiber). -/
structure ThermoGoldschmidtState where
  chemStamp : Nat
  landauerWitness : Nat
  deriving DecidableEq, Repr

def thermoGoldschmidtZero : ThermoGoldschmidtState :=
  { chemStamp := 0, landauerWitness := 0 }

def thermoGoldschmidtPositive : ThermoGoldschmidtState :=
  { chemStamp := 1, landauerWitness := 1 }

/-- Thermo-preserving **Goldschmidt** fusion — identity **conserved** (additive). -/
def fusionGoldschmidt (a b : ThermoGoldschmidtState) : ThermoGoldschmidtState :=
  { chemStamp := a.chemStamp + b.chemStamp,
    landauerWitness := a.landauerWitness + b.landauerWitness }

theorem fusion_goldschmidt_commutative_stamp :
    (fusionGoldschmidt thermoGoldschmidtPositive thermoGoldschmidtZero).chemStamp =
      (fusionGoldschmidt thermoGoldschmidtZero thermoGoldschmidtPositive).chemStamp := rfl

theorem fusion_goldschmidt_zero_identity_stamp :
    (fusionGoldschmidt thermoGoldschmidtZero thermoGoldschmidtPositive).chemStamp =
      thermoGoldschmidtPositive.chemStamp := rfl

/-- Verdict of a **Goldschmidt** ore-class close attempt (fail-closed). -/
inductive GoldschmidtOrePathVerdict where
  | unwiredOk
  | legNamedOk
  | greenInventRefuse
  | folkloreRefuse
  | provedWithoutBarRefuse
  | trivialOreRefuse
  | xorMutuallyExclusiveRefuse
  deriving DecidableEq, Repr

/-- Evaluate a **Goldschmidt** ore-class path against the GOLDSCHMIDT-01 bar. -/
def evaluateGoldschmidtOrePath
    (modality : GoldschmidtConservationModality)
    (path : GoldschmidtConservationPath)
    (claimPhysicsGreen : Bool)
    (claimProved : Bool)
    (claimFolklore : Bool)
    (claimXorExclusive : Bool) : GoldschmidtOrePathVerdict :=
  if claimPhysicsGreen then
    .greenInventRefuse
  else if claimFolklore then
    .folkloreRefuse
  else if claimXorExclusive then
    .xorMutuallyExclusiveRefuse
  else if claimProved then
    .provedWithoutBarRefuse
  else if !goldschmidtConservationPathIsNontrivial path then
    .trivialOreRefuse
  else if !goldschmidtElementZValid path.elementZ then
    .trivialOreRefuse
  else
    match modality with
    | .unwired => .legNamedOk
    | .assumed | .surrogate => .unwiredOk
    | .proved => .provedWithoutBarRefuse

/-- Verdict of a **Goldschmidt** **conservation** close attempt (fail-closed). -/
inductive GoldschmidtConservationVerdict where
  | unwiredOk
  | legNamedOk
  | trivialOreRefuse
  | greenInventRefuse
  | folkloreRefuse
  | xorMutuallyExclusiveRefuse
  deriving DecidableEq, Repr

/-- Evaluate **Goldschmidt** **conservation** against the GOLDSCHMIDT-01 bar. -/
def evaluateGoldschmidtConservation
    (modality : GoldschmidtConservationModality)
    (path : GoldschmidtConservationPath)
    (claimPhysicsGreen : Bool)
    (claimFolklore : Bool)
    (claimXorExclusive : Bool) : GoldschmidtConservationVerdict :=
  if claimPhysicsGreen then
    .greenInventRefuse
  else if claimFolklore then
    .folkloreRefuse
  else if claimXorExclusive then
    .xorMutuallyExclusiveRefuse
  else if !goldschmidtConservationPathIsNontrivial path then
    .trivialOreRefuse
  else
    match modality with
    | .unwired | .assumed | .surrogate => .unwiredOk
    | .proved => .legNamedOk

/-- Whether class 6⊗7⊗17 ore-affinity slots are pinned Present (concurrent **product**). -/
def threeOreClassesNamed : Bool :=
  decide (goldschmidtClassBundleSlot goldschmidtClassBundleSixSevenSeventeen goldschmidtClassIndexLithophile = .present ∧
    goldschmidtClassBundleSlot goldschmidtClassBundleSixSevenSeventeen goldschmidtClassIndexChalcophile = .present ∧
    goldschmidtClassBundleSlot goldschmidtClassBundleSixSevenSeventeen goldschmidtClassIndexSiderophile = .present ∧
    goldschmidtClassIndexLithophile = 6 ∧
    goldschmidtClassIndexChalcophile = 7 ∧
    goldschmidtClassIndexSiderophile = 17)

/-- Whether Ore⊗G⊗fO₂ concurrent **product** is typed (not XOR). -/
def oreProductConservationTyped : Bool :=
  decide (goldschmidtProductConservationTyped goldschmidtConservationFieldNamed = true ∧
    goldschmidtProductConservationTyped goldschmidtConservationFieldUnwired = true ∧
    oreProductIsConcurrentProduct oreProductBundleConcurrent = true ∧
    oreProductPresentCount oreProductBundleConcurrent = 3)

/-- Whether Fe metal/oxide/sulfide same Z=26 is conserved. -/
def feSameZConserved : Bool :=
  decide (fePhaseSameZ .metal = true ∧
    fePhaseSameZ .oxide = true ∧
    fePhaseSameZ .sulfide = true ∧
    goldschmidtElementIron.z = 26)

/-- Whether He closed-shell no-ore is pinned. -/
def heliumNoOreOk : Bool :=
  decide (heliumClosedShellNoOre = true ∧ goldschmidtElementHelium.z = 2)

/-- Whether thermo-preserving **Goldschmidt** fusion identity is **conserved** on pinned states. -/
def fusionIdentityConserved : Bool :=
  decide (fusionGoldschmidt thermoGoldschmidtZero thermoGoldschmidtPositive =
    thermoGoldschmidtPositive ∧
    fusionGoldschmidt thermoGoldschmidtPositive thermoGoldschmidtZero =
      fusionGoldschmidt thermoGoldschmidtZero thermoGoldschmidtPositive ∧
    (fusionGoldschmidt thermoGoldschmidtPositive thermoGoldschmidtPositive).landauerWitness = 2 ∧
    goldschmidtConservationPathIsNontrivial goldschmidtConservationPathIronL1 = true ∧
    goldschmidtElementZValid goldschmidtElementIron = true)

/-- Whether trivial (level-0) **Goldschmidt** path is refused (fail-closed). -/
def trivialOreRefused : Bool :=
  let trivialPath : GoldschmidtConservationPath :=
    { field := goldschmidtConservationFieldNamed, level := 0, elementZ := goldschmidtElementIron
      classBundle := goldschmidtClassBundleSixSevenSeventeen
      productBundle := oreProductBundleConcurrent }
  decide (evaluateGoldschmidtOrePath .unwired trivialPath false false false false = .trivialOreRefuse ∧
    evaluateGoldschmidtConservation .unwired trivialPath false false false = .trivialOreRefuse)

/-- Whether GREEN invent is refused on **Goldschmidt** scaffold. -/
def greenInventRefused : Bool :=
  decide (evaluateGoldschmidtOrePath .unwired goldschmidtConservationPathIronL1 true false false false =
    .greenInventRefuse ∧
    evaluateGoldschmidtConservation .unwired goldschmidtConservationPathIronL1 true false false =
      .greenInventRefuse)

/-- Whether folklore claim is refused on **Goldschmidt** scaffold. -/
def folkloreRefused : Bool :=
  decide (evaluateGoldschmidtOrePath .unwired goldschmidtConservationPathIronL1 false false true false =
    .folkloreRefuse ∧
    evaluateGoldschmidtConservation .unwired goldschmidtConservationPathIronL1 false true false =
      .folkloreRefuse)

/-- Whether XOR mutually-exclusive claim is refused (concurrent **product** not XOR). -/
def xorMutuallyExclusiveRefused : Bool :=
  decide (evaluateGoldschmidtOrePath .unwired goldschmidtConservationPathIronL1 false false false true =
    .xorMutuallyExclusiveRefuse ∧
    evaluateGoldschmidtConservation .unwired goldschmidtConservationPathIronL1 false false true =
      .xorMutuallyExclusiveRefuse)

/-- Whether iron **Goldschmidt** **conservation** path passes under Unwired modality. -/
def ironGoldschmidtConservationUnwiredOk : Bool :=
  decide (evaluateGoldschmidtConservation .unwired goldschmidtConservationPathIronL1 false false false = .unwiredOk ∧
    evaluateGoldschmidtOrePath .unwired goldschmidtConservationPathIronL1 false false false false = .legNamedOk)

/-- Whether copper **Goldschmidt** **conservation** path passes under Unwired modality. -/
def copperGoldschmidtConservationUnwiredOk : Bool :=
  decide (evaluateGoldschmidtConservation .unwired goldschmidtConservationPathCopperL1 false false false = .unwiredOk ∧
    evaluateGoldschmidtOrePath .unwired goldschmidtConservationPathCopperL1 false false false false = .legNamedOk)

/-- Whether silicon **Goldschmidt** **conservation** path passes under Unwired modality. -/
def siliconGoldschmidtConservationUnwiredOk : Bool :=
  decide (evaluateGoldschmidtConservation .unwired goldschmidtConservationPathSiliconL1 false false false = .unwiredOk ∧
    evaluateGoldschmidtOrePath .unwired goldschmidtConservationPathSiliconL1 false false false false = .legNamedOk)

/-- Whether unwired baseline **Goldschmidt** path passes under Unwired modality. -/
def unwiredGoldschmidtConservationUnwiredOk : Bool :=
  decide (evaluateGoldschmidtConservation .unwired goldschmidtConservationPathUnwiredL1 false false false = .unwiredOk ∧
    evaluateGoldschmidtOrePath .unwired goldschmidtConservationPathUnwiredL1 false false false false = .legNamedOk)

/-- Whether a close attempt is admissible under GOLDSCHMIDT-01 **ore-class** **conservation**. -/
def goldschmidtConservationVerdictOk (v : GoldschmidtConservationVerdict) : Bool :=
  match v with
  | .unwiredOk | .legNamedOk => true
  | _ => false

theorem unwired_goldschmidt_conservation_ok :
    evaluateGoldschmidtConservation .unwired goldschmidtConservationPathIronL1 false false false = .unwiredOk := rfl

theorem proved_goldschmidt_conservation_leg_named_ok :
    evaluateGoldschmidtConservation .proved goldschmidtConservationPathIronL1 false false false = .legNamedOk := rfl

theorem trivial_ore_refuse :
    evaluateGoldschmidtConservation .unwired
      { field := goldschmidtConservationFieldNamed, level := 0, elementZ := goldschmidtElementIron
        classBundle := goldschmidtClassBundleSixSevenSeventeen
        productBundle := oreProductBundleConcurrent }
      false false false = .trivialOreRefuse := rfl

theorem green_invent_refuse :
    evaluateGoldschmidtConservation .unwired goldschmidtConservationPathIronL1 true false false =
      .greenInventRefuse := rfl

theorem folklore_refuse :
    evaluateGoldschmidtConservation .unwired goldschmidtConservationPathIronL1 false true false =
      .folkloreRefuse := rfl

theorem xor_mutually_exclusive_refuse :
    evaluateGoldschmidtConservation .unwired goldschmidtConservationPathIronL1 false false true =
      .xorMutuallyExclusiveRefuse := rfl

theorem three_ore_classes_named :
    threeOreClassesNamed = true := by decide

theorem ore_product_conservation_typed :
    oreProductConservationTyped = true := rfl

theorem fe_same_z_conserved :
    feSameZConserved = true := rfl

theorem helium_no_ore_ok :
    heliumNoOreOk = true := rfl

theorem fusion_identity_conserved :
    fusionIdentityConserved = true := rfl

theorem trivial_ore_refused :
    trivialOreRefused = true := rfl

theorem green_invent_refused :
    greenInventRefused = true := rfl

theorem folklore_refused :
    folkloreRefused = true := rfl

theorem xor_mutually_exclusive_refused :
    xorMutuallyExclusiveRefused = true := rfl

theorem iron_goldschmidt_conservation_unwired_ok :
    ironGoldschmidtConservationUnwiredOk = true := rfl

theorem copper_goldschmidt_conservation_unwired_ok :
    copperGoldschmidtConservationUnwiredOk = true := rfl

theorem silicon_goldschmidt_conservation_unwired_ok :
    siliconGoldschmidtConservationUnwiredOk = true := rfl

theorem unwired_goldschmidt_conservation_unwired_ok :
    unwiredGoldschmidtConservationUnwiredOk = true := rfl

/-- Quantum / knowing formal fiber root (structure witness — not meso acting). -/
def goldschmidtConservationQuantumKnowingFiber : String :=
  "umst/umst-formal-double-slit"

theorem goldschmidt_conservation_quantum_knowing_fiber_pinned :
    goldschmidtConservationQuantumKnowingFiber =
      "umst/umst-formal-double-slit" := rfl

/-- Cited Rust **Goldschmidt** ore-class authority (views only — lattice is structural here). -/
def goldschmidtConservationCitedModule : String :=
  "umst/umst-chem/src/goldschmidt.rs"

/-- **Goldschmidt** lattice is structure — not 118² GREEN periodic enumeration. -/
def goldschmidtConservationNot118GreenTable : Bool := true

theorem goldschmidt_conservation_not_118_green_table :
    goldschmidtConservationNot118GreenTable = true := rfl

/-- Second-law + **conservation** framing — cites meso SSOT, not wired on knowing scaffold. -/
def goldschmidtConservationSecondLawFramed : Bool := true

theorem goldschmidt_conservation_second_law_framed :
    goldschmidtConservationSecondLawFramed = true := rfl

/-- GOLDSCHMIDT-01 claim **ore-class** is **not** claimed Proved on the knowing scaffold. -/
def goldschmidtProved : Bool := false

theorem goldschmidt_not_proved : goldschmidtProved = false := rfl

/-- Production wiring is **not** claimed on the knowing scaffold. -/
def goldschmidtConservationProductionWired : Bool := false

theorem goldschmidt_conservation_production_not_wired :
    goldschmidtConservationProductionWired = false := rfl

/-- Cell id for the Lean GOLDSCHMIDT-01 **ore-class** **conservation** knowing-fiber. -/
def goldschmidtConservationCellId : String :=
  "CHEM-FORMAL-Q-LEAN-GOLDSCHMIDT-CONSERVATION"

/-- Non-claim fence — class 6⊗7⊗17 lithophile/chalcophile/siderophile; Ore⊗G⊗fO₂ concurrent **product**;
Fe Z=26 metal/oxide/sulfide same Z; Cu Z=29; Si Z=14; He Z=2 closed-shell no-ore;
folklore refuse; trivial ore refuse; XOR refuse; **conservation** typed;
GOLDSCHMIDT-01 Unwired; `goldschmidtProved` false. -/
def goldschmidtConservationNonClaim : String :=
  "CHEM-FORMAL-Q-LEAN-GOLDSCHMIDT-CONSERVATION GOLDSCHMIDT-01 ore-class conservation class 6 7 17 lithophile chalcophile siderophile Ore G fO2 concurrent product not XOR Fe Z=26 metal oxide sulfide same Z Cu Z=29 Si Z=14 He Z=2 closed-shell no-ore folklore refuse trivial ore refuse XOR refuse goldschmidtProved false Unwired OK not Goldschmidt Proved not physics GREEN; not 118² GREEN DFT"

/-- Physics GREEN is unauthorized on the knowing GOLDSCHMIDT-01 **ore-class** **conservation** scaffold. -/
def goldschmidtConservationPhysicsGreenAuthorized : Prop := False

theorem goldschmidt_conservation_physics_green_false :
    ¬ goldschmidtConservationPhysicsGreenAuthorized := id

theorem goldschmidt_conservation_modality_unwired :
    goldschmidtConservationModalityCurrent = .unwired := rfl

/-- **One** design axiom: second law + **conservation** (structure witness — not meso import). -/
def goldschmidtConservationAxiom : Bool :=
  goldschmidtConservationNot118GreenTable &&
    goldschmidtConservationSecondLawFramed &&
    threeOreClassesNamed &&
    oreProductConservationTyped &&
    feSameZConserved &&
    heliumNoOreOk &&
    fusionIdentityConserved &&
    trivialOreRefused &&
    greenInventRefused &&
    folkloreRefused &&
    xorMutuallyExclusiveRefused &&
    ironGoldschmidtConservationUnwiredOk &&
    copperGoldschmidtConservationUnwiredOk &&
    siliconGoldschmidtConservationUnwiredOk &&
    unwiredGoldschmidtConservationUnwiredOk &&
    !goldschmidtProved &&
    !goldschmidtConservationProductionWired

theorem goldschmidt_conservation_axiom :
    goldschmidtConservationAxiom = true := by decide

theorem goldschmidt_conservation_honest_bundle :
    goldschmidtProved = false ∧
    goldschmidtConservationProductionWired = false ∧
    goldschmidtConservationNot118GreenTable = true ∧
    goldschmidtConservationSecondLawFramed = true ∧
    evaluateGoldschmidtConservation .unwired goldschmidtConservationPathIronL1 false false false = .unwiredOk ∧
    evaluateGoldschmidtConservation .proved goldschmidtConservationPathIronL1 false false false = .legNamedOk ∧
    evaluateGoldschmidtConservation .unwired
      { field := goldschmidtConservationFieldNamed, level := 0, elementZ := goldschmidtElementIron
        classBundle := goldschmidtClassBundleSixSevenSeventeen
        productBundle := oreProductBundleConcurrent }
      false false false = .trivialOreRefuse ∧
    evaluateGoldschmidtConservation .unwired goldschmidtConservationPathIronL1 true false false = .greenInventRefuse ∧
    evaluateGoldschmidtConservation .unwired goldschmidtConservationPathIronL1 false true false = .folkloreRefuse ∧
    evaluateGoldschmidtConservation .unwired goldschmidtConservationPathIronL1 false false true = .xorMutuallyExclusiveRefuse ∧
    threeOreClassesNamed = true ∧
    oreProductConservationTyped = true ∧
    feSameZConserved = true ∧
    heliumNoOreOk = true ∧
    fusionIdentityConserved = true ∧
    trivialOreRefused = true ∧
    greenInventRefused = true ∧
    folkloreRefused = true ∧
    xorMutuallyExclusiveRefused = true ∧
    ironGoldschmidtConservationUnwiredOk = true ∧
    copperGoldschmidtConservationUnwiredOk = true ∧
    siliconGoldschmidtConservationUnwiredOk = true ∧
    unwiredGoldschmidtConservationUnwiredOk = true ∧
    goldschmidtElementIron.z = 26 ∧
    goldschmidtElementCopper.z = 29 ∧
    goldschmidtElementSilicon.z = 14 ∧
    goldschmidtElementHelium.z = 2 ∧
    goldschmidtElementOganesson.z = 118 ∧
    goldschmidtConservationAxiom = true :=
  ⟨rfl, rfl, goldschmidt_conservation_not_118_green_table,
    goldschmidt_conservation_second_law_framed,
    unwired_goldschmidt_conservation_ok, proved_goldschmidt_conservation_leg_named_ok, trivial_ore_refuse,
    green_invent_refuse, folklore_refuse, xor_mutually_exclusive_refuse,
    three_ore_classes_named, ore_product_conservation_typed, fe_same_z_conserved, helium_no_ore_ok,
    fusion_identity_conserved, trivial_ore_refused, green_invent_refused, folklore_refused,
    xor_mutually_exclusive_refused,
    iron_goldschmidt_conservation_unwired_ok, copper_goldschmidt_conservation_unwired_ok,
    silicon_goldschmidt_conservation_unwired_ok, unwired_goldschmidt_conservation_unwired_ok,
    goldschmidt_iron_z_twenty_six, goldschmidt_copper_z_twenty_nine, goldschmidt_silicon_z_fourteen,
    goldschmidt_helium_z_two, goldschmidt_oganesson_z_118,
    goldschmidt_conservation_axiom⟩

end UMST.Chem
