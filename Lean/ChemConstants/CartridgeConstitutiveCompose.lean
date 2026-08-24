-- SPDX-FileCopyrightText: 2026 Santosh Prabhu Shenbagamoorthy and Santhosh Shyamsundar
-- SPDX-License-Identifier: MIT

import ElementElectronic

/-!
# CartridgeConstitutiveCompose — knowing-fiber cartridge ψ/𝒟 additive compose **conservation** (Q lattice)

Cartridge ψ/𝒟 additive compose on the matter fiber is the **dual** of chem Ore monoidal product
(product not XOR); consult ChemistryService; no second periodic table. Pairs `umst-chem` scaffold
`cartridge_constitutive_compose` / **conservation** posture.

- `CartridgeConstitutiveComposeModality` — Unwired / Assumed / Proved / Surrogate (not 118² GREEN table).
- `composePsi` / `composeDissipation` — additive matter-fiber compose, not XOR enum.
- `xorCartridgeMergeRefused` — concurrent Π_c may hold ≥2 constituents, not XOR bucket.
- `evaluateCartridgeComposeClose` — Unwired OK; compose-named OK; XOR merge refuse; second-table refuse;
  WAVE100 lib.rs/eos.rs smuggle refuse; GREEN invent refuse; proved-without-bar refuse;
  production-wired refuse.
- Second-law + **conservation** framing cites meso `UMST.Chem.Conservation` /
  `LandauerLaw.physicalSecondLaw` — not imported.
- No meso / acting theorems. No new physics `axiom`.
- `physics_green` stays false. Does **not** claim cartridge compose Proved or physics GREEN.
- WAVE100 freeze — remainder deferred composition (env/time/cross-domain), not impossibility stop.
-/

namespace UMST.Chem

/-- Design modality for cartridge constitutive compose **conservation** (lattice SSOT). -/
inductive CartridgeConstitutiveComposeModality where
  | unwired | assumed | proved | surrogate
  deriving DecidableEq, Repr

def cartridgeConstitutiveComposeModalityCurrent : CartridgeConstitutiveComposeModality := .unwired

/-- Modality lattice cardinality (Unwired / Assumed / Proved / Surrogate). -/
def cartridgeComposeModalityLatticeCardinality : Nat := 4

theorem cartridge_compose_modality_lattice_cardinality_four :
    cartridgeComposeModalityLatticeCardinality = 4 := rfl

theorem cartridge_compose_modality_lattice_not_118_squared :
    cartridgeComposeModalityLatticeCardinality ≠ 118 * 118 := by decide

/-- IUPAC periodic-table cardinality (Z=1..118). -/
def iupacTableCardinality : Nat := 118

theorem iupac_table_cardinality_118 : iupacTableCardinality = 118 := rfl

/-- ψ additivity on the matter fiber (dual of Ore monoidal product). -/
def psiComposeIsSum : Bool := true

/-- Convex 𝒟 compose is a sum of dissipation potentials. -/
def dissipationComposeIsSum : Bool := true

theorem psi_compose_is_sum_true : psiComposeIsSum = true := rfl

theorem dissipation_compose_is_sum_true : dissipationComposeIsSum = true := rfl

/-- Additive ψ compose (matter dual of Ore). -/
def composePsi (psi_a psi_b : Int) : Int := psi_a + psi_b

/-- Additive 𝒟 compose; negative dissipation refused by caller. -/
def composeDissipation (d_a d_b : Int) : Int := d_a + d_b

theorem compose_psi_additive (a b : Int) : composePsi a b = a + b := rfl

theorem compose_dissipation_additive (a b : Int) : composeDissipation a b = a + b := rfl

theorem compose_psi_witness_2_3 : composePsi 2 3 = 5 := rfl

theorem compose_dissipation_witness_1_1 : composeDissipation 1 1 = 2 := rfl

theorem compose_psi_witness_10_minus_4 : composePsi 10 (-4) = 6 := rfl

theorem compose_dissipation_witness_3_5 : composeDissipation 3 5 = 8 := rfl

/-- XOR cartridge merge refused — exclusive merge theater, not additive compose. -/
def xorCartridgeMergeMarker : String := "xor_cartridge_merge_refused_v1"

def additiveComposeMarker : String := "psi_d_additive_compose_sum_v1"

theorem xor_merge_marker_ne_additive_compose :
    xorCartridgeMergeMarker ≠ additiveComposeMarker := by decide

def xorCartridgeMergeRefused : Bool := true

theorem xor_cartridge_merge_refused_true : xorCartridgeMergeRefused = true := rfl

/-- Whether a second periodic table is owned by cartridges. -/
def cartridgeOwnsPeriodicTable : Bool := false

theorem cartridge_owns_periodic_table_false : cartridgeOwnsPeriodicTable = false := rfl

/-- ChemistryService consult authority — no second periodic table. -/
def chemistryServiceMarker : String := "umst/umst-chem/src/service.rs#ChemistryService"

theorem chemistry_service_marker_named : chemistryServiceMarker ≠ "" := by decide

theorem chemistry_service_consult_required :
    chemistryServiceMarker ≠ "cartridge_second_periodic_table_v1" := by decide

/-- Named cartridge constituent factor tags (bounded scaffold — not XOR enum). -/
inductive CartridgeConstituentTag where
  | continuumScaffold | poromechanicsScaffold | solidInelasticScaffold
  deriving DecidableEq, Repr

def cartridgeConstituentTagString : CartridgeConstituentTag → String
  | .continuumScaffold => "continuum_scaffold"
  | .poromechanicsScaffold => "poromechanics_scaffold"
  | .solidInelasticScaffold => "solid_inelastic_scaffold"

theorem cartridge_constituent_continuum_str :
    cartridgeConstituentTagString .continuumScaffold = "continuum_scaffold" := rfl

theorem cartridge_constituent_poromechanics_str :
    cartridgeConstituentTagString .poromechanicsScaffold = "poromechanics_scaffold" := rfl

theorem cartridge_constituent_solid_inelastic_str :
    cartridgeConstituentTagString .solidInelasticScaffold = "solid_inelastic_scaffold" := rfl

/-- Matter-fiber ψ/𝒟 compose witness — additive dual of Ore tensor product. -/
structure PsiDissipationCompose where
  psiWitness : Int
  dissipationWitness : Int
  deriving DecidableEq, Repr

def cartridgeComposePair : PsiDissipationCompose :=
  { psiWitness := composePsi 2 3, dissipationWitness := composeDissipation 1 1 }

def cartridgeComposeConcurrentCount (w : PsiDissipationCompose) : Nat :=
  (if w.psiWitness ≠ 0 then 1 else 0) + (if w.dissipationWitness ≠ 0 then 1 else 0)

theorem cartridge_compose_pair_psi_five :
    cartridgeComposePair.psiWitness = 5 := rfl

theorem cartridge_compose_pair_dissipation_two :
    cartridgeComposePair.dissipationWitness = 2 := rfl

theorem cartridge_compose_concurrent_count_ge_two :
    cartridgeComposeConcurrentCount cartridgeComposePair ≥ 2 := by decide

/-- Ore dual — chem Ore product tree vs matter ψ additive compose. -/
inductive OreTag where
  | hematite | bauxite | vacuum
  deriving DecidableEq, Repr

inductive OreTree where
  | leaf (tag : OreTag) : OreTree
  | tensor (left right : OreTree) : OreTree
  deriving DecidableEq, Repr

def oreUnitI : OreTree := .leaf .vacuum

def oreTensorProduct (a b : OreTree) : OreTree := .tensor a b

def hematiteLeaf : OreTree := .leaf .hematite
def bauxiteLeaf : OreTree := .leaf .bauxite

def tripleOreProduct : OreTree :=
  oreTensorProduct (oreTensorProduct hematiteLeaf bauxiteLeaf) (.leaf .vacuum)

def oreConstituentCount : OreTree → Nat
  | .leaf .vacuum => 0
  | .leaf _ => 1
  | .tensor l r => oreConstituentCount l + oreConstituentCount r

theorem triple_ore_concurrent_count : oreConstituentCount tripleOreProduct = 2 := rfl

def oreProductNotXor : Bool :=
  decide (oreConstituentCount tripleOreProduct ≥ 2)

theorem ore_product_not_xor_true : oreProductNotXor = true := rfl

def matterFiberDualMarker : String :=
  "cartridge_psi_d_additive_compose_matter_fiber_dual_of_ore_product_v1"

def oreProductMarker : String := "chem_ore_tensor_product_not_xor_v1"

theorem matter_fiber_dual_ne_ore_marker :
    matterFiberDualMarker ≠ oreProductMarker := by decide

/-- Compose conjunct — honest additive matter-fiber dual of Ore. -/
def cartridgeComposeHonestConjunct : Bool :=
  psiComposeIsSum &&
    dissipationComposeIsSum &&
    xorCartridgeMergeRefused &&
    !cartridgeOwnsPeriodicTable &&
    decide (composePsi 2 3 = 5) &&
    decide (composeDissipation 1 1 = 2) &&
    decide (composePsi 10 (-4) = 6) &&
    decide (composeDissipation 3 5 = 8)

theorem cartridge_compose_honest_conjunct_true :
    cartridgeComposeHonestConjunct = true := by decide

def productNotXor : Bool :=
  oreProductNotXor &&
    xorCartridgeMergeRefused &&
    psiComposeIsSum &&
    dissipationComposeIsSum

theorem product_not_xor_true : productNotXor = true := by decide

/-- WAVE100 — lib.rs / eos.rs smuggle refuse (not wired). -/
def wave100LibRsSmuggleMarker : String := "umst/umst-chem/src/lib.rs"

def wave100EosRsSmuggleMarker : String := "umst/umst-chem/src/eos.rs"

def cartridgeComposeWiredInLib : Bool := false

def cartridgeComposeWiredInEos : Bool := false

theorem cartridge_compose_not_wired_lib : cartridgeComposeWiredInLib = false := rfl

theorem cartridge_compose_not_wired_eos : cartridgeComposeWiredInEos = false := rfl

def chartAuthorityIsWave100Smuggle (auth : String) : Bool :=
  decide (auth = wave100LibRsSmuggleMarker ∨ auth = wave100EosRsSmuggleMarker)

theorem lib_rs_smuggle_detected :
    chartAuthorityIsWave100Smuggle wave100LibRsSmuggleMarker = true := rfl

theorem eos_rs_smuggle_detected :
    chartAuthorityIsWave100Smuggle wave100EosRsSmuggleMarker = true := rfl

/-- Verdict of a cartridge compose close attempt (fail-closed). -/
inductive CartridgeComposeVerdict where
  | unwiredOk
  | composeNamedOk
  | xorMergeRefuse
  | secondTableRefuse
  | wave100SmuggleRefuse
  | greenInventRefuse
  | provedWithoutBarRefuse
  | productionWiredRefuse
  deriving DecidableEq, Repr

def cartridgeComposeVerdictOk (v : CartridgeComposeVerdict) : Bool :=
  match v with
  | .unwiredOk | .composeNamedOk => true
  | _ => false

/-- Cartridge compose incidence — authority + level + compose witness. -/
structure CartridgeComposeIncidence where
  witness : PsiDissipationCompose
  authority : String
  level : Nat
  claimSecondTable : Bool
  claimXorMerge : Bool
  deriving DecidableEq, Repr

def cartridgeComposeIncidenceNontrivial (h : CartridgeComposeIncidence) : Bool :=
  decide (0 < h.level)

def cartridgeComposeIncidenceL1 : CartridgeComposeIncidence :=
  { witness := cartridgeComposePair
    authority := "umst/umst-chem/src/x_rows/cartridge_constitutive_compose.rs"
    level := 1
    claimSecondTable := false
    claimXorMerge := false }

def cartridgeComposeIncidenceTrivial : CartridgeComposeIncidence :=
  { witness := cartridgeComposePair
    authority := "umst/umst-chem/src/x_rows/cartridge_constitutive_compose.rs"
    level := 0
    claimSecondTable := false
    claimXorMerge := false }

def cartridgeComposeIncidenceXorMerge : CartridgeComposeIncidence :=
  { witness := cartridgeComposePair
    authority := "umst/umst-chem/src/x_rows/cartridge_constitutive_compose.rs"
    level := 1
    claimSecondTable := false
    claimXorMerge := true }

def cartridgeComposeIncidenceSecondTable : CartridgeComposeIncidence :=
  { witness := cartridgeComposePair
    authority := "umst/umst-chem/src/x_rows/cartridge_constitutive_compose.rs"
    level := 1
    claimSecondTable := true
    claimXorMerge := false }

def cartridgeComposeIncidenceLibRsSmuggle : CartridgeComposeIncidence :=
  { witness := cartridgeComposePair
    authority := wave100LibRsSmuggleMarker
    level := 1
    claimSecondTable := false
    claimXorMerge := false }

def cartridgeComposeIncidenceEosRsSmuggle : CartridgeComposeIncidence :=
  { witness := cartridgeComposePair
    authority := wave100EosRsSmuggleMarker
    level := 1
    claimSecondTable := false
    claimXorMerge := false }

/-- Evaluate cartridge compose incidence against the compose bar. -/
def evaluateCartridgeComposeIncidence
    (modality : CartridgeConstitutiveComposeModality)
    (h : CartridgeComposeIncidence)
    (claimPhysicsGreen : Bool)
    (claimProved : Bool) : CartridgeComposeVerdict :=
  if claimPhysicsGreen then
    .greenInventRefuse
  else if claimProved then
    .provedWithoutBarRefuse
  else if chartAuthorityIsWave100Smuggle h.authority then
    .wave100SmuggleRefuse
  else if h.claimSecondTable then
    .secondTableRefuse
  else if h.claimXorMerge then
    .xorMergeRefuse
  else if !cartridgeComposeIncidenceNontrivial h then
    .xorMergeRefuse
  else
    match modality with
    | .unwired => .composeNamedOk
    | .assumed | .surrogate => .unwiredOk
    | .proved => .provedWithoutBarRefuse

/-- Evaluate cartridge compose close against modality bar. -/
def evaluateCartridgeComposeClose
    (modality : CartridgeConstitutiveComposeModality)
    (claimPhysicsGreen : Bool)
    (claimProductionWired : Bool) : CartridgeComposeVerdict :=
  if claimPhysicsGreen then
    .greenInventRefuse
  else if claimProductionWired then
    .productionWiredRefuse
  else
    match modality with
    | .unwired => .unwiredOk
    | .assumed | .proved | .surrogate => .composeNamedOk

/-- Cartridge compose is **not** claimed Proved on the knowing scaffold. -/
def cartridgeComposeProved : Bool := false

theorem cartridge_compose_proved_false : cartridgeComposeProved = false := rfl

/-- Lattice is structure — not 118² GREEN periodic enumeration. -/
def cartridgeComposeNot118GreenTable : Bool := true

theorem cartridge_compose_not_118_green_table :
    cartridgeComposeNot118GreenTable = true := rfl

/-- Sole axiom count — second law + conservation framing only. -/
def soleAxiomCount : Nat := 1

theorem sole_axiom_count_is_one : soleAxiomCount = 1 := rfl

/-- Production wiring is **not** claimed on the knowing scaffold. -/
def cartridgeComposeProductionWired : Bool := false

theorem cartridge_compose_production_not_wired :
    cartridgeComposeProductionWired = false := rfl

/-- Formal fiber routing — matter constitutive vs quantum knowing. -/
inductive CartridgeFormalFiber where
  | matterConstitutive | quantumKnowing
  deriving DecidableEq, Repr

def cartridgeComposeFiberOk (f : CartridgeFormalFiber) : Bool :=
  match f with
  | .matterConstitutive | .quantumKnowing => true

theorem cartridge_compose_matter_fiber_ok :
    cartridgeComposeFiberOk .matterConstitutive = true := rfl

theorem cartridge_compose_knowing_fiber_ok :
    cartridgeComposeFiberOk .quantumKnowing = true := rfl

/-- Whether trivial (level-0) incidence is refused (fail-closed). -/
def trivialComposeRefused : Bool :=
  decide (evaluateCartridgeComposeIncidence .unwired cartridgeComposeIncidenceTrivial false false =
    .xorMergeRefuse)

/-- Whether XOR merge claim is refused. -/
def xorMergeRefused : Bool :=
  decide (evaluateCartridgeComposeIncidence .unwired cartridgeComposeIncidenceXorMerge false false =
    .xorMergeRefuse)

/-- Whether second periodic table claim is refused. -/
def secondTableRefused : Bool :=
  decide (evaluateCartridgeComposeIncidence .unwired cartridgeComposeIncidenceSecondTable false false =
    .secondTableRefuse)

/-- Whether WAVE100 lib.rs/eos.rs smuggle is refused. -/
def wave100SmuggleRefused : Bool :=
  decide (evaluateCartridgeComposeIncidence .unwired cartridgeComposeIncidenceLibRsSmuggle false false =
    .wave100SmuggleRefuse ∧
    evaluateCartridgeComposeIncidence .unwired cartridgeComposeIncidenceEosRsSmuggle false false =
      .wave100SmuggleRefuse)

/-- Whether GREEN invent is refused on cartridge compose scaffold. -/
def greenInventRefused : Bool :=
  decide (evaluateCartridgeComposeClose .unwired true false = .greenInventRefuse ∧
    cartridgeComposeVerdictOk (evaluateCartridgeComposeClose .unwired true false) = false)

/-- Whether proved-without-bar is refused. -/
def provedWithoutBarRefused : Bool :=
  decide (evaluateCartridgeComposeIncidence .unwired cartridgeComposeIncidenceL1 false true =
    .provedWithoutBarRefuse)

/-- Whether L1 compose passes under Unwired modality. -/
def cartridgeComposeL1UnwiredOk : Bool :=
  decide (evaluateCartridgeComposeIncidence .unwired cartridgeComposeIncidenceL1 false false =
    .composeNamedOk)

/-- Whether unwired close passes without production wiring. -/
def unwiredCloseOk : Bool :=
  decide (evaluateCartridgeComposeClose .unwired false false = .unwiredOk)

theorem unwired_close_without_production_wiring :
    evaluateCartridgeComposeClose .unwired false false = .unwiredOk := rfl

theorem cartridge_compose_l1_named_ok :
    evaluateCartridgeComposeIncidence .unwired cartridgeComposeIncidenceL1 false false =
      .composeNamedOk := rfl

theorem trivial_compose_refuse :
    evaluateCartridgeComposeIncidence .unwired cartridgeComposeIncidenceTrivial false false =
      .xorMergeRefuse := rfl

theorem xor_merge_refuse :
    evaluateCartridgeComposeIncidence .unwired cartridgeComposeIncidenceXorMerge false false =
      .xorMergeRefuse := rfl

theorem second_table_refuse :
    evaluateCartridgeComposeIncidence .unwired cartridgeComposeIncidenceSecondTable false false =
      .secondTableRefuse := rfl

theorem lib_rs_smuggle_refuse :
    evaluateCartridgeComposeIncidence .unwired cartridgeComposeIncidenceLibRsSmuggle false false =
      .wave100SmuggleRefuse := rfl

theorem eos_rs_smuggle_refuse :
    evaluateCartridgeComposeIncidence .unwired cartridgeComposeIncidenceEosRsSmuggle false false =
      .wave100SmuggleRefuse := rfl

theorem green_invent_refuse :
    evaluateCartridgeComposeClose .unwired true false = .greenInventRefuse := rfl

theorem proved_without_bar_refuse :
    evaluateCartridgeComposeIncidence .unwired cartridgeComposeIncidenceL1 false true =
      .provedWithoutBarRefuse := rfl

theorem production_wired_refuse :
    evaluateCartridgeComposeClose .proved false true = .productionWiredRefuse := rfl

/-- Quantum / knowing formal fiber root (structure witness — not meso acting). -/
def cartridgeConstitutiveComposeQuantumKnowingFiber : String :=
  "umst/umst-formal-double-slit"

theorem cartridge_constitutive_compose_quantum_knowing_fiber_pinned :
    cartridgeConstitutiveComposeQuantumKnowingFiber =
      "umst/umst-formal-double-slit" := rfl

/-- Cited Rust cartridge constitutive compose authority (views only — lattice is structural here). -/
def cartridgeConstitutiveComposeCitedModule : String :=
  "umst/umst-chem/src/x_rows/cartridge_constitutive_compose.rs"

/-- Cited ChemistryService authority. -/
def chemistryServiceAuthority : String :=
  "umst/umst-chem/src/service.rs"

/-- Cited INT cross cartridge compose authority. -/
def chemIntCrossCartridgeComposeAuthority : String :=
  "CHEM-INT-CROSS-CARTRIDGE-CONSTITUTIVE-COMPOSE-CONSERVATION"

/-- Cited Ore monoidal dual authority. -/
def oreMonoidalDualAuthority : String :=
  "umst/umst-chem/src/ore_monoidal_product.rs"

/-- Second-law + **conservation** framing — cites meso SSOT, not wired on knowing scaffold. -/
def cartridgeComposeSecondLawConservationFramed : Bool := true

theorem cartridge_compose_second_law_conservation_framed :
    cartridgeComposeSecondLawConservationFramed = true := rfl

/-- Cell id for the Lean cartridge constitutive compose **conservation** knowing-fiber. -/
def cartridgeConstitutiveComposeCellId : String :=
  "CHEM-FORMAL-Q-LEAN-CARTRIDGE-CONSTITUTIVE-COMPOSE-CONSERVATION"

/-- Non-claim fence — cartridge ψ/𝒟 additive compose matter-fiber dual chem Ore product not XOR;
consult ChemistryService no second periodic table XOR cartridge merge refused WAVE100 lib.rs eos.rs
smuggle refuse `cartridgeComposeProved` false Unwired one axiom second law conservation not physics GREEN. -/
def cartridgeConstitutiveComposeNonClaim : String :=
  "CHEM-FORMAL-Q-LEAN-CARTRIDGE-CONSTITUTIVE-COMPOSE-CONSERVATION cartridge psi D additive compose matter-fiber dual chem Ore product not XOR consult ChemistryService no second periodic table XOR cartridge merge refused WAVE100 lib.rs eos.rs smuggle refuse cartridgeComposeProved false Unwired one axiom second law conservation not GREEN DFT not physics GREEN not production_wired WAVE100 freeze remainder deferred composition env time cross-domain not impossibility"

/-- Physics GREEN is unauthorized on the knowing cartridge compose **conservation** scaffold. -/
def cartridgeConstitutiveComposePhysicsGreenAuthorized : Prop := False

theorem cartridge_constitutive_compose_physics_green_false :
    ¬ cartridgeConstitutiveComposePhysicsGreenAuthorized := id

theorem cartridge_constitutive_compose_modality_unwired :
    cartridgeConstitutiveComposeModalityCurrent = .unwired := rfl

/-- **One** design axiom: second law + **conservation** (structure witness — not meso import). -/
def cartridgeConstitutiveComposeAxiom : Bool :=
  cartridgeComposeNot118GreenTable &&
    cartridgeComposeSecondLawConservationFramed &&
    cartridgeComposeHonestConjunct &&
    productNotXor &&
    trivialComposeRefused &&
    xorMergeRefused &&
    secondTableRefused &&
    wave100SmuggleRefused &&
    greenInventRefused &&
    provedWithoutBarRefused &&
    cartridgeComposeL1UnwiredOk &&
    unwiredCloseOk &&
    cartridgeComposeFiberOk .matterConstitutive &&
    cartridgeComposeFiberOk .quantumKnowing &&
    !cartridgeComposeProved &&
    !cartridgeComposeProductionWired &&
    !cartridgeComposeWiredInLib &&
    !cartridgeComposeWiredInEos

theorem cartridge_constitutive_compose_axiom :
    cartridgeConstitutiveComposeAxiom = true := by decide

theorem cartridge_constitutive_compose_honest_bundle :
    cartridgeComposeProved = false ∧
    cartridgeComposeProductionWired = false ∧
    cartridgeComposeNot118GreenTable = true ∧
    cartridgeComposeSecondLawConservationFramed = true ∧
    cartridgeComposeHonestConjunct = true ∧
    productNotXor = true ∧
    evaluateCartridgeComposeIncidence .unwired cartridgeComposeIncidenceL1 false false =
      .composeNamedOk ∧
    evaluateCartridgeComposeIncidence .unwired cartridgeComposeIncidenceTrivial false false =
      .xorMergeRefuse ∧
    evaluateCartridgeComposeIncidence .unwired cartridgeComposeIncidenceXorMerge false false =
      .xorMergeRefuse ∧
    evaluateCartridgeComposeIncidence .unwired cartridgeComposeIncidenceSecondTable false false =
      .secondTableRefuse ∧
    evaluateCartridgeComposeIncidence .unwired cartridgeComposeIncidenceLibRsSmuggle false false =
      .wave100SmuggleRefuse ∧
    evaluateCartridgeComposeIncidence .unwired cartridgeComposeIncidenceEosRsSmuggle false false =
      .wave100SmuggleRefuse ∧
    evaluateCartridgeComposeClose .unwired false false = .unwiredOk ∧
    xorCartridgeMergeRefused = true ∧
    cartridgeOwnsPeriodicTable = false ∧
    soleAxiomCount = 1 ∧
    cartridgeConstitutiveComposeAxiom = true :=
  ⟨rfl, rfl, cartridge_compose_not_118_green_table, cartridge_compose_second_law_conservation_framed,
    cartridge_compose_honest_conjunct_true, product_not_xor_true,
    cartridge_compose_l1_named_ok, trivial_compose_refuse, xor_merge_refuse, second_table_refuse,
    lib_rs_smuggle_refuse, eos_rs_smuggle_refuse, unwired_close_without_production_wiring,
    xor_cartridge_merge_refused_true, cartridge_owns_periodic_table_false, sole_axiom_count_is_one,
    cartridge_constitutive_compose_axiom⟩

end UMST.Chem
