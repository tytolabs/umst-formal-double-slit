-- SPDX-FileCopyrightText: 2026 Santosh Prabhu Shenbagamoorthy and Santhosh Shyamsundar
-- SPDX-License-Identifier: MIT

/-
-/

import Lake
open Lake DSL

package «umst-formal-double-slit» where

require mathlib from git
  "https://github.com/leanprover-community/mathlib4" @ "v4.14.0"

require «umst-formal» from git
  "https://github.com/tytolabs/umst-formal" @ "690fbe6" / "Lean"

/-!
  Self-contained quantum / measurement extension. Build:

  `cd Lean && lake build`

  **Default `roots`** = quantum + epistemic formal layer plus the vendored thermodynamic
  stack.  **Excluded on purpose:** `Test*.lean`, `test_tensor_eigen.lean`, optional
  `LogSum` / `MatrixLog`, `FlashMoERuntimeScaffold.lean`, etc.  Those files are not in
  `roots` so they do not run in default CI; build them explicitly (e.g. `lake build +TestEntropy`)
  when needed.  They have been manually grep-checked for `sorry` / stray `axiom`.

  **Lean root catalog (entries JSON):** From `Lean/`, run **`lake exe export_catalog`**
  to emit **`artifacts/catalog.json`** with `{ version, entries[{ id, module, kind, name }] }`.
  Details: **`tools/lean_export/README.md`**.

  **Python module scan (imports + digests):** **`make lean-catalog-export`** runs
  **`tools/lean_export/export_catalog.py`** — a different JSON shape for tooling that needs
  coarse import edges and per-file content hashes.
-/
-- LandauerLaw is supplied by the umst-formal dependency: the sole physical axiom
-- physicalSecondLaw is declared once, there, and imported here rather than vendored.
lean_lib «UMST.DoubleSlit» where
  roots := #[`DensityState, `TensorPartialTrace, `MeasurementChannel, `DoubleSlitCore, `QuantumClassicalBridge,
    `InfoEntropy, `KroneckerEigen, `GeneralDimension, `LandauerBound, `EpistemicSensing, `EpistemicMI, `EpistemicDynamics,
    `EpistemicTrajectoryMI, `EpistemicPolicy, `EpistemicRuntimeContract, `EpistemicNumericsContract,
    `EpistemicPerStepNumerics, `EpistemicRuntimeSchemaContract, `EpistemicTelemetryBridge,
    `EpistemicTelemetryApproximation, `EpistemicTelemetryQuantitativeUtility,
    `EpistemicTraceDerivedEpsilonCertificate,
    `EpistemicTelemetrySolverCalibration, `EpistemicTraceDrivenCalibrationWitness,
    `PrototypeSolverCalibration, `GateCompat,
    `PMICEntropyInterior, `Complementarity, `PMICVisibility,
    `VonNeumannEntropy, `QuantumMutualInfo, `KleinInequality, `DataProcessingInequality,
    `DoubleSlit, `ProbeOptimization, `ExamplesQubit, `ErasureChannel, `MeasurementCost,
    `EpistemicGalois, `SchrodingerDynamics, `LindbladDynamics, `LindbladStreamD, `FormalFoundations, `SimLeanBridge,
    -- integrated from upstream framework (ℚ thermo gate + activation + Landauer T_LandauerLaw stack)
    `LandauerExtension, `LandauerEinsteinBridge,
    `GeneralResidualCoherence, `WhichPathMeasurementUpdate, `GeneralVisibility,
    `PhysicsConstrainedAI, `InformationCostIdentity]
    -- Optional / future: `MatrixLog, `LogSum (not in roots)
  srcDir := "."

/-!
  Knowing-fiber chemistry (`CHEM-FORMAL-Q-LEAN-CHEM`): Q-lattice electronic quantum numbers,
  SCALE ladder, EDGE-SURFACE sign convention.  `globs` auto-picks up future `Chem*.lean`;
  `ElementElectronic` stays an explicit root until renamed under `Chem*`.

  Build: `lake build ChemGeometry`
-/
lean_lib ChemGeometry where
  roots := #[`ElementElectronic, `ChemGeometry]
  -- `Chem.+` glob activates when `Chem/` subtree exists (future geometry modules).
  srcDir := "."

/-!
  Knowing-fiber chemistry constants (`CHEM-FORMAL-Q-LEAN-EXACT-SI-RATIONAL`): SI-2019 exact
  integer mantissa identity for **k**, **N_A**, DerivedSI **R** = N_A ∘ k.

  Build: `lake build ChemConstants.ExactSiInteger`

  Named Madelung occupancy exceptions (`CHEM-FORMAL-Q-LEAN-NAMED-OCCUPANCY-EXCEPTIONS`):
  finite `NamedException` set La / Ce / Gd / Pt / Au — cites qlattice + madelung_witness, not
  second axiom.

  Build: `lake build ChemConstants.NamedOccupancyExceptions`

  Actinide qlattice occupancy exceptions (`CHEM-FORMAL-Q-LEAN-ACTINIDE-OCCUPANCY-EXCEPTIONS`):
  finite `ActinideException` set Ac / Th / Pa / U / Np / Cm / Lr — cites qlattice +
  madelung_witness, not second axiom; Lr named override agrees Madelung honest.

  Build: `lake build ChemConstants.ActinideOccupancyExceptions`

  D-block qlattice occupancy exceptions (`CHEM-FORMAL-Q-LEAN-DBLOCK-OCCUPANCY-EXCEPTIONS`):
  finite `DBlockException` set Cr / Cu / Nb / Mo / Ru / Rh / Pd / Ag — cites qlattice +
  madelung_witness, not second axiom; DISTINCT from NamedException and ActinideException.

  Build: `lake build ChemConstants.DBlockOccupancyExceptions`

  Occupancy exception Z-set disjointness (`CHEM-FORMAL-Q-LEAN-OCCUPANCY-EXCEPTION-SETS-DISJOINT`):
  Lean composition of Named / Actinide / DBlock occupancy exception modules — pairwise disjoint
  Z-sets; Z = 94 (Pu) in none; Z = 103 (Lr) in actinide not named; Unwired, not GREEN DFT.

  Build: `lake build ChemConstants.OccupancyExceptionSetsDisjoint`

  SCALE occupancy Z-identity commute (`CHEM-FORMAL-Q-LEAN-SCALE-OCCUPANCY-Z-COMMUTE`):
  `liftQM` / `liftMM` / `coarseQM` identity placeholders; Z-identity commute; Ds (110) ≠ Pt (78)
  homolog not copy; Unwired, not SCALE-01 physics GREEN.

  Build: `lake build ChemConstants.ScaleOccupancyZCommute`

  ECO-02 consume-not-fork (`CHEM-FORMAL-Q-LEAN-ECO-02-CONSUME-NOT-FORK`):
  one learner spine; `chemForksLiquidPpoKernel` / `burnKernelCopiedToChem` /
  `liquidPpoProductionWired` false; `bindAntichainUntilMeasured` true; Unwired, not physics GREEN.

  Build: `lake build ChemConstants.Eco02ConsumeNotFork`

  CAT-03 adjunction-cost Landauer (`CHEM-FORMAL-Q-LEAN-ADJUNCTION-COST-LANDAUER`):
  `purewardCost` nonnegative; `freePurificationAdmitted` false when contaminants;
  purification implies positive `minPurewardCost`; Unwired, not CAT-03 Proved, not physics GREEN.

  Build: `lake build ChemConstants.AdjunctionCostLandauer`

  Ore monoidal conservation (`CHEM-FORMAL-Q-LEAN-ORE-MONOIDAL-CONSERVATION`):
  `OreTree` leaf/tensor; unit `I`; associator; product Π_c not XOR;
  `monoidalLawsProved` false; Unwired, not CAT-01 Proved, not 118² GREEN, not physics GREEN.

  Build: `lake build ChemConstants.OreMonoidalConservation`

  Kleisli interact conservation (`CHEM-FORMAL-Q-LEAN-KLEISLI-INTERACT-CONSERVATION`):
  `InteractStep` identity/compose; associator; morphism identity conserved;
  `kleisliLawsProved` false; Unwired, not CAT-00 Proved, not physics GREEN.

  Build: `lake build ChemConstants.KleisliInteractConservation`

  Pullback/pushout conservation (`CHEM-FORMAL-Q-LEAN-PULLBACK-CONSERVATION`):
  `PullbackStep` identity/pullback/pushout; shared-substructure identity conserved;
  `universalPropertiesProved` false; Unwired, not CAT-02 Proved, not physics GREEN.

  Build: `lake build ChemConstants.PullbackConservation`

  Coalgebra conservation (`CHEM-FORMAL-Q-LEAN-COALGEBRA-CONSERVATION`):
  `CoalgebraStep` identity/unfold/fold; ore identity conserved;
  `coalgebraLawsProved` false; Unwired, not CAT-04 Proved, not physics GREEN.

  Build: `lake build ChemConstants.CoalgebraConservation`

  Dependent types conservation (`CHEM-FORMAL-Q-LEAN-DEPENDENT-TYPES-CONSERVATION`):
  ElementId-indexed geometry/thermo; identity conserved;
  `speciesIsL1` true; `type01DepProved` false; Unwired, not TYPE-01 Proved, not physics GREEN.

  Build: `lake build ChemConstants.DependentTypesConservation`

  Linear conservation (`CHEM-FORMAL-Q-LEAN-LINEAR-CONSERVATION`):
  ConservationAxis Mass/Charge/AtomCount/Enthalpy; signed linear exact-balance;
  affine weakening with dissipative witness; `type02LinearProved` false;
  Unwired, not TYPE-02 Proved, not 118² GREEN, not physics GREEN.

  Build: `lake build ChemConstants.LinearConservation`

  Modality conservation (`CHEM-FORMAL-Q-LEAN-MODALITY-CONSERVATION`):
  TYPE-03 claim modality lattice Unwired/Assumed/Proved/Surrogate; path census;
  Unwired OK without census; Proved without census refuse; Proved with defects refuse;
  `type03ModalityProved` false; Unwired, not TYPE-03 Proved, not 118² GREEN, not physics GREEN.

  Build: `lake build ChemConstants.ModalityConservation`

  Effect conservation (`CHEM-FORMAL-Q-LEAN-EFFECT-CONSERVATION`):
  TYPE-04 dissipative effect conservation; Unwired/Assumed/Proved/Surrogate;
  forward Refine requires positive ChemStamp/Landauer witness; free purification refuse;
  reverse contaminate typed; `type04EffectProved` false; Unwired, not TYPE-04 Proved,
  not 118² GREEN, not physics GREEN.

  Build: `lake build ChemConstants.EffectConservation`

  Partial conservation (`CHEM-FORMAL-Q-LEAN-PARTIAL-CONSERVATION`):
  TYPE-05 partial Interact conservation; Unwired/Assumed/Proved/Surrogate;
  admissible vs forbidden partial Interact; total-claim refuse;
  `type05PartialProved` false; Unwired, not TYPE-05 Proved,
  not 118² GREEN, not physics GREEN.

  Build: `lake build ChemConstants.PartialConservation`

  Fold conservation (`CHEM-FORMAL-Q-LEAN-FOLD-CONSERVATION`):
  FP-01 classifier-fold conservation; Unwired/Assumed/Proved/Surrogate;
  conjunctive / disjunctive fold identity conserved; GREEN invent refuse;
  `fp01FoldProved` false; Unwired, not FP-01 Proved,
  not 118² GREEN, not physics GREEN.

  Build: `lake build ChemConstants.FoldConservation`

  Fixpoint conservation (`CHEM-FORMAL-Q-LEAN-FIXPOINT-CONSERVATION`):
  FP-02 fixpoint conservation; Unwired/Assumed/Proved/Surrogate;
  lattice meet/join identity conserved; monotone chain reaches fixed point;
  `fp02FixpointProved` false; Unwired, not FP-02 Proved,
  not 118² GREEN, not physics GREEN.

  Build: `lake build ChemConstants.FixpointConservation`

  Rewrite conservation (`CHEM-FORMAL-Q-LEAN-REWRITE-CONSERVATION`):
  FP-03 rewrite conservation; Unwired/Assumed/Proved/Surrogate;
  thermo-preserving fusion identity conserved; non-preserving step fail-closed;
  `fp03RewriteProved` false; Unwired, not FP-03 Proved,
  not 118² GREEN, not physics GREEN.

  Build: `lake build ChemConstants.RewriteConservation`

  Bond conservation (`CHEM-FORMAL-Q-LEAN-BOND-CONSERVATION`):
  GRAPH-01 bond/reaction edge conservation; Unwired/Assumed/Proved/Surrogate;
  named H–O bond Z=1/8; Og Z=118; forward hydration named; self-loop fail-closed;
  `graph01BondProved` false; Unwired, not GRAPH-01 Proved,
  not 118² GREEN, not physics GREEN.

  Build: `lake build ChemConstants.BondConservation`

  Cut conservation (`CHEM-FORMAL-Q-LEAN-CUT-CONSERVATION`):
  GRAPH-02 cut/separation conservation; Unwired/Assumed/Proved/Surrogate;
  ore/waste partition complement conserved; Fe Z=26; recycle Cu loop Z=29; Og Z=118;
  trivial cut fail-closed; cut ≠ bond; `graph02CutProved` false; Unwired, not GRAPH-02 Proved,
  not 118² GREEN, not physics GREEN.

  Build: `lake build ChemConstants.CutConservation`

  Hyper conservation (`CHEM-FORMAL-Q-LEAN-HYPER-CONSERVATION`):
  GRAPH-03 hypergraph incidence conservation; Unwired/Assumed/Proved/Surrogate;
  multi-constituent ore incidence identity conserved; ternary arity; hematite ≠ gangue;
  Fe Z=26; Og Z=118; trivial hyper fail-closed; hyper ≠ bond; no petgraph fork;
  `graph03HyperProved` false; Unwired, not GRAPH-03 Proved,
  not 118² GREEN, not physics GREEN.

  Build: `lake build ChemConstants.HyperConservation`

  Dissip conservation (`CHEM-FORMAL-Q-LEAN-DISSIP-CONSERVATION`):
  GRAPH-04 **dissip** conservation; Unwired/Assumed/Proved/Surrogate;
  cyclic vs **dissip**ative path identity conserved; reaction-cycle closed;
  bond-path **dissip**ative typed; Fe Z=26; Cu Z=29; Og Z=118;
  trivial **dissip** fail-closed; **dissip** ≠ **bond**; no petgraph fork;
  `graph04DissipProved` false; Unwired, not GRAPH-04 Proved,
  not 118² GREEN, not physics GREEN.

  Build: `lake build ChemConstants.DissipConservation`

  Pattern product conservation (`CHEM-FORMAL-Q-LEAN-PATTERN-PRODUCT-CONSERVATION`):
  PATTERN-00 **PatternBundle** concurrent **product** conservation; Unwired/Assumed/Proved/Surrogate;
  Π_c identity conserved (cardinality 25; ≥2 Present is **product** not XOR);
  carbon nuance allotrope + catalysis + continuum concurrent; XOR mutually-exclusive refuse;
  `pattern00ProductProved` false; Unwired, not PATTERN-00 Proved,
  not 118² GREEN, not physics GREEN.

  Build: `lake build ChemConstants.PatternProductConservation`

  Scale conservation (`CHEM-FORMAL-Q-LEAN-SCALE-CONSERVATION`):
  SCALE-01 **scale** commuting-square **conservation**; Unwired/Assumed/Proved/Surrogate;
  three named legs Q→meso→macro; composed indirect equals Q→macro direct typed **conservation**;
  distinct from ScaleOccupancyZCommute Z-lift; Ds 110 not Pt 78 homolog not copy;
  `scale01CommuteProved` false; Unwired, not SCALE-01 Proved,
  not 118² GREEN, not physics GREEN.

  Build: `lake build ChemConstants.ScaleConservation`

  Density conservation (`CHEM-FORMAL-Q-LEAN-DENSITY-CONSERVATION`):
  DENSITY-01 **density** ladder order **conservation**; Unwired/Assumed/Proved/Surrogate;
  four rungs mSDF→TE-SDF→SDF→FRep; composed indirect equals mSDF→FRep direct typed **conservation**;
  SDF ≠ ρ unless named; live TE-SDF refuse; `densityLadderProved` false; Unwired,
  not DensityLadder Proved, not 118² GREEN, not physics GREEN.

  Build: `lake build ChemConstants.DensityConservation`

  Thermo conservation (`CHEM-FORMAL-Q-LEAN-THERMO-CONSERVATION`):
  THERMO-01 **Thermo_n G(T,P,x) conservation**; Unwired/Assumed/Proved/Surrogate;
  T, P, x named; composed T∘P∘x equals direct G typed **conservation**;
  CALPHAD hull identity conserved; formation-zero ≠ G; measured-scalar invent refuse;
  scrambled order refuse; live Process G refuse; `thermoGProved` false; Unwired,
  not Thermo_n Proved, not 118² GREEN, not physics GREEN.

  Build: `lake build ChemConstants.ThermoConservation`

  Goldschmidt conservation (`CHEM-FORMAL-Q-LEAN-GOLDSCHMIDT-CONSERVATION`):
  GOLDSCHMIDT-01 **ore-class** **conservation**; Unwired/Assumed/Proved/Surrogate;
  lithophile/chalcophile/siderophile class 6⊗7⊗17 concurrent Ore⊗G⊗fO₂ **product** not XOR;
  Fe Z=26 metal/oxide/sulfide same Z; Cu Z=29; Si Z=14; He Z=2 closed-shell no-ore;
  folklore/GREEN/trivial/XOR refuse; `goldschmidtProved` false; Unwired, not Goldschmidt Proved,
  not 118² GREEN, not physics GREEN.

  Build: `lake build ChemConstants.GoldschmidtConservation`

  Allotrope conservation (`CHEM-FORMAL-Q-LEAN-ALLOTROPE-CONSERVATION`):
  ALLOTROPE-01 **allotrope-net** **conservation**; Unwired/Assumed/Proved/Surrogate;
  crystallineLattice/layeredGraphitic/amorphousDisordered class 10⊗11⊗12 concurrent Net⊗Scale⊗Edge **product** not XOR;
  C Z=6 diamond/graphite/fullerene same Z; Si Z=14; O Z=8; He Z=2 closed-shell no-allotrope;
  folklore/GREEN/trivial/XOR refuse; `allotropeProved` false; Unwired, not ALLOTROPE Proved,
  not 118² GREEN, not physics GREEN.

  Build: `lake build ChemConstants.AllotropeConservation`

  Chem-physics chart isomorphism (`CHEM-FORMAL-Q-LEAN-CHEM-PHYSICS-CHART-ISOMORPHISM-CONSERVATION`):
  chemistry is occupancy physics; constitutive engines named charts one second-law conservation object;
  chart isomorphism Thermo_n / DensityLadder / SCALE-01 / Occupancy same Z distinct chart names;
  separate-object-per-chart refuse; WAVE100 lib.rs/eos.rs smuggle refuse; XOR enum refuse;
  not fourth chemistry science; not 26th axiom; `chemPhysicsChartIsomorphismProved` false; Unwired,
  not physics GREEN.

  Build: `lake build ChemConstants.ChemPhysicsChartIsomorphism`

  Cartridge constitutive compose (`CHEM-FORMAL-Q-LEAN-CARTRIDGE-CONSTITUTIVE-COMPOSE-CONSERVATION`):
  cartridge ψ/𝒟 additive compose matter-fiber dual of chem Ore product not XOR;
  consult ChemistryService; no second periodic table; XOR cartridge merge refused;
  WAVE100 lib.rs/eos.rs smuggle refuse; `cartridgeComposeProved` false; Unwired,
  not physics GREEN.

  Build: `lake build ChemConstants.CartridgeConstitutiveCompose`

  Cement hydration not-L0-G (`CHEM-FORMAL-Q-LEAN-CEMENT-HYDRATION-NOT-L0-G-CONSERVATION`):
  continuum hydration α in ψ is L1 occupancy of one cementitious material, not the L0 G-engine;
  `hydrationAlphaIsL0GEngine` false; `cementHydrationNotL0GProved` false; Unwired,
  not physics GREEN.

  Build: `lake build ChemConstants.CementHydrationNotL0G`

  Cartridge Ore consult monoid (`CHEM-FORMAL-Q-LEAN-CARTRIDGE-ORE-CONSULT-MONOID-CONSERVATION`):
  C-S-H (Ca,Si,O,H) and pore solution (Na,Cl,O,H) are Ore consults, not ElementId smuggle;
  Z=1..118 assemblage pattern; consult ChemistryService; no second periodic table;
  `cartridgeOreConsultMonoidProved` false; Unwired, not physics GREEN.

  Build: `lake build ChemConstants.CartridgeOreConsultMonoid`

  DLVO kT not-ψ (`CHEM-FORMAL-Q-LEAN-DLVO-KT-NOT-PSI-CONSERVATION`):
  fluids DLVO kT is a coefficient pin, not constitutive ψ; ExactSI k is a unit morphism;
  engines sort the sheaf; no Landauer-fake constants; `dlvoKtNotPsiProved` false; Unwired,
  not physics GREEN.

  Build: `lake build ChemConstants.DlvoKtNotPsi`

  Engine refuses new SI (`CHEM-FORMAL-Q-LEAN-ENGINE-REFUSES-NEW-SI-CONSERVATION`):
  constitutive engines sort using the existing SI/occupancy/derived-morphism sheaf; they do not
  mint k, R, or ε₀; ExactSI constants are unit morphisms; `engineRefusesNewSiProved` false;
  Unwired, not physics GREEN.

  Build: `lake build ChemConstants.EngineRefusesNewSi`

  Natural occurrence Z118 (`CHEM-FORMAL-Q-LEAN-NATURAL-OCCURRENCE-Z118-CONSERVATION`):
  Z=1..118 natural occurrence class table as Unwired named product classifiers
  (native/oxide/sulfide/silicate/halide+carbonate/atmophile/synthetic-or-trace); not folklore
  lists; concurrent product bits not XOR enum; He atmophile-only; Fe native⊗oxide⊗sulfide product;
  `naturalOccurrenceZ118Proved` false; Unwired, not physics GREEN.

  Build: `lake build ChemConstants.NaturalOccurrenceZ118`

  Occurrence family pattern (`CHEM-FORMAL-Q-LEAN-OCCURRENCE-FAMILY-PATTERN-CONSERVATION`):
  occurrence-class families are concurrent product classifiers (7 tags); ore-engine sorts outliers
  (native Au Z=79 vs oxide-product Fe Z=26 vs closed-shell He atmophile no-ore Z=2); same Z many
  assemblages; not folklore exclusive lists; not XOR enum; `occurrenceFamilyPatternProved` false;
  Unwired, not physics GREEN.

  Build: `lake build ChemConstants.OccurrenceFamilyPattern`

  Occupancy engine sort (`CHEM-FORMAL-Q-LEAN-OCCUPANCY-ENGINE-SORT-CONSERVATION`):
  occupancy engine sorts Madelung family vs Named / Actinide / DBlock exception families;
  Pu 94 absent; homolog ≠ copy (Ds 110 not Pt 78); `occupancyEngineSortProved` false;
  Unwired, not physics GREEN.

  Build: `lake build ChemConstants.OccupancyEngineSort`

  Interact engine closed shell (`CHEM-FORMAL-Q-LEAN-INTERACT-ENGINE-CLOSED-SHELL-CONSERVATION`):
  interact-engine sorts closed-shell blocking / partial Interact refuse / catalysis-not-axiom;
  He no-ore = missing Interact class 5 structure_blocking_inertness, not nobility magic;
  `interactEngineClosedShellProved` false; Unwired, not physics GREEN.

  Build: `lake build ChemConstants.InteractEngineClosedShell`

  Outlier-is-theorem (`CHEM-FORMAL-Q-LEAN-OUTLIER-IS-THEOREM-CONSERVATION`):
  Z=1..118 / Interact / Ore / Refine outliers sorted to theorem | deferred composition remainder |
  typed Absent — not folklore outlier; `outlierIsTheoremProved` false; Unwired, not physics GREEN.

  Build: `lake build ChemConstants.OutlierIsTheorem`

  Madelung-exception-is-theorem (`CHEM-FORMAL-Q-LEAN-MADELUNG-EXCEPTION-IS-THEOREM-CONSERVATION`):
  Named / Actinide / DBlock occupancy exceptions are occupancy-engine sort theorems (observed ≠
  Madelung family); Lr honest override; Pu 94 absent; homolog ≠ copy (Ds vs Pt); terminals
  theorem | deferred composition | typed Absent; `madelungExceptionIsTheoremProved` false; Unwired,
  not physics GREEN.

  Build: `lake build ChemConstants.MadelungExceptionIsTheorem`

  Heavy-Z relativistic continuum (`CHEM-FORMAL-Q-LEAN-HEAVY-Z-RELATIVISTIC-CONTINUUM-CONSERVATION`):
  Cn Z=112 / Fl Z=114 / Og Z=118 relativistic continuum named chart same ChemObject second law
  conservation; not Xe/Rn noble-gas copy; homolog ≠ copy; terminals theorem | deferred composition |
  typed Absent; `heavyZRelativisticContinuumProved` false; Unwired, not physics GREEN.

  Build: `lake build ChemConstants.HeavyZRelativisticContinuum`

  Cross-domain breakthrough protocol (`CHEM-FORMAL-Q-LEAN-CROSS-DOMAIN-BREAKTHROUGH-PROTOCOL-CONSERVATION`):
  X40 cross-domain breakthrough protocol conservation; four fibers from one second-law + conservation
  axiom; honest terminals NewChart / CommutingSquare / NamedRemainder; NewAxiom / Folklore refused;
  cite chem_physics_chart_isomorphism not fork; not 27th axiom; `crossDomainBreakthroughProtocolProved`
  false; Unwired, not physics GREEN.

  Build: `lake build ChemConstants.CrossDomainBreakthroughProtocol`

  Composer research bleeding-edge (`CHEM-FORMAL-Q-LEAN-COMPOSER-RESEARCH-BLEEDING-EDGE-CONSERVATION`):
  umst-chem-research named hypotheses only; research chart conservation on one axiom object;
  cite CHEM_NS_V50_RESEARCH_HYPOTHESES.json read-only; literature new-axiom refused;
  `composerResearchBleedingEdgeProved` false; Unwired, not physics GREEN.

  Build: `lake build ChemConstants.ComposerResearchBleedingEdge`

  Constant-derive second-law census (`CHEM-FORMAL-Q-LEAN-CONSTANT-DERIVE-SECOND-LAW-CENSUS-CONSERVATION`):
  engines consult ExactSI / occupancy / derived-morphism sheaf; do not mint k/R/ε₀;
  α MeasuredCited not Landauer-faked; cite constant_derive_second_law_census.rs not fork;
  sorting cites upstream sheaf pins — not 26th axiom; `constantDeriveSecondLawCensusProved` false;
  Unwired, not physics GREEN.

  Build: `lake build ChemConstants.ConstantDeriveSecondLawCensus`

  Fine-structure α measured remainder (`CHEM-FORMAL-Q-LEAN-FINE-STRUCTURE-ALPHA-MEASURED-REMAINDER-CONSERVATION`):
  CODATA MeasuredCited α deferred composition on second law conservation; consume
  vacuum_permittivity_si_derived not fork; Landauer kT ln 2 alpha derive refused not Landauer-fake;
  not impossibility rest; not 26th axiom; `fineStructureAlphaMeasuredRemainderProved` false;
  Unwired, not physics GREEN.

  Build: `lake build ChemConstants.FineStructureAlphaMeasuredRemainder`

  Continuum pattern-learn (`CHEM-FORMAL-Q-LEAN-CONTINUUM-PATTERN-LEARN-CONSERVATION`):
  X55 named chart concurrent §2 pattern classifiers along vacuum | contained | messy continuum;
  cite pattern_taxonomy SSOT not live PatternBundle Π_c wire; Π_c product not XOR;
  consumes graph liquid-PPO MI observation consume-not-fork BIND antichain;
  explicit env coordinates 15 16 19 20 21 22 not extra axioms; not 26th axiom;
  `continuumPatternLearnProved` false; Unwired, not physics GREEN.

  Build: `lake build ChemConstants.ContinuumPatternLearn`

  Per-element nuance conservation (`CHEM-FORMAL-Q-LEAN-PER-ELEMENT-NUANCE-CONSERVATION`):
  PATTERN-00 class 0 **per_element_nuance** concurrent Π_c factor not XOR; occupied Q-lattice +
  thermo graph + PSP per Z product; homolog ≠ copy; XOR / parallel axiom / GREEN invent refuse;
  cite INT x_row read-only; `perElementNuanceConservationProved` false; Unwired, not physics GREEN.

  Build: `lake build ChemConstants.PerElementNuanceConservation`

  Shared conservation (`CHEM-FORMAL-Q-LEAN-SHARED-CONSERVATION`):
  PATTERN-00 class 1 **shared** concurrent Π_c identity conserved; CEF sublattice + QTAIM bond paths +
  CAT-02 pullback; shared sites neighbor not independent SpeciesId; product not XOR;
  `pattern00SharedProved` false; `cat02PullbackProved` false; Unwired, not physics GREEN.

  Build: `lake build ChemConstants.SharedConservation`
-/
lean_lib ChemConstants where
  roots := #[`ChemConstants.ExactSiInteger, `ChemConstants.NamedOccupancyExceptions,
    `ChemConstants.ActinideOccupancyExceptions, `ChemConstants.DBlockOccupancyExceptions,
    `ChemConstants.OccupancyExceptionSetsDisjoint, `ChemConstants.ScaleOccupancyZCommute,
    `ChemConstants.Eco02ConsumeNotFork, `ChemConstants.AdjunctionCostLandauer,
    `ChemConstants.OreMonoidalConservation, `ChemConstants.KleisliInteractConservation,
    `ChemConstants.PullbackConservation, `ChemConstants.CoalgebraConservation,
    `ChemConstants.DependentTypesConservation, `ChemConstants.LinearConservation,
    `ChemConstants.ModalityConservation, `ChemConstants.EffectConservation,
    `ChemConstants.PartialConservation, `ChemConstants.FoldConservation,
    `ChemConstants.FixpointConservation, `ChemConstants.RewriteConservation,
    `ChemConstants.BondConservation, `ChemConstants.CutConservation,
    `ChemConstants.HyperConservation, `ChemConstants.DissipConservation,
    `ChemConstants.PatternProductConservation, `ChemConstants.ScaleConservation,
    `ChemConstants.DensityConservation, `ChemConstants.ThermoConservation,
    `ChemConstants.GoldschmidtConservation, `ChemConstants.AllotropeConservation,
    `ChemConstants.ChemPhysicsChartIsomorphism,     `ChemConstants.CartridgeConstitutiveCompose,
    `ChemConstants.CementHydrationNotL0G,
    `ChemConstants.CartridgeOreConsultMonoid,
    `ChemConstants.DlvoKtNotPsi,
    `ChemConstants.EngineRefusesNewSi,
    `ChemConstants.NaturalOccurrenceZ118,
    `ChemConstants.OccurrenceFamilyPattern,
    `ChemConstants.OccupancyEngineSort,
    `ChemConstants.InteractEngineClosedShell,
    `ChemConstants.OutlierIsTheorem,
    `ChemConstants.MadelungExceptionIsTheorem,
    `ChemConstants.HeavyZRelativisticContinuum,
    `ChemConstants.CrossDomainBreakthroughProtocol,
    `ChemConstants.ComposerResearchBleedingEdge,
    `ChemConstants.ConstantDeriveSecondLawCensus,
    `ChemConstants.FineStructureAlphaMeasuredRemainder,
    `ChemConstants.ContinuumPatternLearn,
    `ChemConstants.PerElementNuanceConservation,
    `ChemConstants.SharedConservation]
  srcDir := "."

/-- Emit `artifacts/catalog.json` (repo root): pinned Lake roots + schema; see `../tools/lean_export/README.md`. -/
lean_exe export_catalog where
  root := `ExportCatalog
  srcDir := "../tools/lean_export"
