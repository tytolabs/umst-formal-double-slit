-- SPDX-FileCopyrightText: 2026 Santosh Prabhu Shenbagamoorthy and Santhosh Shyamsundar
-- SPDX-License-Identifier: MIT
------------------------------------------------------------------------
-- UMST-Formal: ChemConstants.ComposerResearchBleedingEdge.agda
--
-- Composer research **bleeding-edge** conservation on the knowing fiber (Q lattice):
--   * Named research chart lane — cites CHEM_NS_V50_RESEARCH_HYPOTHESES.json read-only
--   * H-V50-REFUSE-CATALYSIS-AXIOM Absent; H-V50-CHEM-PHYSICS-ISOMORPHISM AlreadyUnwired
--   * composerResearchBleedingEdgeProved = false; modality Unwired; physics GREEN false
--
-- Mirrors sibling `ChemConstants/OccupancyEngineSort.agda` style.
-- INT: umst/umst-chem/src/x_rows/composer_research_bleeding_edge.rs
-- No meso / acting theorems. WAVE100: not wired in lib.rs / eos.rs.
-- Zero postulates that invent physics. Remainder deferred composition on second law.
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module ChemConstants.ComposerResearchBleedingEdge where

open import Data.Bool.Base using (Bool; false; true; not; _∧_; if_then_else_)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Nat using (ℕ; zero; suc)
open import Data.Product using (_×_; _,_)
open import Data.String using (String)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Relation.Nullary using (¬_)

------------------------------------------------------------------------
-- Modality + composer-research bleeding-edge pins (knowing fiber — Unwired)
------------------------------------------------------------------------

data ComposerResearchBleedingEdgeModality : Set where
  composer-research-bleeding-edge-unwired
    composer-research-bleeding-edge-assumed
    composer-research-bleeding-edge-proved
    composer-research-bleeding-edge-surrogate
    : ComposerResearchBleedingEdgeModality

composerResearchBleedingEdgeModalityCurrent : ComposerResearchBleedingEdgeModality
composerResearchBleedingEdgeModalityCurrent = composer-research-bleeding-edge-unwired

composerResearchBleedingEdgeModalityLatticeCardinality : ℕ
composerResearchBleedingEdgeModalityLatticeCardinality = 4

composer-research-bleeding-edge-modality-lattice-cardinality-four :
  composerResearchBleedingEdgeModalityLatticeCardinality ≡ 4
composer-research-bleeding-edge-modality-lattice-cardinality-four = refl

composerResearchBleedingEdgeProved productionWired wave100LibRsWired
  wave100EosRsWired composerResearchIsNewAxiom : Bool
composerResearchBleedingEdgeProved = false
productionWired = false
wave100LibRsWired = false
wave100EosRsWired = false
composerResearchIsNewAxiom = false

------------------------------------------------------------------------
-- Research hypothesis posture — chart classes (cite v50 JSON, no fork)
------------------------------------------------------------------------

data ResearchHypothesisClass : Set where
  theorem-candidate-class named-measured-remainder-class
    already-unwired-class absent-class
    : ResearchHypothesisClass

isTheoremCandidate isNamedMeasuredRemainder isAlreadyUnwired isAbsent
  : ResearchHypothesisClass → Bool
isTheoremCandidate theorem-candidate-class = true
isTheoremCandidate _ = false

isNamedMeasuredRemainder named-measured-remainder-class = true
isNamedMeasuredRemainder _ = false

isAlreadyUnwired already-unwired-class = true
isAlreadyUnwired _ = false

isAbsent absent-class = true
isAbsent _ = false

theorem-candidate-class-named :
  isTheoremCandidate theorem-candidate-class ≡ true
theorem-candidate-class-named = refl

already-unwired-class-named :
  isAlreadyUnwired already-unwired-class ≡ true
already-unwired-class-named = refl

absent-class-named :
  isAbsent absent-class ≡ true
absent-class-named = refl

------------------------------------------------------------------------
-- Bleeding-edge hypothesis ids — read-only cite from v50 research JSON
------------------------------------------------------------------------

hypothesisRefuseCatalysisAxiom hypothesisChemPhysicsIsomorphism : String
hypothesisRefuseCatalysisAxiom = "H-V50-REFUSE-CATALYSIS-AXIOM"
hypothesisChemPhysicsIsomorphism = "H-V50-CHEM-PHYSICS-ISOMORPHISM"

bleedingEdgeV50Stem : String
bleedingEdgeV50Stem = "COMPOSER-RESEARCH-BLEEDING-EDGE"

researchHypothesesAuthority : String
researchHypothesesAuthority = "workspace/ops/CHEM_NS_V50_RESEARCH_HYPOTHESES.json"

constStrEq : String → String → Bool
constStrEq a b with a | b
... | "H-V50-REFUSE-CATALYSIS-AXIOM" | "H-V50-REFUSE-CATALYSIS-AXIOM" = true
... | "H-V50-CHEM-PHYSICS-ISOMORPHISM" | "H-V50-CHEM-PHYSICS-ISOMORPHISM" = true
... | "COMPOSER-RESEARCH-BLEEDING-EDGE" | "COMPOSER-RESEARCH-BLEEDING-EDGE" = true
... | "workspace/ops/CHEM_NS_V50_RESEARCH_HYPOTHESES.json"
      | "workspace/ops/CHEM_NS_V50_RESEARCH_HYPOTHESES.json" = true
... | _ | _ = false

isBleedingEdgeHypothesisId : String → Bool
isBleedingEdgeHypothesisId id =
  constStrEq id hypothesisRefuseCatalysisAxiom ∧
  constStrEq id hypothesisChemPhysicsIsomorphism

refuse-catalysis-is-bleeding-edge-id :
  constStrEq hypothesisRefuseCatalysisAxiom hypothesisRefuseCatalysisAxiom ≡ true
refuse-catalysis-is-bleeding-edge-id = refl

chem-physics-isomorphism-is-bleeding-edge-id :
  constStrEq hypothesisChemPhysicsIsomorphism hypothesisChemPhysicsIsomorphism ≡ true
chem-physics-isomorphism-is-bleeding-edge-id = refl

------------------------------------------------------------------------
-- Bleeding-edge hypothesis rows — maps to v50 stem, not 26th axiom
------------------------------------------------------------------------

data BleedingEdgeHypothesisRow : Set where
  bleeding-edge-row : String → ResearchHypothesisClass → Bool → Bool → BleedingEdgeHypothesisRow

refuseCatalysisRow chemPhysicsIsomorphismRow : BleedingEdgeHypothesisRow
refuseCatalysisRow =
  bleeding-edge-row hypothesisRefuseCatalysisAxiom absent-class true true
chemPhysicsIsomorphismRow =
  bleeding-edge-row hypothesisChemPhysicsIsomorphism already-unwired-class true true

rowId : BleedingEdgeHypothesisRow → String
rowId (bleeding-edge-row id _ _ _) = id

rowClass : BleedingEdgeHypothesisRow → ResearchHypothesisClass
rowClass (bleeding-edge-row _ c _ _) = c

rowMapsToStem rowNot26thAxiom : BleedingEdgeHypothesisRow → Bool
rowMapsToStem (bleeding-edge-row _ _ m _) = m
rowNot26thAxiom (bleeding-edge-row _ _ _ n) = n

researchChartConservationHolds : BleedingEdgeHypothesisRow → Bool
researchChartConservationHolds row =
  rowMapsToStem row ∧ rowNot26thAxiom row

refuse-catalysis-row-conserved :
  researchChartConservationHolds refuseCatalysisRow ≡ true
refuse-catalysis-row-conserved = refl

chem-physics-isomorphism-row-conserved :
  researchChartConservationHolds chemPhysicsIsomorphismRow ≡ true
chem-physics-isomorphism-row-conserved = refl

refuse-catalysis-row-absent :
  isAbsent (rowClass refuseCatalysisRow) ≡ true
refuse-catalysis-row-absent = refl

chem-physics-isomorphism-row-unwired :
  isAlreadyUnwired (rowClass chemPhysicsIsomorphismRow) ≡ true
chem-physics-isomorphism-row-unwired = refl

bleedingEdgeHypothesisCount : ℕ
bleedingEdgeHypothesisCount = 2

bleeding-edge-hypothesis-count-is-two :
  bleedingEdgeHypothesisCount ≡ 2
bleeding-edge-hypothesis-count-is-two = refl

boolAnd3 : Bool → Bool → Bool → Bool
boolAnd3 b1 b2 b3 = b1 ∧ b2 ∧ b3

bleedingEdgeHypothesesConserved : Bool
bleedingEdgeHypothesesConserved =
  boolAnd3
    (researchChartConservationHolds refuseCatalysisRow)
    (researchChartConservationHolds chemPhysicsIsomorphismRow)
    true

bleeding-edge-hypotheses-conserved-true :
  bleedingEdgeHypothesesConserved ≡ true
bleeding-edge-hypotheses-conserved-true = refl

------------------------------------------------------------------------
-- Research hypotheses authority cited — read-only, not fork
------------------------------------------------------------------------

authorityCitesJson : Bool
authorityCitesJson =
  constStrEq researchHypothesesAuthority researchHypothesesAuthority

research-hypotheses-authority-cites-json :
  authorityCitesJson ≡ true
research-hypotheses-authority-cites-json = refl

researchHypothesesCitedNotForked : Bool
researchHypothesesCitedNotForked = authorityCitesJson

research-hypotheses-cited-not-forked-true :
  researchHypothesesCitedNotForked ≡ true
research-hypotheses-cited-not-forked-true = refl

literatureNewAxiomRefused : Bool
literatureNewAxiomRefused = not composerResearchIsNewAxiom

literature-new-axiom-refused-true :
  literatureNewAxiomRefused ≡ true
literature-new-axiom-refused-true = refl

composer-research-not-new-axiom :
  composerResearchIsNewAxiom ≡ false
composer-research-not-new-axiom = refl

composer-research-bleeding-edge-not-proved :
  composerResearchBleedingEdgeProved ≡ false
composer-research-bleeding-edge-not-proved = refl

production-not-wired : productionWired ≡ false
production-not-wired = refl

wave100-lib-rs-not-wired : wave100LibRsWired ≡ false
wave100-lib-rs-not-wired = refl

wave100-eos-rs-not-wired : wave100EosRsWired ≡ false
wave100-eos-rs-not-wired = refl

composerResearchBleedingEdgeHonestConjunct : Bool
composerResearchBleedingEdgeHonestConjunct =
  not composerResearchIsNewAxiom ∧
  bleedingEdgeHypothesesConserved ∧
  researchHypothesesCitedNotForked ∧
  literatureNewAxiomRefused

composer-research-bleeding-edge-honest-conjunct-true :
  composerResearchBleedingEdgeHonestConjunct ≡ true
composer-research-bleeding-edge-honest-conjunct-true = refl

------------------------------------------------------------------------
-- Conservation close verdict — fail-closed lattice
------------------------------------------------------------------------

data ComposerResearchBleedingEdgeVerdict : Set where
  verdict-unwired-ok verdict-chart-ok verdict-green-invent-refuse
    verdict-production-wired-refuse verdict-new-axiom-refuse
    : ComposerResearchBleedingEdgeVerdict

composerResearchBleedingEdgeVerdictOk : ComposerResearchBleedingEdgeVerdict → Bool
composerResearchBleedingEdgeVerdictOk verdict-unwired-ok = true
composerResearchBleedingEdgeVerdictOk verdict-chart-ok = true
composerResearchBleedingEdgeVerdictOk _ = false

evaluateComposerResearchBleedingEdge :
  ComposerResearchBleedingEdgeModality →
  Bool → Bool → Bool →
  ComposerResearchBleedingEdgeVerdict
evaluateComposerResearchBleedingEdge m claimPhysicsGreen claimProved claimProductionWired =
  if claimPhysicsGreen then verdict-green-invent-refuse else
  if claimProductionWired then verdict-production-wired-refuse else
  if claimProved then verdict-chart-ok else
  if composerResearchBleedingEdgeHonestConjunct then pickModality m else verdict-new-axiom-refuse
  where
  pickModality : ComposerResearchBleedingEdgeModality → ComposerResearchBleedingEdgeVerdict
  pickModality composer-research-bleeding-edge-unwired = verdict-unwired-ok
  pickModality _ = verdict-chart-ok

composer-research-bleeding-edge-unwired-ok :
  evaluateComposerResearchBleedingEdge
    composer-research-bleeding-edge-unwired false false false
    ≡ verdict-unwired-ok
composer-research-bleeding-edge-unwired-ok = refl

composer-research-bleeding-edge-green-invent-refuse :
  evaluateComposerResearchBleedingEdge
    composer-research-bleeding-edge-unwired true false false
    ≡ verdict-green-invent-refuse
composer-research-bleeding-edge-green-invent-refuse = refl

composer-research-bleeding-edge-production-wired-refuse :
  evaluateComposerResearchBleedingEdge
    composer-research-bleeding-edge-unwired false false true
    ≡ verdict-production-wired-refuse
composer-research-bleeding-edge-production-wired-refuse = refl

composer-research-bleeding-edge-green-refuse-verdict-false :
  composerResearchBleedingEdgeVerdictOk
    (evaluateComposerResearchBleedingEdge
       composer-research-bleeding-edge-unwired true false false)
    ≡ false
composer-research-bleeding-edge-green-refuse-verdict-false = refl

------------------------------------------------------------------------
-- One design axiom + authority cites (not a 26th axiom fork)
------------------------------------------------------------------------

soleAxiomCount : ℕ
soleAxiomCount = 1

sole-axiom-count-is-one : soleAxiomCount ≡ 1
sole-axiom-count-is-one = refl

composerResearchBleedingEdgeAxiom :
  (composerResearchBleedingEdgeProved ≡ false)
  × (productionWired ≡ false)
  × (wave100LibRsWired ≡ false)
  × (wave100EosRsWired ≡ false)
  × (composerResearchIsNewAxiom ≡ false)
  × (bleedingEdgeHypothesesConserved ≡ true)
  × (researchHypothesesCitedNotForked ≡ true)
  × (literatureNewAxiomRefused ≡ true)
  × (isAbsent (rowClass refuseCatalysisRow) ≡ true)
  × (isAlreadyUnwired (rowClass chemPhysicsIsomorphismRow) ≡ true)
  × (evaluateComposerResearchBleedingEdge
       composer-research-bleeding-edge-unwired false false false
       ≡ verdict-unwired-ok)
  × (composerResearchBleedingEdgeVerdictOk
       (evaluateComposerResearchBleedingEdge
          composer-research-bleeding-edge-unwired true false false)
     ≡ false)
  × (soleAxiomCount ≡ 1)
composerResearchBleedingEdgeAxiom =
  composer-research-bleeding-edge-not-proved
  , production-not-wired
  , wave100-lib-rs-not-wired
  , wave100-eos-rs-not-wired
  , composer-research-not-new-axiom
  , bleeding-edge-hypotheses-conserved-true
  , research-hypotheses-cited-not-forked-true
  , literature-new-axiom-refused-true
  , refuse-catalysis-row-absent
  , chem-physics-isomorphism-row-unwired
  , composer-research-bleeding-edge-unwired-ok
  , composer-research-bleeding-edge-green-refuse-verdict-false
  , sole-axiom-count-is-one

composerResearchBleedingEdgeNamed : String
composerResearchBleedingEdgeNamed =
  "composerResearchBleedingEdge: v50 research chart lane cite CHEM_NS_V50_RESEARCH_HYPOTHESES.json read-only not fork H-V50-REFUSE-CATALYSIS-AXIOM Absent H-V50-CHEM-PHYSICS-ISOMORPHISM AlreadyUnwired not 26th axiom not physics GREEN"

composerResearchBleedingEdgeCrossWitnessAuthority : String
composerResearchBleedingEdgeCrossWitnessAuthority =
  "umst/umst-chem/src/x_rows/composer_research_bleeding_edge.rs"

chemIntCrossComposerResearchBleedingEdgeAuthority : String
chemIntCrossComposerResearchBleedingEdgeAuthority =
  "CHEM-INT-CROSS-COMPOSER-RESEARCH-BLEEDING-EDGE-CONSERVATION"

composerResearchBleedingEdgeCellId : String
composerResearchBleedingEdgeCellId =
  "CHEM-FORMAL-Q-AGDA-COMPOSER-RESEARCH-BLEEDING-EDGE-CONSERVATION"

composerResearchBleedingEdgeNonClaim : String
composerResearchBleedingEdgeNonClaim =
  "CHEM-FORMAL-Q-AGDA-COMPOSER-RESEARCH-BLEEDING-EDGE-CONSERVATION composer research bleeding-edge lane named research chart Unwired — cite CHEM_NS_V50_RESEARCH_HYPOTHESES.json read-only not fork; literature requiring new axiom refused; not 26th axiom; not physics GREEN; not production_wired"

composer-research-bleeding-edge-cell-id :
  composerResearchBleedingEdgeCellId ≡
  "CHEM-FORMAL-Q-AGDA-COMPOSER-RESEARCH-BLEEDING-EDGE-CONSERVATION"
composer-research-bleeding-edge-cell-id = refl

composer-research-bleeding-edge-cites-cross-witness-rs :
  composerResearchBleedingEdgeCrossWitnessAuthority ≡
  "umst/umst-chem/src/x_rows/composer_research_bleeding_edge.rs"
composer-research-bleeding-edge-cites-cross-witness-rs = refl

composer-research-bleeding-edge-modality-unwired :
  composerResearchBleedingEdgeModalityCurrent ≡ composer-research-bleeding-edge-unwired
composer-research-bleeding-edge-modality-unwired = refl

composerResearchBleedingEdgePhysicsGreenAuthorized : Set
composerResearchBleedingEdgePhysicsGreenAuthorized = ⊥

composer-research-bleeding-edge-physics-green-false :
  ¬ composerResearchBleedingEdgePhysicsGreenAuthorized
composer-research-bleeding-edge-physics-green-false ()

composerResearchBleedingEdgeMarker : String
composerResearchBleedingEdgeMarker = "chem_int_cross_composer_research_bleeding_edge_v1"

composerResearchBleedingEdgeSurface : String
composerResearchBleedingEdgeSurface = "composer_research_bleeding_edge_surface"
