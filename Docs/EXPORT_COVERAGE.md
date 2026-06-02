# Lean export coverage (UMST formal stack)

Last audited: 2026-05-21. Canonical pin for **umst-manifold**: Python `export_catalog.py` → `artifacts/catalog.json` + `artifacts/catalog.lock.json`.

See also [`UMST_FORMAL_REPOS_ALIGNMENT.md`](UMST_FORMAL_REPOS_ALIGNMENT.md) for repo roles, [`../../umst-manifold/docs/CATALOG_COVERAGE_AUDIT.md`](../../umst-manifold/docs/CATALOG_COVERAGE_AUDIT.md) for Rust runtime wiring, and [`../../umst-manifold/docs/GOD_GRADE_WITNESS_LADDER.md`](../../umst-manifold/docs/GOD_GRADE_WITNESS_LADDER.md) for witness order (CD → Landauer → constitutive → probe) and v1/v2 trace contracts.

---

## Downstream manifold integration (narrative)

**umst-formal-double-slit** owns the export functor **F** into manifold’s trusted catalog pin. Manifold does **not** import Lean proof terms; it imports **F’s certificate**: `catalog_digest_hex`, `module_count`, and (at build time) the SHA-256 of manifold’s own `artifacts/catalog.lock.json` bytes.

| Stage | Artifact / command | Witness ladder |
|-------|-------------------|----------------|
| Regenerate export (unified) | `APPROVE_CROSS_REPO_MERGE=1` + `--also-lean-root` (below) | — |
| Primary-only regen | `make lean-catalog-export` | — |
| Primary lock (this repo) | `artifacts/catalog.lock.json` | — |
| Downstream lock | `umst-manifold/artifacts/catalog.lock.json` (`upstream_catalog_digest_hex`) | **R0** |
| Build embed | `build.rs` → `UMST_CATALOG_LOCK_SHA256_HEX` | **R0** |
| Stack verify | `UMST_REQUIRE_FORMAL_EXPORT=1 ../umst-manifold/scripts/verify_umst_stack.sh` | **R0** + gate parity |
| Runtime gates | `ThermodynamicTransitionEvaluator`, `ThermodynamicCBF`, mix registry | **R1–R4** (hand-aligned to roots in § 59 roots) |
| Optional digest reject | `formal-witness` feature, `tests/formal_witness.rs` | **R5 v1** |
| Trace schema (future CI) | `EpistemicRuntimeSchemaContract` / `EmittedTraceSchema` | **R5 v2** / **R6** |

**Operational rule:** Treat `catalog.json` like a **semver’d dependency**. Bump digest only with: regen here → update manifold `upstream_catalog_digest_hex` + `module_count` if changed → green `verify_umst_stack.sh` / `umst-catalog-drift.yml`. Details: [`../../umst-manifold/docs/FORMAL_BIDIRECTIONAL_ALIGNMENT.md`](../../umst-manifold/docs/FORMAL_BIDIRECTIONAL_ALIGNMENT.md).

**Hot path vs pin scope:** [`../../umst-manifold/docs/FORMAL_INTEGRATION_STATUS.md`](../../umst-manifold/docs/FORMAL_INTEGRATION_STATUS.md) documents ~**18** Lean modules with hand-aligned Rust (~26% of primary **69**). The unified pin (**119** modules) still changes **R0** when any scanned `.lean` in either fiber edits — CI drift is inventory hygiene, not “only hot modules matter.”

---

## Two exporters (do not conflate)

| Tool | Command | Output shape | Count | Consumer |
|------|---------|--------------|-------|----------|
| **Python** | Production merge command (below) or `make lean-catalog-export` | `{ version, lean_root(s), modules[], module_graph_edges[], digest }` | **119** unified / **69** primary-only | **umst-manifold** digest drift check, `build.rs` lock |
| **Lake** | `cd Lean && lake exe export_catalog` | `{ version, entries[{ id, module, kind, name }] }` | **59** (pinned `roots` only) | Rust / docs wanting `UMST.DoubleSlit.*` ids |

**Rule:** CI and manifold use **Python only** on `artifacts/catalog.json`. If you run the Lake executable, write to a different path (e.g. `artifacts/catalog.roots.json`) or regenerate Python immediately.

---

## The “69” vs “59” vs “119” split

| Count | Meaning |
|-------|---------|
| **59** | `lakefile.lean` `roots` (default `lake build` / Lake `export_catalog` exe) |
| **69** | Primary tree only — every `Lean/**/*.lean` under double-slit (incl. tests not in `roots`) |
| **119** | **Production unified pin** — primary **69** + **50** non-overlapping `umst-formal` modules (basename overlap **12**; primary wins) |

**10** files explain **69 − 59** on the primary tree: `lakefile`, `Test3`–`TestMixed`, `test_tensor_eigen`, `LogSum`, `MatrixLog`, `FlashMoERuntimeScaffold`. All **59 production roots** appear in both Lake and Python scans.

**Pitfall we closed:** Running `cd Lean && lake exe export_catalog` into `artifacts/catalog.json` silently replaced the Python catalog and broke manifold digest checks. **Fix:** Python-only on `catalog.json`; Lake output → `artifacts/catalog.roots.json` (or separate path). See [`../artifacts/README.md`](../artifacts/README.md).

**Dev-only:** `--cross-repo-only` emits `catalog-cross-repo-preview.json` without touching pins — local inspection only; not CI.

---

## Digest pin impact

The digest is SHA-256 (hex) of the JSON catalog body **before** the `digest` key (`sort_keys=True`, compact separators). It is **content-addressed proof inventory**, not a runtime gate score.

| Change type | Effect on manifold |
|-------------|-------------------|
| Any scanned `.lean` edit in either merged fiber | New `catalog_digest_hex` → must update `umst-manifold` `upstream_catalog_digest_hex` |
| Add/remove a scanned file | `module_count` changes → lock `module_count` must match |
| Regen without lock bump | `verify_umst_stack.sh` / `umst-catalog-drift.yml` **fail** (R0 reject) |
| Rebuild manifold after lock bump | New `UMST_CATALOG_LOCK_SHA256_HEX` constant in binaries |
| `FormalFoundations.umst_double_slit_formal_complete` | **Digest pin only** in Rust — no completeness replay ([`../../umst-manifold/docs/claims-vs-proofs.md`](../../umst-manifold/docs/claims-vs-proofs.md)) |

**Categorical reading (witness ladder):** Digest pin is **R0** — export functor `F: \mathbf{Lean} \to \mathbf{CatalogPin}`. Gates **R1–R4** are separate endomorphisms; a green R0 does not imply every module is enforced on the hot path.

---

## Witness ladder cross-links (export repo ↔ manifold)

Normative order and failure priority: [`../../umst-manifold/docs/GOD_GRADE_WITNESS_LADDER.md`](../../umst-manifold/docs/GOD_GRADE_WITNESS_LADDER.md).

| Rung | Manifold doc anchor | Lean / export anchor (this repo) |
|------|---------------------|----------------------------------|
| **R0** | [`GOD_GRADE_WITNESS_LADDER.md` § R0](../../umst-manifold/docs/GOD_GRADE_WITNESS_LADDER.md#r0--catalog-lock-build-time-functor) | Unified export + `artifacts/catalog.lock.json`, `FormalFoundations` (pin theorem) |
| **R1** | CD / 2nd law | `Gate`, `UMSTCore`, `GateCompat`, `Naturality`, … (`umst.gate.cd_transition`) |
| **R2** | Landauer CBF | `LandauerLaw`, `LandauerBound`, `EpistemicMI`, `MeasurementCost`, … |
| **R3** | Constitutive mix | `Activation`, `FiberedActivation`, `ProbeOptimization` (policy), cartridge-facing lemmas |
| **R4** | Probe Kleisli | `Gate.kleisliAdmissibility`, `EpistemicPolicy` (not RL PPO) |
| **R5 v1** | Manifest + digest | `EpistemicRuntimeContract` — optional `formal-witness` in manifold |
| **R5 v2 / R6** | Trace schema | `EpistemicRuntimeSchemaContract`, `EpistemicPerStepNumerics`, telemetry contracts |

Checklist and CI matrix: [`../../umst-manifold/docs/GOD_GRADE_CHECKLIST.md`](../../umst-manifold/docs/GOD_GRADE_CHECKLIST.md). Row-level ledger: [`../../umst-manifold/docs/claims-vs-proofs.md`](../../umst-manifold/docs/claims-vs-proofs.md).

---

## Compositional layers vs catalog

Legend: **In DS** = present in umst-formal-double-slit. **In UF** = umst-formal only (now in unified pin when not basename-overlapped). **Manifold** = `umst-manifold/docs/claims-vs-proofs.md` `catalog_id`.

| Layer | Key Lean artefacts | In DS | In UF | Manifold `catalog_id` |
|-------|------------------|-------|-------|------------------------|
| **Kleisli (list / graded)** | `Gate.kleisliAdmissibility`, `admissibleN_compose` | Yes (`Gate`) | Yes (`Gate`, `Constitutional`, `Economic.KleisliAdmissibilityComposition`) | `umst.gate.kleisli_unit` |
| **DIB Kleisli monad** | `DIBKleisli`: `M`, monad laws | **No** | Yes | `umst.gate.kleisli_unit` (hand-aligned) |
| **Hydration** | `forwardHydrationAdmissible`, `HydratCond`, `Activation.*_has_hydration` | Yes | Yes (`Powers`, `Gate`) | `umst.gate.cd_transition` |
| **Mass** | `MassCond`, `δMass`, `AdmissibleN` mass bound | Yes | Yes (`GraphProperties`) | `umst.gate.cd_transition` |
| **CD (Clausius–Duhem)** | `clausiusDuhemFwd`, `DissipCond`, `gateCheckSound` | Yes (`Gate`, `UMSTCore`) | Yes | `umst.gate.cd_transition` |
| **DPI (data processing)** | `DataProcessingInequality` | Yes | No | — (proved, no Rust id) |
| **PPO / probe policy** | `ProbeOptimization`, `EpistemicPolicy` (finite argmax, not RL PPO) | Yes | Partial (`Economic.EpistemicSensingModule`) | `umst.gate.landauer_cbf` + `kleisli_unit` via `ppo.rs` |

There is **no** Lean module named `PPO`; comments in `EpistemicTelemetryApproximation` refer to surrogate numerics only.

---

## umst-formal-double-slit: modules with proofs (59 roots)

Grouped by proof family (all in default `lake build`; see `PROOF-STATUS.md`):

- **Thermo gate:** `Gate`, `UMSTCore`, `Naturality`, `Activation`, `FiberedActivation`, `MonoidalState`, `GateCompat`, `QRBridge`, `LandauerLaw`, `LandauerExtension`, `LandauerEinsteinBridge`, `MeasurementCost`, `PhysicsConstrainedAI`, `InformationCostIdentity`
- **Quantum / double-slit:** `DensityState`, `MeasurementChannel`, `TensorPartialTrace`, `DoubleSlitCore`, `QuantumClassicalBridge`, `Complementarity`, `WhichPathMeasurementUpdate`, `DoubleSlit`, `GeneralVisibility`, `GeneralResidualCoherence`, `PMICVisibility`, `PMICEntropyInterior`, `SchrodingerDynamics`, `LindbladDynamics`, `LindbladStreamD`
- **Entropy / information:** `InfoEntropy`, `VonNeumannEntropy`, `KleinInequality`, `DataProcessingInequality`, `QuantumMutualInfo`, `KroneckerEigen`, `GeneralDimension`, `LandauerBound`, `ErasureChannel`
- **Epistemic stack:** `EpistemicSensing` … `EpistemicTraceDrivenCalibrationWitness`, `ProbeOptimization`, `EpistemicPolicy`, `EpistemicDynamics`, `EpistemicTrajectoryMI`, `EpistemicGalois`, `EpistemicRuntimeContract` + numerics/telemetry contracts, `PrototypeSolverCalibration`
- **Integration:** `ExamplesQubit`, `SimLeanBridge`, `FormalFoundations`

**Stats:** `python3 scripts/lean_declaration_stats.py` → **537** `theorem` + **34** `lemma` on roots only.

---

## umst-formal (sibling repo): unified into production pin

**62** `.lean` files scanned; **50** contribute unique basenames to the unified export (overlap **12** with double-slit; primary wins).

**Representative classical-only rows now in unified `catalog.json`:**

| Module | Why it matters |
|--------|----------------|
| `DIBKleisli` | DIB pipeline monad laws |
| `Constitutional` | `ConstitutionalSeq`, Kleisli arrows |
| `Powers` | Hydration–strength (Powers 1958) |
| `GraphProperties` | Counterexample to refutable `admissible_trans` |
| `Helmholtz`, `Convergence`, `SeparationBound`, … | Meso/macro gate theory |
| `DEC`, `Adjoint`, `RegimeSoundness`, … | DEC / physics operators |
| `Economic/*` (18 modules) | `KleisliAdmissibilityComposition`, burden, temperature, etc. |
| `Crypto/*`, `Behavior.SDFCanonical` | Optional `lake build` libs |

---

## What `export_catalog.py` includes

Per `build_catalog()`:

- Every `*.lean` under `--lean-root` (default `Lean/`)
- Skips `.lake` / `lake-packages`
- Per module: declaration names (regex), `import_lines`, `content_sha256`, optional `repo` tag when merged
- **Does not:** filter to `roots`, assign `catalog_id`, detect `sorry`, or resolve Mathlib

---

## Cross-repo export — production path (canonical)

Unified catalog is the **operator default** after Track F approval. Set **`APPROVE_CROSS_REPO_MERGE=1`** in the environment (not a repo-root marker file). Primary wins on basename overlap.

```bash
cd umst-formal-double-slit
APPROVE_CROSS_REPO_MERGE=1 python3 tools/lean_export/export_catalog.py \
  --lean-root Lean \
  --also-lean-root ../umst-formal/Lean \
  --also-lean-repo-tag umst-formal
```

| Flag / env | Meaning |
|------------|---------|
| `--also-lean-root` | Second Lean package root (e.g. `../umst-formal/Lean`) |
| `--also-lean-repo-tag` | Label on secondary modules (default `umst-formal`) |
| `--primary-repo-tag` | Label on primary modules (default `umst-formal-double-slit`) |
| `APPROVE_CROSS_REPO_MERGE=1` | Write unified `catalog.json` + `catalog.lock.json` |
| `--cross-repo-only` | **Dev only** — preview JSON only; no pin write |

**Merge policy:** Each module row gets a `repo` tag. On basename overlap (last dotted segment), **primary** wins. Unified digest uses the same SHA-256 rules as single-tree export.

**Primary-only regen** (reverts unified pin if run without `--also-lean-root`):

```bash
make lean-catalog-export   # 69 modules; do not use after unified promotion unless intentional
```

After unified export, bump `umst-manifold/artifacts/catalog.lock.json` and green `verify_umst_stack.sh` ([`../../umst-manifold/docs/FORMAL_FIBER_MERGE_RUNBOOK.md`](../../umst-manifold/docs/FORMAL_FIBER_MERGE_RUNBOOK.md)).

---

## Last production merge (2026-05-21)

Recorded after merge agent completed unified export in `umst-formal-double-slit` (manifold lock bump may lag until Phase 3 of runbook).

| Field | Value |
|-------|-------|
| `catalog_digest_hex` / `merged_digest_hex` | `0697014fb5b90a3aca4db3e5cc226896ca198802c910d5395f254e4262aa6227` |
| `module_count` (unified) | **119** |
| `cross_repo_merge` | `true` |
| Primary modules (`umst-formal-double-slit`) | **69** |
| Secondary modules (`umst-formal`) | **62** |
| `overlap_basename_count` | **12** |
| `only_in_secondary_basename` | **50** |
| `primary_digest_hex` (primary-only snapshot) | `c1d9ba2aa402106a3477f454dd6d28015eb399c1160d8a2e2ba7d16788fdbfcc` |
| `secondary_digest_hex` (secondary-only snapshot) | `534d9e181fd2af301a319b4a6a645e665d7896b2b7e0302a9ffa29a6d52d454c` |

**Overlap basenames (primary wins):** `Activation`, `FiberedActivation`, `FormalFoundations`, `Gate`, `LandauerEinsteinBridge`, `LandauerExtension`, `LandauerLaw`, `MeasurementCost`, `MonoidalState`, `Naturality`, `PhysicsConstrainedAI`, `lakefile`.

**Manifold R0:** `umst-manifold/artifacts/catalog.lock.json` pinned to `upstream_catalog_digest_hex` = `0697014f…` and `module_count: 119` (2026-05-21); `verify_umst_stack.sh` green with sibling `umst-formal`.

---

## Gaps and exporter fix suggestions

1. **Schema collision** — Lake exe overwrites Python `catalog.json`. **Fix:** separate paths or Makefile guard; document in `artifacts/README.md`.
2. **Makefile target** — `make lean-catalog-export` is still primary-only; add `lean-catalog-export-unified` or document production command above as SSOT.
3. **`--roots-only` (optional)** — Emit `module_count: 59` for subset pins.
4. **Exclude noise** — `lakefile.lean`, `Test*.lean`, `test_*.lean` via `--exclude-glob`.
5. **Enrich records** — `in_lake_roots`, `theorem_count`, `lemma_count`, `axiom_count`, `sorry_count`.
6. **Stable ids** — Add optional `catalog_id` from `umst-manifold/docs/claims-vs-proofs.md`.
7. **Align Lake exporter** — Write `UMST.DoubleSlit.<name>` into Python `modules[].module` or emit sidecar `catalog.roots.json` only.

---

## Recommended workflow

```bash
# umst-formal-double-slit — unified production pin
cd umst-formal-double-slit
APPROVE_CROSS_REPO_MERGE=1 python3 tools/lean_export/export_catalog.py \
  --lean-root Lean \
  --also-lean-root ../umst-formal/Lean \
  --also-lean-repo-tag umst-formal
python3 -c "import json; c=json.load(open('artifacts/catalog.json')); l=json.load(open('artifacts/catalog.lock.json')); assert l['module_count']==len(c['modules']); assert l['catalog_digest_hex']==c['digest']"

# umst-manifold — after lock bump
cd ../umst-manifold && UMST_REQUIRE_FORMAL_EXPORT=1 ./scripts/verify_umst_stack.sh
```

Do **not** run `lake exe export_catalog` onto `artifacts/catalog.json` unless you intentionally replace the Python artifact and re-pin manifold.
