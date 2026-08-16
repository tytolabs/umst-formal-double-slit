SPDX-FileCopyrightText: 2026 Santosh Prabhu Shenbagamoorthy and Santhosh Shyamsundar
SPDX-License-Identifier: MIT
# UMST formal repositories — alignment

**Workspace:** multi-repo sibling checkout (local)  
**Date:** 2026-05-21  
**Repos:** [`umst-formal`](../../umst-formal) · [`umst-formal-double-slit`](../) (this tree)

Both repositories exist as sibling checkouts under the workspace root. They are **complementary**, not duplicates of the same artifact.

**God-grade fiber policy:** Double-slit owns the **primary** export functor into manifold; `umst-formal` is the **second catalog fiber** (classical/DEC/Economic lemmas without `catalog.json`). Witness ladder: [`../../umst-manifold/docs/GOD_GRADE_WITNESS_LADDER.md`](../../umst-manifold/docs/GOD_GRADE_WITNESS_LADDER.md). Pipeline: [`../../umst-manifold/docs/FORMAL_BIDIRECTIONAL_ALIGNMENT.md`](../../umst-manifold/docs/FORMAL_BIDIRECTIONAL_ALIGNMENT.md).

### Downstream manifold integration (summary)

Manifold treats this repo’s export as a **versioned proof library** (R0), then applies **gate law** witnesses (R1–R4) in fixed short-circuit order — not Lean replay at runtime.

```text
umst-formal-double-slit/Lean/*.lean
  → make lean-catalog-export (Python, 69 modules)
  → artifacts/catalog.json + catalog.lock.json
  → umst-manifold/artifacts/catalog.lock.json (upstream_catalog_digest_hex)
  → build.rs (UMST_CATALOG_LOCK_SHA256_HEX)
  → runtime/catalog/, GateEvaluator, CBF, formal-witness (R5 v1)
```

Full narrative, digest-impact table, and R0–R6 module mapping: [`EXPORT_COVERAGE.md`](EXPORT_COVERAGE.md). Runtime bucket split (~26% hot path): [`../../umst-manifold/docs/FORMAL_INTEGRATION_STATUS.md`](../../umst-manifold/docs/FORMAL_INTEGRATION_STATUS.md).

---

## 1. Roles

| Repository | Package / lib | Primary scope |
|------------|---------------|---------------|
| **`umst-formal`** | Lake package `umst-formal`, lib `UMST` | Classical UMST gate (ℚ `ThermodynamicState`, `Admissible`), constitutional/Kleisli, Landauer stack, **Economic/** meso-layer, cartridge anchors (`DEC`, `Powers`, `RegimeSoundness`, …), crypto/memory stubs. Multi-language: Lean + Coq + Agda + Haskell + FFI. |
| **`umst-formal-double-slit`** | Lake package `umst-formal-double-slit`, lib `UMST.DoubleSlit` | Quantum measurement layer: density matrices, Kraus/Lüders, Englert complementarity, epistemic runtime contracts, Lindblad/Schrödinger formal hooks, Python/Haskell sims. **Vendors** a subset of the classical gate/Landauer Lean stack from upstream. |

Upstream pointer is documented in [`README.md`](../README.md) (Related code table) and [`CHANGELOG.md`](../CHANGELOG.md) § “integrated from upstream framework”.

---

## 2. Which repo feeds `export_catalog.py`?

**Only `umst-formal-double-slit`.**

| Item | Location |
|------|----------|
| Exporter | `tools/lean_export/export_catalog.py` |
| Lake exe (alternate shape) | `tools/lean_export/ExportCatalog.lean` → `lake exe export_catalog` |
| Default invocation | `make lean-catalog-export` → scans `--lean-root Lean` |
| Artifacts | `artifacts/catalog.json`, `artifacts/catalog.lock.json` (69 modules; digest `c1d9ba2aa402106a3477f454dd6d28015eb399c1160d8a2e2ba7d16788fdbfcc` at time of survey) |

**`umst-formal` has no `export_catalog.py`, no `artifacts/catalog.json`, and no catalog lock.** Its Lean inventory is tracked via `PROOF-STATUS.md` and `python3 scripts/lean_declaration_stats.py` (51 `lakefile` roots; 237 theorem + 24 lemma per status doc).

### Downstream consumers of the catalog

| Consumer | How it uses double-slit export |
|----------|--------------------------------|
| **`umst-manifold`** | Pins `upstream_catalog_digest_hex` in `artifacts/catalog.lock.json`; `build.rs` → `UMST_CATALOG_LOCK_SHA256_HEX`. Traceability: `docs/claims-vs-proofs.md`, [`CATALOG_COVERAGE_AUDIT.md`](../../umst-manifold/docs/CATALOG_COVERAGE_AUDIT.md). |
| **`scripts/verify_umst_stack.sh`** | Resolves `UMST_FORMAL_ROOT` or `../umst-formal-double-slit`, runs `export_catalog.py`, compares digest to manifold lock. |
| **CI** | `.github/workflows/umst-catalog-drift.yml` (monorepo) expects both trees present. |

Rust anchors to **`lean://umst-formal/...`** (e.g. `umst-concrete-cartridge`) are **separate** from the catalog digest pin; they reference the classical repo paths directly, not `catalog.json`.

### Digest pin impact (primary fiber only)

| Event | Required action |
|-------|-----------------|
| Lean edit in double-slit (any scanned `.lean`, incl. tests) | `make lean-catalog-export`; commit `catalog.json` + `catalog.lock.json` |
| Digest or `module_count` changed | Update `umst-manifold/artifacts/catalog.lock.json` (`upstream_catalog_digest_hex`, `module_count`) |
| Manifold consumers | `cargo build` in manifold (new `UMST_CATALOG_LOCK_SHA256_HEX`); `UMST_REQUIRE_FORMAL_EXPORT=1 ./scripts/verify_umst_stack.sh` |
| Cross-repo preview only | `catalog-cross-repo-preview.json` — **no** manifold pin change until `lean-export-cross-repo` milestone closes |

**Learning:** The pin fingerprints **all 69** export rows. Manifold enforces **~18** modules on the gate hot path; the other **51** rows still matter for drift detection and proof-inventory SSOT ([`../../umst-manifold/docs/FORMAL_INTEGRATION_STATUS.md`](../../umst-manifold/docs/FORMAL_INTEGRATION_STATUS.md)). `FormalFoundations.umst_double_slit_formal_complete` is **digest pin only** in Rust — not a runtime completeness check.

**Witness ladder:** R0 = this digest; R1–R4 = vendored `Gate` / `Landauer*` / mix / Kleisli families (see [`../../umst-manifold/docs/GOD_GRADE_WITNESS_LADDER.md`](../../umst-manifold/docs/GOD_GRADE_WITNESS_LADDER.md)); classical-only lemmas stay in **`umst-formal`** until unified export.

---

## 3. Lean inventory (counts)

| Metric | `umst-formal` | `umst-formal-double-slit` |
|--------|---------------|---------------------------|
| `*.lean` under `Lean/` (survey) | 62 files | 69 files in catalog export |
| `lake build` roots | **51** (`Lean/lakefile.lean`) | **59** proof roots + tests/scratch excluded from default build |
| Catalog export scope | N/A | **69** modules (includes `lakefile`, `Test*`, optional `LogSum`/`MatrixLog`, `test_tensor_eigen`, `FlashMoERuntimeScaffold`) — see [69 vs 59](#69-vs-59-learnings) |
| Lean `axiom` | `physicalSecondLaw` (`LandauerLaw.lean`) | Same single project axiom |
| `sorry` | 0 (per `PROOF-STATUS.md`) | 0 (per `PROOF-STATUS.md`) |
| Declaration stats (roots) | 237 `theorem` + 24 `lemma` | 537 `theorem` + 34 `lemma` |

Proof status indexes:

- `umst-formal/PROOF-STATUS.md`
- `umst-formal-double-slit/PROOF-STATUS.md`

### 69 vs 59 learnings

| Count | Meaning | Consumer |
|-------|---------|----------|
| **59** | `lakefile.lean` `roots` — default `lake build` / proof-status headline | Lean CI, `PROOF-STATUS.md`, Lake `export_catalog` **roots** |
| **69** | Python scan of all `Lean/**/*.lean` | **umst-manifold** `upstream_catalog_digest_hex`, `module_count` |
| **+10** | Non-root files in 69-only set | Intentional: test/scratch drift visible in R0 pin |

**Policy:** Manifold and stack verify use **Python / 69** only. Do not point CI at Lake’s 59-entry JSON on `artifacts/catalog.json`. Vendored modules from `umst-formal` count toward **59** roots here but **`umst-formal`** lemmas outside the vendored set are **not** in the 69 digest until cross-repo export merges ([`EXPORT_COVERAGE.md`](EXPORT_COVERAGE.md) § cross-repo scaffold).

---

## 4. Overlap — vendored Lean modules (same basename)

These **10** modules exist in **both** `Lean/` trees. Double-slit **`lakefile.lean`** lists them as “integrated from upstream framework” (ℚ gate + Landauer stack):

| Module | In `umst-formal` roots? | In double-slit roots? | Notes |
|--------|-------------------------|------------------------|-------|
| `Gate.lean` | Yes | Yes | Same lineage; double-slit copy adds SPDX header — **not byte-identical** to upstream. |
| `Naturality.lean` | Yes | Yes | Vendored copy; may drift. |
| `Activation.lean` | Yes | Yes | Vendored copy. |
| `FiberedActivation.lean` | Yes | Yes | Vendored copy. |
| `MonoidalState.lean` | Yes | Yes | Vendored copy. |
| `LandauerLaw.lean` | Yes | Yes | Shared `physicalSecondLaw` axiom. |
| `LandauerExtension.lean` | Yes | Yes | Vendored copy. |
| `LandauerEinsteinBridge.lean` | Yes | Yes | Vendored copy. |
| `MeasurementCost.lean` | Yes | Yes | Vendored copy. |
| `FormalFoundations.lean` | Yes | Yes | **Different closure theorems** (double-slit: `umst_double_slit_formal_complete`; formal: broader UMST foundations). |

**Related but not duplicate paths**

| Upstream (`umst-formal`) | Double-slit | Relationship |
|--------------------------|-------------|--------------|
| `InfoTheory.lean` | `InfoEntropy.lean` | Parallel Shannon/product laws |
| `Economic/PhysicsConstrainedAI.lean` | `PhysicsConstrainedAI.lean` (root) | Different module path |
| `Helmholtz.lean`, `Powers.lean`, `Constitutional.lean`, … | — | **Formal-only** |
| `UMSTCore.lean` | — | **Double-slit-only** classical ℝ gate slice |

---

## 5. Duplicates policy

| Kind | Policy |
|------|--------|
| **Vendored Lean (10 modules)** | Intentional **fork-in-place** for self-contained `lake build` in double-slit. **Source of truth for gate/Landauer ℚ core:** `umst-formal`. Sync via manual/changelog merges. |
| **Coq / Agda** | Double-slit ships **smaller** vendored subsets. Formal has wider Coq (`Constitutional`, `Extraction`, …). |
| **Catalog JSON** | **Single** canonical export: double-slit only. Do not expect `umst-formal` to produce `catalog.json`. |
| **Manifold `catalog_id`s** | Map to theorem **families** in double-slit Lean; some rows cite parallel `umst-formal` modules (`Gate`, `DIBKleisli`, `DEC`) for cement/DEC anchors. |

---

## 6. `umst-formal` — Lean modules **not** in double-slit

Representative **formal-only** areas:

- **Constitutional / Kleisli:** `Constitutional.lean`, `DIBKleisli.lean`, `GaloisGate.lean`, `EnrichedAdmissibility.lean`
- **Material science:** `Helmholtz.lean`, `Powers.lean`, `JenningsGelSpace.lean`, `RegimeSoundness.lean`, …
- **Economic/** (18 modules): burden, hallucination detector, NPV thermodynamic bridge, etc.
- **Infrastructure:** `DEC.lean`, `Adjoint.lean`, `Crypto/*`, `Memory/*`, `Behavior/SDFCanonical.lean`
- **Scratch:** `_check_ext.lean`, `scripts/print_axioms.lean`, `experiments/AutoExperimenterPlaceholder.lean`

---

## 7. `umst-formal-double-slit` — Lean modules **not** in formal

Quantum / epistemic / sim formal layer (59 roots), including: `UMSTCore`, `DensityState`, `MeasurementChannel`, `DoubleSlitCore`, `DoubleSlit`, `Complementarity`, `QuantumClassicalBridge`, `LandauerBound`, `Epistemic*`, `VonNeumannEntropy`, `DataProcessingInequality`, `KleinInequality`, `LindbladDynamics`, `GateCompat`, `QRBridge`, `SimLeanBridge`, …

**Exported but not in default `lake build` roots:** `Test3`–`TestMixed`, `test_tensor_eigen`, `LogSum`, `MatrixLog`, `FlashMoERuntimeScaffold` (still appear in `catalog.json`).

---

## 8. Cross-language inventory (summary)

| Layer | `umst-formal` | `umst-formal-double-slit` |
|-------|---------------|---------------------------|
| **Coq** | ~9 `.v` modules + extraction | ~9 `.v` specs (subset + quantum specs) |
| **Agda** | 8 `.agda` sources | 11 entry modules per `PROOF-STATUS.md` |
| **Haskell** | `umst-formal.cabal`, FFI bridge | `umst-formal-double-slit.cabal`, QC mirrors |
| **Python** | — | `sim/` + tests |

---

## 9. Maintenance workflow

1. **Classical gate / Landauer changes** → edit `umst-formal/Lean/{Gate,Landauer*,Activation,...}.lean`, `lake build`, then **port** to double-slit vendored copies if quantum build must stay aligned.
2. **Quantum / epistemic changes** → edit only double-slit; run `cd Lean && lake build`.
3. **Manifold catalog pin** → from double-slit root: `make lean-catalog-export`; copy digest to `umst-manifold/artifacts/catalog.lock.json`; run `umst-manifold/scripts/verify_umst_stack.sh`.
4. **Declaration counts** → each repo: `python3 scripts/lean_declaration_stats.py`.

---

## 10. Quick reference

| Question | Answer |
|----------|--------|
| Is `umst-formal` missing? | **No** — present at workspace sibling path. |
| Who owns `export_catalog.py`? | **`umst-formal-double-slit` only.** |
| Who consumes the catalog? | **`umst-manifold`** (digest lock); verify script; CI drift workflow. |
| Where is cement/DEC proof anchor? | **`umst-formal`** (`lean://umst-formal/...` in cartridge docs). |
| Where is double-slit / CBF anchor? | **`umst-formal-double-slit`** + manifold `catalog_id` map. |

---

*See also [`EXPORT_COVERAGE.md`](EXPORT_COVERAGE.md) (downstream manifold narrative, digest pin, witness cross-links); [`../../umst-manifold/docs/GOD_GRADE_WITNESS_LADDER.md`](../../umst-manifold/docs/GOD_GRADE_WITNESS_LADDER.md) (R0–R6, failure priority, v1/v2); [`../../umst-manifold/docs/FORMAL_BIDIRECTIONAL_ALIGNMENT.md`](../../umst-manifold/docs/FORMAL_BIDIRECTIONAL_ALIGNMENT.md); [`../../umst-manifold/docs/CATALOG_COVERAGE_AUDIT.md`](../../umst-manifold/docs/CATALOG_COVERAGE_AUDIT.md).*
