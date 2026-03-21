<!--
SPDX-License-Identifier: MIT
Copyright (c) 2026 Santhosh Shyamsundar, Santosh Prabhu Shenbagamoorthy — Studio TYTO
-->

# Coq / Rocq (`Coq/`)

Integrated from `umst-formal`: gate admissibility, Landauér bridge, density-matrix specs, complementarity, and extraction to OCaml.

## Requirements

- **Rocq / Coq** **8.20+** or **9.x** with the **`From Stdlib`** library layout (not legacy `Coq` top-level paths for the files that use `From Stdlib`).

## Local check

From repo root:

```bash
make coq-check
```

This compiles **all** `*.v` files in import order:

`LandauerEinsteinBridge.v` → `DensityStateSpec.v` → `ComplementaritySpec.v` → `VonNeumannEntropySpec.v` → `MeasurementCost.v` → `InfoTheory.v` → `Gate.v` → `Extraction.v` → `Constitutional.v`

Combined with Agda:

```bash
make formal-check
./scripts/formal_check.sh
```

## `_CoqProject` and `coq_makefile` (optional)

`Coq/_CoqProject` lists the logical path `-Q . UMSTFormal` and all modules. To generate a native Coq makefile (e.g. for larger developments):

```bash
cd Coq && coq_makefile -f _CoqProject -o Makefile.coq && make -f Makefile.coq
```

The repo’s canonical developer entry point remains **`make coq-check`** from the root.

## Extraction

`Extraction.v` writes `gate_extracted.ml` / `.mli` under **`Coq/_extract/`** (gitignored). See comments in that file for `ocamlfind` build hints.

## Proof status

`VonNeumannEntropySpec.v` intentionally contains **`Admitted`** placeholders (binary Shannon bound and a diagonal-entropy corner case); everything else in the tree above is intended to compile without admits. See **`PROOF-STATUS.md`**.
