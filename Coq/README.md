<!--
SPDX-License-Identifier: MIT
Copyright (c) 2026 Santhosh Shyamsundar, Santosh Prabhu Shenbagamoorthy — Studio TYTO
-->

# Coq / Rocq (`Coq/`)

Integrated from `umst-formal`: gate admissibility, Landauér bridge, density-matrix specs, complementarity, and extraction to OCaml.

## Requirements

- **Rocq / Coq** **8.20+** or **9.x** with the **`From Stdlib`** library layout — **or** Ubuntu/Pop!_OS **apt** Coq **8.18**, which only provides the classic **`From Coq`** paths (this workspace’s pinned `*.v` use **`From Coq`** so `make coq-check` works on noble without opam).

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

`VonNeumannEntropySpec.v` uses explicit **`Axiom`**s for two real-analysis facts (`shannon_binary_le_ln2`, `negMulLog_zero_interval`) and spectral entropy; there are **no** `Admitted` obligations. See **`PROOF-STATUS.md`**.
