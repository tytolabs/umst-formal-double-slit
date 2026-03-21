# Coq (integrated from `umst-formal`)

`LandauerEinsteinBridge.v` is the **standalone** SI + `E = mc²` mass-equivalent fragment (parameters + algebra). It matches the narrative in `../Lean/LandauerEinsteinBridge.lean`.

## Local check

From repo root:

```bash
make coq-check
```

Or manually:

```bash
cd Coq && coqc -Q . UMSTFormal LandauerEinsteinBridge.v
```

Requires **Coq** with `From Stdlib` (8.20+ style). Generated `*.glob` / `.*.aux` are gitignored.
